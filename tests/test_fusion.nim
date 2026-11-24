## Loop fusion for the plain residual VectorOps lowering.

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times, tables]

type
  Vector[T] = Arr[T]
  Kind = enum skInput, skLen, skZeros, skPlus, skFill, skZip
  Node = ref object of IRNode
    kind: Kind
    name: string
    data: seq[float]
    n: Rep[int]
    left, right, source: Arr[float]
    inline: bool

proc arrayLengthText(a: Arr[float]): string

proc intText(x: Rep[int]): string =
  if x.isStatic: return $x.staticVal
  let n = Node(x.node)
  doAssert n.kind == skLen
  "len(" & arrayLengthText(n.source) & ")"

proc arrayLengthText(a: Arr[float]): string =
  let n = Node(a.node)
  if n.kind == skInput: return n.name
  doAssert n.kind == skFill or n.kind == skZip
  if n.n.isStatic: return $n.n.staticVal
  let lengthNode = Node(n.n.node)
  doAssert lengthNode.kind == skLen
  arrayLengthText(lengthNode.source)

var genSerial = 0
proc freshName(base: string): string =
  inc genSerial
  base & $genSerial

proc vecZeros(n: Rep[int]): Arr[float] =
  newArray[float](n, proc(n: Rep[int]): IRNode = Node(kind: skZeros, n: n))

proc vecPlus(a, b: Arr[float]): Arr[float] =
  if Node(a.node).kind == skZeros: return b
  if Node(b.node).kind == skZeros: return a
  newArray[float](lenArr[float](a, proc(a: Arr[float]): IRNode =
    Node(kind: skLen, source: a)), proc(n: Rep[int]): IRNode =
      Node(kind: skPlus, n: n, left: a, right: b))

proc lowerVectors(v: Arr[float]): Arr[float] =
  let n = Node(v.node)
  case n.kind
  of skZeros:
    newArray[float](n.n, proc(nlen: Rep[int]): IRNode =
      Node(kind: skFill, name: freshName("zeros"), n: nlen))
  of skPlus:
    let a = lowerVectors(n.left); let b = lowerVectors(n.right)
    let ln = lenArr[float](a, proc(x: Arr[float]): IRNode =
      Node(kind: skLen, source: x))
    newArray[float](ln, proc(nlen: Rep[int]): IRNode =
      Node(kind: skZip, name: freshName("plus"), n: nlen, left: a, right: b))
  else:
    v

proc isElementwise(v: Arr[float]): bool =
  let kind = Node(v.node).kind
  kind == skFill or kind == skZip

proc sameLength(a, b: Arr[float]): bool =
  let na = Node(a.node); let nb = Node(b.node)
  isElementwise(a) and isElementwise(b) and intText(na.n) == intText(nb.n)

proc useCount(v: Arr[float], wanted: string): int =
  let n = Node(v.node)
  if n.kind == skZip:
    if Node(n.left.node).name == wanted: inc result
    if Node(n.right.node).name == wanted: inc result
    result += useCount(n.left, wanted)
    result += useCount(n.right, wanted)

proc fuseLoops(v, whole: Arr[float]): Arr[float] =
  ## Bottom-up: each eligible producer is marked inline only after its own
  ## children have been considered.  The output-use count is over all edges
  ## in the lowered graph, so shared producers remain materialized.
  let n = Node(v.node)
  if n.kind != skZip: return v
  discard fuseLoops(n.left, whole)
  discard fuseLoops(n.right, whole)
  for operand in [n.left, n.right]:
    let producer = Node(operand.node)
    if isElementwise(operand) and not producer.inline and
       useCount(whole, producer.name) == 1 and sameLength(operand, v):
      producer.inline = true
  v

proc emitElement(v: Arr[float], index: string): string =
  let n = Node(v.node)
  case n.kind
  of skInput: n.name & "[" & index & "]"
  of skFill: "0.0"
  of skZip: "(" & emitElement(n.left, index) & " + " &
    emitElement(n.right, index) & ")"
  else: doAssert false; ""

proc emitDeps(v: Arr[float]; seen: var Table[string, bool]): string =
  let n = Node(v.node)
  case n.kind
  of skInput:
    if seen.getOrDefault(n.name): return ""
    seen[n.name] = true
    "var " & n.name & ": seq[float] = " & $n.data
  of skZip:
    emitDeps(n.left, seen) & "\n" & emitDeps(n.right, seen)
  else: ""

proc emitArray(v: Arr[float]; seen: var Table[string, bool]): string =
  let n = Node(v.node)
  if n.kind == skInput: return emitDeps(v, seen)
  if n.kind == skFill:
    if n.inline or seen.getOrDefault(n.name): return ""
    seen[n.name] = true
    return "var " & n.name & " = newSeq[float](" & intText(n.n) & ")\n" &
      "var " & n.name & "Index = 0\nwhile " & n.name & "Index < len(" & n.name & "):\n" &
      "  " & n.name & "[" & n.name & "Index] = 0.0\n" &
      "  " & n.name & "Index += 1"
  doAssert n.kind == skZip
  if n.inline: return emitDeps(v, seen)
  if seen.getOrDefault(n.name): return ""
  seen[n.name] = true
  let deps = emitArray(n.left, seen) & "\n" & emitArray(n.right, seen)
  let body = emitElement(n.left, n.name & "Index") & " + " &
    emitElement(n.right, n.name & "Index")
  deps & "\nvar " & n.name & " = newSeq[float](" & intText(n.n) & ")\n" &
    "var " & n.name & "Index = 0\nwhile " & n.name & "Index < len(" & n.name & "):\n" &
    "  " & n.name & "[" & n.name & "Index] = " & body & "\n" &
    "  " & n.name & "Index += 1"

proc residual(v: Arr[float]): string =
  var seen = initTable[string, bool]()
  emitArray(v, seen)

proc compileRun(src, exe, dir: string): string =
  let nim = findExe("nim"); doAssert nim.len > 0
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

when isMainModule:
  var inputSerial = 0
  proc input(xs: seq[float]): Arr[float] =
    inc inputSerial
    Arr[float](node: Node(kind: skInput, name: "input" & $inputSerial, data: xs))

  proc plus(a, b: seq[float]): seq[float] =
    result = newSeq[float](a.len)
    for i in 0 ..< a.len: result[i] = a[i] + b[i]

  proc runAndCheck(v: Arr[float], expected: seq[float], prefix: string) =
    let text = residual(v)
    let dir = getTempDir() / (prefix & "-" & $getCurrentProcessId() & "-" &
      $int(epochTime() * 1000))
    createDir(dir)
    let source = dir / "residual.nim"; let exe = dir / "residual"
    writeFile(source, text & "\necho " & Node(v.node).name)
    doAssert compileRun(source, exe, dir).contains($expected)
    removeDir(dir)

  for xs in [@[], @[7.25], @[-2.0, 3.0], @[1.0, -2.5, 4.0], @[0.0, 0.0]]:
    let a = input(xs); let b = input(xs)
    let lowered = lowerVectors(vecPlus(vecPlus(a, b), a))
    let fused = fuseLoops(lowered, lowered)
    let text = residual(fused)
    doAssert text.count("newSeq[float]") == 1
    doAssert text.count("while") == 1
    runAndCheck(fused, plus(plus(xs, xs), xs), "fusion")

  # The same intermediate is consumed twice, so it must stay materialized.
  let sharedInput = input(@[1.0, -3.0])
  let shared = lowerVectors(vecPlus(sharedInput, input(@[2.0, 4.0])))
  let sharedResult = newArray[float](lenArr[float](shared, proc(a: Arr[float]): IRNode =
    Node(kind: skLen, source: a)), proc(n: Rep[int]): IRNode =
      Node(kind: skZip, name: freshName("plus"), n: n, left: shared, right: shared))
  let guarded = fuseLoops(sharedResult, sharedResult)
  let guardedText = residual(guarded)
  doAssert guardedText.count("newSeq[float]") == 2
  doAssert guardedText.count("while") == 2

  # Different residual lengths are also a hard fusion boundary.
  let short = lowerVectors(vecPlus(input(@[1.0]), input(@[2.0])))
  let long = lowerVectors(vecPlus(input(@[3.0, 4.0]), input(@[5.0, 6.0])))
  let mismatch = lowerVectors(vecPlus(short, long))
  let mismatchFused = fuseLoops(mismatch, mismatch)
  let mismatchText = residual(mismatchFused)
  doAssert mismatchText.count("newSeq[float]") == 2
  doAssert mismatchText.count("while") == 2

  echo "ok: loop fusion"
