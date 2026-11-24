## Horizontal fusion for two reductions over one plain residual vector.

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times, tables]

type
  Kind = enum skInput, skLen, skZeros, skPlus, skFill, skZip
  Node = ref object of IRNode
    kind: Kind
    name: string
    data: seq[float]
    n: Rep[int]
    left, right, source: Arr[float]
    inline: bool

  HorizontalProgram = object
    source: Arr[float]
    returned: Arr[float]
    fused: bool

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

proc vecPlus(a, b: Arr[float]): Arr[float] =
  newArray[float](lenArr[float](a, proc(a: Arr[float]): IRNode =
    Node(kind: skLen, source: a)), proc(n: Rep[int]): IRNode =
      Node(kind: skPlus, n: n, left: a, right: b))

proc lowerVectors(v: Arr[float]): Arr[float] =
  let n = Node(v.node)
  case n.kind
  of skPlus:
    let a = lowerVectors(n.left); let b = lowerVectors(n.right)
    let ln = lenArr[float](a, proc(x: Arr[float]): IRNode =
      Node(kind: skLen, source: x))
    newArray[float](ln, proc(nlen: Rep[int]): IRNode =
      Node(kind: skZip, name: freshName("plus"), n: nlen, left: a, right: b))
  of skZeros:
    newArray[float](n.n, proc(nlen: Rep[int]): IRNode =
      Node(kind: skFill, name: freshName("zeros"), n: nlen))
  else:
    v

proc isElementwise(v: Arr[float]): bool =
  let k = Node(v.node).kind
  k == skFill or k == skZip

proc sameLength(a, b: Arr[float]): bool =
  let na = Node(a.node); let nb = Node(b.node)
  isElementwise(a) and isElementwise(b) and intText(na.n) == intText(nb.n)

proc countRefs(v: Arr[float], wanted: string): int =
  let n = Node(v.node)
  if n.kind == skZip:
    if Node(n.left.node).name == wanted: inc result
    if Node(n.right.node).name == wanted: inc result
    result += countRefs(n.left, wanted)
    result += countRefs(n.right, wanted)

proc useCount(p: HorizontalProgram, wanted: string): int =
  ## The two reduction reads are one combined consumer of the shared input.
  if Node(p.source.node).name == wanted: inc result
  result += countRefs(p.source, wanted)
  if p.returned != nil:
    if Node(p.returned.node).name == wanted: inc result
    result += countRefs(p.returned, wanted)

proc fuseLoops(v: Arr[float], p: HorizontalProgram) =
  let n = Node(v.node)
  if n.kind != skZip: return
  fuseLoops(n.left, p)
  fuseLoops(n.right, p)
  for operand in [n.left, n.right]:
    let producer = Node(operand.node)
    if isElementwise(operand) and not producer.inline and
       useCount(p, producer.name) == 1 and sameLength(operand, v):
      producer.inline = true

proc allChildrenInline(v: Arr[float]): bool =
  let n = Node(v.node)
  case n.kind
  of skFill: true
  of skZip: (Node(n.left.node).inline or Node(n.left.node).kind == skInput) and
    (Node(n.right.node).inline or Node(n.right.node).kind == skInput) and
    allChildrenInline(n.left) and allChildrenInline(n.right)
  else: true

proc fuseHorizontal(p: var HorizontalProgram) =
  fuseLoops(p.source, p)
  let n = Node(p.source.node)
  p.fused = isElementwise(p.source) and useCount(p, n.name) == 1 and
    allChildrenInline(p.source)

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

proc emitProgram(p: HorizontalProgram): string =
  var seen = initTable[string, bool]()
  let deps = if p.fused: emitDeps(p.source, seen) else: emitArray(p.source, seen)
  let sourceName = Node(p.source.node).name
  let x = if p.fused: emitElement(p.source, "fusionIndex") else: sourceName & "[fusionIndex]"
  deps & "\nvar sum = 0.0\nvar sumSq = 0.0\nvar fusionIndex = 0\nwhile fusionIndex < len(" &
    arrayLengthText(p.source) & "):\n  sum += " & x & "\n  sumSq += (" & x & " * " & x & ")\n  fusionIndex += 1\n" &
    "var mean = sum / float(len(" & arrayLengthText(p.source) & "))\n" &
    "var variance = sumSq / float(len(" & arrayLengthText(p.source) & ")) - mean * mean\n"

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

  proc direct(xs: seq[float]): tuple[mean, variance: float] =
    var sum, sumSq: float
    for x in xs:
      sum += x
      sumSq += x * x
    result.mean = sum / xs.len.float
    result.variance = sumSq / xs.len.float - result.mean * result.mean

  proc runAndCheck(p: HorizontalProgram, expected: tuple[mean, variance: float], prefix: string) =
    let text = emitProgram(p)
    let dir = getTempDir() / (prefix & "-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let source = dir / "residual.nim"; let exe = dir / "residual"
    writeFile(source, text & "echo mean, \" \", variance")
    let output = compileRun(source, exe, dir).splitWhitespace
    doAssert parseFloat(output[0]) == expected.mean
    doAssert parseFloat(output[1]) == expected.variance
    removeDir(dir)

  for xs in [@[0.0, 0.0], @[-2.0, 3.5], @[7.25]]:
    let source = lowerVectors(vecPlus(input(xs), input(newSeq[float](xs.len))))
    var p = HorizontalProgram(source: source)
    fuseHorizontal(p)
    let text = emitProgram(p)
    doAssert text.count("while") == 1
    doAssert text.count("newSeq[float]") == 0
    runAndCheck(p, direct(xs), "fusion-horizontal")

  let escaped = lowerVectors(vecPlus(input(@[1.0, -3.0]), input(@[2.0, 4.0])))
  var guarded = HorizontalProgram(source: escaped, returned: escaped)
  fuseHorizontal(guarded)
  let guardedText = emitProgram(guarded)
  doAssert guardedText.count("newSeq[float]") == 1
  doAssert guardedText.count("while") > 1
  runAndCheck(guarded, direct(@[3.0, 1.0]), "fusion-horizontal-guard")

  echo "ok: horizontal fusion"
