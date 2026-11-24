## High-level VectorOps nodes and their plain residual lowering.

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

proc intText(x: Rep[int]): string =
  if x.isStatic: return $x.staticVal
  let n = Node(x.node)
  doAssert n.kind == skLen
  "len(" & Node(n.source.node).name & ")"

var genSerial = 0
proc freshName(base: string): string =
  inc genSerial
  base & $genSerial

proc vecZeros(n: Rep[int]): Arr[float] =
  newArray[float](n, proc(n: Rep[int]): IRNode = Node(kind: skZeros, n: n))

proc vecPlus(a, b: Arr[float]): Arr[float] =
  # VectorsExpOpt: zeros are an additive identity, before lowering.
  if Node(a.node).kind == skZeros: return b
  if Node(b.node).kind == skZeros: return a
  newArray[float](lenArr[float](a, proc(a: Arr[float]): IRNode =
    Node(kind: skLen, source: a)), proc(n: Rep[int]): IRNode =
      Node(kind: skPlus, n: n, left: a, right: b))

proc lowerVectors(v: Arr[float]): Arr[float] =
  ## Equivalent small bottom-up rewrite over Arr anchors.  mapTree works on
  ## client tree values, but Arr references are anchors rather than IR child
  ## trees, so this preserves the same bottom-up rule without changing it.
  let n = Node(v.node)
  case n.kind
  of skZeros:
    newArray[float](n.n, proc(nlen: Rep[int]): IRNode =
      Node(kind: skFill, name: freshName("zeros"), n: nlen))
  of skPlus:
    let a = lowerVectors(n.left); let b = lowerVectors(n.right)
    # Length from the lowered left child, not the original node: the
    # original left may be a high-level plus node with no residual name,
    # which would emit `len()`; the lowered child always has one.
    let ln = lenArr[float](a, proc(x: Arr[float]): IRNode =
      Node(kind: skLen, source: x))
    newArray[float](ln, proc(nlen: Rep[int]): IRNode =
      Node(kind: skZip, name: freshName("plus"), n: nlen, left: a, right: b))
  else:
    v

proc emitArray(v: Arr[float]; seen: var Table[string, bool]; high = false): string =
  let n = Node(v.node)
  if n.kind == skInput:
    if seen.getOrDefault(n.name): return ""
    seen[n.name] = true
    return "var " & n.name & ": seq[float] = " & $n.data
  if n.kind == skLen: return ""
  if n.kind == skZeros:
    return "# VectorZeros(" & intText(n.n) & ")"
  if n.kind == skPlus:
    return "# VectorPlus(" & Node(n.left.node).name & ", " & Node(n.right.node).name & ")"
  if n.kind == skFill:
    if seen.getOrDefault(n.name): return ""
    seen[n.name] = true
    return "var " & n.name & " = newSeq[float](" & intText(n.n) & ")\n" &
      "var " & n.name & "Index = 0\nwhile " & n.name & "Index < len(" & n.name & "):\n" &
      "  " & n.name & "[" & n.name & "Index] = 0.0\n" &
      "  " & n.name & "Index += 1"
  doAssert n.kind == skZip
  if seen.getOrDefault(n.name): return ""
  seen[n.name] = true
  let leftName = Node(n.left.node).name; let rightName = Node(n.right.node).name
  emitArray(n.left, seen) & "\n" & emitArray(n.right, seen) & "\n" &
    "var " & n.name & " = newSeq[float](" & intText(n.n) & ")\n" &
    "var " & n.name & "Index = 0\nwhile " & n.name & "Index < len(" & n.name & "):\n" &
    "  " & n.name & "[" & n.name & "Index] = " & leftName & "[" & n.name & "Index] + " &
    rightName & "[" & n.name & "Index]\n" & "  " & n.name & "Index += 1"

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
  var serial = 0
  proc input(xs: seq[float]): Arr[float] =
    inc serial
    Arr[float](node: Node(kind: skInput, name: "input" & $serial, data: xs))

  proc directPlus(a, b: seq[float]): seq[float] =
    result = newSeq[float](a.len)
    for i in 0 ..< a.len: result[i] = a[i] + b[i]

  for xs in [@[], @[7.25], @[1.0, -2.5, 4.0]]:
    let s = input(xs)
    let z = vecZeros(liftNow(xs.len))
    let high = vecPlus(s, z)
    let pre = residual(high)
    doAssert "VectorPlus" notin pre # optimizer fired
    doAssert "VectorZeros" in residual(z) # high-level node before lowering
    doAssert Node(high.node).kind == skInput
    let loweredZero = lowerVectors(z)
    let zeroText = residual(loweredZero)
    doAssert zeroText.count("newSeq[float]") == 1
    let dir = getTempDir() / ("lowering-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let source = dir / "residual.nim"; let exe = dir / "residual"
    writeFile(source, residual(loweredZero) & "\necho " & Node(loweredZero.node).name)
    let got = compileRun(source, exe, dir)
    doAssert got.contains($newSeq[float](xs.len))
    removeDir(dir)

  let v1data = @[2.0, -3.5, 4.25]
  let v1 = input(v1data)
  let v2 = vecZeros(liftNow(v1data.len))
  let v3 = vecPlus(v1, v2)
  let raw = vecPlus(v1, input(@[1.0, 1.0, 1.0]))
  doAssert "VectorPlus" in residual(raw)
  let tutorial = lowerVectors(vecPlus(v1, v3))
  let tutorialText = residual(tutorial)
  doAssert tutorialText.count("newSeq[float]") == 1
  doAssert tutorialText.count("while") == 1

  let direct = directPlus(v1data, v1data)
  let dir = getTempDir() / ("lowering-final-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"; let exe = dir / "residual"
  writeFile(source, tutorialText & "\necho " & Node(tutorial.node).name)
  doAssert compileRun(source, exe, dir).contains($direct)
  removeDir(dir)

  # Nested plus must not collide on generated array names: each lowered
  # node gets a fresh name, so both zip loops are emitted and chained.
  let nested = lowerVectors(vecPlus(vecPlus(v1, v1), v1))
  let nestedText = residual(nested)
  doAssert nestedText.count("newSeq[float]") == 2
  doAssert nestedText.count("while") == 2
  let nestedDirect = directPlus(direct, v1data)
  let ndir = getTempDir() / ("lowering-nested-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(ndir)
  let nsource = ndir / "residual.nim"; let nexe = ndir / "residual"
  writeFile(nsource, nestedText & "\necho " & Node(nested.node).name)
  doAssert compileRun(nsource, nexe, ndir).contains($nestedDirect)
  removeDir(ndir)
  echo "ok: vector lowering"
