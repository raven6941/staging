## Cartesian-only struct-of-arrays conversion for staged Vector[Complex].

import staging/framework
import staging/arrays
import std/[os, osproc, sequtils, strutils, times]

type
  Complex = object
    re, im: Rep[float]
  VectorComplex = object
    re, im: Arr[float]
    length: Rep[int]
  SoAKind = enum
    skInput, skLen, skRead, skDecl, skWrite, skNeg, skLitI, skAddI,
    skLtI, skVarDecl, skVarRead, skVarWrite, skSeq, skWhile, skIfArray
  SoANode = ref object of IRNode
    kind: SoAKind
    name: string
    data: seq[float]
    arr, thenArr, elseArr, sourceArr: Arr[float]
    length: Rep[int]
    value: Rep[float]
    index: Rep[int]
    cond: Rep[bool]
    intValue, intLeft, intRight: Rep[int]
    vi: Var[int]
    initI: Rep[int]
    a, b, body: Rep[Unit]

  MapProgram = object
    vector: VectorComplex
    body: Rep[Unit]
    index: Var[int]

proc litI(x: int): Rep[int] = liftNow(x)
proc addI(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
  proc(x, y: int): int = x + y,
  proc(x, y: Rep[int]): IRNode = SoANode(kind: skAddI, intLeft: x, intRight: y))
proc ltI(a, b: Rep[int]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal < b.staticVal)
  else: dynamic[bool](SoANode(kind: skLtI, intLeft: a, intRight: b))
proc neg(a: Rep[float]): Rep[float] =
  smartOpUni[float](a, proc(x: float): float = -x,
    proc(x: Rep[float]): IRNode = SoANode(kind: skNeg, value: x))

proc inputArray(name: string, data: seq[float]): Arr[float] =
  Arr[float](node: SoANode(kind: skInput, name: name, data: data))
proc arrayLength(a: Arr[float]): Rep[int] = lenArr[float](a,
  proc(a: Arr[float]): IRNode = SoANode(kind: skLen, arr: a))
proc arrayRead(a: Arr[float], i: Rep[int]): Rep[float] = readArr[float](a, i,
  proc(a: Arr[float], i: Rep[int]): IRNode = SoANode(kind: skRead, arr: a, index: i))
proc arrayWrite(a: Arr[float], i: Rep[int], x: Rep[float]): Rep[Unit] =
  writeArr[float](a, i, x, proc(a: Arr[float], i: Rep[int], x: Rep[float]): IRNode =
    SoANode(kind: skWrite, arr: a, index: i, value: x))

proc structVector(re, im: Arr[float]): VectorComplex =
  VectorComplex(re: re, im: im, length: arrayLength(re))
proc at(v: VectorComplex, i: Rep[int]): Complex =
  Complex(re: arrayRead(v.re, i), im: arrayRead(v.im, i))
proc conj(c: Complex): Complex = Complex(re: c.re, im: neg(c.im))

proc seqR(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
  proc(a, b: Rep[Unit]): IRNode = SoANode(kind: skSeq, a: a, b: b))
proc makeIndex(): Var[int] = newVar[int](litI(0),
  proc(x: Rep[int]): IRNode = SoANode(kind: skVarDecl, name: "mapIndex", initI: x))
proc readIndex(v: Var[int]): Rep[int] = readVar[int](v,
  proc(v: Var[int]): IRNode = SoANode(kind: skVarRead, vi: v))
proc writeIndex(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
  proc(v: Var[int], x: Rep[int]): IRNode = SoANode(kind: skVarWrite, vi: v, intValue: x))

proc mapConj(v: VectorComplex): MapProgram =
  let outIm = newArray[float](v.length,
    proc(n: Rep[int]): IRNode = SoANode(kind: skDecl, name: "mappedIm", length: n,
      sourceArr: v.im))
  let i = makeIndex()
  let body = smartWhile(proc(): Rep[bool] = ltI(readIndex(i), v.length), proc(): Rep[Unit] =
    seqR(arrayWrite(outIm, readIndex(i), neg(arrayRead(v.im, readIndex(i)))),
      writeIndex(i, addI(readIndex(i), litI(1)))),
    proc(c: Rep[bool], b: Rep[Unit]): IRNode = SoANode(kind: skWhile, cond: c, body: b))
  MapProgram(vector: VectorComplex(re: v.re, im: outIm, length: v.length), body: body, index: i)

proc conditionalMap(test: Rep[bool], v: VectorComplex): MapProgram =
  let mapped = mapConj(v)
  let selected = Arr[float](node: SoANode(kind: skIfArray, name: "conditionalIm",
    thenArr: mapped.vector.im, elseArr: v.im, cond: test))
  MapProgram(vector: VectorComplex(re: v.re, im: selected, length: v.length),
    body: mapped.body, index: mapped.index)

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = SoANode(r.node)
  case n.kind
  of skLen: "len(" & SoANode(n.arr.node).name & ")"
  of skAddI: "(" & emitInt(n.intLeft) & " + " & emitInt(n.intRight) & ")"
  of skVarRead: SoANode(n.vi.node).name
  else: raise newException(ValueError, "bad int node")
proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = SoANode(r.node)
  if n.kind == skInput: n.name
  else: "(" & emitInt(n.intLeft) & " < " & emitInt(n.intRight) & ")"
proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let n = SoANode(r.node)
  case n.kind
  of skRead: SoANode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  of skNeg: "(-" & emitFloat(n.value) & ")"
  else: raise newException(ValueError, "bad float node")
proc emitStmt(r: Rep[Unit], ind = ""): string =
  if r.isStatic: return ind & "discard"
  let n = SoANode(r.node)
  case n.kind
  of skSeq: emitStmt(n.a, ind) & "\n" & emitStmt(n.b, ind)
  of skWhile: ind & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.body, ind & "  ")
  of skWrite: ind & SoANode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitFloat(n.value)
  of skVarWrite: ind & SoANode(n.vi.node).name & " = " & emitInt(n.intValue)
  else: raise newException(ValueError, "bad statement node")
proc emitDecl(v: Var[int]): string =
  let n = SoANode(v.node); "var " & n.name & " = " & emitInt(n.initI)
proc emitArray(a: Arr[float], ind = ""): string =
  let n = SoANode(a.node)
  case n.kind
  of skInput: ind & "var " & n.name & " = " & $n.data
  of skDecl: ind & "var " & n.name & " = newSeq[float](" & emitInt(n.length) & ")"
  of skIfArray:
    raise newException(ValueError, "conditional arrays use emitConditionalArray")
  else: raise newException(ValueError, "bad array node")

proc emitConditionalArray(a: Arr[float], ind = ""): string =
  let n = SoANode(a.node)
  doAssert n.kind == skIfArray
  let mapped = SoANode(n.thenArr.node)
  ind & "var " & n.name & ": seq[float]\n" & ind & "if " & emitBool(n.cond) & ":\n" &
    ind & "  " & n.name & " = newSeq[float](" & emitInt(mapped.length) & ")\n" &
    ind & "  var mapIndex = 0\n" & ind & "  while mapIndex < " & emitInt(mapped.length) & ":\n" &
    ind & "    " & n.name & "[mapIndex] = (-" & SoANode(mapped.sourceArr.node).name & "[mapIndex])\n" &
    ind & "    mapIndex += 1\n" & ind & "else:\n" & ind & "  " & n.name & " = " & SoANode(n.elseArr.node).name

proc emitVector(v: VectorComplex): string =
  result = emitArray(v.re) & "\n"
  let imNode = SoANode(v.im.node)
  if imNode.kind == skIfArray:
    result &= emitArray(imNode.elseArr) & "\n" & emitConditionalArray(v.im)
  elif imNode.kind == skDecl:
    result &= emitArray(imNode.sourceArr) & "\n" & emitArray(v.im)
  else: result &= emitArray(v.im)
proc emitComplex(c: Complex): string =
  "Complex(re: " & emitFloat(c.re) & ", im: " & emitFloat(c.im) & ")"

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let built = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert built.exitCode == 0, built.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

when isMainModule:
  let dir = getTempDir() / ("staging-soa-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  for values in [@[(0.0, -2.0), (3.5, 4.0)], @[(-1.5, 0.0), (2.0, -3.25), (0.0, 1.0)]]:
    var re, im: seq[float]
    for p in values: re.add(p[0]); im.add(p[1])
    let v = structVector(inputArray("vectorRe", re), inputArray("vectorIm", im))
    let mapped = mapConj(v)
    let c = at(mapped.vector, litI(1))
    let source = dir / "conj.nim"; let exe = dir / "conj"
    let residual = emitVector(mapped.vector) & "\n" & emitDecl(mapped.index) & "\n" & emitStmt(mapped.body) &
      "\n" & "type Complex = object\n  re, im: float\n" & "let result = " & emitComplex(c) & "\necho result.re, \" \", result.im\n"
    doAssert residual.count("newSeq[float]") == 1, residual
    doAssert residual.count("while ") == 1, residual
    doAssert "vectorRe" in residual and "mappedIm" in residual
    writeFile(source, residual)
    let got = compileRun(source, exe, dir).splitWhitespace.map(parseFloat)
    doAssert abs(got[0] - re[1]) < 1e-9 and abs(got[1] + im[1]) < 1e-9
    let test = dynamic[bool](SoANode(kind: skInput, name: "test"))
    let branched = conditionalMap(test, v)
    let branchText = emitVector(branched.vector)
    doAssert "if test" in branchText and "vectorRe" in branchText
    doAssert branchText.find("if test") > branchText.find("vectorRe")
    let afterIf = branchText.split("if test", 1)[1]
    doAssert "vectorRe[" notin afterIf
    doAssert branchText.count("newSeq[float]") == 1 and branchText.count("while ") == 1
    for flag in [true, false]:
      let bsource = dir / "branch.nim"; let bexe = dir / "branch"
      let text = "var test = " & $flag & "\n" & branchText & "\n" &
        "echo " & SoANode(branched.vector.re.node).name & "[1], \" \", " &
        SoANode(branched.vector.im.node).name & "[1]\n"
      writeFile(bsource, text)
      let gotBranch = compileRun(bsource, bexe, dir).splitWhitespace.map(parseFloat)
      doAssert abs(gotBranch[0] - re[1]) < 1e-9
      doAssert abs(gotBranch[1] - (if flag: -im[1] else: im[1])) < 1e-9
  removeDir(dir)
  echo "ok: Cartesian Vector[Complex] struct-of-arrays"
