## Mixed Cartesian/Polar Vector[Complex] in a struct-of-arrays layout.

import staging/framework
import staging/arrays
import std/[math, os, osproc, sequtils, strutils]
when isMainModule:
  import std/times

type
  ClassTag* = enum ctCartesian, ctPolar
  Complex* = object
    re*, im*, r*, theta*: float
    clzz*: ClassTag
  VectorComplex* = object
    re, im, r, theta: Arr[float]
    clzz: Arr[ClassTag]
    length: Rep[int]
    mapped: bool
    cartesianOnly: bool
  StagedComplex = object
    re, im, r, theta: Rep[float]
    clzz: Rep[ClassTag]
    cartesianOnly: bool
  ConjPart = enum cpRe, cpIm
  Column = enum colRe, colIm, colR, colTheta, colClzz
  MixedKind = enum mkInputF, mkInputTag, mkLen, mkReadF, mkReadTag, mkConjF,
    mkCartF, mkAddF, mkScaleF
  MixedNode = ref object of IRNode
    kind: MixedKind
    name: string
    fdata: seq[float]
    tdata: seq[ClassTag]
    farr: Arr[float]
    tarr: Arr[ClassTag]
    index: Rep[int]
    source: StagedComplex
    part: ConjPart
    left, right: StagedComplex
    scalar: Rep[float]

proc inputF*(name: string, values: seq[float]): Arr[float] =
  Arr[float](node: MixedNode(kind: mkInputF, name: name, fdata: values))
proc inputTag*(name: string, values: seq[ClassTag]): Arr[ClassTag] =
  Arr[ClassTag](node: MixedNode(kind: mkInputTag, name: name, tdata: values))
proc length(a: Arr[float]): Rep[int] = lenArr[float](a,
  proc(x: Arr[float]): IRNode = MixedNode(kind: mkLen, farr: x))
proc readF(a: Arr[float], i: Rep[int]): Rep[float] = readArr[float](a, i,
  proc(x: Arr[float], j: Rep[int]): IRNode = MixedNode(kind: mkReadF, farr: x, index: j))
proc readTag(a: Arr[ClassTag], i: Rep[int]): Rep[ClassTag] = readArr[ClassTag](a, i,
  proc(x: Arr[ClassTag], j: Rep[int]): IRNode = MixedNode(kind: mkReadTag, tarr: x, index: j))

proc mixedVector*(re, im, r, theta: Arr[float], clzz: Arr[ClassTag]): VectorComplex =
  let tags = MixedNode(clzz.node).tdata
  VectorComplex(re: re, im: im, r: r, theta: theta, clzz: clzz, length: length(im),
    cartesianOnly: tags.allIt(it == ctCartesian))
proc rawAt(v: VectorComplex, i: Rep[int]): StagedComplex =
  StagedComplex(re: readF(v.re, i), im: readF(v.im, i), r: readF(v.r, i),
    theta: readF(v.theta, i), clzz: readTag(v.clzz, i), cartesianOnly: v.cartesianOnly)
proc conjPart(c: StagedComplex, part: ConjPart): Rep[float] =
  dynamic[float](MixedNode(kind: mkConjF, source: c, part: part))
proc conj(c: StagedComplex): StagedComplex =
  StagedComplex(re: conjPart(c, cpRe), im: conjPart(c, cpIm), r: liftNow(0.0),
    theta: liftNow(0.0), clzz: liftNow(ctCartesian), cartesianOnly: false)
proc at(v: VectorComplex, i: Rep[int]): StagedComplex =
  if v.mapped: conj(rawAt(v, i)) else: rawAt(v, i)
proc mapConj(v: VectorComplex): VectorComplex =
  VectorComplex(re: v.re, im: v.im, r: v.r, theta: v.theta, clzz: v.clzz,
    length: v.length, mapped: true, cartesianOnly: v.cartesianOnly)

proc cartPart(c: StagedComplex, part: ConjPart): Rep[float] =
  if c.cartesianOnly:
    if part == cpRe: c.re else: c.im
  else:
    dynamic[float](MixedNode(kind: mkCartF, source: c, part: part))

proc addComplex*(a, b: StagedComplex): StagedComplex =
  StagedComplex(re: dynamic[float](MixedNode(kind: mkAddF, left: a, right: b, part: cpRe)),
    im: dynamic[float](MixedNode(kind: mkAddF, left: a, right: b, part: cpIm)),
    r: liftNow(0.0), theta: liftNow(0.0), clzz: liftNow(ctCartesian))
proc scalarComplex*(s: Rep[float], a: StagedComplex): StagedComplex =
  StagedComplex(re: dynamic[float](MixedNode(kind: mkScaleF, source: a, scalar: s, part: cpRe)),
    im: dynamic[float](MixedNode(kind: mkScaleF, source: a, scalar: s, part: cpIm)),
    r: liftNow(0.0), theta: liftNow(0.0), clzz: liftNow(ctCartesian))
proc addAt*(a, b: VectorComplex, i: Rep[int]): StagedComplex =
  addComplex(StagedComplex(re: cartPart(rawAt(a, i), cpRe), im: cartPart(rawAt(a, i), cpIm),
    r: liftNow(0.0), theta: liftNow(0.0), clzz: liftNow(ctCartesian)),
    StagedComplex(re: cartPart(rawAt(b, i), cpRe), im: cartPart(rawAt(b, i), cpIm),
      r: liftNow(0.0), theta: liftNow(0.0), clzz: liftNow(ctCartesian)))
proc scalarAt*(s: Rep[float], a: VectorComplex, i: Rep[int]): StagedComplex =
  scalarComplex(s, StagedComplex(re: cartPart(rawAt(a, i), cpRe), im: cartPart(rawAt(a, i), cpIm),
    r: liftNow(0.0), theta: liftNow(0.0), clzz: liftNow(ctCartesian)))

proc floatName(a: Arr[float]): string = MixedNode(a.node).name
proc tagName(a: Arr[ClassTag]): string = MixedNode(a.node).name
proc indexText(x: Rep[int], used: var set[Column]): string

proc markFloat(name: string, used: var set[Column]) =
  if name == "re" or name.endsWith("Re"): used.incl(colRe)
  elif name == "im" or name.endsWith("Im"): used.incl(colIm)
  elif name == "r" or name.endsWith("R"): used.incl(colR)
  elif name == "theta" or name.endsWith("Theta"): used.incl(colTheta)

proc intText(x: Rep[int], used: var set[Column]): string =
  doAssert not x.isStatic
  let n = MixedNode(x.node)
  doAssert n.kind == mkLen
  let a = MixedNode(n.farr.node)
  markFloat(a.name, used)
  a.name
proc indexText(x: Rep[int], used: var set[Column]): string =
  if x.isStatic: $x.staticVal else: intText(x, used)

proc emitFloat(x: Rep[float], used: var set[Column]): string
proc emitTag(x: Rep[ClassTag], used: var set[Column]): string =
  doAssert not x.isStatic
  let n = MixedNode(x.node)
  case n.kind
  of mkReadTag:
    used.incl(colClzz)
    tagName(n.tarr) & "[" & indexText(n.index, used) & "]"
  else: raise newException(ValueError, "bad tag node")
proc emitFloat(x: Rep[float], used: var set[Column]): string =
  if x.isStatic: return $x.staticVal
  let n = MixedNode(x.node)
  case n.kind
  of mkReadF:
    let a = MixedNode(n.farr.node)
    markFloat(a.name, used)
    a.name & "[" & indexText(n.index, used) & "]"
  of mkConjF:
    let c = n.source
    let tag = emitTag(c.clzz, used)
    let cart = if n.part == cpRe: emitFloat(c.re, used) else: "(-" & emitFloat(c.im, used) & ")"
    let polar = emitFloat(c.r, used) & (if n.part == cpRe: " * cos(-" & emitFloat(c.theta, used) & ")" else: " * sin(-" & emitFloat(c.theta, used) & ")")
    "(if " & tag & " == ctCartesian: " & cart & " else: " & polar & ")"
  of mkCartF:
    let c = n.source
    let tag = emitTag(c.clzz, used)
    let cart = if n.part == cpRe: emitFloat(c.re, used) else: emitFloat(c.im, used)
    let polar = emitFloat(c.r, used) & (if n.part == cpRe: " * cos(" & emitFloat(c.theta, used) & ")" else: " * sin(" & emitFloat(c.theta, used) & ")")
    "(if " & tag & " == ctCartesian: " & cart & " else: " & polar & ")"
  of mkAddF:
    let left = if n.part == cpRe: n.left.re else: n.left.im
    let right = if n.part == cpRe: n.right.re else: n.right.im
    "(" & emitFloat(left, used) & " + " & emitFloat(right, used) & ")"
  of mkScaleF:
    let value = if n.part == cpRe: n.source.re else: n.source.im
    "(" & emitFloat(n.scalar, used) & " * " & emitFloat(value, used) & ")"
  else: raise newException(ValueError, "bad float node")

proc emitArray(a: Arr[float]): string =
  let n = MixedNode(a.node); doAssert n.kind == mkInputF
  "var " & n.name & " = " & $n.fdata
proc emitTags(a: Arr[ClassTag]): string =
  let n = MixedNode(a.node); doAssert n.kind == mkInputTag
  "var " & n.name & " = @[" & n.tdata.mapIt(if it == ctCartesian: "ctCartesian" else: "ctPolar").join(", ") & "]"
proc emitInputs(v: VectorComplex, used: set[Column]): string =
  var lines: seq[string]
  if colRe in used: lines.add(emitArray(v.re))
  if colIm in used: lines.add(emitArray(v.im))
  if colR in used: lines.add(emitArray(v.r))
  if colTheta in used: lines.add(emitArray(v.theta))
  if colClzz in used: lines.add(emitTags(v.clzz))
  lines.join("\n")

proc emitInputs*(a, b: VectorComplex, used: set[Column]): string =
  var lines: seq[string]
  if colRe in used: lines.add(emitArray(a.re)); lines.add(emitArray(b.re))
  if colIm in used: lines.add(emitArray(a.im)); lines.add(emitArray(b.im))
  if colR in used: lines.add(emitArray(a.r)); lines.add(emitArray(b.r))
  if colTheta in used: lines.add(emitArray(a.theta)); lines.add(emitArray(b.theta))
  if colClzz in used: lines.add(emitTags(a.clzz)); lines.add(emitTags(b.clzz))
  lines.join("\n")

proc emitArithmeticProgram*(a, b: VectorComplex, scalar: float,
    doAdd: bool): string =
  var used: set[Column]
  let i = liftNow(0)
  let z = if doAdd: addAt(a, b, i) else: scalarAt(liftNow(scalar), a, i)
  let exprRe = emitFloat(z.re, used)
  let exprIm = emitFloat(z.im, used)
  let inputs = if doAdd: emitInputs(a, b, used) else: emitInputs(a, used)
  let lenName = floatName(a.im)
  result = "import std/math\n\ntype ClassTag = enum ctCartesian, ctPolar\n" &
    inputs & "\nvar i = 0\nwhile i < len(" & lenName & "):\n  echo " &
    exprRe.replace("[0]", "[i]") & ", \" \" , " & exprIm.replace("[0]", "[i]") &
    "\n  i += 1"

proc emitConjComponent(v: VectorComplex, i: Rep[int], used: var set[Column]): string =
  emitFloat(at(v, i).im, used)
proc emitConjComplex(v: VectorComplex, i: Rep[int], used: var set[Column]): string =
  let z = at(v, i)
  "Complex(re: " & emitFloat(z.re, used) & ", im: " & emitFloat(z.im, used) & ", r: 0.0, theta: 0.0, clzz: ctCartesian)"
proc emitComponentProgram(v: VectorComplex): string =
  var used: set[Column]
  let expr = emitConjComponent(v, liftNow(0), used)
  let lenName = floatName(v.im)
  result = "import std/math\n\ntype ClassTag = enum ctCartesian, ctPolar\n" & emitInputs(v, used) & "\nvar i = 0\nwhile i < len(" &
    lenName & "):\n  echo " & expr.replace("[0]", "[i]") & "\n  i += 1"
proc emitComplexProgram(v: VectorComplex): string =
  var used: set[Column]
  let expr = emitConjComplex(v, liftNow(0), used)
  let lenName = floatName(v.im)
  "import std/math\n\ntype ClassTag = enum ctCartesian, ctPolar\n" &
    "type Complex = object\n  re, im, r, theta: float\n  clzz: ClassTag\n" & emitInputs(v, used) &
    "\nvar i = 0\nwhile i < len(" & lenName & "):\n  let z = " & expr.replace("[0]", "[i]") &
    "\n  echo z.re, \" \", z.im\n  i += 1"

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let built = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert built.exitCode == 0, built.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip
proc directConj(x: Complex): Complex =
  if x.clzz == ctCartesian: Complex(re: x.re, im: -x.im, r: 0.0, theta: 0.0, clzz: ctCartesian)
  else: Complex(re: x.r * cos(-x.theta), im: x.r * sin(-x.theta), r: 0.0, theta: 0.0, clzz: ctCartesian)

when isMainModule:
  let dir = getTempDir() / ("staging-soa-mixed-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let cases = @[
    (@[(1.0, -2.0, 0.0, 0.0, ctCartesian), (3.5, 4.0, 0.0, 0.0, ctCartesian)]),
    (@[(0.0, 0.0, 2.0, 0.5, ctPolar), (0.0, 0.0, 1.25, -0.75, ctPolar)]),
    (@[(1.0, -2.0, 0.0, 0.0, ctCartesian), (0.0, 0.0, 2.0, 0.5, ctPolar), (3.5, 4.0, 0.0, 0.0, ctCartesian), (0.0, 0.0, 1.25, -0.75, ctPolar)])]
  for caseNo, values in cases:
    var re, im, radius, theta: seq[float]
    var tags: seq[ClassTag]
    var expected: seq[Complex]
    for x in values:
      re.add(x[0]); im.add(x[1]); radius.add(x[2]); theta.add(x[3]); tags.add(x[4])
      expected.add(directConj(Complex(re: x[0], im: x[1], r: x[2], theta: x[3], clzz: x[4])))
    let v = mapConj(mixedVector(inputF("re", re), inputF("im", im), inputF("r", radius), inputF("theta", theta), inputTag("clzz", tags)))
    let componentText = emitComponentProgram(v)
    # The component query (conj imaginary part) genuinely needs r: the Polar
    # branch is r * sin(-theta). Only re is unneeded here.
    doAssert "var re =" notin componentText, componentText
    doAssert "var r =" in componentText and "var im =" in componentText and "var theta =" in componentText and "var clzz =" in componentText
    let componentSource = dir / ("component" & $caseNo & ".nim")
    writeFile(componentSource, componentText)
    let componentGot = compileRun(componentSource, dir / ("component" & $caseNo), dir).splitWhitespace.map(parseFloat)
    doAssert componentGot.len == expected.len
    for i, x in expected: doAssert abs(componentGot[i] - x.im) < 1e-8
    let text = emitComplexProgram(v)
    doAssert "re[i]" in text and "im[i]" in text and "r[i]" in text and "theta[i]" in text
    let source = dir / ("mixed" & $caseNo & ".nim")
    writeFile(source, text)
    let got = compileRun(source, dir / ("mixed" & $caseNo), dir).splitWhitespace.map(parseFloat)
    doAssert got.len == expected.len * 2
    for i, x in expected:
      doAssert abs(got[i * 2] - x.re) < 1e-8
      doAssert abs(got[i * 2 + 1] - x.im) < 1e-8
  removeDir(dir)
  echo "ok: mixed Cartesian/Polar Vector[Complex] struct-of-arrays"
