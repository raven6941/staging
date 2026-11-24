## Generic vector arithmetic over the sequential VectorOps core.
## Vector[Complex] is intentionally out of scope: this library has no Complex
## struct; FFT/Complex support is tracked separately (Wally, issue #24).

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times, math, sequtils]

type
  Vector[T] = Arr[T]
  VectorKind = enum skInput, skLen, skReadF, skZipAdd, skZipSub, skScalarMul,
    skUnitVector, skVectorNorm, skSqrt, skAddF, skSubF, skMulF, skDivF,
    skLitI, skAddI, skLtI, skDeclI, skReadI, skDeclF, skReadVarF, skWriteI,
    skWriteF, skToFloat, skSeq, skWhile
  VectorNode = ref object of IRNode
    kind: VectorKind
    name: string
    data: seq[float]
    n: Rep[int]
    vec, leftV, rightV: Arr[float]
    index: Rep[int]
    valueF, leftF, rightF: Rep[float]
    leftI, rightI: Rep[int]
    initI: Rep[int]
    initF: Rep[float]
    vi: Var[int]
    vf: Var[float]
    cond: Rep[bool]
    a, b: Rep[Unit]

  VectorSym[I, F, B, S, VI, VF, V] = object
    litI: proc(x: int): I
    litF: proc(x: float): F
    toFloat: proc(x: I): F
    addF, subF, mulF, divF: proc(x, y: F): F
    addI: proc(x, y: I): I
    ltI: proc(x, y: I): B
    unit: proc(): S
    seq: proc(a, b: S): S
    whileLoop: proc(c: proc(): B, body: proc(): S): S
    varNewI: proc(x: I): VI
    readI: proc(v: VI): I
    writeI: proc(v: VI, x: I): S
    varNewF: proc(x: F): VF
    readF: proc(v: VF): F
    writeF: proc(v: VF, x: F): S
    input: proc(data: seq[float]): V
    length: proc(v: V): I
    apply: proc(v: V, i: I): F
    newVector: proc(n: I, left, right: V, subtract: bool): V
    scalarTimesVector: proc(s: F, v: V): V
    vectorNorm: proc(v: V): F
    sqrtF: proc(x: F): F

  Numeric[F] = object
    plus, minus, times: proc(x, y: F): F
    zero: proc(): F

  LoopProgram[I, F, S, V, VI, VF] = object
    body: S
    result: F
    vector: V
    index: VI
    accumulator: VF

proc directSym(): VectorSym[int, float, bool, Unit, ref int, ref float, seq[float]] =
  VectorSym[int, float, bool, Unit, ref int, ref float, seq[float]](
    litI: proc(x: int): int = x, litF: proc(x: float): float = x,
    toFloat: proc(x: int): float = x.float,
    addF: proc(x, y: float): float = x + y,
    subF: proc(x, y: float): float = x - y,
    mulF: proc(x, y: float): float = x * y,
    divF: proc(x, y: float): float = x / y,
    addI: proc(x, y: int): int = x + y,
    ltI: proc(x, y: int): bool = x < y,
    unit: proc(): Unit = Unit(), seq: proc(a, b: Unit): Unit = Unit(),
    whileLoop: proc(c: proc(): bool, body: proc(): Unit): Unit =
      (while c(): discard body(); Unit()),
    varNewI: proc(x: int): ref int = (new(result); result[] = x),
    readI: proc(v: ref int): int = v[],
    writeI: proc(v: ref int, x: int): Unit = (v[] = x; Unit()),
    varNewF: proc(x: float): ref float = (new(result); result[] = x),
    readF: proc(v: ref float): float = v[],
    writeF: proc(v: ref float, x: float): Unit = (v[] = x; Unit()),
    input: proc(data: seq[float]): seq[float] = data,
    length: proc(v: seq[float]): int = v.len,
    apply: proc(v: seq[float], i: int): float = v[i],
    newVector: proc(n: int, left, right: seq[float], subtract: bool): seq[float] =
      (result = newSeq[float](n); for i in 0 ..< n: result[i] = (if subtract: left[i] - right[i] else: left[i] + right[i])),
    scalarTimesVector: proc(s: float, v: seq[float]): seq[float] =
      (result = newSeq[float](v.len); for i, x in v: result[i] = s * x),
    vectorNorm: proc(v: seq[float]): float =
      (for x in v: result += x * x; result = sqrt(result)),
    sqrtF: proc(x: float): float = sqrt(x))

proc stagedSym(): VectorSym[Rep[int], Rep[float], Rep[bool], Rep[Unit], Var[int],
    Var[float], Arr[float]] =
  var number = 0
  result = VectorSym[Rep[int], Rep[float], Rep[bool], Rep[Unit], Var[int],
    Var[float], Arr[float]](
    litI: proc(x: int): Rep[int] = liftNow(x), litF: proc(x: float): Rep[float] = liftNow(x),
    toFloat: proc(x: Rep[int]): Rep[float] = dynamic[float](VectorNode(kind: skToFloat, leftI: x)),
    addF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y, proc(a, b: float): float = a + b,
      proc(a, b: Rep[float]): IRNode = VectorNode(kind: skAddF, leftF: a, rightF: b)),
    subF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y, proc(a, b: float): float = a - b,
      proc(a, b: Rep[float]): IRNode = VectorNode(kind: skSubF, leftF: a, rightF: b)),
    mulF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y, proc(a, b: float): float = a * b,
      proc(a, b: Rep[float]): IRNode = VectorNode(kind: skMulF, leftF: a, rightF: b)),
    divF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y, proc(a, b: float): float = a / b,
      proc(a, b: Rep[float]): IRNode = VectorNode(kind: skDivF, leftF: a, rightF: b)),
    addI: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y, proc(a, b: int): int = a + b,
      proc(a, b: Rep[int]): IRNode = VectorNode(kind: skAddI, leftI: a, rightI: b)),
    ltI: proc(x, y: Rep[int]): Rep[bool] =
      (if x.isStatic and y.isStatic: liftNow(x.staticVal < y.staticVal)
       else: dynamic[bool](VectorNode(kind: skLtI, leftI: x, rightI: y))),
    unit: proc(): Rep[Unit] = unit(), seq: proc(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
      proc(a, b: Rep[Unit]): IRNode = VectorNode(kind: skSeq, a: a, b: b)),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] = smartWhile(c, body,
      proc(c: Rep[bool], b: Rep[Unit]): IRNode = VectorNode(kind: skWhile, cond: c, b: b)),
    varNewI: proc(x: Rep[int]): Var[int] = (inc number; newVar[int](x,
      proc(x: Rep[int]): IRNode = VectorNode(kind: skDeclI, name: "i" & $number, initI: x))),
    readI: proc(v: Var[int]): Rep[int] = readVar[int](v, proc(v: Var[int]): IRNode = VectorNode(kind: skReadI, vi: v)),
    writeI: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = VectorNode(kind: skWriteI, vi: v, leftI: x)),
    varNewF: proc(x: Rep[float]): Var[float] = (inc number; newVar[float](x,
      proc(x: Rep[float]): IRNode = VectorNode(kind: skDeclF, name: "acc" & $number, initF: x))),
    readF: proc(v: Var[float]): Rep[float] = readVar[float](v, proc(v: Var[float]): IRNode = VectorNode(kind: skReadVarF, vf: v)),
    writeF: proc(v: Var[float], x: Rep[float]): Rep[Unit] = writeVar[float](v, x,
      proc(v: Var[float], x: Rep[float]): IRNode = VectorNode(kind: skWriteF, vf: v, valueF: x)),
    input: proc(data: seq[float]): Arr[float] = (inc number; Arr[float](node: VectorNode(kind: skInput, name: "input" & $number, data: data))),
    length: proc(v: Arr[float]): Rep[int] = lenArr[float](v, proc(v: Arr[float]): IRNode = VectorNode(kind: skLen, vec: v)),
    apply: proc(v: Arr[float], i: Rep[int]): Rep[float] = readArr[float](v, i,
      proc(v: Arr[float], i: Rep[int]): IRNode = VectorNode(kind: skReadF, vec: v, index: i)),
    newVector: proc(n: Rep[int], left, right: Arr[float], subtract: bool): Arr[float] = (inc number; newArray[float](n,
      proc(n: Rep[int]): IRNode = VectorNode(kind: (if subtract: skZipSub else: skZipAdd), name: "vec" & $number, n: n, leftV: left, rightV: right))),
    scalarTimesVector: proc(s: Rep[float], v: Arr[float]): Arr[float] =
      (if not s.isStatic and VectorNode(s.node).kind == skDivF and VectorNode(s.node).leftF.isStatic and
          VectorNode(s.node).leftF.staticVal == 1.0 and not VectorNode(s.node).rightF.isStatic and
          VectorNode(s.node).rightF.node of VectorNode and VectorNode(VectorNode(s.node).rightF.node).kind == skVectorNorm and
          VectorNode(VectorNode(s.node).rightF.node).vec == v:
        (inc number; Arr[float](node: VectorNode(kind: skUnitVector, name: "vec" & $number, vec: v)))
       else: (inc number; newArray[float](lenArr[float](v, proc(v: Arr[float]): IRNode = VectorNode(kind: skLen, vec: v)),
         proc(n: Rep[int]): IRNode = VectorNode(kind: skScalarMul, name: "vec" & $number, n: n, vec: v, valueF: s)))),
    vectorNorm: proc(v: Arr[float]): Rep[float] =
      (if VectorNode(v.node).kind == skUnitVector: liftNow(1.0)
       else: dynamic[float](VectorNode(kind: skVectorNorm, vec: v))),
    sqrtF: proc(x: Rep[float]): Rep[float] =
      (if x.isStatic: liftNow(sqrt(x.staticVal)) else: dynamic[float](VectorNode(kind: skSqrt, leftF: x))))

proc numeric[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V]): Numeric[F] =
  Numeric[F](plus: s.addF, minus: s.subF, times: s.mulF, zero: proc(): F = s.litF(0))

proc vecAdd[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], a, b: V): V =
  s.newVector(s.length(a), a, b, false)
proc vecSub[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], a, b: V): V =
  s.newVector(s.length(a), a, b, true)
proc vecSum[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], v: V): F =
  let i = s.varNewI(s.litI(0)); let acc = s.varNewF(n.zero())
  discard s.whileLoop(proc(): B = s.ltI(s.readI(i), s.length(v)), proc(): S =
    s.seq(s.writeF(acc, n.plus(s.readF(acc), s.apply(v, s.readI(i)))),
      s.writeI(i, s.addI(s.readI(i), s.litI(1)))))
  s.readF(acc)
proc vecAvg[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], v: V): F =
  s.divF(vecSum(s, n, v), s.toFloat(s.length(v)))
proc norm[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], v: V): F =
  s.vectorNorm(v)
proc scalarTimesVector[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], x: F, v: V): V =
  s.scalarTimesVector(x, v)
proc unitVector[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], v: V): V =
  scalarTimesVector(s, s.divF(s.litF(1), norm(s, n, v)), v)
proc dist[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], n: Numeric[F], a, b: V): F =
  norm(s, n, vecSub(s, n, a, b))

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = VectorNode(r.node)
  case n.kind
  of skLen: "len(" & VectorNode(n.vec.node).name & ")"
  of skAddI: "(" & emitInt(n.leftI) & " + " & emitInt(n.rightI) & ")"
  of skReadI: VectorNode(n.vi.node).name
  else: raise newException(ValueError, "bad int expression")
proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let n = VectorNode(r.node)
  case n.kind
  of skReadF: VectorNode(n.vec.node).name & "[" & emitInt(n.index) & "]"
  of skReadVarF: VectorNode(n.vf.node).name
  of skAddF: "(" & emitFloat(n.leftF) & " + " & emitFloat(n.rightF) & ")"
  of skSubF: "(" & emitFloat(n.leftF) & " - " & emitFloat(n.rightF) & ")"
  of skMulF: "(" & emitFloat(n.leftF) & " * " & emitFloat(n.rightF) & ")"
  of skDivF: "(" & emitFloat(n.leftF) & " / " & emitFloat(n.rightF) & ")"
  of skSqrt: "sqrt(" & emitFloat(n.leftF) & ")"
  of skVectorNorm: "normResult"
  else: raise newException(ValueError, "bad float expression")
proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = VectorNode(r.node); "(" & emitInt(n.leftI) & " < " & emitInt(n.rightI) & ")"
proc emitStmt(r: Rep[Unit], ind = ""): string =
  if r.isStatic: return ind & "discard"
  let n = VectorNode(r.node)
  case n.kind
  of skSeq: emitStmt(n.a, ind) & "\n" & emitStmt(n.b, ind)
  of skWhile: ind & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b, ind & "  ")
  of skWriteI: ind & VectorNode(n.vi.node).name & " = " & emitInt(n.leftI)
  of skWriteF: ind & VectorNode(n.vf.node).name & " = " & emitFloat(n.valueF)
  else: raise newException(ValueError, "bad statement")
proc emitDeclI(v: Var[int]): string =
  let n = VectorNode(v.node)
  "var " & n.name & " = " & emitInt(n.initI)
proc emitDeclF(v: Var[float]): string =
  let n = VectorNode(v.node)
  "var " & n.name & " = " & emitFloat(n.initF)
proc emitVectorDecl(v: Arr[float]): string =
  let n = VectorNode(v.node)
  case n.kind
  of skInput: "var " & n.name & ": seq[float] = " & $n.data
  of skZipAdd, skZipSub:
    let name = n.name
    let op = if n.kind == skZipSub: " - " else: " + "
    "var " & name & " = newSeq[float](" & emitInt(n.n) & ")\n" &
    "var " & name & "Index = 0\nwhile " & name & "Index < len(" & name & "):\n  " & name & "[" & name & "Index] = " & VectorNode(n.leftV.node).name & "[" & name & "Index]" & op & VectorNode(n.rightV.node).name & "[" & name & "Index]\n  " & name & "Index += 1"
  of skUnitVector:
    # Unit vector: element = input[i] / norm(input). The norm is accumulated
    # first (per-vector name, so several unit vectors can coexist); the
    # UnitVector node carries no length, so use len(input).
    let name = n.name
    let src = VectorNode(n.vec.node).name
    "var " & name & "NormAcc = 0.0\n" &
    "var " & name & "NormIndex = 0\nwhile " & name & "NormIndex < len(" & src & "):\n  " & name & "NormAcc += " & src & "[" & name & "NormIndex] * " & src & "[" & name & "NormIndex]\n  " & name & "NormIndex += 1\n" &
    "let " & name & "Norm = sqrt(" & name & "NormAcc)\n" &
    "var " & name & " = newSeq[float](len(" & src & "))\n" &
    "var " & name & "Index = 0\nwhile " & name & "Index < len(" & name & "):\n  " & name & "[" & name & "Index] = (1.0 / " & name & "Norm) * " & src & "[" & name & "Index]\n  " & name & "Index += 1"
  of skScalarMul:
    let name = n.name
    "var " & name & " = newSeq[float](" & emitInt(n.n) & ")\n" &
    "var " & name & "Index = 0\nwhile " & name & "Index < len(" & name & "):\n  " & name & "[" & name & "Index] = " & emitFloat(n.valueF) & " * " & VectorNode(n.vec.node).name & "[" & name & "Index]\n  " & name & "Index += 1"
  else: raise newException(ValueError, "not a vector declaration")

proc compileRun(src, exe, dir: string): string =
  let nim = findExe("nim"); doAssert nim.len > 0
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

when isMainModule:
  let inputs = [@[1.0, 2.5, -1.5, 4.0], @[7.25], newSeq[float](0)]
  proc total(xs: seq[float]): float =
    for x in xs: result += x
  proc sqDiffSum(xs, ys: seq[float]): float =
    for i in 0 ..< xs.len: result += (xs[i] - ys[i]) * (xs[i] - ys[i])
  let d = directSym(); let dn = numeric(d)
  for a in inputs:
    let b = a.mapIt(it * 2.0); let av = d.input(a); let bv = d.input(b)
    doAssert vecAdd(d, dn, av, bv) == a.zip(b).mapIt(it[0] + it[1])
    doAssert vecSub(d, dn, av, bv) == a.zip(b).mapIt(it[0] - it[1])
    doAssert vecSum(d, dn, av) == total(a)
    if a.len > 0:
      doAssert vecAvg(d, dn, av) == total(a) / a.len.float
      doAssert abs(dist(d, dn, av, bv) - sqrt(sqDiffSum(a, b))) < 1e-9
  proc checkResidual(a: seq[float]) =
    let st = stagedSym(); let nt = numeric(st)
    let left = st.input(a); let right = st.input(a.mapIt(it * 2.0))
    let addv = vecAdd(st, nt, left, right); let subv = vecSub(st, nt, left, right)
    let checkDir = getTempDir() / ("vecarith-case-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000) & "-" & $a.len)
    createDir(checkDir)
    let checkSource = checkDir / "residual.nim"; let checkExe = checkDir / "residual"
    writeFile(checkSource, emitVectorDecl(left) & "\n" & emitVectorDecl(right) & "\n" & emitVectorDecl(addv) & "\n" & emitVectorDecl(subv) &
      "\necho " & VectorNode(addv.node).name & "\necho " & VectorNode(subv.node).name)
    let lines = compileRun(checkSource, checkExe, checkDir).splitLines
    doAssert lines[0].contains($a.mapIt(it * 3.0))
    doAssert lines[1].contains($a.mapIt(it * -1.0))
    removeDir(checkDir)
  checkResidual(inputs[1])
  checkResidual(inputs[2])
  let s = stagedSym(); let sn = numeric(s); let sv = s.input(inputs[0]); let bv = s.input(inputs[0].mapIt(it * 2.0))
  let sumv = vecAdd(s, sn, sv, bv); let difv = vecSub(s, sn, sv, bv)
  let sumText = emitVectorDecl(sv) & "\n" & emitVectorDecl(bv) & "\n" & emitVectorDecl(sumv)
  doAssert "while" in sumText and "DeliteOpLoop" notin sumText and "dispatch" notin sumText
  doAssert sumText.count("while") == 1
  let dir = getTempDir() / ("vecarith-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000)); createDir(dir)
  let source = dir / "residual.nim"; let exe = dir / "residual"
  let body = emitVectorDecl(sv) & "\n" & emitVectorDecl(bv) & "\n" & emitVectorDecl(sumv) & "\n" & emitVectorDecl(difv) &
    "\necho " & VectorNode(sumv.node).name & "\necho " & VectorNode(difv.node).name
  writeFile(source, body); let outputLines = compileRun(source, exe, dir).splitLines
  doAssert outputLines[0].contains("[3.0, 7.5, -4.5, 12.0]") and outputLines[1].contains("[-1.0, -2.5, 1.5, -4.0]")
  doAssert emitVectorDecl(sumv).contains("while")
  let directNorm = norm(d, dn, d.input(inputs[0]))
  doAssert abs(directNorm - sqrt(1.0 + 6.25 + 2.25 + 16.0)) < 1e-9
  let nv = norm(s, sn, sv); doAssert emitFloat(nv) == "normResult"
  let uv = unitVector(s, sn, sv)
  # The norm fold goes through norm() itself: norm of a UnitVector node is
  # the static literal 1, with no division emitted.
  let un = norm(s, sn, uv)
  doAssert un.isStatic and un.staticVal == 1.0 and emitFloat(un) == "1.0"
  doAssert " / " notin emitFloat(un)
  # Emitting the unit vector itself must produce the true unit vector
  # (element / norm), not a placeholder: compile-and-run the residual.
  let uvDir = getTempDir() / ("vecarith-uv-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000)); createDir(uvDir)
  let uvSource = uvDir / "residual.nim"; let uvExe = uvDir / "residual"
  let uvName = VectorNode(uv.node).name
  writeFile(uvSource, "import std/math\n" & emitVectorDecl(sv) & "\n" & emitVectorDecl(uv) & "\necho " & uvName & "\n")
  let uvLines = compileRun(uvSource, uvExe, uvDir).splitLines
  let uvExpected = inputs[0].mapIt(it / directNorm)
  # Compare numerically: (1.0 / norm) * x and x / norm can differ by 1 ulp,
  # so exact string equality would be brittle.
  let uvGot = uvLines[0].strip()[2 .. ^2].split(", ").mapIt(parseFloat(it))
  doAssert uvGot.len == uvExpected.len
  for i in 0 ..< uvGot.len: doAssert abs(uvGot[i] - uvExpected[i]) < 1e-9
  removeDir(uvDir)
  let normDir = getTempDir() / ("vecarith-norm-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000)); createDir(normDir)
  let normSource = normDir / "residual.nim"; let normExe = normDir / "residual"
  writeFile(normSource, "import std/math\n" & emitVectorDecl(sv) & "\nvar normAcc = 0.0\nvar normIndex = 0\nwhile normIndex < len(" & VectorNode(sv.node).name & "):\n  normAcc += " & VectorNode(sv.node).name & "[normIndex] * " & VectorNode(sv.node).name & "[normIndex]\n  normIndex += 1\nlet normResult = sqrt(normAcc)\necho normResult\n")
  doAssert abs(parseFloat(compileRun(normSource, normExe, normDir)) - directNorm) < 1e-9
  removeDir(normDir)
  removeDir(dir)
  echo "ok: generic vector arithmetic"
