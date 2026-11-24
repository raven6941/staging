## Sequential VectorOps core: vectors are residual Arr cells and all iteration
## is unfolded to ordinary while loops.

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times]

type
  Vector[T] = Arr[T]
  VectorKind = enum skInput, skRand, skLen, skReadF, skLitF, skAddF, skDivF,
    skLitI, skAddI, skLtI, skDeclI, skReadI, skWriteI, skDeclF, skReadVarF,
    skWriteF, skToFloat, skSeq, skIf, skWhile
  VectorNode = ref object of IRNode
    kind: VectorKind
    name: string
    data: seq[float]
    n: Rep[int]
    vec: Arr[float]
    index: Rep[int]
    valueF: Rep[float]
    leftF, rightF: Rep[float]
    leftI, rightI: Rep[int]
    cond: Rep[bool]
    initI: Rep[int]
    initF: Rep[float]
    vi: Var[int]
    vf: Var[float]
    a, b, thenB, elseB: Rep[Unit]

  VectorSym[I, F, B, S, VI, VF, V] = object
    litI: proc(x: int): I
    litF: proc(x: float): F
    toFloat: proc(x: I): F
    addF, divF: proc(x, y: F): F
    addI: proc(x, y: I): I
    ltI: proc(x, y: I): B
    ifB: proc(c: B, t, e: proc(): S): S
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
    rand: proc(n: I): V
    length: proc(v: V): I
    apply: proc(v: V, i: I): F

  VectorProgram[I, F, S, V, VI, VF] = object
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
    divF: proc(x, y: float): float = x / y,
    addI: proc(x, y: int): int = x + y,
    ltI: proc(x, y: int): bool = x < y,
    ifB: proc(c: bool, t, e: proc(): Unit): Unit = (if c: t() else: e()),
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
    rand: proc(n: int): seq[float] = (result = newSeq[float](n); for i in 0 ..< n: result[i] = float((i * 17 + 3) mod 101)),
    length: proc(v: seq[float]): int = v.len,
    apply: proc(v: seq[float], i: int): float = v[i])

proc stagedSym(): VectorSym[Rep[int], Rep[float], Rep[bool], Rep[Unit], Var[int],
    Var[float], Arr[float]] =
  var number = 0
  result = VectorSym[Rep[int], Rep[float], Rep[bool], Rep[Unit], Var[int],
    Var[float], Arr[float]](
    litI: proc(x: int): Rep[int] = liftNow(x), litF: proc(x: float): Rep[float] = liftNow(x),
    toFloat: proc(x: Rep[int]): Rep[float] = dynamic[float](VectorNode(kind: skToFloat, leftI: x)),
    addF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y,
      proc(a, b: float): float = a + b,
      proc(a, b: Rep[float]): IRNode = VectorNode(kind: skAddF, leftF: a, rightF: b)),
    divF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y,
      proc(a, b: float): float = a / b,
      proc(a, b: Rep[float]): IRNode = VectorNode(kind: skDivF, leftF: a, rightF: b)),
    addI: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y,
      proc(a, b: int): int = a + b,
      proc(a, b: Rep[int]): IRNode = VectorNode(kind: skAddI, leftI: a, rightI: b)),
    ltI: proc(x, y: Rep[int]): Rep[bool] =
      (if x.isStatic and y.isStatic: liftNow(x.staticVal < y.staticVal)
       else: dynamic[bool](VectorNode(kind: skLtI, leftI: x, rightI: y))),
    ifB: proc(c: Rep[bool], t, e: proc(): Rep[Unit]): Rep[Unit] = smartIf[Unit](c, t, e,
      proc(c: Rep[bool], a, b: Rep[Unit]): IRNode = VectorNode(kind: skIf, cond: c, thenB: a, elseB: b)),
    unit: proc(): Rep[Unit] = unit(),
    seq: proc(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
      proc(a, b: Rep[Unit]): IRNode = VectorNode(kind: skSeq, a: a, b: b)),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] = smartWhile(c, body,
      proc(c: Rep[bool], b: Rep[Unit]): IRNode = VectorNode(kind: skWhile, cond: c, b: b)),
    varNewI: proc(x: Rep[int]): Var[int] = (inc number; newVar[int](x,
      proc(x: Rep[int]): IRNode = VectorNode(kind: skDeclI, name: "i" & $number, initI: x))),
    readI: proc(v: Var[int]): Rep[int] = readVar[int](v,
      proc(v: Var[int]): IRNode = VectorNode(kind: skReadI, vi: v)),
    writeI: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = VectorNode(kind: skWriteI, vi: v, leftI: x)),
    varNewF: proc(x: Rep[float]): Var[float] = (inc number; newVar[float](x,
      proc(x: Rep[float]): IRNode = VectorNode(kind: skDeclF, name: "acc" & $number, initF: x))),
    readF: proc(v: Var[float]): Rep[float] = readVar[float](v,
      proc(v: Var[float]): IRNode = VectorNode(kind: skReadVarF, vf: v)),
    writeF: proc(v: Var[float], x: Rep[float]): Rep[Unit] = writeVar[float](v, x,
      proc(v: Var[float], x: Rep[float]): IRNode = VectorNode(kind: skWriteF, vf: v, valueF: x)),
    input: proc(data: seq[float]): Arr[float] = Arr[float](node: VectorNode(kind: skInput, name: "input", data: data)),
    rand: proc(n: Rep[int]): Arr[float] = newArray[float](n,
      proc(n: Rep[int]): IRNode = VectorNode(kind: skRand, name: "randomVec", n: n)),
    length: proc(v: Arr[float]): Rep[int] = lenArr[float](v,
      proc(v: Arr[float]): IRNode = VectorNode(kind: skLen, vec: v)),
    apply: proc(v: Arr[float], i: Rep[int]): Rep[float] = readArr[float](v, i,
      proc(v: Arr[float], i: Rep[int]): IRNode = VectorNode(kind: skReadF, vec: v, index: i)))

proc sumProgram[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V): VectorProgram[I, F, S, V, VI, VF] =
  let i = s.varNewI(s.litI(0)); let acc = s.varNewF(s.litF(0))
  let body = s.whileLoop(proc(): B = s.ltI(s.readI(i), s.length(v)), proc(): S =
    s.seq(s.writeF(acc, s.addF(s.readF(acc), s.apply(v, s.readI(i)))),
      s.writeI(i, s.addI(s.readI(i), s.litI(1)))))
  VectorProgram[I, F, S, V, VI, VF](body: body, result: s.readF(acc), vector: v,
    index: i, accumulator: acc)

proc sum[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V): F =
  sumProgram(s, v).result

proc foreachProgram[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V,
    body: proc(i: I, x: F): S): tuple[body: S, index: VI] =
  let i = s.varNewI(s.litI(0))
  (body: s.whileLoop(proc(): B = s.ltI(s.readI(i), s.length(v)), proc(): S =
    s.seq(body(s.readI(i), s.apply(v, s.readI(i))),
      s.writeI(i, s.addI(s.readI(i), s.litI(1))))), index: i)

proc foreach[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V,
    body: proc(i: I, x: F): S): S =
  foreachProgram(s, v, body).body

proc countProgram[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V,
    predicate: proc(i: I, x: F): B): tuple[body: S, result: I, index: VI, acc: VI] =
  let i = s.varNewI(s.litI(0)); let acc = s.varNewI(s.litI(0))
  let body = s.whileLoop(proc(): B = s.ltI(s.readI(i), s.length(v)), proc(): S =
    s.seq(s.ifB(predicate(s.readI(i), s.apply(v, s.readI(i))),
      proc(): S = s.writeI(acc, s.addI(s.readI(acc), s.litI(1))),
      proc(): S = s.unit()), s.writeI(i, s.addI(s.readI(i), s.litI(1)))))
  (body: body, result: s.readI(acc), index: i, acc: acc)

proc count[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V,
    predicate: proc(i: I, x: F): B): I =
  countProgram(s, v, predicate).result

proc avg[I, F, B, S, VI, VF, V](s: VectorSym[I, F, B, S, VI, VF, V], v: V): F =
  s.divF(sum(s, v), s.toFloat(s.length(v)))

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = VectorNode(r.node)
  case n.kind
  of skLen: "len(" & VectorNode(n.vec.node).name & ")"
  of skAddI: "(" & emitInt(n.leftI) & " + " & emitInt(n.rightI) & ")"
  of skReadI: VectorNode(n.vi.node).name
  else: raise newException(ValueError, "bad int expression " & $n.kind)

proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let n = VectorNode(r.node)
  case n.kind
  of skReadF: VectorNode(n.vec.node).name & "[" & emitInt(n.index) & "]"
  of skReadVarF: VectorNode(n.vf.node).name
  of skAddF: "(" & emitFloat(n.leftF) & " + " & emitFloat(n.rightF) & ")"
  of skDivF: "(" & emitFloat(n.leftF) & " / " & emitFloat(n.rightF) & ")"
  of skToFloat: "float(" & emitInt(n.leftI) & ")"
  else: raise newException(ValueError, "bad float expression")

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = VectorNode(r.node); doAssert n.kind == skLtI
  "(" & emitInt(n.leftI) & " < " & emitInt(n.rightI) & ")"

proc emitStmt(r: Rep[Unit], ind = ""): string =
  if r.isStatic: return ind & "discard"
  let n = VectorNode(r.node)
  case n.kind
  of skSeq: emitStmt(n.a, ind) & "\n" & emitStmt(n.b, ind)
  of skWhile: ind & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b, ind & "  ")
  of skIf: ind & "if " & emitBool(n.cond) & ":\n" & emitStmt(n.thenB, ind & "  ") & "\n" & ind & "else:\n" & emitStmt(n.elseB, ind & "  ")
  of skWriteI: ind & VectorNode(n.vi.node).name & " = " & emitInt(n.leftI)
  of skWriteF: ind & VectorNode(n.vf.node).name & " = " & emitFloat(n.valueF)
  else: raise newException(ValueError, "bad statement " & $n.kind)

proc emitDeclI(v: Var[int]): string =
  let n = VectorNode(v.node); "var " & n.name & " = " & emitInt(n.initI)
proc emitDeclF(v: Var[float]): string =
  let n = VectorNode(v.node); "var " & n.name & " = " & emitFloat(n.initF)

proc emitVectorDecl(v: Arr[float]): string =
  let n = VectorNode(v.node)
  case n.kind
  of skInput: "var " & n.name & " = " & $n.data
  of skRand:
    "var " & n.name & " = newSeq[float](" & emitInt(n.n) & ")\n" &
      "var randIndex = 0\n" &
      "while randIndex < len(" & n.name & "):\n" &
      "  " & n.name & "[randIndex] = float((randIndex * 17 + 3) mod 101)\n" &
      "  randIndex += 1"
  else: raise newException(ValueError, "not a vector declaration")

proc compileRun(src, exe, dir: string): string =
  let nim = findExe("nim"); doAssert nim.len > 0
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

when isMainModule:
  let values = @[1.0, 2.5, -1.5, 4.0]
  let one = @[7.25]
  let empty = newSeq[float](0)
  proc total(xs: seq[float]): float =
    for x in xs: result += x
  proc positive(xs: seq[float]): int =
    for x in xs:
      if x > 0: inc result
  for input in [values, one, empty]:
    let d = directSym(); let v = d.input(input)
    doAssert sum(d, v) == total(input)
    doAssert d.length(v) == input.len
    doAssert count(d, v, proc(i: int, x: float): bool = x > 0) == positive(input)
    var seen = 0.0
    discard foreach(d, v, proc(i: int, x: float): Unit = (seen += x; Unit()))
    doAssert seen == total(input)
    if input.len > 0: doAssert avg(d, v) == total(input) / input.len.float

  let ss = stagedSym(); let sv = ss.input(values); let p = sumProgram(ss, sv)
  let text = emitStmt(p.body)
  doAssert "while" in text and "DeliteOpLoop" notin text
  let stagedAvg = avg(ss, sv)
  doAssert "float(len(input))" in emitFloat(stagedAvg)
  let stagedForeach = foreach(ss, sv, proc(i: Rep[int], x: Rep[float]): Rep[Unit] = ss.unit())
  doAssert "while" in emitStmt(stagedForeach)
  let stagedCount = count(ss, sv, proc(i: Rep[int], x: Rep[float]): Rep[bool] = ss.ltI(ss.litI(0), i))
  doAssert not stagedCount.isStatic
  # foreach/count residual, compiled and run: the foreach accumulator must
  # match the direct total and the count (indices > 0) must match len - 1.
  # The earlier draft only asserted the staged count was non-static and
  # never emitted its loop, so a broken count loop would have passed.
  let cs = stagedSym(); let cv = cs.input(values)
  let facc = cs.varNewF(cs.litF(0))
  let fp = foreachProgram(cs, cv, proc(i: Rep[int], x: Rep[float]): Rep[Unit] =
    cs.writeF(facc, cs.addF(cs.readF(facc), x)))
  let cp = countProgram(cs, cv, proc(i: Rep[int], x: Rep[float]): Rep[bool] =
    cs.ltI(cs.litI(0), i))
  let ctext = emitStmt(cs.seq(fp.body, cp.body))
  doAssert "while" in ctext and "DeliteOpLoop" notin ctext
  let cdir = getTempDir() / ("vectorops-fc-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(cdir)
  let csource = cdir / "residual.nim"; let cexe = cdir / "residual"
  writeFile(csource, emitVectorDecl(cv) & "\n" & emitDeclI(fp.index) & "\n" &
    emitDeclF(facc) & "\n" & emitDeclI(cp.index) & "\n" & emitDeclI(cp.acc) & "\n" &
    ctext & "\necho " & emitFloat(cs.readF(facc)) & "\necho " & emitInt(cp.result) & "\n")
  let cout = compileRun(csource, cexe, cdir).splitWhitespace
  doAssert parseFloat(cout[0]) == total(values)
  doAssert parseInt(cout[1]) == values.len - 1
  removeDir(cdir)
  let dir = getTempDir() / ("vectorops-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"; let exe = dir / "residual"
  writeFile(source, emitVectorDecl(sv) & "\n" & emitDeclI(p.index) & "\n" &
    emitDeclF(p.accumulator) & "\n" & text & "\necho " & emitFloat(p.result) & "\n")
  doAssert parseFloat(compileRun(source, exe, dir)) == total(values)
  removeDir(dir)

  let rs = stagedSym(); let rv = rs.rand(rs.litI(9)); let rl = rs.length(rv)
  let rdir = getTempDir() / ("vectorops-rand-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(rdir)
  let rsource = rdir / "residual.nim"; let rexe = rdir / "residual"
  writeFile(rsource, emitVectorDecl(rv) & "\necho " & emitInt(rl) & "\n")
  doAssert compileRun(rsource, rexe, rdir) == "9"
  removeDir(rdir)
  echo "ok: sequential VectorOps"
