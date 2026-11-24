import staging/framework
import staging/arrays
import std/[os, osproc, sequtils, strutils, times]

type
  K = enum kInput, kDecl, kLen, kRead, kWrite, kAdd, kSub, kMul, kLe,
    kVarDecl, kVarRead, kVarWrite, kSeq, kWhile
  N = ref object of IRNode
    kind: K
    name: string
    il, ir: Rep[int]
    fl, fr: Rep[float]
    cond: Rep[bool]
    iinit: Rep[int]
    finit: Rep[float]
    arr: Arr[float]
    index: Rep[int]
    value: Rep[float]
    iv: Var[int]
    fv: Var[float]
    a, b, body: Rep[Unit]
  Program = object
    body: Rep[Unit]
    input, output: Arr[float]
    j: Var[int]
    w1Prev, w1Cur, w1Next, wmCur, wmNext, w2Prev, w2Cur: Var[float]

proc ai(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
  proc(x, y: int): int = x + y, proc(x, y: Rep[int]): IRNode = N(kind: kAdd, il: x, ir: y))
proc si(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
  proc(x, y: int): int = x - y, proc(x, y: Rep[int]): IRNode = N(kind: kSub, il: x, ir: y))
proc af(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x + y, proc(x, y: Rep[float]): IRNode = N(kind: kAdd, fl: x, fr: y))
proc sf(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x - y, proc(x, y: Rep[float]): IRNode = N(kind: kSub, fl: x, fr: y))
proc mf(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x * y, proc(x, y: Rep[float]): IRNode = N(kind: kMul, fl: x, fr: y))
proc rf(a: Arr[float], i: Rep[int]): Rep[float] = readArr[float](a, i,
  proc(a: Arr[float], i: Rep[int]): IRNode = N(kind: kRead, arr: a, index: i))
proc w1(a: Arr[float], i: Rep[int]): Rep[float] = mf(rf(a, i), rf(a, ai(i, liftNow(1))))
proc wm(a: Arr[float], i: Rep[int]): Rep[float] = af(sf(rf(a, i), w1(a, i)), w1(a, si(i, liftNow(1))))
proc seqs(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
  proc(a, b: Rep[Unit]): IRNode = N(kind: kSeq, a: a, b: b))

proc build(): Program =
  let input = Arr[float](node: N(kind: kInput, name: "input"))
  let n = lenArr[float](input, proc(a: Arr[float]): IRNode = N(kind: kLen, arr: a))
  let output = newArray[float](n, proc(x: Rep[int]): IRNode = N(kind: kDecl, name: "output", il: x))
  proc fv(name: string, x: Rep[float]): Var[float] = newVar[float](x,
    proc(x: Rep[float]): IRNode = N(kind: kVarDecl, name: name, finit: x))
  let j = newVar[int](liftNow(2), proc(x: Rep[int]): IRNode = N(kind: kVarDecl, name: "j", iinit: x))
  let p = fv("w1Prev", w1(input, liftNow(1)))
  let c = fv("w1Cur", w1(input, liftNow(2)))
  let q = fv("w2Prev", mf(wm(input, liftNow(1)), wm(input, liftNow(2))))
  let qcur = fv("w2Cur", liftNow(0.0))
  let mcur = fv("wmCur", liftNow(0.0))
  let xnext = fv("w1Next", liftNow(0.0))
  let mnext = fv("wmNext", liftNow(0.0))
  let jr = readVar[int](j, proc(v: Var[int]): IRNode = N(kind: kVarRead, iv: v))
  let pr = readVar[float](p, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v))
  let cr = readVar[float](c, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v))
  let qr = readVar[float](q, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v))
  let curm = af(sf(rf(input, jr), cr), pr)
  let next = w1(input, ai(jr, liftNow(1)))
  let nextm = af(sf(rf(input, ai(jr, liftNow(1))),
    readVar[float](xnext, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v))), cr)
  let cur2 = mf(readVar[float](mcur, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v)),
    readVar[float](mnext, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v)))
  let qcurWrite = writeVar[float](qcur, cur2,
    proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x))
  let outputStmt = writeArr[float](output, jr, af(sf(readVar[float](mcur,
    proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v)),
    readVar[float](qcur, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v))), qr),
    proc(a: Arr[float], i: Rep[int], x: Rep[float]): IRNode = N(kind: kWrite, arr: a, index: i, value: x))
  var body = writeVar[float](mcur, curm, proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x))
  body = seqs(body, writeVar[float](xnext, next, proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x)))
  body = seqs(body, writeVar[float](mnext, nextm, proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x)))
  body = seqs(body, qcurWrite); body = seqs(body, outputStmt)
  body = seqs(body, writeVar[float](p, cr, proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x)))
  body = seqs(body, writeVar[float](c, readVar[float](xnext, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v)), proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x)))
  body = seqs(body, writeVar[float](q, readVar[float](qcur, proc(v: Var[float]): IRNode = N(kind: kVarRead, fv: v)), proc(v: Var[float], x: Rep[float]): IRNode = N(kind: kVarWrite, fv: v, value: x)))
  body = seqs(body, writeVar[int](j, ai(jr, liftNow(1)), proc(v: Var[int], x: Rep[int]): IRNode = N(kind: kVarWrite, iv: v, il: x)))
  let cond = dynamic[bool](N(kind: kLe, il: jr, ir: si(n, liftNow(3))))
  let loop = smartWhile(proc(): Rep[bool] = cond, proc(): Rep[Unit] = body,
    proc(c: Rep[bool], b: Rep[Unit]): IRNode = N(kind: kWhile, cond: c, body: b))
  Program(body: loop, input: input, output: output, j: j, w1Prev: p, w1Cur: c, w1Next: xnext, wmCur: mcur, wmNext: mnext, w2Prev: q, w2Cur: qcur)

proc ei(x: Rep[int]): string =
  if x.isStatic: return $x.staticVal
  let n = N(x.node)
  case n.kind
  of kAdd: "(" & ei(n.il) & " + " & ei(n.ir) & ")"
  of kSub: "(" & ei(n.il) & " - " & ei(n.ir) & ")"
  of kLen: "len(" & N(n.arr.node).name & ")"
  of kVarRead: N(n.iv.node).name
  else: raise newException(ValueError, "bad int")
proc ef(x: Rep[float]): string =
  if x.isStatic: return $x.staticVal
  let n = N(x.node)
  case n.kind
  of kRead: N(n.arr.node).name & "[" & ei(n.index) & "]"
  of kAdd: "(" & ef(n.fl) & " + " & ef(n.fr) & ")"
  of kSub: "(" & ef(n.fl) & " - " & ef(n.fr) & ")"
  of kMul: "(" & ef(n.fl) & " * " & ef(n.fr) & ")"
  of kVarRead: N(n.fv.node).name
  else: raise newException(ValueError, "bad float")
proc eb(x: Rep[bool]): string =
  let n = N(x.node); doAssert n.kind == kLe
  "(" & ei(n.il) & " <= " & ei(n.ir) & ")"
proc es(x: Rep[Unit], ind = ""): string =
  if x.isStatic: return ind & "discard"
  let n = N(x.node)
  case n.kind
  of kSeq: es(n.a, ind) & "\n" & es(n.b, ind)
  of kWhile: ind & "while " & eb(n.cond) & ":\n" & es(n.body, ind & "  ")
  of kWrite: ind & N(n.arr.node).name & "[" & ei(n.index) & "] = " & ef(n.value)
  of kVarWrite: ind & (if n.iv != nil: N(n.iv.node).name & " = " & ei(n.il) else: N(n.fv.node).name & " = " & ef(n.value))
  else: raise newException(ValueError, "bad stmt")
proc decl(a: Arr[float]): string = "var output = newSeq[float](len(input))"
proc decl(v: Var[int]): string = "var " & N(v.node).name & " = " & ei(N(v.node).iinit)
proc decl(v: Var[float]): string = "var " & N(v.node).name & " = " & ef(N(v.node).finit)
proc run(src, exe, dir: string): string =
  let r = execCmdEx(quoteShell(findExe("nim")) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  let q = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert q.exitCode == 0, q.output
  q.output.strip
proc direct(a: seq[float]): seq[float] =
  result = newSeq[float](a.len)
  for j in 2 .. a.len - 3:
    proc w1(k: int): float = a[k] * a[k + 1]
    proc wm(k: int): float = a[k] - w1(k) + w1(k - 1)
    proc w2(k: int): float = wm(k) * wm(k + 1)
    result[j] = wm(j) - w2(j) + w2(j - 1)

when isMainModule:
  let p = build(); let text = es(p.body)
  doAssert text.count("while ") == 1 and text.count("output[") == 1
  doAssert text.count("input[(j + 1)] * input[((j + 1) + 1)]") == 1, text
  for n in [4, 5, 8]:
    var a = newSeq[float](n)
    for i in 0 ..< n: a[i] = float(i + 2)
    let dir = getTempDir() / ("staging-stencil-" & $getCurrentProcessId() & "-" & $n & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let src = dir / "residual.nim"
    var s = "var input = @[" & a.mapIt($it).join(", ") & "]\n" & decl(p.output) & "\n" & decl(p.j) & "\n" & decl(p.w1Prev) & "\n" & decl(p.w1Cur) & "\n" & decl(p.w1Next) & "\n" & decl(p.wmCur) & "\n" & decl(p.wmNext) & "\n" & decl(p.w2Prev) & "\n" & decl(p.w2Cur) & "\n" & text & "\n"
    for i in 0 ..< n: s.add("echo output[" & $i & "]\n")
    writeFile(src, s)
    let got = run(src, dir / "residual", dir).splitLines
    let want = direct(a)
    for i in 0 ..< n: doAssert abs(parseFloat(got[i]) - want[i]) < 1e-8, $i & " got=" & got[i] & " want=" & $want[i]
    removeDir(dir)
  echo "ok: dynamic staged stencil with carried sliding products"
