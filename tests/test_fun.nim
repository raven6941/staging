## Step 3: residual functions, keyed recursive registry, and multi-proc codegen.

import staging/framework
import staging/traversal
import std/[os, osproc, strutils, tables, times]

type
  FunKind = enum fkInput, fkAdd, fkSub, fkEq, fkMul, fkIf, fkApp, fkRef, fkArg, fkDef
  FunNode = ref object of IRNode
    case kind: FunKind
    of fkInput: name: string
    of fkAdd, fkSub, fkMul: left, right: Rep[int]
    of fkEq: eqLeft, eqRight: Rep[int]
    of fkIf:
      cond: Rep[bool]
      thenB, elseB: Rep[int]
    of fkApp:
      fn: Rep[proc(x: int): int]
      arg: Rep[int]
    of fkRef: funName: string
    of fkArg: discard
    of fkDef:
      defName: string
      funBody: Rep[int]

  FunState = ref object
    refs: Table[string, Rep[proc(x: int): int]]
    defs: seq[FunNode]

  FunSym[I, B, F] = object
    input: proc(name: string): I
    lit: proc(n: int): I
    add, sub, mul: proc(a, b: I): I
    eq: proc(a, b: I): B
    ifB: proc(c: B, t, e: proc(): I): I
    fun: proc(key: string, body: proc(x: I): I): F
    app: proc(f: F, x: I): I

proc directAck(m, n: int): int =
  if m == 0: n + 1
  elif n == 0: directAck(m - 1, 1)
  else: directAck(m - 1, directAck(m, n - 1))

proc directFunSym(): FunSym[int, bool, proc(x: int): int] =
  var refs = initTable[string, proc(x: int): int]()
  result = FunSym[int, bool, proc(x: int): int](
    input: proc(name: string): int =
      if name == "n": 3 else: raise newException(ValueError, name),
    lit: proc(n: int): int = n,
    add: proc(a, b: int): int = a + b,
    sub: proc(a, b: int): int = a - b,
    mul: proc(a, b: int): int = a * b,
    eq: proc(a, b: int): bool = a == b,
    ifB: proc(c: bool, t, e: proc(): int): int = (if c: t() else: e()),
    fun: proc(key: string, body: proc(x: int): int): proc(x: int): int =
      if refs.hasKey(key): refs[key]
      else:
        let f: proc(x: int): int = proc(x: int): int = body(x)
        refs[key] = f
        f,
    app: proc(f: proc(x: int): int, x: int): int = f(x))

proc stagedFunSym(state: FunState): FunSym[Rep[int], Rep[bool], Rep[proc(x: int): int]] =
  result = FunSym[Rep[int], Rep[bool], Rep[proc(x: int): int]](
    input: proc(name: string): Rep[int] =
      dynamic[int](FunNode(kind: fkInput, name: name)),
    lit: proc(n: int): Rep[int] = lift(n),
    add: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x + y,
      proc(x, y: Rep[int]): IRNode = FunNode(kind: fkAdd, left: x, right: y)),
    sub: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x - y,
      proc(x, y: Rep[int]): IRNode = FunNode(kind: fkSub, left: x, right: y)),
    mul: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x * y,
      proc(x, y: Rep[int]): IRNode = FunNode(kind: fkMul, left: x, right: y)),
    eq: proc(a, b: Rep[int]): Rep[bool] =
      if a.isStatic and b.isStatic: lift(a.staticVal == b.staticVal)
      else: dynamic[bool](FunNode(kind: fkEq, eqLeft: a, eqRight: b)),
    ifB: proc(c: Rep[bool], t, e: proc(): Rep[int]): Rep[int] =
      smartIf[int](c, t, e,
        proc(c: Rep[bool], t, e: Rep[int]): IRNode =
          FunNode(kind: fkIf, cond: c, thenB: t, elseB: e)),
    fun: proc(key: string, body: proc(x: Rep[int]): Rep[int]): Rep[proc(x: int): int] =
      if state.refs.hasKey(key):
        state.refs[key]
      else:
        let refRep = dynamic[proc(x: int): int](FunNode(kind: fkRef, funName: key))
        state.refs[key] = refRep
        smartFun[int, int](key, body,
          proc(): Rep[proc(x: int): int] = refRep,
          proc(): Rep[int] = dynamic[int](FunNode(kind: fkArg)),
          proc(body: Rep[int]): IRNode =
            let n = FunNode(kind: fkDef, defName: key, funBody: body)
            state.defs.add(n)
            n),
    app: proc(f: Rep[proc(x: int): int], x: Rep[int]): Rep[int] =
      dynamic[int](FunNode(kind: fkApp, fn: f, arg: x)))

proc ackProgram[I, B, F](s: FunSym[I, B, F]): I =
  proc ack(m: int): F =
    s.fun("ack_" & $m,
      proc(n: I): I =
        if m == 0:
          s.add(n, s.lit(1))
        else:
          s.ifB(s.eq(n, s.lit(0)),
            proc(): I = s.app(ack(m - 1), s.lit(1)),
            proc(): I = s.app(ack(m - 1), s.app(ack(m), s.sub(n, s.lit(1))))))
  s.app(ack(2), s.input("n"))

proc factProgram(s: FunSym[Rep[int], Rep[bool], Rep[proc(x: int): int]];
                 bodyCalls: ref int): Rep[int] =
  proc factBody(n: Rep[int]): Rep[int] =
    inc bodyCalls[]
    s.ifB(s.eq(n, s.lit(0)),
      proc(): Rep[int] = s.lit(1),
      proc(): Rep[int] = s.mul(n, s.app(s.fun("fact", factBody),
        s.sub(n, s.lit(1)))))
  s.app(s.fun("fact", factBody), s.input("n"))

proc emitBool(r: Rep[bool]): string
proc emitFun(r: Rep[proc(x: int): int]): string

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = FunNode(r.node)
  case n.kind
  of fkInput: n.name
  of fkArg: "n"
  of fkAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of fkSub: "(" & emitInt(n.left) & " - " & emitInt(n.right) & ")"
  of fkMul: "(" & emitInt(n.left) & " * " & emitInt(n.right) & ")"
  of fkEq: raise newException(ValueError, "bool in int position")
  of fkIf: "(if " & emitBool(n.cond) & ": " & emitInt(n.thenB) &
    " else: " & emitInt(n.elseB) & ")"
  of fkApp: emitFun(n.fn) & "(" & emitInt(n.arg) & ")"
  else: raise newException(ValueError, "not an int expression")

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = FunNode(r.node)
  doAssert n.kind == fkEq
  "(" & emitInt(n.eqLeft) & " == " & emitInt(n.eqRight) & ")"

proc emitFun(r: Rep[proc(x: int): int]): string =
  if r.isStatic: raise newException(ValueError, "static function")
  let n = FunNode(r.node)
  doAssert n.kind == fkRef
  n.funName

proc childNodes(n: FunNode): seq[FunNode] =
  case n.kind
  of fkInput, fkRef, fkArg: discard
  of fkAdd, fkSub, fkMul:
    if not n.left.isStatic: result.add(FunNode(n.left.node))
    if not n.right.isStatic: result.add(FunNode(n.right.node))
  of fkEq:
    if not n.eqLeft.isStatic: result.add(FunNode(n.eqLeft.node))
    if not n.eqRight.isStatic: result.add(FunNode(n.eqRight.node))
  of fkIf:
    if not n.cond.isStatic: result.add(FunNode(n.cond.node))
    if not n.thenB.isStatic: result.add(FunNode(n.thenB.node))
    if not n.elseB.isStatic: result.add(FunNode(n.elseB.node))
  of fkApp:
    result.add(FunNode(n.fn.node))
    if not n.arg.isStatic: result.add(FunNode(n.arg.node))
  of fkDef:
    if not n.funBody.isStatic: result.add(FunNode(n.funBody.node))

proc funCallbacks(): TraversalCallbacks[FunNode] =
  TraversalCallbacks[FunNode](
    children: childNodes,
    key: proc(n: FunNode): string = $n.kind,
    isComposite: proc(n: FunNode): bool = true,
    isBoundary: proc(n: FunNode): bool = false,
    rebuild: proc(n: FunNode; kids: seq[FunNode]): FunNode = n,
    makeRef: proc(x: string): FunNode = FunNode(kind: fkRef, funName: x),
    makeLet: proc(x: string; a, b: FunNode): FunNode = a)

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim compiler not found on PATH"
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

when isMainModule:
  # Load-bearing check: without smartFun plus the keyed registry this test
  # cannot be written: recursive staging re-enters the body and does not
  # produce the three residual definitions below.
  let direct = ackProgram(directFunSym())
  doAssert direct == directAck(2, 3)

  let state = FunState(refs: initTable[string, Rep[proc(x: int): int]](), defs: @[])
  let staged = ackProgram(stagedFunSym(state))
  doAssert not staged.isStatic and state.defs.len == 3
  doAssert state.defs[0].defName == "ack_0"
  doAssert state.defs[1].defName == "ack_1"
  doAssert state.defs[2].defName == "ack_2"
  doAssert occurrences(state.defs[2], funCallbacks()).getOrDefault("fkDef") == 1
  doAssert occurrences(state.defs[2], funCallbacks()).getOrDefault("fkApp") > 0
  # The parameter binding and the function name are distinct nodes:
  # ack_0's body (n + 1) mentions the argument once and no function ref.
  let ack0Body = occurrences(FunNode(state.defs[0].funBody.node), funCallbacks())
  doAssert ack0Body.getOrDefault("fkArg") == 1 and ack0Body.getOrDefault("fkRef") == 0

  var calls: ref int
  new(calls)
  calls[] = 0
  let factState = FunState(refs: initTable[string, Rep[proc(x: int): int]](), defs: @[])
  discard factProgram(stagedFunSym(factState), calls)
  doAssert calls[] == 1, "self-recursive body must be built exactly once"

  # Fun nodes are effectful unless the DSL has proved them pure; never feed a
  # subtree containing one to insertLets/insertLetsCb.  This DSL has no CSP
  # helpers, so import derivation from CSP is not applicable here.
  var source = ""
  for d in state.defs:
    source.add("proc " & d.defName & "(n: int): int =\n  " & emitInt(d.funBody) & "\n\n")
  source.add("when isMainModule:\n  echo " & emitInt(staged) & "\n")
  doAssert source.count("proc ack_") == 3
  for n in [0, 1, 2, 3, 4]:
    let dir = getTempDir() / ("staging-fun-" & $getCurrentProcessId() & "-" &
      $n & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let file = dir / "residual.nim"
    let exe = dir / "residual"
    writeFile(file, "let n = " & $n & "\n" & source)
    doAssert parseInt(compileRun(file, exe, dir)) == directAck(2, n)
    removeDir(dir)
  echo "ok: residual fun registry, recursive staging, traversal, and multi-proc codegen"
