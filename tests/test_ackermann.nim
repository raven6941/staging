## Staged Ackermann specialization: a static tower of residual functions.

import staging/framework
import std/[os, osproc, strutils, tables, times]

type
  AckKind = enum
    akInput, akAdd, akSub, akEq, akIf, akApp, akRef, akArg, akComment, akDef
  AckNode = ref object of IRNode
    case kind: AckKind
    of akInput: inputName: string
    of akAdd, akSub: left, right: Rep[int]
    of akEq: eqLeft, eqRight: Rep[int]
    of akIf:
      cond: Rep[bool]
      thenB, elseB: Rep[int]
    of akApp:
      fn: Rep[proc(x: int): int]
      arg: Rep[int]
    of akRef: funName: string
    of akArg: discard
    of akComment:
      label: string
      commented: Rep[int]
    of akDef:
      defName: string
      funBody: Rep[int]

  AckState = ref object
    refs: Table[string, Rep[proc(x: int): int]]
    defs: seq[AckNode]

proc mkAckIf(c: Rep[bool], t, e: Rep[int]): IRNode =
  AckNode(kind: akIf, cond: c, thenB: t, elseB: e)

proc directAck(m, n: int): int =
  if m == 0: n + 1
  elif n == 0: directAck(m - 1, 1)
  else: directAck(m - 1, directAck(m, n - 1))

proc stagedAck(state: AckState, m: int): Rep[proc(x: int): int]

proc ackElse(state: AckState, m: int, n: Rep[int]): Rep[int] =
  let arg = smartOp[int](n, liftNow(1),
    proc(x, y: int): int = x - y,
    proc(x, y: Rep[int]): IRNode = AckNode(kind: akSub, left: x, right: y))
  let inner = dynamic[int](AckNode(kind: akApp, fn: stagedAck(state, m), arg: arg))
  dynamic[int](AckNode(kind: akApp, fn: stagedAck(state, m - 1), arg: inner))

proc ackBody(state: AckState, m: int, key: string, n: Rep[int]): Rep[int] =
  let body =
    if m == 0:
      smartOp[int](n, liftNow(1), proc(x, y: int): int = x + y,
        proc(x, y: Rep[int]): IRNode = AckNode(kind: akAdd, left: x, right: y))
    else:
      let zero = if n.isStatic: liftNow(n.staticVal == 0)
                 else: dynamic[bool](AckNode(kind: akEq, eqLeft: n, eqRight: liftNow(0)))
      smartIf[int](zero,
        proc(): Rep[int] = dynamic[int](AckNode(kind: akApp,
          fn: stagedAck(state, m - 1), arg: liftNow(1))),
        proc(): Rep[int] = ackElse(state, m, n), mkAckIf)
  dynamic[int](AckNode(kind: akComment, label: key, commented: body))

proc stagedAck(state: AckState, m: int): Rep[proc(x: int): int] =
  let key = "ack_" & $m
  if state.refs.hasKey(key): return state.refs[key]
  let refRep = dynamic[proc(x: int): int](AckNode(kind: akRef, funName: key))
  # Publish before entering the body: recursive calls return this reference.
  state.refs[key] = refRep
  discard smartFun[int, int](key,
    proc(n: Rep[int]): Rep[int] = ackBody(state, m, key, n),
    proc(): Rep[proc(x: int): int] = refRep,
    proc(): Rep[int] = dynamic[int](AckNode(kind: akArg)),
    proc(body: Rep[int]): IRNode =
      let d = AckNode(kind: akDef, defName: key, funBody: body)
      state.defs.add(d)
      d)
  refRep

proc ackProgram(state: AckState, m: int): Rep[int] =
  dynamic[int](AckNode(kind: akApp, fn: stagedAck(state, m),
    arg: dynamic[int](AckNode(kind: akInput, inputName: "n"))))

proc emitBool(r: Rep[bool]): string
proc emitFun(r: Rep[proc(x: int): int]): string

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = AckNode(r.node)
  case n.kind
  of akInput: n.inputName
  of akArg: "n"
  of akAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of akSub: "(" & emitInt(n.left) & " - " & emitInt(n.right) & ")"
  of akEq: raise newException(ValueError, "bool in int position")
  of akIf: "(if " & emitBool(n.cond) & ": " & emitInt(n.thenB) &
    " else: " & emitInt(n.elseB) & ")"
  of akApp: emitFun(n.fn) & "(" & emitInt(n.arg) & ")"
  of akComment: "(block:\n    # // " & n.label & "\n    " & emitInt(n.commented) & ")"
  else: raise newException(ValueError, "not an int expression")

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = AckNode(r.node)
  doAssert n.kind == akEq
  "(" & emitInt(n.eqLeft) & " == " & emitInt(n.eqRight) & ")"

proc emitFun(r: Rep[proc(x: int): int]): string =
  let n = AckNode(r.node)
  doAssert n.kind == akRef
  n.funName

proc commentIsPure(n: AckNode): bool = n.kind != akComment

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

proc residualSource(state: AckState, residual: Rep[int]): string =
  result = "import std/os\n\n"
  for d in state.defs:
    result.add("proc " & d.defName & "(n: int): int\n")
  result.add("\n")
  for d in state.defs:
    result.add("proc " & d.defName & "(n: int): int =\n  " & emitInt(d.funBody) & "\n\n")
  result.add("when isMainModule:\n  echo " & emitInt(residual) & "\n")

when isMainModule:
  for m in 0..2:
    for n in 0..5:
      doAssert directAck(m, n) == (if m == 0: n + 1 elif m == 1: n + 2 else: 2 * n + 3)
      let state = AckState(refs: initTable[string, Rep[proc(x: int): int]](), defs: @[])
      let residual = ackProgram(state, m)
      doAssert commentIsPure(AckNode(state.defs[0].funBody.node)) == false
      let source = residualSource(state, residual)
      let dir = getTempDir() / ("staging-ackermann-" & $getCurrentProcessId() & "-" &
        $m & "-" & $n & "-" & $int(epochTime() * 1000))
      createDir(dir)
      let file = dir / "residual.nim"
      let exe = dir / "residual"
      writeFile(file, "let n = " & $n & "\n" & source)
      doAssert parseInt(compileRun(file, exe, dir)) == directAck(m, n)
      removeDir(dir)

  let state = AckState(refs: initTable[string, Rep[proc(x: int): int]](), defs: @[])
  let residual = ackProgram(state, 2)
  let source = residualSource(state, residual)
  doAssert state.defs.len == 3
  doAssert source.count("proc ack_") == 6 # three forward declarations + definitions
  doAssert source.count("proc ack_0(n: int): int =") == 1
  doAssert source.count("proc ack_1(n: int): int =") == 1
  doAssert source.count("proc ack_2(n: int): int =") == 1
  doAssert source.count("# // ack_0") == 1
  doAssert source.count("# // ack_1") == 1
  doAssert source.count("# // ack_2") == 1
  doAssert source.contains("ack_0(1)") and source.contains("ack_0(ack_1((n - 1)))")
  doAssert source.contains("ack_1(1)") and source.contains("ack_1(ack_2((n - 1)))")
  doAssert commentIsPure(AckNode(state.defs[0].funBody.node)) == false
  echo "ok: staged Ackermann tower, keyed fun reuse, comments, and residual execution"
