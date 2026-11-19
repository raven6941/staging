## Acceptance tests for smartIf: thunked branches and residual conditionals.

import staging/framework
import std/[os, osproc, strutils, times]

type
  ArithNodeKind = enum akAdd, akMul, akVar, akIf
  ArithNode = ref object of IRNode
    case kind: ArithNodeKind
    of akAdd, akMul: left, right: Rep[int]
    of akVar: varName: string
    of akIf:
      condition: Rep[bool]
      thenBranch, elseBranch: Rep[int]

proc `$`(r: Rep[bool]): string =
  if r.isStatic: "static(" & $r.staticVal & ")"
  else: "dynamic(" & ArithNode(r.node).varName & ")"

proc `$`(r: Rep[int]): string =
  if r.isStatic: "static(" & $r.staticVal & ")"
  else:
    let n = ArithNode(r.node)
    case n.kind
    of akAdd: "dynamic((" & $n.left & " + " & $n.right & "))"
    of akMul: "dynamic((" & $n.left & " * " & $n.right & "))"
    of akVar: "dynamic(" & n.varName & ")"
    of akIf: "dynamic((if " & $n.condition & ": " & $n.thenBranch &
      " else: " & $n.elseBranch & "))"

proc addR(a, b: Rep[int]): Rep[int] =
  smartOp[int](a, b, proc(x, y: int): int = x + y,
    proc(x, y: Rep[int]): IRNode = ArithNode(kind: akAdd, left: x, right: y))

proc mulR(a, b: Rep[int]): Rep[int] =
  smartOp[int](a, b, proc(x, y: int): int = x * y,
    proc(x, y: Rep[int]): IRNode = ArithNode(kind: akMul, left: x, right: y))

proc varR(name: string): Rep[int] =
  dynamic[int](ArithNode(kind: akVar, varName: name))

proc condR(name: string): Rep[bool] =
  dynamic[bool](ArithNode(kind: akVar, varName: name))

proc ifR(cond: Rep[bool], thenB, elseB: proc(): Rep[int]): Rep[int] =
  smartIf[int](cond, thenB, elseB,
    proc(c: Rep[bool], t, e: Rep[int]): IRNode =
      ArithNode(kind: akIf, condition: c, thenBranch: t, elseBranch: e))

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: $r.staticVal
  else: ArithNode(r.node).varName

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = ArithNode(r.node)
  case n.kind
  of akVar: n.varName
  of akAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of akMul: "(" & emitInt(n.left) & " * " & emitInt(n.right) & ")"
  of akIf: "(if " & emitBool(n.condition) & ": " & emitInt(n.thenBranch) &
    " else: " & emitInt(n.elseBranch) & ")"

proc compileAndRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim compiler not found on PATH"
  let nimcache = dir / "nimcache"
  createDir(nimcache)
  let compiled = execCmdEx(
    quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(nimcache) &
      " --out:" & quoteShell(exe) & " " & quoteShell(source),
    {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert compiled.exitCode == 0, "generated residual did not compile:\n" & compiled.output
  let ran = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert ran.exitCode == 0, "generated residual did not run:\n" & ran.output
  ran.output.strip

when isMainModule:
  # Static condition: only the selected thunk runs and its value is folded.
  var untakenBuilt = false
  let folded = smartIf[int](lift(true),
    proc(): Rep[int] = lift(7),
    proc(): Rep[int] =
      untakenBuilt = true
      dynamic[int](ArithNode(kind: akVar, varName: "untaken")),
    proc(c: Rep[bool], t, e: Rep[int]): IRNode =
      ArithNode(kind: akIf, condition: c, thenBranch: t, elseBranch: e))
  doAssert folded.isStatic and folded.staticVal == 7
  doAssert not untakenBuilt, "static smartIf built the untaken branch"

  # Static-false condition folds the other way: the then thunk is untaken.
  var thenBuilt = false
  let foldedFalse = smartIf[int](lift(false),
    proc(): Rep[int] =
      thenBuilt = true
      dynamic[int](ArithNode(kind: akVar, varName: "untaken")),
    proc(): Rep[int] = lift(9),
    proc(c: Rep[bool], t, e: Rep[int]): IRNode =
      ArithNode(kind: akIf, condition: c, thenBranch: t, elseBranch: e))
  doAssert foldedFalse.isStatic and foldedFalse.staticVal == 9
  doAssert not thenBuilt, "static-false smartIf built the untaken branch"

  # Dynamic condition: both branches become children of one residual if node.
  let residual = ifR(condR("c"),
    proc(): Rep[int] = addR(varR("x"), lift(1)),
    proc(): Rep[int] = mulR(varR("x"), lift(2)))
  doAssert not residual.isStatic
  let ifNode = ArithNode(residual.node)
  doAssert ifNode.kind == akIf
  doAssert ArithNode(ifNode.thenBranch.node).kind == akAdd
  doAssert ArithNode(ifNode.elseBranch.node).kind == akMul

  # A staging-time exception in an untaken branch must never be observed.
  let safe = smartIf[int](lift(true),
    proc(): Rep[int] = lift(11),
    proc(): Rep[int] = raise newException(ValueError, "untaken branch built"),
    proc(c: Rep[bool], t, e: Rep[int]): IRNode =
      ArithNode(kind: akIf, condition: c, thenBranch: t, elseBranch: e))
  doAssert safe.isStatic and safe.staticVal == 11

  # Emit the dynamic residual and compare compiled execution with direct
  # evaluation, for both values of the condition.
  let x = 5
  let directTrue = if true: x + 1 else: x * 2
  let directFalse = if false: x + 1 else: x * 2
  doAssert directTrue == 6 and directFalse == 10
  let residualProg = ifR(condR("c"),
    proc(): Rep[int] = addR(varR("x"), lift(1)),
    proc(): Rep[int] = mulR(varR("x"), lift(2)))
  for cVal in [true, false]:
    let generated = "let c = " & $cVal & "\nlet x = " & $x &
      "\nwhen isMainModule:\n  echo " & emitInt(residualProg) & "\n"
    let dir = getTempDir() / ("staging-smartif-" & $getCurrentProcessId() &
      "-" & $cVal & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let source = dir / "residual.nim"
    let exe = dir / "residual"
    writeFile(source, generated)
    let expected = if cVal: directTrue else: directFalse
    doAssert parseInt(compileAndRun(source, exe, dir)) == expected,
      "residual with c=" & $cVal & " disagrees with direct evaluation"
    removeDir(dir)
  echo "ok: smartIf folds, residualizes, short-circuits, and codegens"
