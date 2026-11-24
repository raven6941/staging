## Acceptance tests for path-local condition tracking over smartIf.

import staging/framework
import std/[os, osproc, strutils, times]

type
  DynNodeKind = enum dkVar, dkEq, dkIf
  DynNode = ref object of IRNode
    case kind: DynNodeKind
    of dkVar: name: string
    of dkEq: left: Rep[int]
    of dkIf:
      condition: Rep[bool]
      thenBranch, elseBranch: Rep[int]

proc intVar(name: string): Rep[int] =
  dynamic[int](DynNode(kind: dkVar, name: name))

proc eqZero(value: Rep[int]): Rep[bool] =
  dynamic[bool](DynNode(kind: dkEq, left: value))

proc ifR(ctx: ConditionContext, cond: Rep[bool],
        thenB, elseB: proc(): Rep[int]): Rep[int] =
  trackedIf[int](ctx, cond, thenB, elseB,
    proc(c: Rep[bool], t, e: Rep[int]): IRNode =
      DynNode(kind: dkIf, condition: c, thenBranch: t, elseBranch: e))

proc plainIf(cond: Rep[bool], thenB, elseB: proc(): Rep[int]): Rep[int] =
  smartIf[int](cond, thenB, elseB,
    proc(c: Rep[bool], t, e: Rep[int]): IRNode =
      DynNode(kind: dkIf, condition: c, thenBranch: t, elseBranch: e))

proc emitInt(value: Rep[int]): string

proc emitBool(value: Rep[bool]): string =
  if value.isStatic: return $value.staticVal
  let node = DynNode(value.node)
  case node.kind
  of dkEq: "(" & emitInt(node.left) & " == 0)"
  of dkVar: node.name
  of dkIf: raise newException(ValueError, "integer node used as condition")

proc emitInt(value: Rep[int]): string =
  if value.isStatic: return $value.staticVal
  let node = DynNode(value.node)
  case node.kind
  of dkVar: node.name
  of dkEq: raise newException(ValueError, "boolean node used as integer")
  of dkIf: "(if " & emitBool(node.condition) & ": " &
    emitInt(node.thenBranch) & " else: " & emitInt(node.elseBranch) & ")"

proc compileRun(source, exe, dir: string): string =
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

proc runResidual(program: Rep[int], n, m, expected: int) =
  let dir = getTempDir() / ("staging-dynvar-" & $getCurrentProcessId() &
    "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  writeFile(source, "let n = " & $n & "\nlet m = " & $m &
    "\nwhen isMainModule:\n  echo " & emitInt(program) & "\n")
  doAssert parseInt(compileRun(source, exe, dir)) == expected
  removeDir(dir)

proc warmupTracked(n: Rep[int]): Rep[int] =
  let ctx = newConditionContext()
  let condition = eqZero(n)
  ifR(ctx, condition,
    proc(): Rep[int] = ifR(ctx, condition,
      proc(): Rep[int] = liftNow(0),
      proc(): Rep[int] = liftNow(2)),
    proc(): Rep[int] = liftNow(1))

proc warmupUntracked(n: Rep[int]): Rep[int] =
  let condition = eqZero(n)
  plainIf(condition,
    proc(): Rep[int] = plainIf(condition,
      proc(): Rep[int] = liftNow(0),
      proc(): Rep[int] = liftNow(2)),
    proc(): Rep[int] = liftNow(1))

when isMainModule:
  let n = intVar("n")
  let tracked = warmupTracked(n)
  let untracked = warmupUntracked(n)
  let trackedText = emitInt(tracked)
  let untrackedText = emitInt(untracked)
  doAssert trackedText.count("if ") == 1, trackedText
  doAssert untrackedText.count("if ") == 2, untrackedText
  runResidual(tracked, 0, 0, 0)
  runResidual(tracked, 3, 0, 1)

  let negatedCtx = newConditionContext()
  let negatedCondition = eqZero(n)
  let negated = ifR(negatedCtx, negatedCondition,
    proc(): Rep[int] = liftNow(1),
    proc(): Rep[int] = ifR(negatedCtx, negatedCondition,
      proc(): Rep[int] = liftNow(0),
      proc(): Rep[int] = liftNow(2)))
  doAssert emitInt(negated).count("if ") == 1
  runResidual(negated, 0, 0, 1)
  runResidual(negated, 3, 0, 2)

  # A separately-built condition is not the same path fact.
  let differentCtx = newConditionContext()
  let different = ifR(differentCtx, eqZero(n),
    proc(): Rep[int] = ifR(differentCtx, eqZero(intVar("m")),
      proc(): Rep[int] = liftNow(0),
      proc(): Rep[int] = liftNow(2)),
    proc(): Rep[int] = liftNow(1))
  doAssert emitInt(different).count("if ") == 2

  # Facts are restored after each sibling branch.
  let siblingCtx = newConditionContext()
  let siblingCondition = eqZero(n)
  discard ifR(siblingCtx, siblingCondition,
    proc(): Rep[int] = liftNow(4),
    proc(): Rep[int] = liftNow(5))
  let sibling = ifR(siblingCtx, siblingCondition,
    proc(): Rep[int] = liftNow(6),
    proc(): Rep[int] = liftNow(7))
  doAssert emitInt(sibling).count("if ") == 1

  echo "ok: tracked conditionals fold nested tests, preserve identity, and restore siblings"
