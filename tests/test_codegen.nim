## End-to-end worked example: stage an arithmetic interpreter and run its code.

import staging/framework
import std/[os, osproc, strutils, times]

type
  ArithNodeKind = enum akAdd, akMul, akVar
  ArithNode = ref object of IRNode
    case kind: ArithNodeKind
    of akVar: varName: string
    of akAdd, akMul: left, right: Rep[int]

type
  ArithSym[R] = object
    lit*: proc(n: int): R
    vr*: proc(name: string): R
    add*: proc(a, b: R): R
    mul*: proc(a, b: R): R

proc addNode(a, b: Rep[int]): ArithNode =
  ArithNode(kind: akAdd, left: a, right: b)

proc mulNode(a, b: Rep[int]): ArithNode =
  ArithNode(kind: akMul, left: a, right: b)

proc directArith(x: int): ArithSym[int] =
  ArithSym[int](
    lit: proc(n: int): int = n,
    vr: proc(name: string): int =
      if name == "x": x else: raise newException(ValueError, "unbound: " & name),
    add: proc(a, b: int): int = a + b,
    mul: proc(a, b: int): int = a * b,
  )

proc stagedArith(): ArithSym[Rep[int]] =
  ArithSym[Rep[int]](
    lit: proc(n: int): Rep[int] = liftNow(n),
    vr: proc(name: string): Rep[int] =
      dynamic[int](ArithNode(kind: akVar, varName: name)),
    add: proc(a, b: Rep[int]): Rep[int] =
      smartOp[int](a, b, proc(x, y: int): int = x + y,
        proc(x, y: Rep[int]): IRNode = addNode(x, y)),
    mul: proc(a, b: Rep[int]): Rep[int] =
      smartOp[int](a, b, proc(x, y: int): int = x * y,
        proc(x, y: Rep[int]): IRNode = mulNode(x, y)),
  )

proc program[R](s: ArithSym[R]): R =
  ## (x + (1 + 2)) * 2: the inner addition folds while x remains dynamic.
  s.mul(s.add(s.vr("x"), s.add(s.lit(1), s.lit(2))), s.lit(2))

proc emit(r: Rep[int]): string =
  if r.isStatic:
    return $r.staticVal
  let n = ArithNode(r.node)
  case n.kind
  of akVar: n.varName
  of akAdd: "(" & emit(n.left) & " + " & emit(n.right) & ")"
  of akMul: "(" & emit(n.left) & " * " & emit(n.right) & ")"

proc compileAndRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0,
    "nim compiler not found on PATH; the codegen test requires Nim"

  let nimcache = dir / "nimcache"
  createDir(nimcache)
  let compileResult = execCmdEx(
    quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(nimcache) &
      " --out:" & quoteShell(exe) &
      " " & quoteShell(source),
    {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert compileResult.exitCode == 0,
    "generated residual did not compile:\n" & compileResult.output

  let runResult = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut},
    workingDir = dir)
  doAssert runResult.exitCode == 0,
    "generated residual did not run:\n" & runResult.output
  runResult.output.strip

proc checkResidual(x: int) =
  let direct = program(directArith(x))
  let residual = program(stagedArith())
  doAssert not residual.isStatic, "x should remain dynamic"
  doAssert emit(residual) == "((x + 3) * 2)",
    "static subexpression was not folded in the residual"

  let dir = getTempDir() / ("staging-codegen-" & $getCurrentProcessId() &
    "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  let sourceText = "let x = " & $x & "\n\nwhen isMainModule:\n  echo " &
    emit(residual) & "\n"
  writeFile(source, sourceText)
  doAssert "staging/" notin sourceText and "import staging" notin sourceText,
    "residual must not depend on the staging library"
  let output = compileAndRun(source, exe, dir)
  doAssert parseInt(output) == direct,
    "generated result " & output & " differs from direct result " & $direct
  removeDir(dir)

when isMainModule:
  doAssert program(directArith(5)) == 16
  doAssert program(directArith(-3)) == 0
  checkResidual(5)
  checkResidual(-3)
  echo "ok: staged arithmetic emitted, compiled, and ran as ordinary Nim"
