## Framework validation: arithmetic DSL via the staging core.
##
## Proves the framework is generic (not tied to any particular DSL).
## Builds a fresh arithmetic DSL using only framework primitives:
## Rep[T], IRNode, lift, dynamic, smartOp.
##
## Adapted from Eponym's tests/framework_test.nim (which imported only
## staging/framework); the echo-based checks are replaced with doAssert
## so a failure fails the run.

import staging/framework

# --- DSL-specific IR nodes (extend IRNode) ---

type
  ArithNodeKind = enum akAdd, akMul, akVar

  ArithNode = ref object of IRNode
    case kind: ArithNodeKind
    of akVar: varName: string
    of akAdd, akMul: left, right: Rep[int]

proc `$`(n: ArithNode): string =
  # Forward declaration: Rep[int] $ defined below
  case n.kind
  of akVar: n.varName
  of akAdd, akMul: "(...)"  # placeholder, full def after Rep $

proc `$`(r: Rep[int]): string =
  if r.isStatic: "static(" & $r.staticVal & ")"
  else:
    let n = ArithNode(r.node)
    case n.kind
    of akVar: "dynamic(" & n.varName & ")"
    of akAdd: "dynamic((" & $n.left & " + " & $n.right & "))"
    of akMul: "dynamic((" & $n.left & " * " & $n.right & "))"

# --- DSL smart constructors via framework smartOp ---

proc addNode(a, b: Rep[int]): ArithNode =
  ArithNode(kind: akAdd, left: a, right: b)

proc mulNode(a, b: Rep[int]): ArithNode =
  ArithNode(kind: akMul, left: a, right: b)

proc varNode(name: string): ArithNode =
  ArithNode(kind: akVar, varName: name)

proc addR(a, b: Rep[int]): Rep[int] =
  smartOp[int](a, b,
    proc(x, y: int): int = x + y,
    proc(x, y: Rep[int]): IRNode = addNode(x, y))

proc mulR(a, b: Rep[int]): Rep[int] =
  smartOp[int](a, b,
    proc(x, y: int): int = x * y,
    proc(x, y: Rep[int]): IRNode = mulNode(x, y))

proc varR(name: string): Rep[int] =
  dynamic[int](varNode(name))

# --- Tagless-final DSL ---

type
  ArithSym[R] = object
    lit*: proc(n: int): R
    vr*: proc(name: string): R
    add*: proc(a, b: R): R
    mul*: proc(a, b: R): R

proc directArith(): ArithSym[int] =
  ArithSym[int](
    lit: proc(n: int): int = n,
    vr: proc(name: string): int = raise newException(ValueError, "unbound: " & name),
    add: proc(a, b: int): int = a + b,
    mul: proc(a, b: int): int = a * b,
  )

proc stagedArith(): ArithSym[Rep[int]] =
  ArithSym[Rep[int]](
    lit: proc(n: int): Rep[int] = lift(n),
    vr: proc(name: string): Rep[int] = varR(name),
    add: addR,
    mul: mulR,
  )

# --- Test programs ---

proc prog1[R](s: ArithSym[R]): R =
  ## (1 + 2) * 3 — fully static, should fold
  s.mul(s.add(s.lit(1), s.lit(2)), s.lit(3))

proc prog2[R](s: ArithSym[R]): R =
  ## (x + 1) * 2 — x dynamic, should residualize
  s.mul(s.add(s.vr("x"), s.lit(1)), s.lit(2))

when isMainModule:
  echo "=== staging framework: generic arithmetic DSL ==="

  # Direct execution
  let d = directArith()
  doAssert prog1(d) == 9, "direct prog1 should be 9"
  echo "ok: direct prog1 = 9"

  # Staged: fully static should fold
  let s = stagedArith()
  let r1 = prog1(s)
  echo "staged prog1: ", r1
  doAssert r1.isStatic and r1.staticVal == 9,
    "fully static program should fold to 9 at staging time"
  echo "ok: fully static folded to 9 at staging time"

  # Staged: dynamic var should residualize
  let r2 = prog2(s)
  echo "staged prog2: ", r2
  doAssert not r2.isStatic, "program with a dynamic var should residualize"
  doAssert $r2 == "dynamic((dynamic((dynamic(x) + static(1))) * static(2)))",
    "residual shape mismatch: " & $r2
  echo "ok: dynamic variable residualized to IR"

  # getStatic on a dynamic Rep must fail at staging time
  var raised = false
  try:
    discard getStatic(r2)
  except AssertionDefect:
    raised = true
  doAssert raised, "getStatic on a dynamic Rep should raise"
  echo "ok: getStatic on dynamic Rep raises (staging-time error)"

  echo "=== framework is generic: Rep[T], IRNode, lift, dynamic, smartOp only ==="
