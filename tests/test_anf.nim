import staging/anf
import std/[tables]

type
  ExprKind = enum ekLit, ekInput, ekRef, ekAdd, ekMul
  Expr = ref object
    kind: ExprKind
    value: int
    name: string
    left, right: Expr

proc lit(v: int): Expr = Expr(kind: ekLit, value: v)
proc input(name: string): Expr = Expr(kind: ekInput, name: name)
proc refE(name: string): Expr = Expr(kind: ekRef, name: name)
proc add(a, b: Expr): Expr = Expr(kind: ekAdd, left: a, right: b)
proc mul(a, b: Expr): Expr = Expr(kind: ekMul, left: a, right: b)

proc exprChildren(e: Expr): seq[Expr] =
  case e.kind
  of ekAdd, ekMul: @[e.left, e.right]
  else: @[]

proc exprRebuild(e: Expr; kids: seq[Expr]): Expr =
  case e.kind
  of ekAdd: add(kids[0], kids[1])
  of ekMul: mul(kids[0], kids[1])
  else: e

proc exprKey(e: Expr): string =
  case e.kind
  of ekLit: "lit(" & $e.value & ")"
  of ekInput: "in(" & e.name & ")"
  of ekRef: "ref(" & e.name & ")"
  of ekAdd: "add(" & exprKey(e.left) & "," & exprKey(e.right) & ")"
  of ekMul: "mul(" & exprKey(e.left) & "," & exprKey(e.right) & ")"

proc exprIsAtomic(e: Expr): bool =
  e.kind in {ekLit, ekInput, ekRef}

proc exprRefName(e: Expr): string =
  if e.kind == ekRef: e.name else: ""

let cb = AnfCallbacks[Expr](
  children: exprChildren,
  rebuild: exprRebuild,
  key: exprKey,
  isAtomic: exprIsAtomic,
  refName: exprRefName,
  makeRef: refE)

proc evalExpr(e: Expr; env: Table[string, int]): int =
  case e.kind
  of ekLit: e.value
  of ekInput, ekRef: env[e.name]
  of ekAdd: evalExpr(e.left, env) + evalExpr(e.right, env)
  of ekMul: evalExpr(e.left, env) * evalExpr(e.right, env)

proc arithOpt(e: Expr): Expr =
  ## ArithExpOpt-style: identities + constant folding, visible directly
  ## because ANF right-hand sides have atomic children.
  case e.kind
  of ekAdd:
    if e.left.kind == ekLit and e.left.value == 0: return e.right
    if e.right.kind == ekLit and e.right.value == 0: return e.left
    if e.left.kind == ekLit and e.right.kind == ekLit:
      return lit(e.left.value + e.right.value)
  of ekMul:
    if e.left.kind == ekLit and e.left.value == 1: return e.right
    if e.right.kind == ekLit and e.right.value == 1: return e.left
    if (e.left.kind == ekLit and e.left.value == 0) or
       (e.right.kind == ekLit and e.right.value == 0): return lit(0)
    if e.left.kind == ekLit and e.right.kind == ekLit:
      return lit(e.left.value * e.right.value)
  else: discard
  e

proc checkAnfInvariant[T](prog: AnfProg[T]; cb: AnfCallbacks[T]) =
  for stmt in prog.stmts:
    for child in cb.children(stmt.rhs):
      doAssert cb.isAtomic(child), "ANF rhs child must be atomic"

when isMainModule:
  let env = {"a": 3, "b": 5}.toTable

  # ArithExpOpt: (2 * 3) + 0 folds to 6; x * 1 and 0 * x simplify.
  let folded = optAnf(toAnf(add(mul(lit(2), lit(3)), lit(0)), cb), cb, arithOpt)
  doAssert folded.stmts.len == 0
  doAssert folded.result.kind == ekLit and folded.result.value == 6
  doAssert evalExpr(fromAnf(folded, cb), env) == 6

  let simplified = optAnf(toAnf(mul(add(input("a"), lit(0)), lit(1)), cb),
                           cb, arithOpt)
  doAssert simplified.stmts.len == 0
  doAssert evalExpr(fromAnf(simplified, cb), env) == 3

  ## `0 * x` drops the multiply but leaves its operand binding dead;
  ## DCE — a pass ANF makes trivial — sweeps it.
  let zeroed = dceAnf(optAnf(toAnf(mul(lit(0), add(input("a"), input("b"))), cb),
                             cb, arithOpt), cb)
  doAssert zeroed.stmts.len == 0
  doAssert evalExpr(fromAnf(zeroed, cb), env) == 0

  # Stencil CSE as ANF: (a + b) * (a + b) binds the sum once.
  let stencil = toAnf(mul(add(input("a"), input("b")),
                          add(input("a"), input("b"))), cb)
  doAssert stencil.stmts.len == 3
  checkAnfInvariant(stencil, cb)
  let deduped = cseAnf(stencil, cb)
  doAssert deduped.stmts.len == 2
  doAssert deduped.stmts[0].rhs.kind == ekAdd
  doAssert deduped.stmts[1].rhs.kind == ekMul
  doAssert evalExpr(fromAnf(deduped, cb), env) ==
    evalExpr(mul(add(input("a"), input("b")), add(input("a"), input("b"))), env)

  # Round-trip preserves value on a nested expression.
  let nested = add(mul(input("a"), add(input("b"), lit(2))),
                   mul(input("a"), input("b")))
  let rt = fromAnf(toAnf(nested, cb), cb)
  doAssert evalExpr(rt, env) == evalExpr(nested, env)
  doAssert evalExpr(rt, {"a": 7, "b": 11}.toTable) ==
    evalExpr(nested, {"a": 7, "b": 11}.toTable)

  echo "ok: ANF conversion, ArithExpOpt rewrite, and stencil CSE"
