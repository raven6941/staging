import staging/anf
import std/[tables]

type
  ExprKind = enum ekLit, ekInput, ekRef, ekAdd, ekMul, ekLoop, ekEffect, ekRead,
    ekDiverge
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
proc loop(body: Expr): Expr = Expr(kind: ekLoop, left: body)
proc effect(): Expr = Expr(kind: ekEffect)
proc readVar(): Expr = Expr(kind: ekRead)
proc diverge(): Expr = Expr(kind: ekDiverge)

proc exprChildren(e: Expr): seq[Expr] =
  case e.kind
  of ekAdd, ekMul: @[e.left, e.right]
  of ekLoop: @[e.left]
  else: @[]

proc exprRebuild(e: Expr; kids: seq[Expr]): Expr =
  case e.kind
  of ekAdd: add(kids[0], kids[1])
  of ekMul: mul(kids[0], kids[1])
  of ekLoop: loop(kids[0])
  else: e

proc exprKey(e: Expr): string =
  case e.kind
  of ekLit: "lit(" & $e.value & ")"
  of ekInput: "in(" & e.name & ")"
  of ekRef: "ref(" & e.name & ")"
  of ekAdd: "add(" & exprKey(e.left) & "," & exprKey(e.right) & ")"
  of ekMul: "mul(" & exprKey(e.left) & "," & exprKey(e.right) & ")"
  of ekLoop: "loop(" & exprKey(e.left) & ")"
  of ekEffect: "effect"
  of ekRead: "read"
  of ekDiverge: "diverge"

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
  of ekLoop: evalExpr(e.left, env)
  of ekEffect, ekRead, ekDiverge: 99

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

proc exprFreeVars(e: Expr): seq[string] =
  if e.kind == ekRef: return @[e.name]
  for child in exprChildren(e):
    for name in exprFreeVars(child):
      if name notin result: result.add(name)

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

  # Boundary regions keep loop-body bindings out of the enclosing region.
  let boundaryCb = AnfCallbacks[Expr](
    children: exprChildren, rebuild: exprRebuild, key: exprKey,
    isAtomic: exprIsAtomic, refName: exprRefName, makeRef: refE,
    isBoundary: proc(e: Expr): bool = e.kind == ekLoop,
    binders: proc(e: Expr): seq[string] = @["i"],
    freeVars: proc(e: Expr): seq[string] = @[],
    isPure: proc(e: Expr): bool = e.kind != ekEffect)
  let loopProg = toAnf(loop(add(input("a"), input("b"))), boundaryCb)
  doAssert loopProg.stmts.len == 1
  doAssert loopProg.stmts[0].nested.len == 1
  doAssert loopProg.stmts[0].nested[0].stmts.len == 1
  doAssert evalExpr(fromAnf(loopProg, boundaryCb), env) == 8
  let cross = cseAnf(toAnf(add(loop(add(input("a"), input("b"))),
                              add(input("a"), input("b"))), boundaryCb),
                     boundaryCb)
  doAssert cross.stmts.len == 3
  doAssert cross.stmts[0].nested[0].stmts.len == 1

  # Effects are roots, including through a pure binding that refers to one.
  let effectProg = toAnf(add(effect(), lit(1)), boundaryCb)
  doAssert dceAnf(effectProg, boundaryCb).stmts.len == 2
  doAssert cseAnf(toAnf(add(effect(), effect()), boundaryCb), boundaryCb).
    stmts.len == 3

  # An effect made unreferenced by a rewrite is still kept by DCE:
  # `effect() * 0` folds to 0, but the read must still happen.
  let zeroedEffect = dceAnf(optAnf(
    toAnf(mul(effect(), lit(0)), boundaryCb), boundaryCb, arithOpt),
    boundaryCb)
  doAssert zeroedEffect.stmts.len == 1
  doAssert evalExpr(fromAnf(zeroedEffect, boundaryCb), env) == 0

  # Totality is a separate attestation from purity: folding diverge() * 0
  # must not delete the diverging binding.
  var totalCb = boundaryCb
  totalCb.isTotal = proc(e: Expr): bool = e.kind != ekDiverge
  let zeroedDiverge = dceAnf(optAnf(
    toAnf(mul(diverge(), lit(0)), totalCb), totalCb, arithOpt), totalCb)
  doAssert zeroedDiverge.stmts.len == 1
  # CSE remains pure-only: identical diverging occurrences still merge.
  doAssert cseAnf(toAnf(add(diverge(), diverge()), totalCb), totalCb).
    stmts.len == 2

  # Nil isTotal is deliberately lenient: existing isPure-only clients retain
  # old DCE behaviour, and must attest totality when they have diverging nodes.
  let lenientDiverge = dceAnf(optAnf(
    toAnf(mul(diverge(), lit(0)), boundaryCb), boundaryCb, arithOpt),
    boundaryCb)
  doAssert lenientDiverge.stmts.len == 0

  # A rule rewriting a loop node away must not discard an effect inside
  # the loop body; a pure loop body still rewrites.
  proc loopDrop(e: Expr): Expr =
    if e.kind == ekLoop: lit(0) else: e
  # A non-total nested region blocks the boundary rewrite, just like an
  # effectful region does.
  let droppedDivergeLoop = optAnf(
    toAnf(loop(diverge()), totalCb), totalCb, loopDrop)
  doAssert droppedDivergeLoop.stmts.len == 1
  doAssert droppedDivergeLoop.stmts[0].nested[0].stmts.len == 1
  let droppedLoop = optAnf(
    toAnf(loop(add(effect(), lit(1))), boundaryCb), boundaryCb, loopDrop)
  doAssert droppedLoop.stmts.len == 1
  doAssert droppedLoop.stmts[0].nested[0].stmts.len == 2
  doAssert evalExpr(fromAnf(droppedLoop, boundaryCb), env) == 100
  let droppedPureLoop = optAnf(
    toAnf(loop(add(input("a"), lit(1))), boundaryCb), boundaryCb, loopDrop)
  doAssert droppedPureLoop.stmts.len == 0
  doAssert evalExpr(fromAnf(droppedPureLoop, boundaryCb), env) == 0

  # LICM moves only the invariant inner binding, preserving the region
  # result's reference to it and therefore its evaluation.
  var licmCb = boundaryCb
  licmCb.freeVars = exprFreeVars
  licmCb.isTotal = proc(e: Expr): bool = true
  let beforeLicm = toAnf(loop(add(mul(input("n"), lit(2)), input("a"))), licmCb)
  doAssert beforeLicm.stmts[0].nested[0].stmts.len == 2
  let moved = licmAnf(beforeLicm, licmCb)
  doAssert moved.stmts.len == 2
  doAssert moved.stmts[0].rhs.kind == ekMul
  doAssert moved.stmts[1].nested[0].stmts.len == 1
  doAssert evalExpr(fromAnf(moved, licmCb), {"a": 3, "n": 4}.toTable) == 11

  # LICM splices every invariant binding before the loop, in original order,
  # without duplicating them or reordering the surrounding bindings.
  let multiHoist = toAnf(
    add(loop(add(mul(input("n"), lit(2)), add(input("a"), lit(1)))),
        input("b")), licmCb)
  let multiMoved = licmAnf(multiHoist, licmCb)
  doAssert multiMoved.stmts.len == 4
  doAssert multiMoved.stmts[0].rhs.kind == ekMul
  doAssert multiMoved.stmts[1].rhs.kind == ekAdd
  doAssert multiMoved.stmts[2].rhs.kind == ekLoop
  doAssert multiMoved.stmts[2].nested[0].stmts.len == 1
  doAssert multiMoved.stmts[2].nested[0].stmts[0].rhs.kind == ekAdd
  doAssert multiMoved.stmts[3].rhs.kind == ekAdd
  doAssert evalExpr(fromAnf(multiMoved, licmCb),
                    {"a": 3, "b": 5, "n": 4}.toTable) == 17

  # A loop binder, a mutable/read binding, an effect, and a non-total node
  # each prevent motion. The read dependency also checks transitivity.
  let boundBody = licmAnf(
    toAnf(loop(add(refE("i"), input("a"))), licmCb), licmCb)
  doAssert boundBody.stmts[0].nested[0].stmts.len == 1

  var readCb = licmCb
  readCb.isPure = proc(e: Expr): bool = e.kind notin {ekEffect, ekRead}
  let readBody = licmAnf(
    toAnf(loop(add(readVar(), refE("t0"))), readCb), readCb)
  doAssert readBody.stmts[0].nested[0].stmts.len == 2

  let effectBody = licmAnf(toAnf(loop(effect()), licmCb), licmCb)
  doAssert effectBody.stmts[0].nested[0].stmts.len == 1
  var divergeLicmCb = licmCb
  divergeLicmCb.isTotal = proc(e: Expr): bool = e.kind != ekDiverge
  let divergeBody = licmAnf(toAnf(loop(diverge()), divergeLicmCb), divergeLicmCb)
  doAssert divergeBody.stmts[0].nested[0].stmts.len == 1
  var unsafePure = licmCb
  unsafePure.isPure = proc(e: Expr): bool = true
  doAssert licmAnf(toAnf(loop(effect()), unsafePure), unsafePure).
    stmts[1].nested[0].stmts.len == 0

  var partial = licmCb
  partial.isTotal = proc(e: Expr): bool = false
  doAssert licmAnf(toAnf(loop(mul(input("n"), lit(2))), partial), partial).
    stmts[0].nested[0].stmts.len == 1

  # No free-variable information means no LICM, even when all other
  # callbacks claim that motion would be safe.
  var noFreeVars = licmCb
  noFreeVars.freeVars = nil
  let unchanged = licmAnf(toAnf(loop(mul(input("n"), lit(2))), noFreeVars),
                          noFreeVars)
  doAssert unchanged.stmts.len == 1
  doAssert unchanged.stmts[0].nested[0].stmts.len == 1

  # A nil isTotal means no LICM either (#167 decision: the conservative
  # default stands — a nil isTotal must not default to isPure, since a
  # pure-but-diverging binding hoisted out of a loop that never runs
  # would change a terminating program into a diverging one).
  var noTotal = licmCb
  noTotal.isTotal = nil
  let unmoved = licmAnf(toAnf(loop(mul(input("n"), lit(2))), noTotal),
                        noTotal)
  doAssert unmoved.stmts.len == 1
  doAssert unmoved.stmts[0].nested[0].stmts.len == 1

  echo "ok: ANF conversion, ArithExpOpt rewrite, and stencil CSE"
