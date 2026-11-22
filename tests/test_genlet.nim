## Tests for the generic genlet pass (staging/genlet).
##
## The demo: a small arithmetic evaluator staged over `GTree`. The shared
## composite term is evaluated before and after let-insertion and must
## agree; the pass must also leave atom-only and small-shared-term trees
## alone, and must never hoist a term across a `let` binder.

import tables
import strutils
import staging/genlet

proc evalTree(t: GTree; env: Table[string, int]): int =
  ## Tiny interpreter over GTree: atoms are int literals or variables,
  ## nodes are add/mul, lets extend the environment.
  case t.kind
  of gkAtom:
    try: parseInt(t.name)
    except ValueError: env[t.name]
  of gkNode:
    case t.op
    of "add": evalTree(t.children[0], env) + evalTree(t.children[1], env)
    of "sub": evalTree(t.children[0], env) - evalTree(t.children[1], env)
    of "mul": evalTree(t.children[0], env) * evalTree(t.children[1], env)
    else: raise newException(ValueError, "unknown op: " & t.op)
  of gkLet:
    var env2 = env
    env2[t.binder] = evalTree(t.bound, env)
    evalTree(t.body, env2)

proc atom(n: string): GTree = gatom(n)
proc add(a, b: GTree): GTree = gnode("add", @[a, b])
proc mul(a, b: GTree): GTree = gnode("mul", @[a, b])
proc sub(a, b: GTree): GTree = gnode("sub", @[a, b])

proc powerSq(b: GTree; n: int): GTree =
  if n == 0: atom("1")
  elif n mod 2 == 0:
    let y = powerSq(b, n div 2)
    mul(y, y)
  else:
    mul(b, powerSq(b, n - 1))

# Stencil helpers mirroring ~/workspace/buildout/staging-vetting/stencil.nim:
# w1(j) = a(j)*a(j+1), wm(j) = a(j) - w1(j) + w1(j-1),
# w2(j) = wm(j)*wm(j+1), b(j) = wm(j) - w2(j) + w2(j-1).
proc sA(j: int): GTree = atom("a" & $j)
proc sW1(j: int): GTree = mul(sA(j), sA(j + 1))
proc sWm(j: int): GTree = add(sub(sA(j), sW1(j)), sW1(j - 1))
proc sW2(j: int): GTree = mul(sWm(j), sWm(j + 1))
proc sB(j: int): GTree = add(sub(sWm(j), sW2(j)), sW2(j - 1))

# --- A client IR using the callback API (no GTree involved) ---

type
  CKind = enum ckAtom, ckAdd, ckMul, ckLet
  CNode = ref object
    kind: CKind
    name: string
    children: seq[CNode]

proc cAtom(name: string): CNode = CNode(kind: ckAtom, name: name)
proc cAdd(a, b: CNode): CNode = CNode(kind: ckAdd, children: @[a, b])
proc cMul(a, b: CNode): CNode = CNode(kind: ckMul, children: @[a, b])
proc cLet(name: string; bound, body: CNode): CNode =
  CNode(kind: ckLet, name: name, children: @[bound, body])

proc cKey(n: CNode): string =
  case n.kind
  of ckAtom: n.name
  of ckAdd: "add(" & cKey(n.children[0]) & "," & cKey(n.children[1]) & ")"
  of ckMul: "mul(" & cKey(n.children[0]) & "," & cKey(n.children[1]) & ")"
  of ckLet: "let(" & n.name & "," & cKey(n.children[0]) & "," & cKey(n.children[1]) & ")"

proc cEval(n: CNode; env: Table[string, int]): int =
  case n.kind
  of ckAtom:
    try: parseInt(n.name)
    except ValueError: env[n.name]
  of ckAdd: cEval(n.children[0], env) + cEval(n.children[1], env)
  of ckMul: cEval(n.children[0], env) * cEval(n.children[1], env)
  of ckLet:
    var env2 = env
    env2[n.name] = cEval(n.children[0], env)
    cEval(n.children[1], env2)

proc cCallbacks(): GenletCallbacks[CNode] = GenletCallbacks[CNode](
  children: proc(n: CNode): seq[CNode] = n.children,
  key: cKey,
  isComposite: proc(n: CNode): bool = n.kind != ckAtom,
  isBoundary: proc(n: CNode): bool = n.kind == ckLet,
  rebuild: proc(n: CNode; children: seq[CNode]): CNode =
    CNode(kind: n.kind, name: n.name, children: children),
  makeRef: cAtom,
  makeLet: cLet,
)

proc cRender(n: CNode): string =
  case n.kind
  of ckAtom: n.name
  of ckAdd: "add(" & cRender(n.children[0]) & ", " & cRender(n.children[1]) & ")"
  of ckMul: "mul(" & cRender(n.children[0]) & ", " & cRender(n.children[1]) & ")"
  of ckLet: "(let " & n.name & " = " & cRender(n.children[0]) &
    " in " & cRender(n.children[1]) & ")"

when isMainModule:
  echo "=== generic genlet: arithmetic residual demo ==="

  # Shared composite term t = (x+1) * (y+2): 7 nodes, used 3 times.
  # Work-based rule: n=3, s=7, so it qualifies (as do its subterms).
  let t = mul(add(atom("x"), atom("1")), add(atom("y"), atom("2")))
  doAssert treeNodes(t) == 7
  let expr = add(t, add(t, t))
  doAssert treeNodes(expr) == 23
  echo "before: ", expr

  let env = {"x": 2, "y": 3}.toTable
  doAssert evalTree(expr, env) == 45, "t = 3*5 = 15; expr = 15 + (15+15)"

  var ctx = newGenletCtx()
  let hoisted = insertLets(expr, ctx)
  echo "after:  ", hoisted
  doAssert ctx.counter == 3, "every repeated pure composite should be hoisted"
  doAssert treeNodes(hoisted) == 17, "23 nodes -> 17 nodes"
  doAssert evalTree(hoisted, env) == 45, "let-insertion must preserve value"
  doAssert $hoisted == "(let genlet1 = add(y, 2) in (let genlet0 = add(x, 1) in " &
    "(let genlet2 = mul(genlet0, genlet1) in add(genlet2, add(genlet2, genlet2)))))"
  echo "ok: repeated pure composites hoisted, value preserved"

  # No-op: atoms only — nothing qualifies, tree returned unchanged.
  let atomsOnly = add(atom("x"), atom("x"))
  var ctx2 = newGenletCtx()
  let atomsOut = insertLets(atomsOnly, ctx2)
  doAssert ctx2.counter == 0
  doAssert $atomsOut == $atomsOnly
  echo "ok: atom-only duplication left alone (no spurious lets)"

  # Policy change (Aaron 2026-11-22: runtime work over code size, hoist
  # every repeated pure piece): the delta = 0 boundary case is hoisted.
  let small = mul(atom("x"), atom("y"))  # 3 nodes
  let twice = add(small, small)
  var ctx3 = newGenletCtx()
  let twiceOut = insertLets(twice, ctx3)
  doAssert ctx3.counter == 1, "n=2, s=3 boundary must be hoisted"
  doAssert $twiceOut == "(let genlet0 = mul(x, y) in add(genlet0, genlet0))"
  doAssert evalTree(twiceOut, env) == 12
  echo "ok: twice-shared small term hoisted at the delta=0 boundary"

  # Binary-squaring power(x, 7), matching staging-vetting/power.nim section 3.
  # The three repeated pure composites all qualify under the work-based rule.
  let powerResidual = powerSq(atom("x"), 7)
  var powerCtx = newGenletCtx()
  let powerOut = insertLets(powerResidual, powerCtx)
  doAssert powerCtx.counter == 3, "power(x,7) must insert exactly three lets: " & $powerOut
  doAssert evalTree(powerOut, {"x": 2}.toTable) == 128
  doAssert $powerOut ==
    "(let genlet0 = mul(x, 1) in " &
    "(let genlet1 = mul(genlet0, genlet0) in " &
    "(let genlet2 = mul(x, genlet1) in " &
    "mul(x, mul(genlet2, genlet2)))))"
  echo "ok: power(x,7) hoists all three repeated composites"

  # Boundary: a term shared across a `let` must NOT be hoisted across it.
  # The body's occurrence pair hoists inside the body (with t's own
  # repeated subterms); the bound occurrence remains in the outer
  # binding, and no let is placed above the outer let.
  let across = glet("z", t, add(t, t))
  var ctx4 = newGenletCtx()
  let acrossOut = insertLets(across, ctx4)
  doAssert ctx4.counter == 3, "body sharing hoists inside, bound occurrence stays"
  doAssert $acrossOut == "(let z = mul(add(x, 1), add(y, 2)) in " &
    "(let genlet1 = add(y, 2) in (let genlet0 = add(x, 1) in " &
    "(let genlet2 = mul(genlet0, genlet1) in add(genlet2, genlet2)))))"
  doAssert evalTree(acrossOut, env) == 30, "let z = 15 in 15 + 15"
  echo "ok: let binder is not crossed; body sharing is hoisted inside"

  # But hoisting *inside* a let body is still allowed.
  let inside = glet("z", atom("9"), add(t, add(t, t)))
  var ctx5 = newGenletCtx()
  let insideOut = insertLets(inside, ctx5)
  doAssert ctx5.counter == 3, "all repeated pure composites inside the body should hoist"
  doAssert evalTree(insideOut, env) == 45, "value preserved"
  doAssert $insideOut == "(let z = 9 in (let genlet1 = add(y, 2) in " &
    "(let genlet0 = add(x, 1) in (let genlet2 = mul(genlet0, genlet1) in " &
    "add(genlet2, add(genlet2, genlet2))))))",
    "let must land inside the outer let's body: " & $insideOut
  echo "ok: hoist inside a let body works, binder not crossed"

  # Scope-aware placement, real stencil shape (vetting port (c)):
  # b(2) + b(3) over a[0..5]. The old pass hoisted wm(2)/wm(3) and
  # left mul(a2,a3) computed 4x; scope-aware placement binds it once,
  # at the root, before the wm hoists collapse its count. The five
  # insertions are the three shared w1 products plus wm(2) and wm(3).
  let stencil = add(sB(2), sB(3))
  var stencilCtx = newGenletCtx()
  let stencilOut = insertLets(stencil, stencilCtx)
  let stencilEnv = {"a0": 1, "a1": 2, "a2": 3, "a3": 4, "a4": 5,
                    "a5": 6}.toTable
  doAssert evalTree(stencilOut, stencilEnv) == -21
  # The work-based rule adds three composites beyond the old five: the two
  # repeated sub(a2, w1(2)) / sub(a3, w1(3)) pieces (each n=3, s=5 in the
  # original tree), and the repeated mul(wm(2), wm(3)) piece (n=2, s=19
  # in the original tree). All now qualify by n>=2, s>=3, so the
  # deliberate measured count is eight.
  doAssert stencilCtx.counter == 8,
    "expected the work-based stencil composites: " & $stencilOut
  doAssert count($stencilOut, "mul(a2, a3)") == 1,
    "mul(a2, a3) must be computed once: " & $stencilOut
  doAssert count($stencilOut, "sub(a2, genlet") == 1,
    "wm(2) must be bound once: " & $stencilOut
  doAssert count($stencilOut, "sub(a3, genlet") == 1,
    "wm(3) must be bound once: " & $stencilOut
  echo "ok: scope-aware placement shares stencil intermediates globally"

  # A term referring to an intervening binder must not be hoisted ACROSS
  # it — but hoisting it inside the body, where the binder is still in
  # scope, is correct and fires under the work-based rule. The root hoist
  # is refused (no let above the outer let); the body pair is shared
  # inside, and the outside occurrence stays raw.
  let scopedTerm = mul(atom("z"), atom("q"))
  let scopedTree = add(glet("z", atom("2"), add(scopedTerm, scopedTerm)),
                       scopedTerm)
  var scopedCtx = newGenletCtx()
  let scopedOut = insertLets(scopedTree, scopedCtx)
  doAssert scopedCtx.counter == 1, "only the in-body hoist may fire"
  doAssert $scopedOut ==
    "add((let z = 2 in (let genlet0 = mul(z, q) in add(genlet0, genlet0))), mul(z, q))"
  doAssert count($scopedOut, "mul(z, q)") == 2
  echo "ok: scope check refuses the across-binder hoist; in-body sharing fires"

  # Load-bearing version of the same check: this term DOES qualify under
  # the work-based rule (3 occurrences, 7 nodes), so only the scope check
  # can refuse the root hoist — it occurs twice inside a let binding z
  # and once outside it, and mentions z. The root hoist does not fire
  # (no let above the outer let); the two in-body hoists fire inside
  # (mul(z, q), then big itself), and the outside pair is shared locally
  # — it was already outside z's scope in the input, so sharing it there
  # preserves meaning. The input is deliberately ill-scoped in exactly
  # this way to stress the check.
  let big = add(mul(atom("z"), atom("q")), mul(atom("z"), atom("q")))
  let scopedTree2 = add(glet("z", atom("2"), add(big, big)), big)
  var scopedCtx2 = newGenletCtx()
  let scopedOut2 = insertLets(scopedTree2, scopedCtx2)
  doAssert scopedCtx2.counter == 3,
    "scope check must refuse the root hoist, not the in-scope ones"
  doAssert $scopedOut2 ==
    "add((let z = 2 in (let genlet0 = mul(z, q) in " &
    "(let genlet1 = add(genlet0, genlet0) in add(genlet1, genlet1)))), " &
    "(let genlet2 = mul(z, q) in add(genlet2, genlet2)))"
  doAssert count($scopedOut2, "add(mul(z, q), mul(z, q))") == 0,
    "no raw big term may remain: " & $scopedOut2
  doAssert count($scopedOut2, "mul(z, q)") == 2
  echo "ok: scope check refuses a qualifying binder-dependent root hoist"

  # The same cases through a client's own IR and callbacks.
  let ct = cMul(cAdd(cAtom("x"), cAtom("1")),
                cAdd(cAtom("y"), cAtom("2")))
  let cexpr = cAdd(ct, cAdd(ct, ct))
  var cctx = newGenletCtx()
  let cout = insertLetsCb(cexpr, cctx, cCallbacks())
  doAssert cctx.counter == 3
  doAssert cEval(cout, env) == 45, "callback let-insertion must preserve value"
  doAssert cRender(cout) ==
    "(let genlet0 = add(x, 1) in (let genlet1 = add(y, 2) in " &
    "(let genlet2 = mul(genlet0, genlet1) in add(genlet2, add(genlet2, genlet2)))))"
  echo "ok: callback client hoisted shared composite, value preserved"

  # Policy change (Aaron 2026-11-22: runtime work over code size, hoist
  # every repeated pure piece): callback n=2, s=3 is hoisted.
  let csmall = cMul(cAtom("x"), cAtom("y"))
  var cctx2 = newGenletCtx()
  let csmallOut = insertLetsCb(cAdd(csmall, csmall), cctx2, cCallbacks())
  doAssert cctx2.counter == 1
  doAssert cRender(csmallOut) == "(let genlet0 = mul(x, y) in add(genlet0, genlet0))"
  doAssert cEval(csmallOut, env) == 12
  echo "ok: callback twice-shared small term hoisted"

  var cctx3 = newGenletCtx()
  discard insertLetsCb(cAdd(cAtom("x"), cAtom("x")), cctx3, cCallbacks())
  doAssert cctx3.counter == 0
  echo "ok: callback atom-only duplication left alone"

  var cctx4 = newGenletCtx()
  let cacross = cLet("z", ct, cAdd(ct, ct))
  let cacrossOut = insertLetsCb(cacross, cctx4, cCallbacks())
  doAssert cctx4.counter == 3, "body sharing hoists inside, bound occurrence stays"
  doAssert cRender(cacrossOut) ==
    "(let z = mul(add(x, 1), add(y, 2)) in " &
    "(let genlet0 = add(x, 1) in (let genlet1 = add(y, 2) in " &
    "(let genlet2 = mul(genlet0, genlet1) in add(genlet2, genlet2)))))"
  doAssert cEval(cacrossOut, env) == 30
  echo "ok: callback let binder is not crossed; body sharing is hoisted inside"

  var cctx5 = newGenletCtx()
  let cinside = cLet("z", cAtom("9"), cAdd(ct, cAdd(ct, ct)))
  let cinsideOut = insertLetsCb(cinside, cctx5, cCallbacks())
  doAssert cctx5.counter == 3
  doAssert cEval(cinsideOut, env) == 45
  doAssert cRender(cinsideOut) ==
    "(let z = 9 in (let genlet0 = add(x, 1) in (let genlet1 = add(y, 2) in " &
    "(let genlet2 = mul(genlet0, genlet1) in add(genlet2, add(genlet2, genlet2))))))"
  echo "ok: callback hoist inside a let body works"

  echo "=== generic genlet ok ==="
