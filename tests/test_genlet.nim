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
    of "mul": evalTree(t.children[0], env) * evalTree(t.children[1], env)
    else: raise newException(ValueError, "unknown op: " & t.op)
  of gkLet:
    var env2 = env
    env2[t.binder] = evalTree(t.bound, env)
    evalTree(t.body, env2)

proc atom(n: string): GTree = gatom(n)
proc add(a, b: GTree): GTree = gnode("add", @[a, b])
proc mul(a, b: GTree): GTree = gnode("mul", @[a, b])

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
  # Savings test: (3-1)*(7-1) - 7 - 3 = 2 > 0, so it qualifies.
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
  doAssert ctx.counter == 1, "exactly one let should be inserted"
  doAssert treeNodes(hoisted) == 13, "23 nodes -> 13 nodes"
  doAssert evalTree(hoisted, env) == 45, "let-insertion must preserve value"
  doAssert "(let genlet0 = " in $hoisted
  doAssert $hoisted == "(let genlet0 = mul(add(x, 1), add(y, 2)) in add(genlet0, add(genlet0, genlet0)))"
  echo "ok: shared composite hoisted under one residual let, value preserved"

  # No-op: atoms only — nothing qualifies, tree returned unchanged.
  let atomsOnly = add(atom("x"), atom("x"))
  var ctx2 = newGenletCtx()
  let atomsOut = insertLets(atomsOnly, ctx2)
  doAssert ctx2.counter == 0
  doAssert $atomsOut == $atomsOnly
  echo "ok: atom-only duplication left alone (no spurious lets)"

  # No-op: term shared only twice never qualifies (savings always -4).
  let small = mul(atom("x"), atom("y"))  # 3 nodes
  let twice = add(small, small)
  var ctx3 = newGenletCtx()
  discard insertLets(twice, ctx3)
  doAssert ctx3.counter == 0, "n=2 sharing must not qualify"
  echo "ok: twice-shared small term left alone (savings test)"

  # Boundary: a term shared across a `let` must NOT be hoisted across it.
  # t occurs once in the bound part and twice in the body; counted
  # separately neither side qualifies, and the pass never crosses the let.
  let across = glet("z", t, add(t, t))
  var ctx4 = newGenletCtx()
  let acrossOut = insertLets(across, ctx4)
  doAssert ctx4.counter == 0, "must not hoist across a let binder"
  doAssert $acrossOut == $across
  echo "ok: let binder is a sharing boundary"

  # But hoisting *inside* a let body is still allowed.
  let inside = glet("z", atom("9"), add(t, add(t, t)))
  var ctx5 = newGenletCtx()
  let insideOut = insertLets(inside, ctx5)
  doAssert ctx5.counter == 1, "hoist inside the body should still happen"
  doAssert evalTree(insideOut, env) == 45, "value preserved"
  doAssert ($insideOut).startsWith("(let z = 9 in (let genlet0 = "),
    "let must land inside the outer let's body: " & $insideOut
  echo "ok: hoist inside a let body works, binder not crossed"

  # The same cases through a client's own IR and callbacks.
  let ct = cMul(cAdd(cAtom("x"), cAtom("1")),
                cAdd(cAtom("y"), cAtom("2")))
  let cexpr = cAdd(ct, cAdd(ct, ct))
  var cctx = newGenletCtx()
  let cout = insertLetsCb(cexpr, cctx, cCallbacks())
  doAssert cctx.counter == 1
  doAssert cEval(cout, env) == 45, "callback let-insertion must preserve value"
  doAssert cRender(cout) ==
    "(let genlet0 = mul(add(x, 1), add(y, 2)) in add(genlet0, add(genlet0, genlet0)))"
  echo "ok: callback client hoisted shared composite, value preserved"

  let csmall = cMul(cAtom("x"), cAtom("y"))
  var cctx2 = newGenletCtx()
  discard insertLetsCb(cAdd(csmall, csmall), cctx2, cCallbacks())
  doAssert cctx2.counter == 0
  echo "ok: callback twice-shared small term left alone"

  var cctx3 = newGenletCtx()
  discard insertLetsCb(cAdd(cAtom("x"), cAtom("x")), cctx3, cCallbacks())
  doAssert cctx3.counter == 0
  echo "ok: callback atom-only duplication left alone"

  var cctx4 = newGenletCtx()
  let cacross = cLet("z", ct, cAdd(ct, ct))
  let cacrossOut = insertLetsCb(cacross, cctx4, cCallbacks())
  doAssert cctx4.counter == 0
  doAssert cRender(cacrossOut) == cRender(cacross)
  echo "ok: callback let binder is a sharing boundary"

  var cctx5 = newGenletCtx()
  let cinside = cLet("z", cAtom("9"), cAdd(ct, cAdd(ct, ct)))
  let cinsideOut = insertLetsCb(cinside, cctx5, cCallbacks())
  doAssert cctx5.counter == 1
  doAssert cEval(cinsideOut, env) == 45
  doAssert cRender(cinsideOut).startsWith("(let z = 9 in (let genlet0 = ")
  echo "ok: callback hoist inside a let body works"

  echo "=== generic genlet ok ==="
