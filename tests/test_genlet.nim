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

  echo "=== generic genlet ok ==="
