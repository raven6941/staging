## Worked relational genlet example over a small, toy goal tree.

import tables
import strutils
import staging/genlet

type
  RKind = enum
    rkAtom, rkVar, rkPair,
    rkSucceed, rkFail, rkEq, rkConj, rkDisj, rkFresh, rkCall

  RNode = ref object
    kind: RKind
    name: string
    left, right, body: RNode
    binder: string

proc atom(name: string): RNode = RNode(kind: rkAtom, name: name)
proc logicVar(name: string): RNode = RNode(kind: rkVar, name: name)
proc pair(a, b: RNode): RNode = RNode(kind: rkPair, left: a, right: b)
proc succeed(): RNode = RNode(kind: rkSucceed)
proc fail(): RNode = RNode(kind: rkFail)
proc eq(a, b: RNode): RNode = RNode(kind: rkEq, left: a, right: b)
proc conj(a, b: RNode): RNode = RNode(kind: rkConj, left: a, right: b)
proc disj(a, b: RNode): RNode = RNode(kind: rkDisj, left: a, right: b)
proc fresh(name: string; body: RNode): RNode =
  RNode(kind: rkFresh, binder: name, body: body)
proc call(name: string): RNode = RNode(kind: rkCall, name: name)

proc `$`(n: RNode): string =
  case n.kind
  of rkAtom, rkVar, rkCall: n.name
  of rkPair: "(" & $n.left & ", " & $n.right & ")"
  of rkSucceed: "succeed"
  of rkFail: "fail"
  of rkEq: "(" & $n.left & " == " & $n.right & ")"
  of rkConj: "(" & $n.left & " ∧ " & $n.right & ")"
  of rkDisj: "(" & $n.left & " ∨ " & $n.right & ")"
  of rkFresh: "fresh " & n.binder & "; " & $n.body

proc rChildren(n: RNode): seq[RNode] =
  case n.kind
  of rkPair, rkEq, rkConj, rkDisj: @[n.left, n.right]
  of rkFresh: @[n.body]
  else: @[]

proc rFreeVars(n: RNode): seq[string] =
  proc walk(n: RNode; bound: seq[string]; found: var seq[string]) =
    case n.kind
    of rkVar:
      if n.name notin bound and n.name notin found: found.add(n.name)
    of rkFresh:
      var nested = bound
      nested.add(n.binder)
      walk(n.body, nested, found)
    else:
      for child in rChildren(n): walk(child, bound, found)
  walk(n, @[], result)

proc rCallbacks(): TraversalCallbacks[RNode] =
  TraversalCallbacks[RNode](
    children: rChildren,
    key: proc(n: RNode): string = $n,
    isComposite: proc(n: RNode): bool =
      n.kind notin {rkAtom, rkVar, rkSucceed, rkFail, rkCall},
    isBoundary: proc(n: RNode): bool = n.kind in {rkFresh, rkDisj},
    rebuild: proc(n: RNode; children: seq[RNode]): RNode =
      case n.kind
      of rkPair: pair(children[0], children[1])
      of rkEq: eq(children[0], children[1])
      of rkConj: conj(children[0], children[1])
      of rkDisj: disj(children[0], children[1])
      of rkFresh: fresh(n.binder, children[0])
      else: n,
    makeRef: logicVar,
    makeLet: proc(binder: string; bound, body: RNode): RNode =
      fresh(binder, conj(eq(logicVar(binder), bound), body)),
    binders: proc(n: RNode): seq[string] =
      if n.kind == rkFresh: @[n.binder] else: @[],
    freeVars: rFreeVars,
    isPure: proc(n: RNode): bool = n.kind != rkCall or n.name != "trace")

type Subst = Table[string, RNode]

proc deref(t: RNode; s: Subst): RNode =
  result = t
  while result.kind == rkVar and result.name in s:
    result = s[result.name]

proc unify(a, b: RNode; s: var Subst): bool =
  let x = deref(a, s)
  let y = deref(b, s)
  if x.kind == rkVar:
    s[x.name] = y
    return true
  if y.kind == rkVar:
    s[y.name] = x
    return true
  if x.kind != y.kind: return false
  case x.kind
  of rkAtom: x.name == y.name
  of rkPair: unify(x.left, y.left, s) and unify(x.right, y.right, s)
  else: false

proc evalGoal(g: RNode; s: var Subst): bool =
  ## The opaque call is deliberately deterministic: `trace` always succeeds.
  case g.kind
  of rkSucceed: true
  of rkFail: false
  of rkEq: unify(g.left, g.right, s)
  of rkConj: evalGoal(g.left, s) and evalGoal(g.right, s)
  of rkDisj:
    var left = s
    if evalGoal(g.left, left):
      s = left
      true
    else:
      evalGoal(g.right, s)
  of rkFresh:
    var nested = s
    let ok = evalGoal(g.body, nested)
    if ok: s = nested
    ok
  of rkCall: g.name == "trace"
  else: false

proc agrees(a, b: RNode): bool =
  var sa = initTable[string, RNode]()
  var sb = initTable[string, RNode]()
  evalGoal(a, sa) == evalGoal(b, sb)

when isMainModule:
  let t = pair(atom("a"), atom("b"))
  let before = conj(eq(t, atom("p")), eq(t, atom("q")))
  var ctx = newGenletCtx()
  let after = insertLetsCb(before, ctx, rCallbacks())
  doAssert $after == "fresh genlet0; ((genlet0 == (a, b)) ∧ " &
    "((genlet0 == p) ∧ (genlet0 == q)))"
  doAssert ctx.counter == 1
  echo "ok: conjunction shares one relational term with one fresh binder"

  let scoped = conj(
    fresh("x", conj(eq(pair(logicVar("x"), atom("b")), atom("p")),
                         eq(pair(logicVar("x"), atom("b")), atom("q")))),
    eq(pair(logicVar("x"), atom("b")), atom("r")))
  var scopedCtx = newGenletCtx()
  let scopedOut = insertLetsCb(scoped, scopedCtx, rCallbacks())
  doAssert not ($scopedOut).startsWith("fresh genlet")
  doAssert ($scopedOut).contains("fresh x;")
  echo "ok: fresh binder is a sharing boundary"

  let branched = disj(eq(t, atom("p")), eq(t, atom("q")))
  var branchCtx = newGenletCtx()
  let branchOut = insertLetsCb(branched, branchCtx, rCallbacks())
  doAssert branchCtx.counter == 0
  doAssert $branchOut == $branched
  echo "ok: disjunction is a sharing boundary"

  let effect = conj(conj(call("trace"), succeed()),
                    conj(call("trace"), succeed()))
  var effectCtx = newGenletCtx()
  let effectOut = insertLetsCb(effect, effectCtx, rCallbacks())
  doAssert effectCtx.counter == 0
  doAssert $effectOut == $effect
  echo "ok: effectful candidates are never hoisted"

  let queries = [
    conj(eq(t, atom("p")), eq(t, atom("p"))),
    conj(eq(t, atom("p")), eq(t, atom("q"))),
    fresh("x", eq(pair(logicVar("x"), atom("b")), t)),
    disj(call("trace"), fail())]
  for query in queries:
    var evalCtx = newGenletCtx()
    let rewritten = insertLetsCb(query, evalCtx, rCallbacks())
    doAssert agrees(query, rewritten), "evaluator disagrees for " & $query
  echo "ok: direct ground evaluator agrees before and after insertion"
