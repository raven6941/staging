import std/sets
import staging/modes

type
  GoalKind = enum
    gEq, gConj, gDisj, gFresh

  Goal = ref object
    case kind: GoalKind
    of gEq:
      variable: string
    of gConj, gDisj:
      goals: seq[Goal]
    of gFresh:
      binder: string
      body: Goal

proc eqGoal(variable: string): Goal =
  Goal(kind: gEq, variable: variable)

proc conj(goals: seq[Goal]): Goal =
  Goal(kind: gConj, goals: goals)

proc disj(goals: seq[Goal]): Goal =
  Goal(kind: gDisj, goals: goals)

proc fresh(binder: string; body: Goal): Goal =
  Goal(kind: gFresh, binder: binder, body: body)

proc callbacks(): TraversalCallbacks[Goal] =
  TraversalCallbacks[Goal](
    children: proc(node: Goal): seq[Goal] =
      case node.kind
      of gEq: @[]
      of gConj, gDisj: node.goals
      of gFresh: @[node.body],
    key: proc(node: Goal): string = $node.kind,
    isComposite: proc(node: Goal): bool = node.kind != gEq,
    isBoundary: proc(node: Goal): bool = node.kind == gFresh,
    rebuild: proc(node: Goal; children: seq[Goal]): Goal = node,
    makeRef: proc(name: string): Goal = eqGoal(name),
    makeLet: proc(name: string; bound, body: Goal): Goal = fresh(name, body),
    binders: proc(node: Goal): seq[string] =
      if node.kind == gFresh: @[node.binder] else: @[])

proc modeCallbacks(): ModeCallbacks[Goal] =
  ModeCallbacks[Goal](
    cb: callbacks(),
    binds: proc(node: Goal): seq[string] =
      if node.kind == gEq: @[node.variable] else: @[],
    isDisj: proc(node: Goal): bool = node.kind == gDisj)

proc setOf(names: varargs[string]): HashSet[string] =
  result = initHashSet[string]()
  for name in names:
    result.incl(name)

proc check(goal: Goal; expected: HashSet[string]) =
  doAssert boundOnAllPaths(goal, modeCallbacks()) == expected

when isMainModule:
  # Conjunction unions, including nested conjunctions.
  check(conj(@[eqGoal("x"), eqGoal("y")]), setOf("x", "y"))
  check(conj(@[eqGoal("x"), conj(@[eqGoal("y"), eqGoal("z")])]),
    setOf("x", "y", "z"))

  # Disjunction intersects, including a branch that binds nothing.
  check(disj(@[
    conj(@[eqGoal("x"), eqGoal("y")]),
    conj(@[eqGoal("x"), eqGoal("z")])]), setOf("x"))
  check(disj(@[eqGoal("x"), conj(@[])]), setOf())

  # Fresh binders are local, while an identical name outside remains visible.
  check(fresh("x", eqGoal("x")), setOf())
  check(eqGoal("x"), setOf("x"))
  check(fresh("x", conj(@[eqGoal("x"), eqGoal("y")])), setOf("y"))
  check(conj(@[eqGoal("x"), fresh("x", eqGoal("x"))]), setOf("x"))

  # Appendo-shaped mixed nesting: the second child is a disjunction whose
  # branches bind xs, and xs plus ys, so only xs survives the intersection.
  let mixed = conj(@[
    eqGoal("prefix"),
    disj(@[eqGoal("xs"), conj(@[eqGoal("xs"), eqGoal("ys")])])])
  check(mixed, setOf("prefix", "xs"))

  # Load-bearing negative check: x is not bound on every disjunct.
  let oneSided = disj(@[eqGoal("x"), eqGoal("y")])
  let oneSidedResult = boundOnAllPaths(oneSided, modeCallbacks())
  doAssert "x" notin oneSidedResult
  doAssert "y" notin oneSidedResult

  echo "ok: generic mode fold"
