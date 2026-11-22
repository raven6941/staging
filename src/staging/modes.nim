## Generic mode vocabulary and bound-on-all-paths analysis.
##
## The library owns the mode vocabulary and the structural fold; a client
## owns the goal tree and the query describing which positions bind.  The
## fold unions sequential (conjunction) children and intersects alternative
## (disjunction) children.  A boundary's binders are hidden from its parent,
## using `TraversalCallbacks.binders` together with `isBoundary`.
##
## `mGround` is runtime-checked by the client, not decided by this library.
## Static implies ground at staging time, but ground does not imply static:
## a ground runtime value is not statically known.  This fold must never be
## used as a groundness prover.  Eponym's `modes.nim` adoption is a separate
## step; its binding positions and concrete mode tables remain client-owned.

import std/sets
import staging/traversal

export TraversalCallbacks

type
  Mode* = enum
    ## The variable must be bound (ground) on entry to the goal.
    mIn
    ## The variable is bound on exit, on every successful path.
    mOut
    ## Groundness is checked at runtime, not statically; this library does
    ## not perform a static check for this mode.
    mGround

  ModeCallbacks*[T] = object
    cb*: TraversalCallbacks[T]
    ## The variables bound by this node's own binding positions.
    binds*: proc(node: T): seq[string]
    ## True when children are alternatives; false means sequential children.
    isDisj*: proc(node: T): bool

proc boundOnAllPaths*[T](node: T; mc: ModeCallbacks[T]): HashSet[string] =
  ## Return variables guaranteed bound after `node` succeeds on every path.
  ## Conjunction children are unioned; disjunction children are intersected.
  ## A boundary hides the names returned by its `binders` query from callers.
  result = initHashSet[string]()
  for name in mc.binds(node):
    result.incl(name)

  let children = mc.cb.children(node)
  if children.len > 0:
    var childResult: HashSet[string]
    if mc.isDisj(node):
      childResult = boundOnAllPaths(children[0], mc)
      for i in 1 ..< children.len:
        let branch = boundOnAllPaths(children[i], mc)
        var common = initHashSet[string]()
        for name in childResult:
          if name in branch:
            common.incl(name)
        childResult = common
    else:
      childResult = initHashSet[string]()
      for child in children:
        for name in boundOnAllPaths(child, mc):
          childResult.incl(name)
    for name in childResult:
      result.incl(name)

  if mc.cb.isBoundary(node) and not mc.cb.binders.isNil:
    for name in mc.cb.binders(node):
      result.excl(name)
