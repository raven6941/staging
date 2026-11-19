## Generic, bottom-up traversal and substitution over client residual trees.

import std/[tables, sets]

type
  TraversalCallbacks*[T] = object
    children*: proc(node: T): seq[T]
    key*: proc(node: T): string
    isComposite*: proc(node: T): bool
    isBoundary*: proc(node: T): bool
    rebuild*: proc(node: T; children: seq[T]): T
    makeRef*: proc(binder: string): T
    makeLet*: proc(binder: string; bound, body: T): T
    ## Optional scope information.  A nil freeVars retains the historical
    ## genlet rule: substitution does not enter boundary nodes.
    binders*: proc(node: T): seq[string]
    freeVars*: proc(node: T): seq[string]
    isPure*: proc(node: T): bool

  ## Compatibility name retained for clients of genlet's original API.
  GenletCallbacks*[T] = TraversalCallbacks[T]

  ## One composite occurrence and the binders visible at that occurrence.
  GlobalOccurrence*[T] = object
    node*: T
    binders*: seq[string]

proc intersects(a: seq[string]; scope: HashSet[string]): bool =
  for name in a:
    if name in scope: return true

proc mapTreeImpl[T](node: T; cb: TraversalCallbacks[T];
                    rule: proc(node: T): T; scope: HashSet[string]): T =
  var kids: seq[T] = @[]
  let crossing = cb.isBoundary(node)
  var childScope = scope
  if crossing and not cb.binders.isNil:
    for name in cb.binders(node): childScope.incl(name)
  for child in cb.children(node):
    kids.add(mapTreeImpl(child, cb, rule, childScope))
  let rebuilt = cb.rebuild(node, kids)
  let candidate = rule(rebuilt)
  if cb.freeVars.isNil or candidate == rebuilt:
    return candidate
  if intersects(cb.freeVars(candidate), scope):
    return rebuilt
  candidate

proc mapTree*[T](root: T; cb: TraversalCallbacks[T];
                 rule: proc(node: T): T): T =
  ## Recurse into children, rebuild, then apply rule.  A rule that returns
  ## its input means "no rewrite".  Scope checks reject a replacement whose
  ## free variables would be captured by an intervening boundary.
  mapTreeImpl(root, cb, rule, initHashSet[string]())

proc substImpl[T](node: T; cb: TraversalCallbacks[T];
                  subst: Table[string, T]; scope: HashSet[string]): T =
  # With no free-variable query, preserve genlet's boundary discipline.
  if cb.isBoundary(node) and cb.freeVars.isNil:
    return node

  var childScope = scope
  if cb.isBoundary(node) and not cb.binders.isNil:
    for name in cb.binders(node): childScope.incl(name)

  if not cb.isBoundary(node):
    let k = cb.key(node)
    if k in subst:
      let replacement = subst[k]
      if cb.freeVars.isNil or not intersects(cb.freeVars(replacement), scope):
        return replacement

  var kids: seq[T] = @[]
  for child in cb.children(node):
    kids.add(substImpl(child, cb, subst, childScope))
  cb.rebuild(node, kids)

proc substTree*[T](root: T; cb: TraversalCallbacks[T];
                   subst: Table[string, T]): T =
  ## Replace keyed nodes, refusing a replacement that would capture a name
  ## bound by any enclosing boundary.  V1 deliberately treats every child
  ## of a boundary, including its bound value, as being in binder scope.
  substImpl(root, cb, subst, initHashSet[string]())

proc occurrences*[T](root: T; cb: TraversalCallbacks[T]): CountTable[string] =
  ## Count composite nodes, matching the original genlet counting contract.
  var freq = initCountTable[string]()
  proc walk(node: T) =
    if cb.isBoundary(node): return
    if cb.isComposite(node): freq.inc(cb.key(node))
    for child in cb.children(node): walk(child)
  walk(root)
  result = freq

proc globalOccurrences*[T](root: T; cb: TraversalCallbacks[T]):
    Table[string, seq[GlobalOccurrence[T]]] =
  ## Global counting counterpart to `occurrences`: do not stop at
  ## boundaries, and retain each occurrence's binder context.
  var found = initTable[string, seq[GlobalOccurrence[T]]]()
  proc walk(node: T; scope: seq[string]) =
    if cb.isComposite(node) and not cb.isBoundary(node):
      let k = cb.key(node)
      found.mgetOrPut(k, @[]).add(GlobalOccurrence[T](node: node,
        binders: scope))
    var childScope = scope
    if cb.isBoundary(node) and not cb.binders.isNil:
      for name in cb.binders(node):
        if name notin childScope: childScope.add(name)
    for child in cb.children(node): walk(child, childScope)
  walk(root, @[])
  result = found
