## genlet: residual let-insertion over a generic residual tree.
##
## REWRITTEN for the standalone library. The Eponym original
## (`src/experimental/staging/genlet.nim`, issue #61) performs this pass over
## relational `RelGoal` data — `RTerm` terms, `rgEq`/`rgFresh` goals, with
## `run`/`freshVar` from miniKanren in its self-test — so it cannot leave
## Eponym as written. This version is the same algorithm over a generic
## tree (`GTree`), with no relational or Eponym dependency (stdlib only).
##
## The problem: partial evaluators duplicate computations. When a static
## function is applied twice in the residual, the application is computed
## twice. The standard fix is *let-insertion* — name the shared computation
## once with a residual `let`. Danvy's TDPE route and MetaOCaml's `genlet`
## do it by capturing the code-generation continuation up to a delimiter;
## this pass achieves the same sharing as a residual post-pass (common-
## subterm elimination with residual binders):
##
##   P[t] ∧ Q[t]   →   let gN = t in P[gN] ∧ Q[gN]
##
## (In tree form: a node whose subtree contains a repeated composite
## subterm `t` is rewritten to a `let` binding `t` once and substituting
## a placeholder atom for every occurrence.)
##
## When to insert: pure savings test, carried over unchanged from the
## original. Replacing n occurrences of a term of s nodes with placeholders
## removes (n-1)*(s-1) term nodes and adds the residual equation (s+1 term
## nodes, ~3 extra nodes for the equation, the binder, and the added
## structure). Hoist only when the net is positive; this self-calibrates —
## on residuals with no real composite duplication, nothing qualifies and
## the pass is a no-op. Note the arithmetic: with n = 2 the saving is
## always -4, so a term shared only twice never qualifies; sharing pays
## from n = 3 with a term of at least 6 nodes.
##
## Sharing boundaries: let nodes are scope-checked boundaries, not absolute
## counting/substitution boundaries. When freeVars is supplied, occurrences
## may cross a let only when the candidate's free variables do not intersect
## binders introduced on the way to any occurrence. With freeVars nil, the
## conservative per-region boundary behaviour remains in force.
##
## Placement order: at each node the pass hoists before recursing, and
## among qualifying candidates takes the smallest first. A larger term
## hoisted first collapses the counts of the smaller terms inside it,
## so the smaller term must go first (its hoist leaves larger terms'
## counts untouched — their copies change identically). See
## callbackInsert / callbackHoist.
##
## Effect policy: the pass is a size optimization for pure computations.
## Let-insertion is never required for correctness here, only an optional
## size optimization. When effectful primitives appear, insertion must be
## restricted to computations the effect annotation marks duplicable.
## This module does not track effects; clients with effectful nodes must
## only feed it pure subtrees (or extend `GTree` with an effect mark).
##
## What this is NOT: it is not the relational genlet. The original's
## `RelGoal`/`RTerm` version, its `insertLetsIntoSpecs` driver over
## specialized relation bodies, and its miniKanren agreement self-test
## stay in Eponym. A client whose residual is a `RelGoal` should use that
## version; a client whose residual is any other tree should use this one,
## or map its IR onto `GTree`.

import tables
import sequtils
import strutils
import sets
import staging/traversal

export TraversalCallbacks, GenletCallbacks

type
  GTreeKind* = enum
    gkAtom  ## leaf: a variable name or a literal
    gkNode  ## composite: an operator applied to children
    gkLet   ## residual let: binder = bound in body

  GTree* = ref object
    ## A generic residual tree. Clients either build their residual
    ## directly as a `GTree` or map their own IR onto it for this pass.
    case kind*: GTreeKind
    of gkAtom:
      name*: string
    of gkNode:
      op*: string
      children*: seq[GTree]
    of gkLet:
      binder*: string
      bound*: GTree
      body*: GTree

  GenletCtx* = object
    counter*: int  ## fresh-name supply for inserted binders

proc newGenletCtx*(): GenletCtx = GenletCtx(counter: 0)

proc gatom*(name: string): GTree = GTree(kind: gkAtom, name: name)

proc gnode*(op: string; children: seq[GTree]): GTree =
  GTree(kind: gkNode, op: op, children: children)

proc glet*(binder: string; bound, body: GTree): GTree =
  GTree(kind: gkLet, binder: binder, bound: bound, body: body)

proc `$`*(t: GTree): string =
  ## Canonical structural rendering; doubles as the structural key used
  ## for counting occurrences (two subtrees with the same `$` are the
  ## same term for sharing purposes).
  case t.kind
  of gkAtom: t.name
  of gkNode:
    t.op & "(" & t.children.mapIt($it).join(", ") & ")"
  of gkLet:
    "(let " & t.binder & " = " & $t.bound & " in " & $t.body & ")"

proc treeNodes*(t: GTree): int =
  ## Node count: atom = 1, node = 1 + children, let = 1 + bound + body.
  case t.kind
  of gkAtom: result = 1
  of gkNode:
    result = 1
    for c in t.children: result += treeNodes(c)
  of gkLet: result = 1 + treeNodes(t.bound) + treeNodes(t.body)

proc gtreeFreeVars(t: GTree): seq[string] =
  var found = initHashSet[string]()
  proc walk(n: GTree; bound: HashSet[string]) =
    case n.kind
    of gkAtom:
      try: discard parseInt(n.name)
      except ValueError:
        if n.name notin bound: found.incl(n.name)
    of gkNode:
      for c in n.children: walk(c, bound)
    of gkLet:
      var nested = bound
      nested.incl(n.binder)
      walk(n.bound, nested)
      walk(n.body, nested)
  walk(t, initHashSet[string]())
  for name in found: result.add(name)

proc gtreeCallbacks*(): TraversalCallbacks[GTree] =
  TraversalCallbacks[GTree](
    children: proc(n: GTree): seq[GTree] =
      case n.kind
      of gkAtom: @[]
      of gkNode: n.children
      of gkLet: @[n.bound, n.body],
    key: proc(n: GTree): string = $n,
    isComposite: proc(n: GTree): bool = n.kind != gkAtom,
    isBoundary: proc(n: GTree): bool = n.kind == gkLet,
    rebuild: proc(n: GTree; cs: seq[GTree]): GTree =
      case n.kind
      of gkAtom: n
      of gkNode: gnode(n.op, cs)
      of gkLet: glet(n.binder, cs[0], cs[1]),
    makeRef: gatom,
    makeLet: glet,
    binders: proc(n: GTree): seq[string] = @[n.binder],
    freeVars: gtreeFreeVars)

proc insertLetsCb*[T](root: T; ctx: var GenletCtx;
                      cb: GenletCallbacks[T]): T

proc insertLets*(g: GTree; ctx: var GenletCtx): GTree =
  ## Hoist at each node before recursing into its children (see
  ## callbackInsert), so a candidate spanning several children is
  ## decided while its count is still whole. Loops per node because one
  ## hoist can reveal the next candidate; each hoist strictly reduces
  ## node count — the savings test implies a true change of
  ## -(n-1)*(s-1) + 2 < 0 — so the loop terminates.
  var cb = gtreeCallbacks()
  insertLetsCb(g, ctx, cb)

## Callback-based genlet
##
## `insertLetsCb` applies the same pass to a client's own residual tree.  The
## client supplies the small amount of tree knowledge needed by the pass;
## no intermediate `GTree` is built.

proc callbackSize[T](node: T; cb: GenletCallbacks[T]): int =
  result = 1
  for child in cb.children(node):
    result += callbackSize(child, cb)

proc callbackSamples[T](node: T; cb: GenletCallbacks[T];
                        sample: var Table[string, T]) =
  if cb.isBoundary(node):
    return
  if cb.isComposite(node):
    let k = cb.key(node)
    if k notin sample:
      sample[k] = node
  for child in cb.children(node):
    callbackSamples(child, cb, sample)

proc callbackHoist[T](node: T; ctx: var GenletCtx;
                      cb: GenletCallbacks[T]; changed: var bool): T =
  var freq = initCountTable[string]()
  var sample = initTable[string, T]()
  var contexts = initTable[string, seq[seq[string]]]()
  if cb.freeVars.isNil:
    freq = occurrences(node, cb)
    callbackSamples(node, cb, sample)
  else:
    let global = globalOccurrences(node, cb)
    for k, entries in global:
      freq[k] = entries.len
      if entries.len > 0:
        sample[k] = entries[0].node
        for entry in entries:
          contexts.mgetOrPut(k, @[]).add(entry.binders)

  var bestKey = ""
  var bestSize = 0
  var bestSave = 0
  for k, n in freq:
    if n > 1:
      let size = callbackSize(sample[k], cb)
      let save = (n - 1) * (size - 1) - size - 3
      if save <= 0:
        continue
      var scopeSafe = true
      if not cb.freeVars.isNil:
        let free = cb.freeVars(sample[k])
        for context in contexts[k]:
          for name in free:
            if name in context: scopeSafe = false
      if not scopeSafe:
        continue
      # Smallest qualifying composite first: hoisting a containing term
      # collapses the counts of the terms inside it (their copies are
      # replaced by the new reference, leaving only the bound copy), so
      # a larger term hoisted first can push a smaller shared term below
      # the savings threshold before the pass ever sees it at the shared
      # site (stencil: wm(2)/wm(3) hoisted first leave mul(a2,a3) at 4
      # occurrences, saving exactly 0). Hoisting the smaller term first
      # leaves larger terms' counts untouched — their copies change
      # identically — so nothing is lost. Ties break by greatest saving,
      # then by key, so placement is deterministic.
      if bestKey == "" or size < bestSize or
          (size == bestSize and save > bestSave) or
          (size == bestSize and save == bestSave and k < bestKey):
        bestKey = k
        bestSize = size
        bestSave = save
  if bestKey == "":
    return node

  let name = "genlet" & $ctx.counter
  inc ctx.counter
  changed = true
  var replacements = initTable[string, T]()
  replacements[bestKey] = cb.makeRef(name)
  cb.makeLet(name, sample[bestKey], substTree(node, cb, replacements))

proc callbackInsert[T](node: T; ctx: var GenletCtx;
                       cb: GenletCallbacks[T]): T =
  if not cb.isComposite(node):
    return node

  # A boundary is never itself a hoist site: recurse into its children
  # and return rebuilt. (A term occurring on both sides of a boundary
  # is only hoisted above it by an ancestor's hoist, and only when the
  # scope check allows.)
  if cb.isBoundary(node):
    var children: seq[T] = @[]
    for child in cb.children(node):
      children.add(callbackInsert(child, ctx, cb))
    return cb.rebuild(node, children)

  # Hoist at this node FIRST, on global counts over the subtree as it
  # stands: a candidate that only qualifies at this site (its
  # occurrences span several children) must be decided before the
  # children's own hoists rewrite the subtree and collapse its count
  # (stencil: mul(a2,a3) qualifies only at the root; the wm hoists
  # below would leave it at 4 occurrences, saving 0).
  var current = node
  while true:
    var changed = false
    let next = callbackHoist(current, ctx, cb, changed)
    if not changed:
      break
    current = next

  # Then recurse into the children, so sharing inside a region (and
  # inside a just-inserted let's bound value) is still found.
  var children: seq[T] = @[]
  for child in cb.children(current):
    children.add(callbackInsert(child, ctx, cb))
  var rebuilt = cb.rebuild(current, children)

  # And hoist again: the children's rewriting can reveal a candidate
  # at this node (e.g. substitution making two subterms equal).
  while true:
    var changed = false
    let next = callbackHoist(rebuilt, ctx, cb, changed)
    if not changed:
      return rebuilt
    rebuilt = next

proc insertLetsCb*[T](root: T; ctx: var GenletCtx;
                      cb: GenletCallbacks[T]): T =
  ## Hoist-first traversal: at each non-boundary node the pass hoists on
  ## global counts over the subtree as it stands, then recurses into the
  ## children, then hoists again. Boundary nodes are never hoist sites
  ## themselves; their children are traversed separately. When freeVars
  ## is supplied, occurrences inside a boundary are counted with
  ## occurrences outside it and may be hoisted above it, but only when
  ## the scope check proves the candidate mentions none of the
  ## intervening binders; with freeVars nil the old per-region
  ## discipline holds.
  callbackInsert(root, ctx, cb)
