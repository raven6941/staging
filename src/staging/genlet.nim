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
## Sharing boundaries: insertion never crosses a `let` binder. A `let` is
## both a counting boundary (occurrences inside it are not counted with
## occurrences outside it) and a substitution boundary (occurrences inside
## it are not replaced). This is the generic form of the original's
## `rgFresh`/`rgDisj` boundary discipline: no variable is ever lifted out
## of its scope and no branch structure is reshuffled. Hoisting *inside* a
## let body is still allowed — the boundary only blocks crossing it.
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
  ## Bottom-up: inner lets first, then hoist at each node.
  ## Loops per node because one hoist can reveal the next candidate; each
  ## hoist strictly reduces node count (savings test), so the loop
  ## terminates.
  var cb = gtreeCallbacks()
  cb.freeVars = nil
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
  freq = occurrences(node, cb)
  callbackSamples(node, cb, sample)

  var bestKey = ""
  var bestSave = 0
  for k, n in freq:
    if n > 1:
      let size = callbackSize(sample[k], cb)
      let save = (n - 1) * (size - 1) - size - 3
      if save > bestSave:
        bestSave = save
        bestKey = k
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

  var children: seq[T] = @[]
  for child in cb.children(node):
    children.add(callbackInsert(child, ctx, cb))
  var rebuilt = cb.rebuild(node, children)

  # A boundary may contain independently hoistable terms, but it is never
  # itself a candidate and its children must not be counted with its parent.
  if cb.isBoundary(node):
    return rebuilt

  while true:
    var changed = false
    let next = callbackHoist(rebuilt, ctx, cb, changed)
    if not changed:
      return rebuilt
    rebuilt = next

proc insertLetsCb*[T](root: T; ctx: var GenletCtx;
                      cb: GenletCallbacks[T]): T =
  ## Bottom-up callback-based let insertion. Composite children are rebuilt
  ## through `cb.rebuild`; boundary nodes are handled by their own child
  ## traversal and are never counted or substituted as part of their parent.
  callbackInsert(root, ctx, cb)
