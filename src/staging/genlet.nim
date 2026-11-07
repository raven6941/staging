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

proc countTerms(t: GTree; freq: var CountTable[string];
                sample: var Table[string, GTree]) =
  ## Count composite (gkNode) subtrees by structural key in the tree
  ## rooted at t. Stops at gkLet boundaries: those are the sharing
  ## boundaries, so counted occurrences are always replaceable under one
  ## residual binder placed at the hoist site.
  case t.kind
  of gkAtom: discard
  of gkNode:
    let k = $t
    freq.inc(k)
    if k notin sample: sample[k] = t
    for c in t.children: countTerms(c, freq, sample)
  of gkLet: discard  # sharing boundary

proc substShared(g, target, repl: GTree): GTree =
  ## Replace occurrences of target in g with repl, using the same boundary
  ## discipline as countTerms (so exactly the counted occurrences are
  ## replaced). A node equal to target is replaced whole, without
  ## descending into it.
  case g.kind
  of gkAtom: g
  of gkNode:
    if $g == $target: repl
    else: gnode(g.op, g.children.mapIt(substShared(it, target, repl)))
  of gkLet: g  # boundary: not counted, not touched

proc hoist(g: GTree; ctx: var GenletCtx): GTree =
  ## Insert one residual let at this node for the candidate with the
  ## largest positive node savings, if any.
  var freq = initCountTable[string]()
  var sample = initTable[string, GTree]()
  countTerms(g, freq, sample)
  var bestKey = ""
  var bestSave = 0
  for k, n in freq:
    if n > 1:
      let s = treeNodes(sample[k])
      # Savings: (n-1) occurrences replaced by 1-node placeholders,
      # minus the residual equation (s term nodes + ~3 nodes: the let
      # itself, the binder, the added structure).
      let save = (n - 1) * (s - 1) - s - 3
      if save > bestSave:
        bestSave = save
        bestKey = k
  if bestKey == "": return g
  let t = sample[bestKey]
  let name = "genlet" & $ctx.counter
  inc ctx.counter
  glet(name, t, substShared(g, t, gatom(name)))

proc insertLets*(g: GTree; ctx: var GenletCtx): GTree =
  ## Bottom-up: inner lets first, then hoist at each node.
  ## Loops per node because one hoist can reveal the next candidate; each
  ## hoist strictly reduces node count (savings test), so the loop
  ## terminates.
  case g.kind
  of gkAtom: g
  of gkLet:
    # Binder boundary: recurse into bound and body separately; never
    # hoist a term across the let.
    glet(g.binder, insertLets(g.bound, ctx), insertLets(g.body, ctx))
  of gkNode:
    var rebuilt = gnode(g.op, g.children.mapIt(insertLets(it, ctx)))
    while true:
      let g2 = hoist(rebuilt, ctx)
      if g2 == rebuilt: break
      rebuilt = g2
    rebuilt
