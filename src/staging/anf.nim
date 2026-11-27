## Tree-to-ANF conversion and ANF rewrites.
##
## Decision: ANF is a separate, generic pass over the residual tree, NOT
## Def nodes in the residual and NOT a new IR with its own traversal.
##
## - Def nodes in the residual are rejected: the residual is DSL-owned
##   (the framework never inspects IRNode), so forcing a Def/Exp split on
##   every DSL would be invasive and would break the library's
##   codegen-agnostic stance. ANF as a pass leaves the residual tree
##   untouched; DSLs opt in per pass.
## - ANF with its own traversal is rejected as unnecessary: the flat
##   binding list makes traversal a linear scan, and the existing generic
##   `mapTree`/`substTree` already cover tree passes. Rewrites over ANF
##   are plain scans over bindings plus a substitution table.
##
## Mechanism: `toAnf` names every composite subexpression (post-order,
## fresh name per composite node) so each binding's right-hand side has
## only atomic children — literals, inputs, and references. That is the
## whole normal form, and it is where rewrites belong: an
## `ArithExpOpt`-style rule sees `x + 0` directly instead of hunting it
## inside a nested tree, and CSE is a keyed dedup of the flat binding
## list. `fromAnf` substitutes bindings back, in reverse order, so the
## result is again an ordinary residual tree and genlet/codegen keep
## working unchanged. `dceAnf` drops bindings nothing references — one
## backward walk, since a binding only mentions earlier bindings.
##
## Regions: when `isBoundary` is supplied, each boundary node's children
## normalize into nested regions attached to the binding (`nested` on
## `AnfBinding`), so a binding named inside a loop/fun body never appears
## in the enclosing list. `cseAnf`/`dceAnf`/`optAnf` run per region; a
## duplicate is never merged across a boundary when it mentions a binder.
## With no boundary callback the behaviour is exactly the old flat list.
##
## Soundness notes for clients:
## - `key` must distinguish nodes structurally, including child reference
##   names; two bindings with equal keys are the same computation.
## - Effect discipline: with `isPure` supplied, an effectful binding is
##   a root — never merged by `cseAnf`, never dropped by `dceAnf` — and a
##   binding whose right-hand side transitively contains an effect is
##   likewise a root; `optAnf` never applies a rule to a binding whose
##   nested region contains an effect. When `isTotal` is supplied, a
##   pure-but-non-total binding is also a DCE root and a nested non-total
##   binding blocks the corresponding `optAnf` rewrite. Nil `isTotal` is the
##   lenient pure-only default and is a client obligation, like `key` and
##   `isPure`. Without `isPure` the old client
##   obligation stands: an effectful nullary node (a `read()` with no
##   children) must get a distinct key per occurrence, or the client must
##   keep it out of CSE; otherwise two reads would collapse into one.
##   `isAtomic` lets the client force such a node to be bound (never
##   inlined as an atom) even though it has no children.
## - For LICM, `freeVars` must exclude any name whose value the region may
##   change (Var reads, mutable cells). Listing Var reads in `freeVars` gives
##   unsound motion; this is a client obligation like `key` / `isPure`.
## - A rewrite rule must return an atom (literal, input, or reference)
##   or its input unchanged; returning a composite node is a client bug
##   and is asserted against.

import std/[tables]

type
  AnfCallbacks*[T] = object
    children*: proc(node: T): seq[T]
    rebuild*: proc(node: T; children: seq[T]): T
    key*: proc(node: T): string
    isAtomic*: proc(node: T): bool
    refName*: proc(node: T): string
    makeRef*: proc(name: string): T
    isBoundary*: proc(node: T): bool
    binders*: proc(node: T): seq[string]
    freeVars*: proc(node: T): seq[string]
    isPure*: proc(node: T): bool
    isTotal*: proc(node: T): bool

  AnfProg*[T] = object
    stmts*: seq[AnfBinding[T]]
    result*: T

  AnfBinding*[T] = object
    name*: string
    rhs*: T
    ## One nested region per child of a boundary RHS.  The corresponding
    ## child in rhs is the result of that region.  Keeping this metadata on
    ## the binding avoids introducing a second client IR while making region
    ## boundaries explicit to all ANF passes.
    nested*: seq[AnfProg[T]]

proc hasEffect[T](node: T; cb: AnfCallbacks[T]): bool =
  if not cb.isPure.isNil and not cb.isPure(node): return true
  for child in cb.children(node):
    if hasEffect(child, cb): return true
  false

proc effectNames[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): Table[string, bool] =
  var effects = initTable[string, bool]()
  proc rhsEffectful(node: T): bool =
    if not cb.isPure.isNil and not cb.isPure(node): return true
    if cb.isAtomic(node):
      let name = cb.refName(node)
      return name.len > 0 and name in effects
    for child in cb.children(node):
      if rhsEffectful(child): return true
    false
  for stmt in prog.stmts:
    var effectful = rhsEffectful(stmt.rhs)
    for region in stmt.nested:
      if effectNames(region, cb).len > 0: effectful = true
    if effectful: effects[stmt.name] = true
  effects

proc nonTotalNames[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): Table[string, bool] =
  var nonTotals = initTable[string, bool]()
  proc rhsNonTotal(node: T): bool =
    if not cb.isTotal.isNil and not cb.isTotal(node): return true
    if cb.isAtomic(node):
      let name = cb.refName(node)
      return name.len > 0 and name in nonTotals
    for child in cb.children(node):
      if rhsNonTotal(child): return true
    false
  for stmt in prog.stmts:
    var nonTotal = rhsNonTotal(stmt.rhs)
    for region in stmt.nested:
      if nonTotalNames(region, cb).len > 0: nonTotal = true
    if nonTotal: nonTotals[stmt.name] = true
  nonTotals

proc substRefs*[T](node: T; subst: Table[string, T];
                   cb: AnfCallbacks[T]): T =
  ## Replace reference nodes by the substitution table, following alias
  ## chains (a name may map to a reference to another name).
  let name = cb.refName(node)
  if name.len > 0 and name in subst:
    var target = subst[name]
    while cb.refName(target).len > 0 and cb.refName(target) in subst:
      target = subst[cb.refName(target)]
    return target
  if cb.isAtomic(node):
    return node
  var kids: seq[T] = @[]
  for child in cb.children(node):
    kids.add(substRefs(child, subst, cb))
  cb.rebuild(node, kids)

proc toAnf*[T](root: T; cb: AnfCallbacks[T];
               prefix = "t"): AnfProg[T] =
  ## Name every composite subexpression. Each binding's right-hand side
  ## has only atomic children; the result is an atom or a reference.
  var counter = 0
  proc norm(node: T; prog: var AnfProg[T]): T =
    if cb.isAtomic(node):
      return node
    var kids: seq[T] = @[]
    var nested: seq[AnfProg[T]] = @[]
    let region = not cb.isBoundary.isNil and cb.isBoundary(node)
    for child in cb.children(node):
      if region:
        var childProg = AnfProg[T](stmts: @[])
        let childResult = norm(child, childProg)
        childProg.result = childResult
        kids.add(childResult)
        nested.add(childProg)
      else:
        kids.add(norm(child, prog))
    let rebuilt = cb.rebuild(node, kids)
    let name = prefix & $counter
    inc counter
    prog.stmts.add(AnfBinding[T](name: name, rhs: rebuilt, nested: nested))
    cb.makeRef(name)
  var prog = AnfProg[T](stmts: @[])
  prog.result = norm(root, prog)
  prog

proc fromAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): T =
  ## Substitute bindings back, last to first, so references to later
  ## bindings are expanded before the bindings they mention are.
  var result = prog.result
  var subst = initTable[string, T]()
  for i in countdown(prog.stmts.high, 0):
    var stmt = prog.stmts[i]
    if stmt.nested.len > 0:
      var kids: seq[T] = @[]
      let originalKids = cb.children(stmt.rhs)
      for j, child in originalKids:
        if j < stmt.nested.len:
          kids.add(fromAnf(stmt.nested[j], cb))
        else:
          kids.add(child)
      stmt.rhs = cb.rebuild(stmt.rhs, kids)
    subst[stmt.name] = stmt.rhs
    result = substRefs(result, subst, cb)
  result

proc cseAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): AnfProg[T] =
  ## Drop bindings whose right-hand side duplicates an earlier binding's
  ## key, rewriting later references to the first name. Pure bindings
  ## only; see the header note on effectful nodes.
  var seen = initTable[string, string]()
  var aliases = initTable[string, T]()
  var outProg = AnfProg[T](stmts: @[])
  let effects = effectNames(prog, cb)
  for stmt in prog.stmts:
    var nested: seq[AnfProg[T]] = @[]
    for region in stmt.nested:
      nested.add(cseAnf(region, cb))
    let rhs = substRefs(stmt.rhs, aliases, cb)
    let k = cb.key(rhs)
    let effectful = stmt.name in effects
    if k in seen or effectful:
      if effectful:
        outProg.stmts.add(AnfBinding[T](name: stmt.name, rhs: rhs,
                                        nested: nested))
      else:
        aliases[stmt.name] = cb.makeRef(seen[k])
    else:
      seen[k] = stmt.name
      outProg.stmts.add(AnfBinding[T](name: stmt.name, rhs: rhs,
                                      nested: nested))
  outProg.result = substRefs(prog.result, aliases, cb)
  outProg

proc dceAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): AnfProg[T] =
  ## Drop bindings no later binding and no result references. One
  ## backward walk suffices: a binding's right-hand side only mentions
  ## earlier bindings, so a name is live iff it is used by the result or
  ## by a kept later binding.
  var used = initTable[string, bool]()
  let effects = effectNames(prog, cb)
  let nonTotals = nonTotalNames(prog, cb)
  proc markUsed(node: T) =
    if cb.isAtomic(node):
      let name = cb.refName(node)
      if name.len > 0: used[name] = true
    else:
      for child in cb.children(node): markUsed(child)
  markUsed(prog.result)
  var kept: seq[AnfBinding[T]] = @[]
  for i in countdown(prog.stmts.high, 0):
    let stmt = prog.stmts[i]
    if stmt.name in used or stmt.name in effects or stmt.name in nonTotals:
      markUsed(stmt.rhs)
      var keptStmt = stmt
      for j in 0 ..< keptStmt.nested.len:
        keptStmt.nested[j] = dceAnf(keptStmt.nested[j], cb)
      kept.insert(keptStmt, 0)
  AnfProg[T](stmts: kept, result: prog.result)

proc optAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T];
                rule: proc(node: T): T): AnfProg[T] =
  ## Apply `rule` to each binding's right-hand side (children already
  ## atomic) and to the final result. A rule that replaces a binding's
  ## right-hand side with an atom drops the binding; later references
  ## are rewritten to the replacement. A rule returning its input means
  ## no rewrite.
  var aliases = initTable[string, T]()
  var outProg = AnfProg[T](stmts: @[])
  for stmt in prog.stmts:
    var nested: seq[AnfProg[T]] = @[]
    for region in stmt.nested:
      nested.add(optAnf(region, cb, rule))
    # A rewrite that replaces a boundary binding's right-hand side with
    # an atom discards its nested regions, so it must never fire when a
    # region contains an effect: the region's bindings exist nowhere
    # else, and dropping them would delete the effect. Pure regions
    # still rewrite (that is the point of the rule).
    var regionEffect = false
    var regionNonTotal = false
    for region in nested:
      if effectNames(region, cb).len > 0: regionEffect = true
      if not cb.isTotal.isNil and nonTotalNames(region, cb).len > 0:
        regionNonTotal = true
    let rhs = substRefs(stmt.rhs, aliases, cb)
    let rewritten = if regionEffect or regionNonTotal: rhs else: rule(rhs)
    if rewritten == rhs:
      ## `==` is identity for ref nodes and structural equality for
      ## value nodes; either way a rule returning an equal node means
      ## no rewrite, which is always a safe reading.
      outProg.stmts.add(AnfBinding[T](name: stmt.name, rhs: rhs,
                                      nested: nested))
    else:
      doAssert cb.isAtomic(rewritten),
        "ANF rewrite must return an atom or its input unchanged"
      aliases[stmt.name] = rewritten
  var res = substRefs(prog.result, aliases, cb)
  let rewrittenRes = rule(res)
  if rewrittenRes == res:
    outProg.result = res
  else:
    doAssert cb.isAtomic(rewrittenRes),
      "ANF rewrite must return an atom or its input unchanged"
    outProg.result = rewrittenRes
  outProg

proc licmAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): AnfProg[T] =
  ## Hoist pure, total loop/fun-body bindings into the enclosing region.
  ## This pass is deliberately standalone; optAnf's pipeline runs it after
  ## cseAnf and before dceAnf so newly dead bindings can be swept afterward.
  ## Missing safety callbacks conservatively disable motion.
  if cb.isBoundary.isNil or cb.binders.isNil or cb.freeVars.isNil or
     cb.isPure.isNil or cb.isTotal.isNil:
    return prog

  proc hoistRegion(region: AnfProg[T]; boundary: T): seq[AnfBinding[T]] =
    var bound = initTable[string, bool]()
    for stmt in region.stmts: bound[stmt.name] = true
    var hoisted = initTable[string, bool]()
    let boundaryNames = cb.binders(boundary)
    let resultName = cb.refName(region.result)
    var moved: seq[AnfBinding[T]] = @[]
    for stmt in region.stmts:
      var canMove = stmt.nested.len == 0 and cb.isPure(stmt.rhs) and
                    cb.isTotal(stmt.rhs)
      if canMove:
        let vars = cb.freeVars(stmt.rhs)
        # A result with region-local inputs cannot be spliced out without
        # also changing the boundary/result interface. A dependency-free
        # result (including a nullary effect under a deliberately permissive
        # isPure callback) is safe to reference from the parent region.
        if stmt.name == resultName and vars.len > 0:
          canMove = false
        for name in vars:
          if name in boundaryNames:
            canMove = false
          elif name in bound and name notin hoisted:
            canMove = false
      if canMove:
        moved.add(stmt)
        hoisted[stmt.name] = true
    moved

  var outProg = prog
  var i = 0
  while i < outProg.stmts.len:
    var stmt = outProg.stmts[i]
    var movedBefore: seq[AnfBinding[T]] = @[]
    var inserted = 0
    for j in 0 ..< stmt.nested.len:
      stmt.nested[j] = licmAnf(stmt.nested[j], cb)
      let moved = hoistRegion(stmt.nested[j], stmt.rhs)
      if moved.len > 0:
        inserted += moved.len
        var retained: seq[AnfBinding[T]] = @[]
        for candidate in stmt.nested[j].stmts:
          var keep = true
          for movedStmt in moved:
            if candidate.name == movedStmt.name: keep = false
          if keep: retained.add(candidate)
        stmt.nested[j].stmts = retained
        movedBefore.add(moved)
    outProg.stmts[i] = stmt
    if movedBefore.len > 0:
      for k in countdown(movedBefore.high, 0):
        outProg.stmts.insert(movedBefore[k], i)
      i += inserted
    inc i
  outProg
