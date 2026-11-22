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
## Soundness notes for clients:
## - `key` must distinguish nodes structurally, including child reference
##   names; two bindings with equal keys are the same computation.
## - CSE is sound only for pure bindings. An effectful nullary node (a
##   `read()` with no children) must get a distinct key per occurrence,
##   or the client must keep it out of CSE; otherwise two reads would
##   collapse into one. `isAtomic` lets the client force such a node to
##   be bound (never inlined as an atom) even though it has no children.
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

  AnfBinding*[T] = object
    name*: string
    rhs*: T

  AnfProg*[T] = object
    stmts*: seq[AnfBinding[T]]
    result*: T

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
  var prog = AnfProg[T](stmts: @[])
  proc norm(node: T): T =
    if cb.isAtomic(node):
      return node
    var kids: seq[T] = @[]
    for child in cb.children(node):
      kids.add(norm(child))
    let rebuilt = cb.rebuild(node, kids)
    let name = prefix & $counter
    inc counter
    prog.stmts.add(AnfBinding[T](name: name, rhs: rebuilt))
    cb.makeRef(name)
  prog.result = norm(root)
  prog

proc fromAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): T =
  ## Substitute bindings back, last to first, so references to later
  ## bindings are expanded before the bindings they mention are.
  var result = prog.result
  var subst = initTable[string, T]()
  for i in countdown(prog.stmts.high, 0):
    let stmt = prog.stmts[i]
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
  for stmt in prog.stmts:
    let rhs = substRefs(stmt.rhs, aliases, cb)
    let k = cb.key(rhs)
    if k in seen:
      aliases[stmt.name] = cb.makeRef(seen[k])
    else:
      seen[k] = stmt.name
      outProg.stmts.add(AnfBinding[T](name: stmt.name, rhs: rhs))
  outProg.result = substRefs(prog.result, aliases, cb)
  outProg

proc dceAnf*[T](prog: AnfProg[T]; cb: AnfCallbacks[T]): AnfProg[T] =
  ## Drop bindings no later binding and no result references. One
  ## backward walk suffices: a binding's right-hand side only mentions
  ## earlier bindings, so a name is live iff it is used by the result or
  ## by a kept later binding.
  var used = initTable[string, bool]()
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
    if stmt.name in used:
      markUsed(stmt.rhs)
      kept.insert(stmt, 0)
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
    let rhs = substRefs(stmt.rhs, aliases, cb)
    let rewritten = rule(rhs)
    if rewritten == rhs:
      ## `==` is identity for ref nodes and structural equality for
      ## value nodes; either way a rule returning an equal node means
      ## no rewrite, which is always a safe reading.
      outProg.stmts.add(AnfBinding[T](name: stmt.name, rhs: rhs))
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
