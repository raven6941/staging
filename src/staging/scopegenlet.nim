## Construction-time, scope-placed let insertion for GTree.
##
## `genletAt` is deliberately separate from `insertLets`: it records a
## binding while a residual tree is being built, so effectful expressions are
## evaluated once as well as pure expressions.  `accumulate` is the convenient
## perform/reify delimiter; its callback is evaluated eagerly.

import std/[tables, sets]
import staging/genlet

type
  ScopeState = ref object
    ctx: GenletCtx
    refs: Table[string, Scope]

  Scope* = ref object
    parent: Scope
    state: ScopeState
    bindings: seq[tuple[name: string, value: GTree]]
    byKey: Table[string, string]
    closed: bool

var currentScope: Scope

proc newScope*(): Scope =
  ## Make an explicit root insertion scope.  Scopes made by `accumulate` are
  ## children of the currently active scope.
  let state = ScopeState(ctx: newGenletCtx(),
                         refs: initTable[string, Scope]())
  result = Scope(parent: nil, state: state, byKey: initTable[string, string]())

proc childScope(parent: Scope): Scope =
  result = Scope(parent: parent, state: parent.state,
                 byKey: initTable[string, string]())

proc visible(target, owner: Scope): bool =
  ## An owner is visible at target iff target is that scope or a descendant.
  var p = target
  while not p.isNil:
    if p == owner: return true
    p = p.parent
  false

proc checkRefs(t: GTree; target: Scope; local: HashSet[string] = initHashSet[string]()) =
  ## Generated reference names are tracked separately from ordinary atoms.
  ## This catches an inner reference retained by an outer residual before the
  ## inner delimiter returns.
  case t.kind
  of gkAtom:
    if t.name in local or not target.state.refs.hasKey(t.name): return
    let owner = target.state.refs[t.name]
    if not visible(target, owner):
      raise newException(ValueError,
        "scopegenlet: reference " & t.name & " escapes its insertion scope")
  of gkNode:
    for c in t.children: checkRefs(c, target, local)
  of gkLet:
    checkRefs(t.bound, target, local)
    var bodyLocal = local
    bodyLocal.incl(t.binder)
    checkRefs(t.body, target, bodyLocal)

proc genletAt*(scope: Scope; value: GTree): GTree =
  ## Bind `value` once at `scope` and return its residual reference.
  ## Structurally equal values share a binding within that scope.
  if scope.isNil: raise newException(ValueError, "scopegenlet: nil scope")
  if scope.closed:
    raise newException(ValueError, "scopegenlet: insertion into a closed scope")
  checkRefs(value, scope)
  let key = $value
  if scope.byKey.hasKey(key): return gatom(scope.byKey[key])
  let name = "genlet" & $scope.state.ctx.counter
  inc scope.state.ctx.counter
  scope.byKey[key] = name
  scope.bindings.add((name: name, value: value))
  scope.state.refs[name] = scope
  gatom(name)

proc finish(scope: Scope; body: GTree): GTree =
  if scope.closed:
    raise newException(ValueError,
      "scopegenlet: insertion scope already closed")
  checkRefs(body, scope)
  result = body
  for i in countdown(scope.bindings.high, 0):
    result = glet(scope.bindings[i].name, scope.bindings[i].value, result)
  scope.closed = true

proc closeScope*(scope: Scope; body: GTree): GTree =
  ## Close a scope created by `newScope`, splicing its bindings as lets
  ## around `body`. Scopes created by `accumulate` close themselves; use
  ## this only for explicitly created scopes.
  finish(scope, body)

proc accumulate*(body: proc(): GTree): GTree =
  ## Delimit a scope and splice performed bindings around the callback result.
  let parent = currentScope
  let scope = if parent.isNil: newScope() else: childScope(parent)
  currentScope = scope
  try:
    result = finish(scope, body())
  finally:
    currentScope = parent

proc accumulate*(body: proc(scope: Scope): GTree): GTree =
  ## Variant exposing the newly delimited scope for explicit `genletAt` calls.
  let parent = currentScope
  let scope = if parent.isNil: newScope() else: childScope(parent)
  currentScope = scope
  try:
    result = finish(scope, body(scope))
  finally:
    currentScope = parent

proc perform*(value: GTree): GTree =
  ## Eagerly register a residual statement in the active accumulate scope.
  if currentScope.isNil:
    raise newException(ValueError, "scopegenlet: perform outside accumulate")
  genletAt(currentScope, value)

