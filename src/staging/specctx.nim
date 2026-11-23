## Small control skeleton for client-side partial deduction.
##
## The client still owns terms, unification, and residual code.  SpecCtx only
## owns the repeated bookkeeping: signatures are memoized, new specializations
## consume fuel, recursive signatures are guarded, and dynamic variables are
## checked at the staging boundary.

import std/[sets, tables]

type
  SpecState* = enum
    ssNew
    ssCached
    ssRecursive
    ssOutOfFuel

  SpecCtx*[Env, Key, Value] = ref object
    env*: Env
    staticSignature*: proc(env: Env): Key
    memo*: Table[Key, Value]
    active*: HashSet[Key]
    dynamicVars*: HashSet[string]
    fuel*: int

proc newSpecCtx*[Env, Key, Value](env: Env;
    staticSignature: proc(env: Env): Key;
    fuel: int; dynamicVars: HashSet[string]): SpecCtx[Env, Key, Value] =
  result = SpecCtx[Env, Key, Value](
    env: env, staticSignature: staticSignature,
    memo: initTable[Key, Value](), active: initHashSet[Key](),
    dynamicVars: dynamicVars, fuel: fuel)

proc begin*[Env, Key, Value](ctx: SpecCtx[Env, Key, Value]; env: Env;
    dynamicVars: HashSet[string]): (SpecState, Key) =
  ## A client must declare every variable it leaves dynamic.  The declaration
  ## may be narrower for a particular call, but never wider than the context's
  ## contract.
  for name in dynamicVars:
    if name notin ctx.dynamicVars:
      raise newException(ValueError,
        "dynamic variable is outside SpecCtx contract: " & name)
  let key = ctx.staticSignature(env)
  if key in ctx.memo:
    return (ssCached, key)
  if key in ctx.active:
    return (ssRecursive, key)
  if ctx.fuel <= 0:
    return (ssOutOfFuel, key)
  dec ctx.fuel
  ctx.active.incl(key)
  (ssNew, key)

proc finish*[Env, Key, Value](ctx: SpecCtx[Env, Key, Value]; key: Key;
    value: Value) =
  ctx.memo[key] = value
  ctx.active.excl(key)

proc abort*[Env, Key, Value](ctx: SpecCtx[Env, Key, Value]; key: Key) =
  ## Release a signature when client-side specialization fails.
  ctx.active.excl(key)
