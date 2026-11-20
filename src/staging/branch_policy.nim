## Branch-resolution vocabulary for staged relational search.
##
## A stager reports whether each branch was solved, impossible, or left for
## runtime.  This module deliberately owns only the policy decision: clients
## own their goal tree, terms, unifier, and residual representation.
##
## The Eponym mapping is intentionally recorded here for the follow-up:
## `appRedex` is `bpGather` with a fallback escape, `consIndex` is `bpLater`,
## and `inferD` keeps its ground-answer restriction.  This module does not
## modify Eponym.
##
## Staticness and groundness are different lattices.  Static means known at
## staging time and therefore ground at staging time; ground does not imply
## static (a ground runtime value can be `Rep[T, false]` containing a ground
## term).  This mode vocabulary never uses "static" to mean groundness.

import std/tables

type
  StageOutcome* = enum
    soDone      ## solved at staging time
    soFail      ## statically impossible; prune this branch
    soResidual  ## residual goal remains for runtime

  BranchPolicy* = enum
    bpGather    ## one specialized residual per staging-time branch
    bpFallback  ## one dynamic call; search runs at runtime
    bpLater     ## one opaque call; never inline or specialize

  PolicyEntry* = object
    ## A per-call-site policy.  `bound` is used by bpGather and is the
    ## maximum number of surviving residual branches before fallback.
    policy*: BranchPolicy
    bound*: int

  ResidualPlanKind* = enum
    rpkGather
    rpkFallback
    rpkLater
    rpkPrune
    rpkRefuse

  ResidualPlan* = object
    ## The result of resolving one staging-time call site.  `branches` is
    ## populated only for rpkGather and contains no soFail branches.
    case kind*: ResidualPlanKind
    of rpkGather:
      branches*: seq[StageOutcome]
    of rpkFallback, rpkLater, rpkPrune, rpkRefuse:
      discard

  PolicyTable* = Table[string, PolicyEntry]

proc gatherPolicy*(bound: int): PolicyEntry =
  PolicyEntry(policy: bpGather, bound: bound)

proc fallbackPolicy*(): PolicyEntry =
  PolicyEntry(policy: bpFallback, bound: 0)

proc laterPolicy*(): PolicyEntry =
  PolicyEntry(policy: bpLater, bound: 0)

proc setPolicy*(table: var PolicyTable; site: string; entry: PolicyEntry) =
  table[site] = entry

proc getPolicy*(table: PolicyTable; site: string): PolicyEntry =
  ## Missing site policies are an explicit client error rather than an
  ## accidental fallback.  A client can use hasKey when absence is useful.
  if not table.hasKey(site):
    raise newException(KeyError, "no branch policy for site '" & site & "'")
  table[site]

proc initPolicyTable*(): PolicyTable =
  initTable[string, PolicyEntry]()

proc resolveBranch*(outcomes: openArray[StageOutcome]; entry: PolicyEntry;
                    nonGroundAnswer = false): ResidualPlan =
  ## Turn staging outcomes and a site policy into a residual plan.
  ##
  ## bpLater and bpFallback are unconditional policy choices.  For gather,
  ## failed branches disappear, a non-ground answer is refused, and a bound
  ## overflow escapes to one dynamic call.  A Done branch remains in the
  ## residual branch list: it represents a disjunct with learned bindings,
  ## rather than permission to discard other runtime answers.
  case entry.policy
  of bpLater:
    ResidualPlan(kind: rpkLater)
  of bpFallback:
    ResidualPlan(kind: rpkFallback)
  of bpGather:
    var surviving: seq[StageOutcome] = @[]
    for outcome in outcomes:
      if outcome != soFail:
        surviving.add(outcome)
    if surviving.len == 0:
      return ResidualPlan(kind: rpkPrune)
    if nonGroundAnswer:
      return ResidualPlan(kind: rpkRefuse)
    if surviving.len > entry.bound:
      return ResidualPlan(kind: rpkFallback)
    ResidualPlan(kind: rpkGather, branches: surviving)
