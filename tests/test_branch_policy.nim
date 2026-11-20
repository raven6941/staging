## Load-bearing tests for staging/branch_policy.
##
## In particular, a naive implementation that gathers unconditionally fails
## the bound-escape and non-ground-refusal checks below.

import staging/branch_policy

proc checkGather() =
  let plan = resolveBranch([soDone, soResidual], gatherPolicy(2))
  doAssert plan.kind == rpkGather
  doAssert plan.branches == @[soDone, soResidual]

proc checkFallback() =
  let plan = resolveBranch([soResidual, soDone], fallbackPolicy())
  doAssert plan.kind == rpkFallback

proc checkBoundEscape() =
  # Load-bearing: unconditional gathering fails this test.
  let plan = resolveBranch([soResidual, soResidual], gatherPolicy(1))
  doAssert plan.kind == rpkFallback

proc checkNonGroundRefusal() =
  # Load-bearing: ignoring nonGroundAnswer fails this test.
  let plan = resolveBranch([soResidual], gatherPolicy(1), nonGroundAnswer = true)
  doAssert plan.kind == rpkRefuse

proc checkPrune() =
  let plan = resolveBranch([soFail, soFail], gatherPolicy(4))
  doAssert plan.kind == rpkPrune

proc checkLater() =
  let plan = resolveBranch([soFail, soDone, soResidual], laterPolicy())
  doAssert plan.kind == rpkLater

proc checkBoundary() =
  let plan = resolveBranch([soDone, soResidual], gatherPolicy(2))
  doAssert plan.kind == rpkGather
  doAssert plan.branches.len == 2

proc checkTable() =
  var table = initPolicyTable()
  table.setPolicy("specialize", gatherPolicy(2))
  table.setPolicy("opaque", laterPolicy())
  let gather = resolveBranch([soResidual], table.getPolicy("specialize"))
  let later = resolveBranch([soResidual], table.getPolicy("opaque"))
  doAssert gather.kind == rpkGather
  doAssert later.kind == rpkLater

when isMainModule:
  checkGather()
  checkFallback()
  checkBoundEscape()
  checkNonGroundRefusal()
  checkPrune()
  checkLater()
  checkBoundary()
  checkTable()
  echo "=== branch policy ok ==="
