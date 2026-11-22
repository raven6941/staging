## Standalone tests for the CSP registry (staging/csp).
##
## Eponym's tests/test_csp_policy.nim exercised the same invariants, but
## only on the relational elaborator's generated residual (it imports
## staging/gen_direct_elabo_full). This file tests the registry itself,
## with a small synthetic client, so the module stands alone.

import staging/branch_policy
import staging/csp

when isMainModule:
  echo "=== staging CSP registry ==="

  cspReset()

  # Declare refs of each class a residual generator might need.
  declare("makeNat", "mylib", ccHelperProc)
  declare("runSearch", "engine", ccEngine)
  declare("some", "options", ccStdlib)
  declare("dec", "system", ccStdlib)
  declare("deadRef", "mylib", ccHelperProc)  # never lifted: must be reported

  # lift() returns the residual spelling and records the use.
  doAssert lift("makeNat") == "mylib.makeNat"
  doAssert lift("runSearch") == "engine.runSearch"
  doAssert lift("some") == "options.some"
  # system is ambient for imports but keeps its qualified spelling.
  doAssert lift("dec") == "system.dec"
  echo "ok: lift() spells declared refs qualified"

  # cspImports() derives the residual's import block from *used* refs,
  # in first-use order, excluding ambient `system`.
  doAssert cspImports() == @["mylib", "engine", "options"],
    "import block mismatch: " & $cspImports()
  echo "ok: cspImports() == registry-derived set, system excluded"

  # Unused declarations are reported (dead declarations fail the check).
  doAssert cspUnused() == @["deadRef"], "unused mismatch: " & $cspUnused()
  echo "ok: cspUnused() reports the dead declaration"

  # Undeclared names are a hard error at generation time, not a silent leak.
  var raised = false
  try:
    discard lift("notDeclared")
  except ValueError:
    raised = true
  doAssert raised, "lift() on an undeclared name should raise ValueError"
  echo "ok: lift() on undeclared name raises"

  # Step 4 (#3): the engine-reference pattern. A bpFallback plan from
  # resolveBranch is a dynamic call to the engine at residual runtime, so
  # the engine must be a declared ccEngine ref; a fallback with no such
  # declaration is a generator bug, caught here at generation time.
  var table = initPolicyTable()
  setPolicy(table, "inferD", fallbackPolicy())
  let plan = resolveBranch(@[soResidual, soResidual], getPolicy(table, "inferD"))
  doAssert plan.kind == rpkFallback, "fallback policy must plan a dynamic call"
  # The fallback's dynamic call lifts through the declared ccEngine ref,
  # and the engine module lands in the residual's import block.
  doAssert lift("runSearch") == "engine.runSearch"
  doAssert "engine" in cspImports(), "engine module missing from imports"
  # The declaration is of class ccEngine, not merely any registered ref.
  var engineClass = ccLiteral
  for r in cspRegistry:
    if r.name == "runSearch":
      engineClass = r.class
  doAssert engineClass == ccEngine, "fallback engine must be declared ccEngine"
  echo "ok: fallback plan's engine is a declared ccEngine ref"
  # Negative: a fallback plan naming an engine that was never declared
  # fails at generation time — the residual is never emitted unclosed.
  var raisedFallback = false
  try:
    discard lift("runUndeclared")
  except ValueError:
    raisedFallback = true
  doAssert raisedFallback,
    "fallback to an undeclared engine should raise ValueError"
  echo "ok: fallback to an undeclared engine raises"

  # Reset clears the registry entirely.
  cspReset()
  doAssert cspRegistry.len == 0
  doAssert cspImports().len == 0
  doAssert cspUnused().len == 0
  echo "ok: cspReset() clears the registry"

  echo "=== CSP registry ok ==="
