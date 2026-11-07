## Standalone tests for the CSP registry (staging/csp).
##
## Eponym's tests/test_csp_policy.nim exercised the same invariants, but
## only on the relational elaborator's generated residual (it imports
## staging/gen_direct_elabo_full). This file tests the registry itself,
## with a small synthetic client, so the module stands alone.

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

  # Reset clears the registry entirely.
  cspReset()
  doAssert cspRegistry.len == 0
  doAssert cspImports().len == 0
  doAssert cspUnused().len == 0
  echo "ok: cspReset() clears the registry"

  echo "=== CSP registry ok ==="
