# Package

version       = "0.1.0"
author        = "raven6941"
description   = "Lightweight modular staging for Nim: Rep[T] binding times, residual let-insertion, cross-stage persistence"
license       = "MIT"
srcDir        = "src"

# Dependencies

requires "nim >= 2.0.0"

# Tasks

task test, "Run the self-tests":
  exec "nim c -r --hints:off --path:src tests/test_branch_policy.nim"
  exec "nim c -r --hints:off --path:src tests/test_framework.nim"
  exec "nim c -r --hints:off --path:src tests/test_rep_static.nim"
  exec "nim c -r --hints:off --path:src tests/test_smartif.nim"
  exec "nim c -r --hints:off --path:src tests/test_codegen.nim"
  exec "nim c -r --hints:off --path:src tests/test_csp.nim"
  exec "nim c -r --hints:off --path:src tests/test_genlet.nim"
  exec "nim c -r --hints:off --path:src tests/test_relgenlet.nim"
  exec "nim c -r --hints:off --path:src tests/test_partial_deduction.nim"
  exec "nim c -r --hints:off --path:src tests/test_traversal.nim"
  exec "nim c -r --hints:off --path:src tests/test_modes.nim"
  exec "nim c -r --hints:off --path:src tests/test_vars.nim"
  exec "nim c -r --hints:off --path:src tests/test_while.nim"
  exec "nim c -r --hints:off --path:src tests/test_regex.nim"
  exec "nim c -r --hints:off --path:src tests/test_stream.nim"
  exec "nim c -r --hints:off --path:src tests/test_vectorops.nim"
  exec "nim c -r --hints:off --path:src tests/test_vecarith.nim"
  exec "nim c -r --hints:off --path:src tests/test_shonan.nim"
  exec "nim c -r --hints:off --path:src tests/test_query.nim"
  exec "nim c -r --hints:off --path:src tests/test_arrays.nim"
  exec "nim c -r --hints:off --path:src tests/test_structs.nim"
  exec "nim c -r --hints:off --path:src tests/test_complex.nim"
  exec "nim c -r --hints:off --path:src tests/test_union.nim"
  exec "nim c -r --hints:off --path:src tests/test_soa.nim"
  exec "nim c -r --hints:off --path:src tests/test_hoas.nim"
  exec "nim c -r --hints:off --path:src tests/test_anf.nim"
  exec "nim c -r --hints:off --path:src tests/test_fun.nim"
  exec "nim c -r --hints:off --path:src tests/test_effects.nim"
