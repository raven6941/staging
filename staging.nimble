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
  exec "nim c -r --hints:off --path:src tests/test_framework.nim"
  exec "nim c -r --hints:off --path:src tests/test_csp.nim"
  exec "nim c -r --hints:off --path:src tests/test_genlet.nim"
