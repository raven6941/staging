# staging

Lightweight modular staging for Nim, in the style of BER MetaOCaml and LMS
(Rompf & Odersky). A small library for writing staged programs: binding-time
annotations, `Rep[T]` for staged values, residual let-insertion (`genlet`),
and an explicit cross-stage persistence policy (`csp`).

Extracted from Eponym's `src/experimental/staging/` (the generic core under
Eponym's staged relational elaborator), as an independent library. The
relational staging client stays in Eponym — see [Scope](#scope).

## What staging is

A staged program runs in two phases: *staging time* (now, at compile time
or generation time) and *runtime* (later, when the residual program runs).
Some values are known at staging time (static); others are only known at
runtime (dynamic). The stager evaluates everything it can now and emits a
*residual program* — ordinary code — for the rest.

```nim
import staging/framework

# Rep[int]: either a static int, or a residual IR node for later.
let folded = lift(1) + lift(2)   # computed now, if your DSL folds it
```

The framework itself does not generate code. It provides the binding-time
discipline; your DSL provides the residual nodes and the smart constructors.
That is the whole design: a small system, no graph IR, no runtime codegen,
no optimization passes — except one, `genlet`.

## Modules

| Module | What it is |
|---|---|
| `staging/framework` | `Rep[T]`, `IRNode`, `lift`, `dynamic`, `smartOp` / `smartOpUni`, tagless-final hook. No imports at all. |
| `staging/csp` | Cross-stage persistence registry: declare every present-stage name the residual may reference, emit it only via `lift`, derive the residual's import block from the registry. No imports at all. |
| `staging/genlet` | Residual let-insertion over a generic tree (`GTree`): common-subterm elimination with residual `let` binders, gated by a node-savings test. Stdlib only (`tables`, `sequtils`, `strutils`). |

## Worked example: staging an arithmetic evaluator

The test suite (`tests/test_framework.nim`) builds a tagless-final
arithmetic DSL and runs the same program three ways — direct, fully static,
and residualized:

```nim
type
  ArithSym[R] = object
    lit*: proc(n: int): R
    vr*: proc(name: string): R
    add*: proc(a, b: R): R
    mul*: proc(a, b: R): R

proc prog1[R](s: ArithSym[R]): R =
  s.mul(s.add(s.lit(1), s.lit(2)), s.lit(3))  # (1 + 2) * 3

proc prog2[R](s: ArithSym[R]): R =
  s.mul(s.add(s.vr("x"), s.lit(1)), s.lit(2))  # (x + 1) * 2
```

Instantiate the DSL with `R = int` to run it, or with `R = Rep[int]` to
stage it. `smartOp` folds when both operands are static and builds a
residual node otherwise. Actual output from `nimble test`:

```
=== staging framework: generic arithmetic DSL ===
ok: direct prog1 = 9
staged prog1: static(9)
ok: fully static folded to 9 at staging time
staged prog2: dynamic((dynamic((dynamic(x) + static(1))) * static(2)))
ok: dynamic variable residualized to IR
ok: getStatic on dynamic Rep raises (staging-time error)
```

`prog1` folds entirely at staging time (static 9). `prog2` keeps `x`
dynamic and residualizes the rest: the `+1` and `*2` survive as residual
nodes, the literal `2` stays static inside them.

### genlet: sharing the residual

A stager that duplicates a shared computation pays for it twice at runtime.
`genlet` hoists a repeated composite subterm under one residual `let`
(`tests/test_genlet.nim`, actual output):

```
before: add(mul(add(x, 1), add(y, 2)), add(mul(add(x, 1), add(y, 2)), mul(add(x, 1), add(y, 2))))
after:  (let genlet0 = mul(add(x, 1), add(y, 2)) in add(genlet0, add(genlet0, genlet0)))
```

The shared 7-node term, used 3 times (23 nodes total), becomes one binding
plus three placeholders (13 nodes). The pass is gated by a savings test —
a term shared only twice never qualifies — and it never hoists across a
`let` binder. Evaluation before and after agrees (45 with x=2, y=3).

### csp: what the residual may name

Every name the residual references but does not define must be declared
with a persistence class (`ccLiteral`, `ccHelperProc`, `ccEngine`,
`ccType`, `ccStdlib`); the generator emits it only via `lift`, and the
residual's import block is derived from the used declarations
(`tests/test_csp.nim`). Undeclared names raise at generation time instead
of leaking silently into the residual.

## Install

Requires Nim >= 2.0.0. No dependencies beyond the standard library.

```
nimble install staging
```

or clone and use `--path:src`.

## Tests

```
nimble test
```

Runs `tests/test_framework.nim`, `tests/test_csp.nim`, and
`tests/test_genlet.nim`. Verified on Nim 2.2.12 and 2.4.0.

## Scope — what this library does NOT yet include

Honest boundaries, not roadmap promises:

- **The relational staging client stays in Eponym.** `RelGoal`/`StageGoal`
  goal representations, mode analysis, the `relcompile` residual compiler,
  and the relational `genlet` over `RelGoal`/`RTerm` all depend on
  miniKanren and on Eponym's elaborator core. They are the motivating
  application of this framework, not part of it. If you want staged
  relational programming, that lives in Eponym's
  `src/experimental/staging/` for now.
- **The generic `genlet` works on `GTree`, not on your IR.** Your DSL's
  residual nodes are opaque `IRNode`s to the framework. To use `genlet`
  you build your residual as a `GTree` (or map your IR onto one). A
  callback-based version that traverses client IR directly is a possible
  v0.2, not in v0.1.0.
- **No runtime codegen, no graph IR, no optimization passes.** The
  residual is a tree your DSL interprets, prints, or compiles. `genlet`
  is the only optimization, and it is a size optimization for pure
  computations — clients with effectful nodes must only feed it pure
  subtrees.
- **No macro/bracket syntax.** Staging is expressed through `Rep[T]` and
  smart constructors in ordinary Nim code, not through MetaOCaml-style
  brackets and escape. A macro layer is out of scope for v0.1.0.

## License

MIT — see LICENSE.
