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
| `staging/framework` | `Rep[T]`, `IRNode`, `lift`, `dynamic`, `smartOp` / `smartOpUni`, `smartLet`, `smartIf`, residual `Var[T]` cells with `readVar` / `writeVar`, `Rep[Unit]` statements with `seqR`, and the tagless-final hook. No imports at all. |
| `staging/csp` | Cross-stage persistence registry: declare every present-stage name the residual may reference, emit it only via `lift`, derive the residual's import block from the registry. No imports at all. |
| `staging/genlet` | Residual let-insertion over `GTree`, or directly over a client IR through callbacks: common-subterm elimination with residual `let` binders, hoisting every repeated pure composite with at least 3 nodes. Stdlib only (`tables`, `sequtils`, `strutils`). |
| `staging/branch_policy` | Decision vocabulary for staged relational branching: tri-state outcomes, per-site gather/fallback/later policies with gather bounds, and residual plans including prune/refuse. Stdlib only (`tables`). |

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
    letB*: proc(bound: R, body: proc(value: R): R): R

proc prog1[R](s: ArithSym[R]): R =
  s.mul(s.add(s.lit(1), s.lit(2)), s.lit(3))  # (1 + 2) * 3

proc prog2[R](s: ArithSym[R]): R =
  s.mul(s.add(s.vr("x"), s.lit(1)), s.lit(2))  # (x + 1) * 2

proc progLet[R](s: ArithSym[R]): R =
  s.letB(s.add(s.vr("x"), s.lit(1)),
    proc(t: R): R = s.add(t, t))  # let t = x + 1 in t + t
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

### Binding forms in the tagless-final hook

Expression operations are not enough for a generic evaluator: inlining a
dynamic `let` binding duplicates its computation at every use. A Sym-style
DSL that supports bindings should expose a callback-based `letB` operation:
the direct evaluator calls the body with the bound value, while the staged
evaluator uses `smartLet` to create one residual reference and one residual
let node. Thus the same evaluator handles direct, static, and staged `let`
programs without a separate staged evaluator. `tests/test_framework.nim`
checks this with `let t = x + 1 in t + t` and verifies that the bound
expression occurs once in the residual.

`smartLet` is about preserving the semantics of a source-language binding
form during staging. It is separate from `genlet`, whose `GTree` and
`insertLetsCb` APIs perform residual common-subterm elimination after a DSL
has built its residual representation. The same callback pattern can later
extend to other binding forms such as lambdas or loops, but only `letB` is
part of this release.

`smartIf` takes thunked branches: a static condition calls only the selected
branch, while a dynamic condition calls both and builds one residual node.

Effect annotations are an optional `TraversalCallbacks.isPure` query used by
genlet. A missing query means pure; returning false makes a node a sharing
boundary that genlet will not hoist, duplicate, or cross, while traversal
continues through its children. This is intentionally only a two-level
classification, not an effect-summary or reordering system.

Residual while loops use the same thunk discipline: a static-false condition
folds to `unit()`, while every other condition builds one residual `while`
node. The condition and body are built once at staging time, so staging-time
state in the body is not residual loop state. `tests/test_while.nim` emits a
scanner-shaped sum loop, compiles it in a clean directory, and compares it
with direct evaluation, including a dynamic zero bound.

Residual functions use `Rep[proc(A): B]` and `smartFun`. DSLs supply an
explicit key and keyed registry: a reference is published before the body is
built, so recursive calls become residual calls and each body is built once.
`tests/test_fun.nim` stages the Ackermann tower, traverses function nodes, and
emits its three residual procedures as one compilable Nim program.

### From staging to runnable code

The complete path from a staged value to a runnable program is demonstrated
by `tests/test_codegen.nim`. It uses the same tagless-final arithmetic shape,
stages `(x + (1 + 2)) * 2`, and emits ordinary Nim source for the residual;
the `1 + 2` part is folded during staging. The test writes that source to a
clean temporary directory, invokes the `nim` compiler without this library's
`src` on its path, runs the resulting binary, and checks its result against
direct evaluation. This is deliberately a DSL-level emitter: the framework
supplies binding-time specialization and the DSL supplies the residual-node
printer.

### genlet: sharing the residual

A stager that duplicates a shared computation pays for it twice at runtime.
`genlet` hoists repeated pure composites under residual `let`s
(`tests/test_genlet.nim`, actual output):

```
before: add(mul(add(x, 1), add(y, 2)), add(mul(add(x, 1), add(y, 2)), mul(add(x, 1), add(y, 2))))
after:  (let genlet1 = add(y, 2) in (let genlet0 = add(x, 1) in (let genlet2 = mul(genlet0, genlet1) in add(genlet2, add(genlet2, genlet2)))))
```

The shared 7-node term, used 3 times (23 nodes total), becomes three bindings
plus three placeholders (17 nodes). The pass hoists any repeated pure
composite with at least 3 nodes, and it never hoists across a
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

Runs `tests/test_framework.nim`, `tests/test_codegen.nim`,
`tests/test_csp.nim`, and `tests/test_genlet.nim`. The codegen test
additionally compiles and runs its emitted residual program. Verified on Nim
2.2.12 and 2.4.0.

## Scope — what this library does NOT yet include

Honest boundaries, not roadmap promises:

- **The relational staging client stays in Eponym.** `RelGoal`/`StageGoal`
  goal representations, mode analysis, the `relcompile` residual compiler,
  and the relational `genlet` over `RelGoal`/`RTerm` all depend on
  miniKanren and on Eponym's elaborator core. They are the motivating
  application of this framework, not part of it. If you want staged
  relational programming, that lives in Eponym's
  `src/experimental/staging/` for now.
- **`genlet` has two residual-tree interfaces.** `insertLets` works on the
  standalone `GTree` when a generic representation is convenient. For a DSL
  that already has its own residual IR, `insertLetsCb` traverses that IR
  directly through `GenletCallbacks`: the client supplies child enumeration,
  structural keys, rebuilding, binder-reference construction, and residual
  let construction. Use the callback form to avoid copying or mapping the IR
  to `GTree`; use `GTree` when the generic representation is simpler. Both
  forms use the same work-based hoisting rule, treat `let` binders as sharing boundaries,
  and honor `isPure`: nil means pure, while false marks a sharing boundary.
  The classification's long-term home (callbacks or a framework-level node
  tag) remains open until another consumer needs it.
- **`traversal` provides the shared IR API.** `TraversalCallbacks` describes a
  client tree for bottom-up `mapTree`, binder-aware `substTree`, and
  `occurrences`; `GenletCallbacks` is its source-compatible alias.
- **No built-in runtime codegen, graph IR, or optimization passes.** The
  residual is a tree your DSL interprets, prints, or compiles. The worked
  arithmetic example shows a small DSL-level emitter; the framework itself
  remains code-generation agnostic. `genlet` is the only optimization, and it
  is a size optimization for pure computations — clients with effectful nodes
  honor the optional `isPure` classification: nil means pure, while false
  marks a sharing boundary.
- **No macro/bracket syntax.** Staging is expressed through `Rep[T]` and
  smart constructors in ordinary Nim code, not through MetaOCaml-style
  brackets and escape. A macro layer is out of scope for v0.1.0.

## Direction

The boundary above is the v0.1.0 state, not a permanent one. This
library is expected to grow facilities targeted specifically at
supporting the relational engine — the staged-relational client above
is its motivating application — and the engine
([raven6941/minikanren](https://github.com/raven6941/minikanren)) may
eventually depend on this library. For now the engine stands alone
with no staging dependency, and the relational client stays in Eponym.

## License

MIT — see LICENSE.
