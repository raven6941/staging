## Generic staging framework.
##
## Binding-time distinction and specialization machinery usable by any DSL.
## Depends on nothing (no Eponym, no relations, no other staging module).
##
## Design:
## - `Rep[T, S]`: staged value. `S` is static by construction along this
##   code path: true means a staging-time-known value, false means a value
##   that may require residual IR. The static/dynamic distinction is the
##   essence of staging.
## - `IRNode`: base class for residual IR. DSLs extend with their own nodes.
## - `smartOp`: generic smart constructor. Folds when both args static,
##   builds IR otherwise. DSLs instantiate with their ops.
## - `smartLet`: generic binding constructor. Static bindings are passed
##   directly to the body; dynamic bindings get one residual reference and
##   one residual let node.
## - Tagless-final hook: any `Sym[R]` works with a uniform `R = Rep[T, S]`.
##
## Nim-level `static[T]` means a Nim compile-time constant. `Rep[T, true]`
## means a staging-time-known value by construction along this code path;
## these are different notions of static. Combinators that take Nim-level
## constants say so explicitly in their own signatures.
##
## This is the "smaller system": no graph IR, no runtime codegen, no
## optimization passes. Just binding times + specialization. The DSL
## provides the nodes; the framework provides the discipline.
##
## Origin: extracted from Eponym's `src/experimental/staging/framework.nim`,
## where it was the generic core under the staged relational elaborator
## (Track C). The code is unchanged; only the header is reworded for the
## standalone library.

type
  IRNode* = ref object of RootObj
    ## Base class for residual IR nodes. DSLs extend this with their
    ## own node types (e.g., ArithAdd, ArithMul).
    ## The framework never inspects IRNode — it's opaque residual code.
    discard

  Rep*[T; S: static[bool] = false] = ref object
    ## A staged value of type T. `S` guarantees staticness by construction
    ## along this code path; it does not claim semantic knowledge of every
    ## staging-time computation.
    when S:
      staticVal*: T
    else:
      node*: IRNode

  Unit* = object
    ## The value carried by residual statements.
    discard

  Var*[T] = ref object
    ## A residual runtime cell. The DSL's node is the cell's declaration and
    ## the anchor used by its read/write nodes.
    node*: IRNode

proc lift*[T](x: T): Rep[T, true] =
  ## Lift a static value into Rep. This is the "static" injection.
  Rep[T, true](staticVal: x)

proc dynamic*[T](node: IRNode): Rep[T, false] =
  ## Wrap a residual IR node as a dynamic Rep. This is the "dynamic" injection.
  Rep[T, false](node: node)

proc getStatic*[T](r: Rep[T, true]): T =
  ## Extract a value whose staging-time staticness is guaranteed by its type.
  ## A dynamic argument is rejected by Nim at the call site; the assertion
  ## path for the old default Rep[T] is intentionally no longer reachable.
  r.staticVal

proc smartOp*[T; A, B: static[bool]](a: Rep[T, A], b: Rep[T, B],
                 staticOp: proc(x, y: T): T,
                 mkNode: proc(x: Rep[T, A], y: Rep[T, B]): IRNode): Rep[T, A and B] =
  ## Generic smart constructor.
  ## - Both static → compute now (staging-time evaluation).
  ## - Otherwise → build residual IR node (defer to runtime).
  ##
  ## DSLs instantiate this with their operation and node constructor.
  ## This is the single staging rule from which others derive.
  when A and B:
    lift(staticOp(a.staticVal, b.staticVal))
  else:
    dynamic[T](mkNode(a, b))

proc smartOpUni*[T; S: static[bool]](a: Rep[T, S],
                    staticOp: proc(x: T): T,
                    mkNode: proc(x: Rep[T, S]): IRNode): Rep[T, S] =
  ## Unary version of smartOp.
  when S:
    lift(staticOp(a.staticVal))
  else:
    dynamic[T](mkNode(a))

proc smartLet*[T; S: static[bool]](bound: Rep[T, S],
                  body: proc(value: Rep[T, S]): Rep[T, S],
                  mkRef: proc(): Rep[T, false],
                  mkNode: proc(bound: Rep[T, S], body: Rep[T, S]): IRNode): Rep[T, S] =
  ## Generic staging rule for a tagless-final `letB` operation.
  ##
  ## A direct evaluator can implement `letB` by calling `body(bound)`. A
  ## staged evaluator should use this helper: static bindings are handled by
  ## substitution/folding, while dynamic bindings are shared through one
  ## residual reference and one residual let node.
  when S:
    body(bound)
  else:
    let bodyResult = body(mkRef())
    dynamic[T](mkNode(bound, bodyResult))

proc smartFun*[A, B; S: static[bool]](key: string, body: proc(x: Rep[A, S]): Rep[B, S],
                     mkRef: proc(): Rep[proc(x: A): B, false],
                     mkArg: proc(): Rep[A, S],
                     mkNode: proc(body: Rep[B, S]): IRNode): Rep[proc(x: A): B, false] =
  ## Build one residual function body and return its residual reference.
  ##
  ## The keyed registry belongs to the DSL: Nim closures have no reliable
  ## identity, and only the DSL knows how to type and name its definitions.
  ## The DSL must publish a reference before calling smartFun, so recursive
  ## lookups return mkRef() and never re-enter this body builder.  This helper
  ## owns the common build-once discipline: body is called exactly once per
  ## registry miss.  The argument reference is a separate node from the
  ## function reference (mkArg vs mkRef): the parameter binding and the
  ## function name must stay distinct, or a pass that rewrites one would
  ## rewrite the other.
  discard key  # Consumed by the DSL's keyed registry.
  let refRep = mkRef()
  let bodyResult = body(mkArg())
  discard mkNode(bodyResult)
  refRep

proc smartIf*[T; C, S: static[bool]](cond: Rep[bool, C],
                 thenB, elseB: proc(): Rep[T, S],
                 mkNode: proc(c: Rep[bool, C], t, e: Rep[T, S]): IRNode): Rep[T, C and S] =
  ## Generic staging rule for a residual conditional.
  ##
  ## A static condition evaluates only the selected branch thunk. A dynamic
  ## condition evaluates both branch thunks and builds one residual if node.
  when C:
    if cond.staticVal:
      thenB()
    else:
      elseB()
  else:
    let thenResult = thenB()
    let elseResult = elseB()
    dynamic[T](mkNode(cond, thenResult, elseResult))

proc unit*(): Rep[Unit, true] =
  ## The pure statement/value used for an empty residual statement.
  lift(Unit())

proc newVar*[T; S: static[bool]](init: Rep[T, S],
                mkNode: proc(init: Rep[T, S]): IRNode): Var[T] =
  ## Allocate a residual cell. Vars are always dynamic: only their init
  ## expression may be static. Rep[Unit] plus seqR won the statement design
  ## question: it composes with smartIf while keeping the same Sym vocabulary;
  ## DSLs that need it can use separate value/statement type parameters.
  Var[T](node: mkNode(init))

proc readVar*[T](v: Var[T],
                 mkNode: proc(v: Var[T]): IRNode): Rep[T, false] =
  ## Read a runtime cell; reads are deliberately not folded here.
  dynamic[T](mkNode(v))

proc writeVar*[T; S: static[bool]](v: Var[T], val: Rep[T, S],
                  mkNode: proc(v: Var[T], val: Rep[T, S]): IRNode): Rep[Unit, false] =
  ## Write a runtime cell; no read-after-write optimization is attempted.
  dynamic[Unit](mkNode(v, val))

proc seqR*[A, B: static[bool]](a: Rep[Unit, A], b: Rep[Unit, B],
           mkNode: proc(a: Rep[Unit, A], b: Rep[Unit, B]): IRNode): Rep[Unit, A and B] =
  ## Sequence two residual statements. Unit is a real staged value so this
  ## remains usable from a tagless-final Sym without a special void channel.
  when A and B:
    unit()
  else:
    dynamic[Unit](mkNode(a, b))

proc smartWhile*[C, B: static[bool]](cond: proc(): Rep[bool, C],
                 body: proc(): Rep[Unit, B],
                 mkNode: proc(c: Rep[bool, C], b: Rep[Unit, B]): IRNode): Rep[Unit, false] =
  ## Generic staging rule for a residual while loop.
  ##
  ## A static-false condition folds the loop to unit without calling the body
  ## thunk.  Every other condition, including static true, builds one
  ## residual loop node.  The condition and body are thunks because Nim is
  ## strict: the body is built once at staging time, verbatim, rather than
  ## once per residual iteration.  Staging-time state in the body (such as a
  ## Nim var or table) is therefore touched once; DSL authors must not
  ## confuse it with residual runtime state.
  let c = cond()
  when C:
    if not c.staticVal:
      return dynamic[Unit](IRNode(nil))
  let b = body()
  dynamic[Unit](mkNode(c, b))

# --- Tagless-final hook ---
#
# Any DSL written as Sym[R] (or similar dictionary-passing style) can
# be staged by instantiating R = Rep[T]. The framework doesn't need to
# know Sym specifically — Rep[T] is just a type that DSLs can use as R.
#
# Example (see tests/test_framework.nim):
#   type ArithSym[R] = object
#     lit: proc(n: int): R
#     add: proc(a, b: R): R
#     letB: proc(bound: R, body: proc(value: R): R): R
#   proc prog[R](s: ArithSym[R]): R = s.add(s.lit(1), s.lit(2))
#   prog[Rep[int]](stagedArith)  # builds IR via smartOp

when isMainModule:
  echo "Staging framework loaded. See tests/test_framework.nim for usage."
