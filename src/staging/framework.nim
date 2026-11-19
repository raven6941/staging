## Generic staging framework.
##
## Binding-time distinction and specialization machinery usable by any DSL.
## Depends on nothing (no Eponym, no relations, no other staging module).
##
## Design:
## - `Rep[T]`: staged value. Either static (known now) or dynamic (IR node
##   for later). The static/dynamic distinction is the essence of staging.
## - `IRNode`: base class for residual IR. DSLs extend with their own nodes.
## - `smartOp`: generic smart constructor. Folds when both args static,
##   builds IR otherwise. DSLs instantiate with their ops.
## - `smartLet`: generic binding constructor. Static bindings are passed
##   directly to the body; dynamic bindings get one residual reference and
##   one residual let node.
## - Tagless-final hook: any `Sym[R]` works with `R = Rep[T]`.
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

  Rep*[T] = ref object
    ## A staged value of type T.
    ## - If isStatic: value known at staging time, in staticVal.
    ## - If not: value known at runtime, represented by node (residual IR).
    isStatic*: bool
    staticVal*: T      # valid iff isStatic
    node*: IRNode      # valid iff not isStatic

proc lift*[T](x: T): Rep[T] =
  ## Lift a static value into Rep. This is the "static" injection.
  Rep[T](isStatic: true, staticVal: x)

proc dynamic*[T](node: IRNode): Rep[T] =
  ## Wrap a residual IR node as a dynamic Rep. This is the "dynamic" injection.
  Rep[T](isStatic: false, node: node)

proc getStatic*[T](r: Rep[T]): T =
  ## Extract static value. Fails if r is dynamic — this is a staging-time
  ## error (you asked for something static that isn't). If the DSL
  ## requires staticness here, the type-level spelling is Rep[T, true]
  ## (staging#9); this assertion is the residual path for values whose
  ## staticness the types cannot see.
  assert r.isStatic, "getStatic: Rep is dynamic, not static — the value " &
    "must be known at staging time; if the DSL requires staticness here, " &
    "see Rep[T, true] (staging#9)"
  r.staticVal

proc smartOp*[T](a, b: Rep[T],
                 staticOp: proc(x, y: T): T,
                 mkNode: proc(x, y: Rep[T]): IRNode): Rep[T] =
  ## Generic smart constructor.
  ## - Both static → compute now (staging-time evaluation).
  ## - Otherwise → build residual IR node (defer to runtime).
  ##
  ## DSLs instantiate this with their operation and node constructor.
  ## This is the single staging rule from which others derive.
  if a.isStatic and b.isStatic:
    lift(staticOp(a.staticVal, b.staticVal))
  else:
    dynamic[T](mkNode(a, b))

proc smartOpUni*[T](a: Rep[T],
                    staticOp: proc(x: T): T,
                    mkNode: proc(x: Rep[T]): IRNode): Rep[T] =
  ## Unary version of smartOp.
  if a.isStatic:
    lift(staticOp(a.staticVal))
  else:
    dynamic[T](mkNode(a))

proc smartLet*[T](bound: Rep[T],
                  body: proc(value: Rep[T]): Rep[T],
                  mkRef: proc(): Rep[T],
                  mkNode: proc(bound, body: Rep[T]): IRNode): Rep[T] =
  ## Generic staging rule for a tagless-final `letB` operation.
  ##
  ## A direct evaluator can implement `letB` by calling `body(bound)`. A
  ## staged evaluator should use this helper: static bindings are handled by
  ## substitution/folding, while dynamic bindings are shared through one
  ## residual reference and one residual let node.
  if bound.isStatic:
    body(bound)
  else:
    let bodyResult = body(mkRef())
    dynamic[T](mkNode(bound, bodyResult))

proc smartIf*[T](cond: Rep[bool],
                 thenB, elseB: proc(): Rep[T],
                 mkNode: proc(c: Rep[bool], t, e: Rep[T]): IRNode): Rep[T] =
  ## Generic staging rule for a residual conditional.
  ##
  ## A static condition evaluates only the selected branch thunk. A dynamic
  ## condition evaluates both branch thunks and builds one residual if node.
  if cond.isStatic:
    if cond.staticVal:
      thenB()
    else:
      elseB()
  else:
    let thenResult = thenB()
    let elseResult = elseB()
    dynamic[T](mkNode(cond, thenResult, elseResult))

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
