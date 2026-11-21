## Generic staging framework.
##
## Binding-time distinction and specialization machinery usable by any DSL.
## Depends on nothing (no Eponym, no relations, no other staging module).
##
## Design:
## - `Rep[T, S]`: staged value. `S` is a boundary annotation: true means a
##   value constructed with a static guarantee, while the runtime flag below
##   records staging-time knowledge for every Rep.
## - `IRNode`: base class for residual IR. DSLs extend with their own nodes.
## - `smartOp`: generic smart constructor. Folding is driven by the runtime
##   flag, while S propagates a static guarantee through purely static ops.
## - `smartLet`: generic binding constructor. Static bindings are passed
##   directly to the body; dynamic bindings get one residual reference and
##   one residual let node.
## - Tagless-final hook: Sym programs use plain `Rep[T]`; mixed static and
##   dynamic values are intentionally represented by the runtime flag.
##
## Rule: a Sym program's `lit` and every plain-Rep literal/fold branch uses
## `liftNow`, never `lift`. `lift` is reserved for constructing a
## `Rep[T, true]` boundary value; `liftNow` records staging-time knowledge
## without changing the plain `Rep[T]` shape.
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
    ## A staged value of type T. All three fields exist for every S:
    ## `staticVal` is valid iff `isStatic`, and `node` is valid iff not.
    ## Every Rep[T, true] is flag-static. Construct Rep[T, true] only via
    ## lift or the both-static branches of smartOp/smartOpUni; DSLs must not
    ## hand-construct that instantiation.
    isStatic*: bool
    staticVal*: T
    node*: IRNode

  Unit* = object
    ## The value carried by residual statements.
    discard

  Var*[T] = ref object
    ## A residual runtime cell. The DSL's node is the cell's declaration and
    ## the anchor used by its read/write nodes.
    node*: IRNode

proc lift*[T](x: T): Rep[T, true] =
  ## Static injection, reserved for constructing a Rep[T, true] boundary.
  Rep[T, true](isStatic: true, staticVal: x)

proc liftNow*[T](x: T): Rep[T] =
  ## Lift a staging-time-known value without a type-level static guarantee.
  ## Sym literals and all plain-Rep literal/fold branches must use liftNow,
  ## never lift: lift returns Rep[T, true].
  Rep[T](isStatic: true, staticVal: x)

proc dynamic*[T](node: IRNode): Rep[T, false] =
  ## Wrap a residual IR node as a dynamic Rep. This is the "dynamic" injection.
  Rep[T, false](isStatic: false, node: node)

proc getStatic*[T](r: Rep[T, true]): T =
  ## Extract a value whose staging-time staticness is guaranteed by its type.
  ## A dynamic argument is rejected by Nim at the call site; the assertion
  ## path for the old default Rep[T] is intentionally no longer reachable.
  r.staticVal

proc smartOp*[T; A, B: static[bool]](a: Rep[T, A], b: Rep[T, B],
                 staticOp: proc(x, y: T): T,
                 mkNode: proc(x: Rep[T, A], y: Rep[T, B]): IRNode): Rep[T, A and B] =
  ## Generic smart constructor.
  ## The `when` selects a constructor matching the declared return type.
  ## When the type does not guarantee staticness, the runtime flag decides
  ## whether to fold; a dynamic node is never fabricated as Rep[T, true].
  ##
  ## DSLs instantiate this with their operation and node constructor.
  ## This is the single staging rule from which others derive.
  when A and B:
    lift(staticOp(a.staticVal, b.staticVal))
  else:
    if a.isStatic and b.isStatic:
      liftNow(staticOp(a.staticVal, b.staticVal))
    else:
      dynamic[T](mkNode(a, b))

proc smartOpUni*[T; S: static[bool]](a: Rep[T, S],
                    staticOp: proc(x: T): T,
                    mkNode: proc(x: Rep[T, S]): IRNode): Rep[T, S] =
  ## Unary version of smartOp.
  when S:
    lift(staticOp(a.staticVal))
  else:
    if a.isStatic:
      liftNow(staticOp(a.staticVal))
    else:
      dynamic[T](mkNode(a))

proc smartOp*[T](a, b: Rep[T], staticOp: proc(x, y: T): T,
                 mkNode: proc(x, y: Rep[T]): IRNode): Rep[T] =
  ## Compatibility form for plain-Rep DSLs. Nim does not infer omitted
  ## static generic parameters when the caller explicitly writes [T].
  ## Sym programs therefore use this form, while typed direct-style code
  ## uses the threaded overload above.
  if a.isStatic and b.isStatic:
    liftNow(staticOp(a.staticVal, b.staticVal))
  else:
    dynamic[T](mkNode(a, b))

proc smartOpUni*[T](a: Rep[T], staticOp: proc(x: T): T,
                    mkNode: proc(x: Rep[T]): IRNode): Rep[T] =
  ## Plain-Rep compatibility form; folding remains flag-driven.
  if a.isStatic:
    liftNow(staticOp(a.staticVal))
  else:
    dynamic[T](mkNode(a))

proc smartLet*[T](bound: Rep[T],
                  body: proc(value: Rep[T]): Rep[T],
                  mkRef: proc(): Rep[T],
                  mkNode: proc(bound: Rep[T], body: Rep[T]): IRNode): Rep[T] =
  ## Generic staging rule for a tagless-final `letB` operation.
  ##
  ## A direct evaluator can implement `letB` by calling `body(bound)`. A
  ## staged evaluator should use this helper: static bindings are handled by
  ## substitution/folding, while dynamic bindings are shared through one
  ## residual reference and one residual let node.
  ## This helper stays plain-Rep: no acceptance case needs S propagated here,
  ## and threading it would make the dynamic mkRef/mkNode branch ill-typed.
  if bound.isStatic:
    body(bound)
  else:
    let bodyResult = body(mkRef())
    dynamic[T](mkNode(bound, bodyResult))

proc smartFun*[A, B](key: string, body: proc(x: Rep[A]): Rep[B],
                     mkRef: proc(): Rep[proc(x: A): B],
                     mkArg: proc(): Rep[A],
                     mkNode: proc(body: Rep[B]): IRNode): Rep[proc(x: A): B] =
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

proc smartIf*[T](cond: Rep[bool],
                 thenB, elseB: proc(): Rep[T],
                 mkNode: proc(c: Rep[bool], t, e: Rep[T]): IRNode): Rep[T] =
  ## Generic staging rule for a residual conditional.
  ##
  ## A static condition evaluates only the selected branch thunk. A dynamic
  ## condition evaluates both branch thunks and builds one residual if node.
  ## It stays plain-Rep because threading S would force different mkNode
  ## types for a static versus dynamic condition without an acceptance need.
  if cond.isStatic:
    if cond.staticVal:
      thenB()
    else:
      elseB()
  else:
    let thenResult = thenB()
    let elseResult = elseB()
    dynamic[T](mkNode(cond, thenResult, elseResult))

proc unit*(): Rep[Unit] =
  ## The pure statement/value used for an empty residual statement.
  liftNow(Unit())

proc newVar*[T](init: Rep[T],
                mkNode: proc(init: Rep[T]): IRNode): Var[T] =
  ## Allocate a residual cell. Vars are always dynamic: only their init
  ## expression may be static. Rep[Unit] plus seqR won the statement design
  ## question: it composes with smartIf while keeping the same Sym vocabulary;
  ## DSLs that need it can use separate value/statement type parameters.
  Var[T](node: mkNode(init))

proc readVar*[T](v: Var[T],
                 mkNode: proc(v: Var[T]): IRNode): Rep[T] =
  ## Read a runtime cell; reads are deliberately not folded here.
  dynamic[T](mkNode(v))

proc writeVar*[T](v: Var[T], val: Rep[T],
                  mkNode: proc(v: Var[T], val: Rep[T]): IRNode): Rep[Unit] =
  ## Write a runtime cell; no read-after-write optimization is attempted.
  dynamic[Unit](mkNode(v, val))

proc seqR*(a, b: Rep[Unit],
           mkNode: proc(a, b: Rep[Unit]): IRNode): Rep[Unit] =
  ## Sequence two residual statements. Unit is a real staged value so this
  ## remains usable from a tagless-final Sym without a special void channel.
  if a.isStatic and b.isStatic:
    liftNow(Unit())
  else:
    dynamic[Unit](mkNode(a, b))

proc smartWhile*(cond: proc(): Rep[bool],
                 body: proc(): Rep[Unit],
                 mkNode: proc(c: Rep[bool], b: Rep[Unit]): IRNode): Rep[Unit] =
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
  if c.isStatic and not c.staticVal:
    return liftNow(Unit())
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
