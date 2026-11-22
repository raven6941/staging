## Pure staging-time products for grouping related `Rep` fields.
##
## A product is a value-level grouping, not a residual cell or IR node.
## Construction and projection are staging-time and free; arithmetic on its
## fields residualizes through the DSL's `smartOp`s.  A DSL defines its own
## struct type as a Nim object of Reps; this module supplies only generic
## product vocabulary, not an emitter or a residual struct node.
##
## Field operations fold exactly when the underlying smart operations fold:
## both static fields produce static result fields, so a product of two
## static Reps is fully static.  Plain-Rep literals and fold branches use
## `liftNow`; `lift` remains reserved for boundary values.  Products are pure,
## unlike array subtrees, so a product subtree may be passed to genlet's
## `insertLets` when that facility is used by a DSL.
##
## Rejected alternatives: a cell anchor would incorrectly impose identity and
## mutation on a pure struct value; a residual construction/projection node
## would add nothing to the existing field-wise residual form.

import staging/framework

type
  Prod2*[A, B] = object
    fst*: Rep[A]
    snd*: Rep[B]

proc prod2*[A, B](a: Rep[A], b: Rep[B]): Prod2[A, B] =
  Prod2[A, B](fst: a, snd: b)

proc mapProd2*[A, B](p, q: Prod2[A, B],
                     op: proc(x, y: Rep[A]): Rep[A],
                     opB: proc(x, y: Rep[B]): Rep[B]): Prod2[A, B] =
  prod2(op(p.fst, q.fst), opB(p.snd, q.snd))
