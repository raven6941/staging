## Step 2 acceptance tests: type-level staging staticness.

import staging/framework

type
  ArithKind = enum akLeaf, akAdd
  ArithNode = ref object of IRNode
    case kind: ArithKind
    of akLeaf: value: int
    of akAdd:
      left, right: Rep[int, false]

proc leaf(x: int): ArithNode = ArithNode(kind: akLeaf, value: x)

proc asDynamic[S: static[bool]](r: Rep[int, S]): Rep[int, false] =
  when S:
    dynamic[int](leaf(r.staticVal))
  else:
    r

proc addR[A, B: static[bool]](a: Rep[int, A], b: Rep[int, B]): Rep[int, A and B] =
  smartOp(a, b,
    proc(x, y: int): int = x + y,
    proc(x: Rep[int, A], y: Rep[int, B]): IRNode =
      ArithNode(kind: akAdd, left: asDynamic(x), right: asDynamic(y)))

proc dyn(name: string): Rep[int, false] =
  dynamic[int](leaf(name.len))

proc needsDynamic(r: Rep[int]): int =
  discard r
  0

proc join(flag: bool): Rep[int] =
  ## Joins intentionally collapse to the default dynamic instantiation.
  if flag: dynamic[int](leaf(1)) else: dyn("x")

when isMainModule:
  let folded = addR(lift(1), lift(2))
  doAssert compiles(getStatic(folded))
  doAssert getStatic(folded) == 3

  let mixed = addR(folded, dyn("x"))
  doAssert not compiles(getStatic(mixed))
  doAssert mixed is Rep[int, false]

  # Vetting stencil port, stencil.nim lines 95-103: the old dynamic
  # getStatic(nDyn) staging-time assertion is now a compile-time rejection.
  let dynRep: Rep[int] = dyn("dynamic")
  doAssert not compiles(getStatic(dynRep))

  doAssert join(true) is Rep[int, false]
  doAssert not compiles(needsDynamic(lift(1)))

  echo "ok: type-level staticness, mixed folding, joins, and non-subtyping"
