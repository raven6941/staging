## Residual mutable arrays.
##
## An Arr is a residual CELL, following Var[T]: its node is the declaration
## anchor, and indexing is expressed only through readArr/writeArr nodes. An
## array cell cannot be passed as a first-class staged value the way a Rep can;
## this is the cost of retaining mutation without threading a new array value
## through every write. Arrays are effectful: writes are observable through
## later reads, so never feed an array-node subtree to genlet's insertLets
## unless the DSL has proved that subtree pure. As elsewhere in the framework,
## literals and folded branches use liftNow; lift is reserved for Rep[T, true].

import staging/framework

type
  Arr*[T] = ref object
    ## The residual declaration and anchor for this array cell.
    node*: IRNode

proc newArray*[T](len: Rep[int],
                  mkNode: proc(len: Rep[int]): IRNode): Arr[T] =
  ## Allocate a dynamic residual array. A static length expression is allowed,
  ## but the cell itself remains runtime state.
  Arr[T](node: mkNode(len))

proc readArr*[T](a: Arr[T], i: Rep[int],
                 mkNode: proc(a: Arr[T], i: Rep[int]): IRNode): Rep[T] =
  ## Reads are never folded: an earlier write may have changed the slot.
  dynamic[T](mkNode(a, i))

proc writeArr*[T](a: Arr[T], i: Rep[int], v: Rep[T],
                  mkNode: proc(a: Arr[T], i: Rep[int], v: Rep[T]): IRNode): Rep[Unit] =
  ## Writes are effectful statements; no read-after-write optimization occurs.
  dynamic[Unit](mkNode(a, i, v))

proc lenArr*[T](a: Arr[T],
                mkNode: proc(a: Arr[T]): IRNode): Rep[int] =
  ## Obtain the residual length from the array cell.
  dynamic[int](mkNode(a))
