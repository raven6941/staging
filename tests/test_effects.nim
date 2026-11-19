## Step 4: minimal effect annotations.
##
## The load-bearing genlet case below fails without the isPure wiring: the
## repeated effectful composite qualifies on savings and is hoisted. With the
## wiring it remains three separate occurrences. Traversal still visits its
## children, because effect annotations are sharing boundaries, not opaque
## nodes.

import std/[tables, strutils]
import staging/framework
import staging/genlet
import staging/traversal

type
  EKind = enum ekRead, ekRef, ekLit, ekMul, ekLet
  ENode = ref object of IRNode
    kind: EKind
    children: seq[ENode]
    name: string

proc eRead(): Rep[int] = dynamic[int](ENode(kind: ekRead))
proc eRef(name: string): Rep[int] = dynamic[int](ENode(kind: ekRef, name: name))
proc eLit(n: int): Rep[int] = dynamic[int](ENode(kind: ekLit, name: $n))
proc eMul(a, b: Rep[int]): Rep[int] =
  dynamic[int](ENode(kind: ekMul, children: @[cast[ENode](a.node), cast[ENode](b.node)]))

proc power(base: Rep[int]; n: int): Rep[int] =
  if n == 0: eLit(1)
  else: eMul(base, power(base, n - 1))

proc eLetNode(bound, body: Rep[int]): IRNode =
  ENode(kind: ekLet, children: @[cast[ENode](bound.node), cast[ENode](body.node)])

proc eval(n: ENode; env: var Table[string, int]; reads: var int): int =
  case n.kind
  of ekRead:
    inc reads
    2
  of ekRef: env[n.name]
  of ekLit: parseInt(n.name)
  of ekMul: eval(n.children[0], env, reads) * eval(n.children[1], env, reads)
  of ekLet:
    let value = eval(n.children[0], env, reads)
    var nested = env
    nested["r"] = value
    eval(n.children[1], nested, reads)

proc eKey(n: ENode): string =
  case n.kind
  of ekRead: "read"
  of ekRef: "ref(" & n.name & ")"
  of ekLit: n.name
  of ekMul: "mul(" & eKey(n.children[0]) & "," & eKey(n.children[1]) & ")"
  of ekLet: "let(" & eKey(n.children[0]) & "," & eKey(n.children[1]) & ")"

proc eCallbacks(): GenletCallbacks[ENode] =
  var cb = TraversalCallbacks[ENode](
    children: proc(n: ENode): seq[ENode] = n.children,
    key: eKey,
    isComposite: proc(n: ENode): bool = n.kind != ekRef,
    isBoundary: proc(n: ENode): bool = n.kind == ekLet,
    rebuild: proc(n: ENode; cs: seq[ENode]): ENode =
      ENode(kind: n.kind, name: n.name, children: cs),
    makeRef: proc(name: string): ENode = ENode(kind: ekRef, name: name),
    makeLet: proc(name: string; bound, body: ENode): ENode =
      ENode(kind: ekLet, name: name, children: @[bound, body]))
  cb.isPure = proc(n: ENode): bool = n.kind != ekRead
  cb

when isMainModule:
  let naive = power(eRead(), 4).node
  var env = initTable[string, int]()
  var naiveReads = 0
  doAssert eval(ENode(naive), env, naiveReads) == 16
  doAssert naiveReads == 4

  # smartLet is the construction-time placement mechanism: bind the one
  # effectful read, then power the residual reference four times.
  let bound = smartLet[int](eRead(),
    proc(r: Rep[int]): Rep[int] = power(r, 4),
    proc(): Rep[int] = eRef("r"),
    proc(b, body: Rep[int]): IRNode = eLetNode(b, body))
  var boundReads = 0
  doAssert eval(ENode(bound.node), env, boundReads) == 16
  doAssert boundReads == 1
  echo "ok: smartLet makes power(read(), 4) perform one read"

  # This effectful composite would qualify under the savings test if pure.
  let effect = gnode("read", @[
    gnode("add", @[gatom("2"), gatom("3")]),
    gnode("add", @[gatom("4"), gatom("5")])])
  let repeated = gnode("add", @[effect, gnode("add", @[effect, effect])])
  var effectCb = gtreeCallbacks()
  effectCb.isPure = proc(n: GTree): bool = n.kind != gkNode or n.op != "read"
  var effectCtx = newGenletCtx()
  let effectOut = insertLetsCb(repeated, effectCtx, effectCb)
  doAssert effectCtx.counter == 0
  doAssert count($effectOut, "read(add(2, 3), add(4, 5))") == 3

  # Pure twin: same shape, with no effect annotation.
  let pure = gnode("pure", @[
    gnode("add", @[gatom("2"), gatom("3")]),
    gnode("add", @[gatom("4"), gatom("5")])])
  let pureRepeated = gnode("add", @[pure, gnode("add", @[pure, pure])])
  var pureCtx = newGenletCtx()
  discard insertLetsCb(pureRepeated, pureCtx, gtreeCallbacks())
  doAssert pureCtx.counter == 1
  echo "ok: effectful composite is not hoisted; pure twin is"

  # Traversal is still structural and sees through the effectful node.
  var seen = 0
  discard mapTree(repeated, effectCb,
    proc(n: GTree): GTree =
      if n.kind == gkAtom and n.name == "2": inc seen
      n)
  doAssert seen == 3
  echo "ok: traversal sees children of effectful nodes"

  # globalOccurrences still counts across let boundaries (binder in
  # scope); only effectful nodes stop the walk.
  let shared = gnode("add", @[gatom("2"), gatom("3")])
  let letTree = gnode("add", @[
    glet("z", gatom("9"), shared),
    shared])
  let letOccs = globalOccurrences(letTree, gtreeCallbacks())
  doAssert letOccs["add(2, 3)"].len == 2
  var inLet = 0
  for o in letOccs["add(2, 3)"]:
    if o.binders == @["z"]: inc inLet
  doAssert inLet == 1
  var effCb2 = gtreeCallbacks()
  effCb2.isPure = proc(n: GTree): bool = n.kind != gkNode or n.op != "read"
  let effOccs = globalOccurrences(gnode("read", @[shared]), effCb2)
  doAssert "add(2, 3)" notin effOccs
  echo "ok: global counts cross let boundaries but stop at effectful nodes"

  # A pure candidate CONTAINING an effect must not be hoisted either:
  # sharing it would execute the effect fewer times.
  let r = gnode("read", @[gatom("a"), gatom("b")])
  let inner = gnode("add", @[r, gnode("add", @[gatom("x"), gatom("y")])])
  let containsTree = gnode("add", @[inner, gnode("add", @[inner, inner])])
  var containCtx = newGenletCtx()
  let containOut = insertLetsCb(containsTree, containCtx, effCb2)
  doAssert containCtx.counter == 0
  doAssert count($containOut, "read(a, b)") == 3

  # Pure twin: same shape, no effect — the candidate IS hoisted.
  let pr = gnode("pure", @[gatom("a"), gatom("b")])
  let pinner = gnode("add", @[pr, gnode("add", @[gatom("x"), gatom("y")])])
  let pureContains = gnode("add", @[pinner, gnode("add", @[pinner, pinner])])
  var pureContainCtx = newGenletCtx()
  discard insertLetsCb(pureContains, pureContainCtx, gtreeCallbacks())
  doAssert pureContainCtx.counter == 1
  echo "ok: pure candidate containing an effect is not hoisted; pure twin is"

