## Re-walk cost measurement (#177): pass-pipeline staging time vs residual size.
##
## The #176 design note settled the graph-IR question as keep tree+passes,
## with reopen trigger 1 = "a concrete DSL whose residual is large enough
## that pass re-walking dominates staging time". This fixture turns that
## theoretical counterpoint into numbers: it times the documented ANF pass
## pipeline (toAnf -> cseAnf -> licmAnf -> dceAnf -> fromAnf) against
## residual size, on the ANF test DSL (the only node type with full ANF
## callbacks), in three shapes — a deep chain, a balanced tree, and a
## loop-nested body — plus construction time for the same residual, so the
## re-walk share is visible separately from staging/construction time.
##
## Threshold, named BEFORE measuring (post-hoc verdicts are not allowed):
## trigger 1 FIRES iff either (a) at some N <= 10_000 bindings, total
## pass-pipeline time exceeds residual-construction time by >= 2x, or
## (b) any single pass's time per binding grows > 2x over a 10x increase
## in N (superlinear growth) within N <= 10_000. It stays CLOSED with
## numbers iff at the largest existing client residual (O(10) nodes) pass
## time is below construction time and growth is linear (flat time per
## binding) through N = 10_000.
##
## Existing clients anchor the small end of the scale (counted from their
## construction code, not timed here — the passes are generic over the
## node type, so per-node cost transfers): compiler demo `sample` residual
## is 5 Def nodes, TPCH-Q1 is 4 residual nodes, SoA-mixed is ~10 MixedNodes
## per element expression, LINQ nested queries are O(20) nodes. The
## scaling fixture is what carries the verdict; the clients say where
## real residuals sit on its N axis.
##
## `insertLets`/genlet is not timed here: it re-walks at construction time
## over `GTree`, not as a post-hoc pass over this residual. `optAnf` is
## not timed either: it is a client-supplied rewrite rule, not part of the
## documented base pipeline.
##
## Usage: `nim c -r --path:src tests/test_rewalk_bench.nim` runs the
## small range (fast enough for `nimble test`). Add `-d:rewalkFull` for
## the full range up to N = 10_000, and `-d:release` for the numbers that
## go in the measurement note.

import staging/anf
import std/[algorithm, tables, times]

type
  ExprKind = enum ekLit, ekInput, ekRef, ekAdd, ekMul, ekLoop, ekEffect
  Expr = ref object
    kind: ExprKind
    value: int
    name: string
    left, right: Expr

proc lit(v: int): Expr = Expr(kind: ekLit, value: v)
proc input(name: string): Expr = Expr(kind: ekInput, name: name)
proc refE(name: string): Expr = Expr(kind: ekRef, name: name)
proc add(a, b: Expr): Expr = Expr(kind: ekAdd, left: a, right: b)
proc mul(a, b: Expr): Expr = Expr(kind: ekMul, left: a, right: b)
proc loop(body: Expr): Expr = Expr(kind: ekLoop, left: body)

proc exprChildren(e: Expr): seq[Expr] =
  case e.kind
  of ekAdd, ekMul: @[e.left, e.right]
  of ekLoop: @[e.left]
  else: @[]

proc exprRebuild(e: Expr; kids: seq[Expr]): Expr =
  case e.kind
  of ekAdd: add(kids[0], kids[1])
  of ekMul: mul(kids[0], kids[1])
  of ekLoop: loop(kids[0])
  else: e

proc exprKey(e: Expr): string =
  case e.kind
  of ekLit: "lit(" & $e.value & ")"
  of ekInput: "in(" & e.name & ")"
  of ekRef: "ref(" & e.name & ")"
  of ekAdd: "add(" & exprKey(e.left) & "," & exprKey(e.right) & ")"
  of ekMul: "mul(" & exprKey(e.left) & "," & exprKey(e.right) & ")"
  of ekLoop: "loop(" & exprKey(e.left) & ")"
  of ekEffect: "effect"

proc exprIsAtomic(e: Expr): bool =
  e.kind in {ekLit, ekInput, ekRef}

proc exprRefName(e: Expr): string =
  if e.kind == ekRef: e.name else: ""

proc exprFreeVars(e: Expr): seq[string] =
  if e.kind == ekRef: return @[e.name]
  for child in exprChildren(e):
    for name in exprFreeVars(child):
      if name notin result: result.add(name)

let cb = AnfCallbacks[Expr](
  children: exprChildren,
  rebuild: exprRebuild,
  key: exprKey,
  isAtomic: exprIsAtomic,
  refName: exprRefName,
  makeRef: refE,
  isBoundary: proc(e: Expr): bool = e.kind == ekLoop,
  binders: proc(e: Expr): seq[string] = @["i"],
  freeVars: exprFreeVars,
  isPure: proc(e: Expr): bool = e.kind != ekEffect,
  isTotal: proc(e: Expr): bool = true)

proc evalExpr(e: Expr; env: Table[string, int]): int =
  ## Modular evaluation: the balanced shape multiplies freely, so reduce
  ## mod M after each op to keep the round-trip check from overflowing.
  ## Both sides of the check use the same semantics.
  const M = 1_000_000_007
  case e.kind
  of ekLit: e.value
  of ekInput, ekRef: env[e.name]
  of ekAdd: (evalExpr(e.left, env) + evalExpr(e.right, env)) mod M
  of ekMul: (evalExpr(e.left, env) * evalExpr(e.right, env)) mod M
  of ekLoop: evalExpr(e.left, env)
  of ekEffect: 99

proc countNodes(e: Expr): int =
  result = 1
  for child in exprChildren(e):
    result += countNodes(child)

proc buildChain(n: int): Expr =
  ## Deep tree: x0 = input, xi = x(i-1) + 1. N composite nodes.
  var x = input("x")
  for i in 1 .. n:
    x = add(x, lit(1))
  x

proc buildBalanced(leaves: int; lo = 0): Expr =
  ## Bushy tree over `leaves` distinct inputs, alternating add/mul.
  if leaves == 1:
    return input("v" & $lo)
  let half = leaves div 2
  let l = buildBalanced(half, lo)
  let r = buildBalanced(leaves - half, lo + half)
  if (lo div half) mod 2 == 0: add(l, r) else: mul(l, r)

proc buildLoop(n: int): Expr =
  ## N-op chain over the loop binder inside a loop body. Every op mentions
  ## the binder, so licmAnf moves nothing (the scan cost is what is
  ## measured) — a hoisting body cannot go through the full pipeline here:
  ## dceAnf after licmAnf drops hoisted bindings (#178), so the loop shape
  ## deliberately stays hoist-free until that is fixed.
  var body = refE("i")
  for i in 1 .. n:
    body = add(body, lit(1))
  loop(body)

proc median3(times: array[3, float]): float =
  var t = @[times[0], times[1], times[2]]
  t.sort()
  t[1]

proc timeIt(reps: int; body: proc()): float =
  ## Median CPU seconds over `reps` runs.
  var ts: array[3, float]
  for i in 0 ..< 3:
    let start = cpuTime()
    for _ in 0 ..< reps:
      body()
    ts[i] = cpuTime() - start
  median3(ts) / reps.float

proc runRow(shape: string; n: int; build: proc(): Expr) =
  let probe = build()
  let nodes = countNodes(probe)
  let bindings = toAnf(probe, cb).stmts.len +
    (if shape == "loop": toAnf(probe, cb).stmts[0].nested[0].stmts.len else: 0)
  # Correctness at this size: the pipeline round-trips the value.
  var env = {"x": 0, "a": 3, "n": 4, "i": 5}.toTable
  for i in 0 ..< n:
    env["v" & $i] = i mod 7
  let want = evalExpr(probe, env)
  let piped = fromAnf(dceAnf(licmAnf(cseAnf(toAnf(probe, cb), cb), cb), cb), cb)
  doAssert evalExpr(piped, env) == want, shape & " pipeline round-trip"
  # Timings: construction, then each pass on a fresh pipeline per rep.
  let tBuild = timeIt(3, proc() = discard build())
  let tToAnf = timeIt(3, proc() = discard toAnf(probe, cb))
  let anf = toAnf(probe, cb)
  let tCse = timeIt(3, proc() = discard cseAnf(anf, cb))
  let csed = cseAnf(anf, cb)
  let tLicm = timeIt(3, proc() = discard licmAnf(csed, cb))
  let licmed = licmAnf(csed, cb)
  let tDce = timeIt(3, proc() = discard dceAnf(licmed, cb))
  let dced = dceAnf(licmed, cb)
  let tFrom = timeIt(3, proc() = discard fromAnf(dced, cb))
  let tPass = tToAnf + tCse + tLicm + tDce + tFrom
  let ratio = if tBuild > 0: tPass / tBuild else: 0.0
  echo shape, " N=", n, " nodes=", nodes, " bindings=", bindings,
    " build=", tBuild * 1000, "ms",
    " toAnf=", tToAnf * 1000, "ms",
    " cse=", tCse * 1000, "ms",
    " licm=", tLicm * 1000, "ms",
    " dce=", tDce * 1000, "ms",
    " from=", tFrom * 1000, "ms",
    " passTotal=", tPass * 1000, "ms",
    " pass/build=", ratio,
    " usPerBinding=", (tPass * 1e6) / bindings.float

when isMainModule:
  echo "shape N nodes bindings buildMs toAnfMs cseMs licmMs dceMs fromMs passTotalMs pass/build usPerBinding"
  when defined(rewalkFull):
    const chainNs = [100, 300, 1000, 3000, 5000]
    const balNs = [100, 300, 1000, 3000, 10000]
    const loopNs = [100, 300, 1000, 3000, 5000]
  else:
    const chainNs = [100, 300]
    const balNs = [100, 300]
    const loopNs = [100, 300]
  for n in chainNs:
    runRow("chain", n, proc(): Expr = buildChain(n))
  for n in balNs:
    runRow("balanced", n, proc(): Expr = buildBalanced(n))
  for n in loopNs:
    runRow("loop", n, proc(): Expr = buildLoop(n))
  echo "ok: re-walk bench (threshold in header; see #177)"
