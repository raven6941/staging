import std/[tables, strutils]
import staging/genlet
import staging/scopegenlet

proc atom(n: string): GTree = gatom(n)
proc mul(a, b: GTree): GTree = gnode("mul", @[a, b])

proc evalTree(t: GTree; env: Table[string, int]; reads: var int): int =
  case t.kind
  of gkAtom:
    if t.name == "read":
      inc reads
      return 2
    try: parseInt(t.name)
    except ValueError: env[t.name]
  of gkNode:
    doAssert t.op == "mul"
    evalTree(t.children[0], env, reads) * evalTree(t.children[1], env, reads)
  of gkLet:
    var e = env
    e[t.binder] = evalTree(t.bound, env, reads)
    evalTree(t.body, e, reads)

proc powerP(b: GTree; n: int): GTree =
  ## Binary-squaring power that performs every multiplication: the
  ## 02_basics eager shape, one residual let per mul.
  if n == 0: atom("1")
  elif n mod 2 == 0:
    let y = powerP(b, n div 2)
    perform(mul(y, y))
  else: perform(mul(b, powerP(b, n - 1)))

when isMainModule:
  # Construction-time binary-squaring sharing: no post-pass is involved.
  let p = accumulate(proc(): GTree =
    let x = atom("x")
    let p1 = perform(mul(x, atom("1")))
    let p2 = perform(mul(p1, p1))
    let p3 = perform(mul(x, p2))
    mul(x, mul(p3, p3)))
  doAssert count($p, "let genlet") == 3
  doAssert $p == "(let genlet0 = mul(x, 1) in (let genlet1 = " &
    "mul(genlet0, genlet0) in (let genlet2 = mul(x, genlet1) in " &
    "mul(x, mul(genlet2, genlet2)))))"
  var reads = 0
  doAssert evalTree(p, {"x": 2}.toTable, reads) == 128
  doAssert reads == 0

  # The recursive power through perform: one let per mul (5 muls for n=7).
  let pp = accumulate(proc(): GTree = powerP(atom("x"), 7))
  doAssert count($pp, "let genlet") == 5
  reads = 0
  doAssert evalTree(pp, {"x": 2}.toTable, reads) == 128
  doAssert reads == 0

  let effect = accumulate(proc(): GTree =
    let r = perform(atom("read"))
    mul(mul(r, r), mul(r, r)))
  reads = 0
  doAssert evalTree(effect, initTable[string, int](), reads) == 16
  doAssert reads == 1

  let outer = accumulate(proc(scope: Scope): GTree =
    let shared = genletAt(scope, mul(atom("x"), atom("1")))
    accumulate(proc(): GTree =
      let local = perform(mul(shared, shared))
      local))
  doAssert count($outer, "let genlet") == 2
  doAssert $outer == "(let genlet0 = mul(x, 1) in " &
    "(let genlet1 = mul(genlet0, genlet0) in genlet1))"

  var escaped = false
  try:
    discard accumulate(proc(scope: Scope): GTree =
      var leaked: GTree
      discard accumulate(proc(): GTree =
        leaked = perform(atom("read"))
        atom("0"))
      discard genletAt(scope, leaked)
      atom("0"))
  except ValueError:
    escaped = true
  doAssert escaped

  let s = newScope()
  let same = genletAt(s, mul(atom("a"), atom("b")))
  doAssert $genletAt(s, mul(atom("a"), atom("b"))) == $same
  let closed = closeScope(s, mul(same, same))
  doAssert $closed == "(let genlet0 = mul(a, b) in mul(genlet0, genlet0))"
  var doubleClose = false
  try: discard closeScope(s, same)
  except ValueError: doubleClose = true
  doAssert doubleClose

  var outsideFailed = false
  try: discard perform(atom("x"))
  except ValueError: outsideFailed = true
  doAssert outsideFailed
  echo "ok: scopegenlet construction-time insertion, effects, and nesting"

