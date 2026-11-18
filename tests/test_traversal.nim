## Regression tests for the generic traversal API.

import std/[os, osproc, strutils, tables, times]
import staging/genlet
import staging/traversal

proc num(t: GTree): int = parseInt(t.name)

proc eval(t: GTree; env: Table[string, int]): int =
  case t.kind
  of gkAtom:
    try: parseInt(t.name)
    except ValueError: env[t.name]
  of gkNode:
    case t.op
    of "add": eval(t.children[0], env) + eval(t.children[1], env)
    of "sub": eval(t.children[0], env) - eval(t.children[1], env)
    of "mul": eval(t.children[0], env) * eval(t.children[1], env)
    else: raise newException(ValueError, t.op)
  of gkLet:
    var e = env
    e[t.binder] = eval(t.bound, env)
    eval(t.body, e)

proc rewrite(t: GTree): GTree =
  if t.kind == gkNode and t.op == "add":
    let a = t.children[0]
    let b = t.children[1]
    if a.kind == gkNode and a.op == "add":
      return gnode("add", @[a.children[0], gnode("add", @[a.children[1], b])])
    if a.kind == gkAtom and b.kind == gkAtom:
      try: return gatom($(num(a) + num(b)))
      except ValueError: discard
  t

proc nimExpr(t: GTree): string =
  case t.kind
  of gkAtom: t.name
  of gkNode:
    "(" & nimExpr(t.children[0]) & " " &
      (if t.op == "add": "+" elif t.op == "sub": "-" else: "*") &
      " " & nimExpr(t.children[1]) & ")"
  of gkLet: "(block: let " & t.binder & " = " & nimExpr(t.bound) &
    "; " & nimExpr(t.body) & ")"

proc emittedValue(t: GTree; expected: int): bool =
  let dir = getTempDir() / ("staging-traversal-" & $getCurrentProcessId() &
    "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  var main = "when isMainModule:\n"
  if t.kind == gkLet:
    main &= "  let " & t.binder & " = " & nimExpr(t.bound) & "\n"
    main &= "  echo " & nimExpr(t.body) & "\n"
  else:
    main &= "  echo " & nimExpr(t) & "\n"
  writeFile(source, "let x = 4\nlet a2 = 2\nlet a3 = 3\n" & main)
  let c = execCmdEx("nim c --hints:off --nimcache:" & quoteShell(dir / "cache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source),
    {poUsePath, poStdErrToStdOut}, workingDir = dir)
  if c.exitCode != 0: removeDir(dir); return false
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut},
    workingDir = dir)
  removeDir(dir)
  r.exitCode == 0 and parseInt(r.output.strip) == expected

when isMainModule:
  let cb = gtreeCallbacks()
  let original = gnode("add", @[
    gnode("add", @[gatom("x"), gatom("1")]), gatom("2")])
  let mapped = mapTree(original, cb, rewrite)
  doAssert $mapped == "add(x, add(1, 2))"
  doAssert eval(original, {"x": 4}.toTable) == eval(mapped, {"x": 4}.toTable)
  doAssert emittedValue(mapped, 7)

  # The constant-folding arm of the rule fires where both children are
  # already atoms: (1 + 2) + x folds the inner addition to 3.
  let foldable = gnode("add", @[
    gnode("add", @[gatom("1"), gatom("2")]), gatom("x")])
  let folded = mapTree(foldable, cb, rewrite)
  doAssert $folded == "add(3, x)"
  doAssert eval(folded, {"x": 4}.toTable) == 7
  doAssert emittedValue(folded, 7)

  # Two separately-built residuals share t. The client pass finds the
  # overlap by intersecting occurrence counts, binds each shared key
  # once at their common root, and substitutes references. (The bound
  # sample comes from this demo's own construction; a real pass collects
  # samples alongside counts, as genlet does.)
  let t = gnode("mul", @[gatom("a2"), gatom("a3")])
  let wm2 = gnode("sub", @[gatom("a2"), t])
  let wm3 = gnode("sub", @[gatom("a3"), t])
  let b2 = gnode("mul", @[wm2, t])
  let b3 = gnode("add", @[wm3, t])
  let f2 = occurrences(b2, cb)
  let f3 = occurrences(b3, cb)
  var sharedKeys: seq[string] = @[]
  for k in f2.keys:
    if k in f3: sharedKeys.add(k)
  doAssert sharedKeys.len == 1 and sharedKeys[0] == $t,
    "exactly one shared composite expected, got: " & $sharedKeys
  var replacements = initTable[string, GTree]()
  for k in sharedKeys:
    replacements[k] = gatom("sharedT")
  let combined = gnode("add", @[
    substTree(b2, cb, replacements), substTree(b3, cb, replacements)])
  let residual = glet("sharedT", t, combined)
  let env = {"a2": 2, "a3": 3}.toTable
  doAssert eval(residual, env) == -21
  doAssert count($residual, "mul(a2, a3)") == 1
  doAssert count($residual, "sub(a2, sharedT)") == 1
  doAssert count($residual, "sub(a3, sharedT)") == 1
  doAssert emittedValue(residual, -21)

  # A replacement mentioning an intervening binder is refused.
  let scoped = glet("x", gatom("1"), gnode("add", @[gatom("y"), gatom("2")]))
  var bad = initTable[string, GTree]()
  bad["y"] = gatom("x")
  doAssert $substTree(scoped, cb, bad) == $scoped
  echo "ok: traversal rewrite, overlap sharing, emitted execution, and hygiene"
