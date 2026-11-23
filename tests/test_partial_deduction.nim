## Step-5 verdict: SpecCtx saves the client 13 lines of bookkeeping and makes
## memoization, fuel exhaustion, recursion guarding, and the dynamic-variable
## contract consistent.  The relation-specific specialization remains client
## code; the skeleton is therefore small, but it is used and earns its place.

import std/[os, osproc, sets, strutils, tables, times]
import staging/specctx

type
  TermKind = enum tkVar, tkNil, tkCons, tkInt
  Term = ref object
    kind: TermKind
    value: int
    name: string
    head, tail: Term

  AppendoEnv = object
    first: Term

proc tv(name: string): Term = Term(kind: tkVar, name: name)
proc tn(): Term = Term(kind: tkNil)
proc ti(value: int): Term = Term(kind: tkInt, value: value)
proc tc(head, tail: Term): Term = Term(kind: tkCons, head: head, tail: tail)

proc listTerm(values: openArray[int]): Term =
  result = tn()
  for i in countdown(values.high, 0): result = tc(ti(values[i]), result)

proc `$`(term: Term): string =
  case term.kind
  of tkVar: term.name
  of tkNil: "[]"
  of tkInt: $term.value
  of tkCons: "(" & $term.head & ":" & $term.tail & ")"

proc signature(env: AppendoEnv): string = $env.first

proc directRun(xs, ys, zs: seq[int]): bool = xs & ys == zs

type Residual = object
  source: string
  shape: string

proc specialize(ctx: SpecCtx[AppendoEnv, string, Residual]; first: Term;
    dynamicVars: HashSet[string]): Residual =
  let env = AppendoEnv(first: first)
  let (state, key) = ctx.begin(env, dynamicVars)
  case state
  of ssCached: return ctx.memo[key]
  of ssRecursive, ssOutOfFuel:
    return Residual(source: "fallback", shape: "fallback")
  of ssNew: discard

  try:
    if first.kind == tkVar:
      result = Residual(source: "fallback", shape: "fallback")
    else:
      var values: seq[int] = @[]
      var cursor = first
      while cursor.kind == tkCons:
        doAssert cursor.head.kind == tkInt
        values.add(cursor.head.value)
        cursor = cursor.tail
      doAssert cursor.kind == tkNil
      var checks = ""
      for i, value in values:
        if i > 0: checks.add(" and ")
        checks.add("zs[" & $i & "] == " & $value)
      if checks.len == 0: checks = "true"
      result = Residual(
        source: "proc residual(ys, zs: seq[int]): bool =\n" &
          "  zs.len >= " & $values.len & " and " & checks &
          " and ys == zs[" & $values.len & "..<zs.len]",
        shape: key)
    ctx.finish(key, result)
  except:
    ctx.abort(key)
    raise

proc compileAndRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0
  createDir(dir / "nimcache")
  let compiled = execCmdEx(
    quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
      " --out:" & quoteShell(exe) & " " & quoteShell(source),
    {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert compiled.exitCode == 0, compiled.output
  let ran = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert ran.exitCode == 0, ran.output
  ran.output.strip

proc checkResidual(residual: Residual; xs, ys, zs: seq[int]; expected: bool) =
  let dir = getTempDir() / ("staging-partial-" & $getCurrentProcessId() &
    "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  let body = if residual.source == "fallback":
      "proc appendoEngine(xs, ys, zs: seq[int]): bool = xs & ys == zs\n" &
        "proc residual(xs, ys, zs: seq[int]): bool = appendoEngine(xs, ys, zs)\n" &
        "echo residual(" & $xs & ", " & $ys & ", " & $zs & ")"
    else:
      residual.source & "\necho residual(" & $ys & ", " & $zs & ")"
  writeFile(source, "import std/sequtils\n" & body & "\n")
  doAssert parseBool(compileAndRun(source, exe, dir)) == expected
  removeDir(dir)

when isMainModule:
  let dynamicVars = ["ys", "zs"].toHashSet
  var ctx = newSpecCtx[AppendoEnv, string, Residual](
    AppendoEnv(first: tn()), signature, 8, dynamicVars)
  let ground = listTerm([1, 2])
  let ys = @[3]
  let zs = @[1, 2, 3]
  let specialized = specialize(ctx, ground, dynamicVars)
  doAssert specialized.shape == "(1:(2:[]))"
  doAssert directRun(@[1, 2], ys, zs)
  checkResidual(specialized, @[1, 2], ys, zs, true)
  checkResidual(specialized, @[1, 2], ys, @[1, 2, 4], false)
  doAssert not directRun(@[1, 2], ys, @[1, 2, 4])
  echo "ok: ground appendo statically unrolls one residual per list shape"

  let cached = specialize(ctx, ground, dynamicVars)
  doAssert cached.source == specialized.source
  doAssert ctx.memo.len == 1
  doAssert ctx.fuel == 7
  echo "ok: SpecCtx memoizes the ground static signature"

  let dynamic = specialize(ctx, tv("xs"), dynamicVars)
  doAssert dynamic.shape == "fallback"
  doAssert directRun(@[1], ys, @[1, 3])
  checkResidual(dynamic, @[1], ys, @[1, 3], true)
  echo "ok: non-ground appendo uses the unstaged fallback relation"

  var exhausted = newSpecCtx[AppendoEnv, string, Residual](
    AppendoEnv(first: tn()), signature, 0, dynamicVars)
  doAssert specialize(exhausted, listTerm([4]), dynamicVars).shape == "fallback"
  echo "ok: SpecCtx fuel and dynamic-variable soundness guard specialization"
