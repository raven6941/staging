## Step 2: residual while loops, using the Step 1 Var/Unit machinery.

import staging/framework
import staging/traversal
import std/[os, osproc, strutils, times, tables]

type
  SumKind = enum skInput, skLit, skLe, skAdd, skDecl, skRead, skWrite,
    skSeq, skWhile
  SumNode = ref object of IRNode
    kind: SumKind
    name: string
    left, right: Rep[int]
    cond: Rep[bool]
    init: Rep[int]
    v: Var[int]
    val: Rep[int]
    a, b: Rep[Unit]

  SumSym[I, B, S, C] = object
    input: proc(name: string): I
    lit: proc(n: int): I
    le: proc(a, b: I): B
    add: proc(a, b: I): I
    unit: proc(): S
    whileLoop: proc(cond: proc(): B, body: proc(): S): S
    var_new: proc(init: I): C
    readVar: proc(v: C): I
    writeVar: proc(v: C, x: I): S
    seq: proc(a, b: S): S

  SumProgram[I, S, C] = object
    body: S
    result: I
    index, accumulator: C

proc directWhile(c: proc(): bool, body: proc(): Unit): Unit =
  while c(): discard body()
  Unit()

proc directNew(init: int): ref int =
  new(result)
  result[] = init

proc directSum(n: int): SumSym[int, bool, Unit, ref int] =
  SumSym[int, bool, Unit, ref int](
    input: proc(name: string): int = n,
    lit: proc(n: int): int = n,
    le: proc(a, b: int): bool = a <= b,
    add: proc(a, b: int): int = a + b,
    unit: proc(): Unit = Unit(),
    whileLoop: directWhile,
    var_new: directNew,
    readVar: proc(v: ref int): int = v[],
    writeVar: proc(v: ref int, x: int): Unit = (v[] = x; Unit()),
    seq: proc(a, b: Unit): Unit = Unit())

proc stagedSum(): SumSym[Rep[int], Rep[bool], Rep[Unit], Var[int]] =
  var varNumber = 0
  result = SumSym[Rep[int], Rep[bool], Rep[Unit], Var[int]](
    input: proc(name: string): Rep[int] =
      dynamic[int](SumNode(kind: skInput, name: name)),
    lit: proc(n: int): Rep[int] = liftNow(n),
    le: proc(a, b: Rep[int]): Rep[bool] =
      if a.isStatic and b.isStatic: liftNow(a.staticVal <= b.staticVal)
      else: dynamic[bool](SumNode(kind: skLe, left: a, right: b)),
    add: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x + y,
      proc(x, y: Rep[int]): IRNode = SumNode(kind: skAdd, left: x, right: y)),
    unit: proc(): Rep[Unit] = unit(),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] =
      smartWhile(c, body,
        proc(c: Rep[bool], b: Rep[Unit]): IRNode =
          SumNode(kind: skWhile, cond: c, b: b)),
    var_new: proc(init: Rep[int]): Var[int] =
      (inc varNumber; newVar[int](init,
        proc(init: Rep[int]): IRNode = SumNode(kind: skDecl,
          name: (if varNumber == 1: "i" else: "acc"), init: init))),
    readVar: proc(v: Var[int]): Rep[int] = readVar[int](v,
      proc(v: Var[int]): IRNode = SumNode(kind: skRead, v: v)),
    writeVar: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = SumNode(kind: skWrite, v: v, val: x)),
    seq: proc(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
      proc(a, b: Rep[Unit]): IRNode = SumNode(kind: skSeq, a: a, b: b)))

proc sumProgram[I, B, S, C](s: SumSym[I, B, S, C]): SumProgram[I, S, C] =
  let n = s.input("n")
  let index = s.var_new(s.lit(1))
  let accumulator = s.var_new(s.lit(0))
  let loop = s.whileLoop(
    proc(): B = s.le(s.readVar(index), n),
    proc(): S = s.seq(
      s.writeVar(accumulator, s.add(s.readVar(accumulator), s.readVar(index))),
      s.writeVar(index, s.add(s.readVar(index), s.lit(1))))
  )
  SumProgram[I, S, C](body: loop, result: s.readVar(accumulator),
    index: index, accumulator: accumulator)

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = SumNode(r.node)
  case n.kind
  of skInput: n.name
  of skAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of skRead: SumNode(n.v.node).name
  else: raise newException(ValueError, "not an int expression")

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = SumNode(r.node)
  doAssert n.kind == skLe
  "(" & emitInt(n.left) & " <= " & emitInt(n.right) & ")"

proc emitStmt(r: Rep[Unit], indent = ""): string =
  if r.isStatic: return indent & "discard"
  let n = SumNode(r.node)
  case n.kind
  of skSeq: emitStmt(n.a, indent) & "\n" & emitStmt(n.b, indent)
  of skWhile: indent & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b, indent & "  ")
  of skWrite: indent & SumNode(n.v.node).name & " = " & emitInt(n.val)
  else: raise newException(ValueError, "not a statement")

proc emitDecl(v: Var[int], name: string): string =
  let n = SumNode(v.node)
  doAssert n.kind == skDecl
  "var " & name & " = " & emitInt(n.init)

proc childNodes(n: SumNode): seq[SumNode] =
  case n.kind
  of skInput, skLit: discard
  of skLe:
    if not n.left.isStatic: result.add(SumNode(n.left.node))
    if not n.right.isStatic: result.add(SumNode(n.right.node))
  of skAdd:
    if not n.left.isStatic: result.add(SumNode(n.left.node))
    if not n.right.isStatic: result.add(SumNode(n.right.node))
  of skDecl:
    if not n.init.isStatic: result.add(SumNode(n.init.node))
  of skRead: result.add(SumNode(n.v.node))
  of skWrite:
    result.add(SumNode(n.v.node))
    if not n.val.isStatic: result.add(SumNode(n.val.node))
  of skSeq:
    if not n.a.isStatic: result.add(SumNode(n.a.node))
    if not n.b.isStatic: result.add(SumNode(n.b.node))
  of skWhile:
    if not n.cond.isStatic: result.add(SumNode(n.cond.node))
    if not n.b.isStatic: result.add(SumNode(n.b.node))

proc sumCallbacks(): TraversalCallbacks[SumNode] =
  TraversalCallbacks[SumNode](
    children: childNodes,
    key: proc(n: SumNode): string = $n.kind,
    isComposite: proc(n: SumNode): bool = true,
    isBoundary: proc(n: SumNode): bool = false,
    rebuild: proc(n: SumNode; kids: seq[SumNode]): SumNode = n,
    makeRef: proc(x: string): SumNode = SumNode(kind: skInput, name: x),
    makeLet: proc(x: string; a, b: SumNode): SumNode = a)

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim compiler not found on PATH"
  let r = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

when isMainModule:
  # Load-bearing check: without smartWhile this scanner-sum test cannot be
  # written through the staged Sym; with it, this test emits and runs it.
  var staticFalseBodyCalls = 0
  let folded = smartWhile(
    proc(): Rep[bool] = liftNow(false),
    proc(): Rep[Unit] = (inc staticFalseBodyCalls; unit()),
    proc(c: Rep[bool], b: Rep[Unit]): IRNode = SumNode(kind: skWhile, cond: c, b: b))
  doAssert folded.isStatic and staticFalseBodyCalls == 0

  var dynamicBodyCalls = 0
  discard smartWhile(
    proc(): Rep[bool] = dynamic[bool](SumNode(kind: skInput, name: "dynamic")),
    proc(): Rep[Unit] = (inc dynamicBodyCalls; unit()),
    proc(c: Rep[bool], b: Rep[Unit]): IRNode = SumNode(kind: skWhile, cond: c, b: b))
  doAssert dynamicBodyCalls == 1

  let staged = sumProgram(stagedSum())
  doAssert not staged.body.isStatic and not staged.result.isStatic
  let loopNode = SumNode(staged.body.node)
  doAssert loopNode.kind == skWhile
  # The while node is traversable: callbacks expose its condition and body.
  let seen = occurrences(loopNode, sumCallbacks())
  doAssert seen.getOrDefault("skWhile") == 1
  doAssert seen.getOrDefault("skLe") > 0 and seen.getOrDefault("skWrite") > 0
  # This tree contains var writes and is effectful; never feed it to
  # insertLets/insertLetsCb unless the DSL has proved the subtree pure.

  let bodyText = emitStmt(staged.body)
  doAssert "while" in bodyText
  for n in [0, 1, 2, 5, 10]:
    var expected = 0
    for i in 1 .. n: expected += i
    let direct = sumProgram(directSum(n))
    doAssert direct.result == expected
    let dir = getTempDir() / ("staging-while-" & $getCurrentProcessId() &
      "-" & $n & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let source = dir / "residual.nim"
    let exe = dir / "residual"
    writeFile(source, emitDecl(staged.index, "i") & "\n" &
      emitDecl(staged.accumulator, "acc") & "\nlet n = " & $n & "\n\n" &
      bodyText & "\necho " & emitInt(staged.result) & "\n")
    doAssert parseInt(compileRun(source, exe, dir)) == expected
    removeDir(dir)
  echo "ok: residual while folds, traverses, stages its body once, and codegens"
