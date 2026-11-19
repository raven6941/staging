## Step 1: residual mutable variables, statements, and COUNT codegen.

import staging/framework
import staging/traversal
import std/[os, osproc, strutils, tables, times]

type
  Cell = ref object
    value: int
  CountKind = enum ckInput, ckGt, ckAnd, ckAdd, ckDecl, ckRead, ckWrite,
    ckSeq, ckIf
  CountNode = ref object of IRNode
    kind: CountKind
    name: string
    left, right: Rep[int]
    bl, br: Rep[bool]
    init: Rep[int]
    v: Var[int]
    val: Rep[int]
    a, b: Rep[Unit]
    cond: Rep[bool]
    thenB, elseB: Rep[Unit]
  CountSym[I, B, S, C] = object
    input: proc(name: string): I
    lit: proc(n: int): I
    gt: proc(a, b: I): B
    andB: proc(a, b: B): B
    add: proc(a, b: I): I
    unit: proc(): S
    ifB: proc(c: B, t, e: proc(): S): S
    var_new: proc(init: I): C
    readVar: proc(v: C): I
    writeVar: proc(v: C, x: I): S
    seq: proc(a, b: S): S
  CountProgram[I, S, C] = object
    body: S
    result: I
    cell: C

proc directCount(values: seq[int]): CountSym[int, bool, Unit, Cell] =
  CountSym[int, bool, Unit, Cell](
    input: proc(name: string): int =
      let idx = parseInt(name[3 .. ^1])
      if name.startsWith("age"): values[idx * 2]
      else: values[idx * 2 + 1],
    lit: proc(n: int): int = n,
    gt: proc(a, b: int): bool = a > b,
    andB: proc(a, b: bool): bool = a and b,
    add: proc(a, b: int): int = a + b,
    unit: proc(): Unit = Unit(),
    ifB: proc(c: bool, t, e: proc(): Unit): Unit = (if c: t() else: e()),
    var_new: proc(init: int): Cell = Cell(value: init),
    readVar: proc(v: Cell): int = v.value,
    writeVar: proc(v: Cell, x: int): Unit = (v.value = x; Unit()),
    seq: proc(a, b: Unit): Unit = Unit())

proc stagedCount(): CountSym[Rep[int], Rep[bool], Rep[Unit], Var[int]] =
  CountSym[Rep[int], Rep[bool], Rep[Unit], Var[int]](
    input: proc(name: string): Rep[int] =
      dynamic[int](CountNode(kind: ckInput, name: name)),
    lit: proc(n: int): Rep[int] = lift(n),
    gt: proc(a, b: Rep[int]): Rep[bool] =
      if a.isStatic and b.isStatic: lift(a.staticVal > b.staticVal)
      else: dynamic[bool](CountNode(kind: ckGt, left: a, right: b)),
    andB: proc(a, b: Rep[bool]): Rep[bool] =
      if a.isStatic and b.isStatic: lift(a.staticVal and b.staticVal)
      else: dynamic[bool](CountNode(kind: ckAnd, bl: a, br: b)),
    add: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x + y,
      proc(x, y: Rep[int]): IRNode = CountNode(kind: ckAdd, left: x, right: y)),
    unit: proc(): Rep[Unit] = unit(),
    ifB: proc(c: Rep[bool], t, e: proc(): Rep[Unit]): Rep[Unit] =
      smartIf[Unit](c, t, e,
        proc(c: Rep[bool], t, e: Rep[Unit]): IRNode =
          CountNode(kind: ckIf, cond: c, thenB: t, elseB: e)),
    var_new: proc(init: Rep[int]): Var[int] = newVar[int](init,
      proc(init: Rep[int]): IRNode = CountNode(kind: ckDecl, name: "count", init: init)),
    readVar: proc(v: Var[int]): Rep[int] = readVar[int](v,
      proc(v: Var[int]): IRNode = CountNode(kind: ckRead, v: v)),
    writeVar: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = CountNode(kind: ckWrite, v: v, val: x)),
    seq: proc(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
      proc(a, b: Rep[Unit]): IRNode = CountNode(kind: ckSeq, a: a, b: b)))

proc countProgram[I, B, S, C](s: CountSym[I, B, S, C]): CountProgram[I, S, C] =
  let acc = s.var_new(s.lit(0))
  var body = s.unit()
  for i in 0 .. 3:
    let pred = s.andB(s.gt(s.input("age" & $i), s.lit(30)),
      s.gt(s.input("sal" & $i), s.lit(50_000)))
    let stmt = s.ifB(pred,
      proc(): S = s.writeVar(acc, s.add(s.readVar(acc), s.lit(1))),
      proc(): S = s.unit())
    body = s.seq(body, stmt)
  CountProgram[I, S, C](body: body, result: s.readVar(acc), cell: acc)

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = CountNode(r.node)
  case n.kind
  of ckInput: n.name
  of ckAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of ckRead: CountNode(n.v.node).name
  else: raise newException(ValueError, "not an int expression")

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = CountNode(r.node)
  case n.kind
  of ckGt: "(" & emitInt(n.left) & " > " & emitInt(n.right) & ")"
  of ckAnd: "(" & emitBool(n.bl) & " and " & emitBool(n.br) & ")"
  else: raise newException(ValueError, "not a bool expression")

proc emitStmt(r: Rep[Unit]): string =
  if r.isStatic: return "discard"
  let n = CountNode(r.node)
  case n.kind
  of ckSeq: emitStmt(n.a) & "\n" & emitStmt(n.b)
  of ckIf: "if " & emitBool(n.cond) & ":\n  " & emitStmt(n.thenB) &
    "\nelse:\n  " & emitStmt(n.elseB)
  of ckWrite: CountNode(n.v.node).name & " = " & emitInt(n.val)
  else: raise newException(ValueError, "not a statement")

proc emitDecl(v: Var[int]): string =
  let n = CountNode(v.node)
  doAssert n.kind == ckDecl
  "var " & n.name & " = " & emitInt(n.init)

proc childNodes(n: CountNode): seq[CountNode] =
  # No nested helpers: a seq `result` cannot be captured by a closure.
  case n.kind
  of ckInput: discard
  of ckGt:
    if not n.left.isStatic: result.add(CountNode(n.left.node))
    if not n.right.isStatic: result.add(CountNode(n.right.node))
  of ckAnd:
    if not n.bl.isStatic: result.add(CountNode(n.bl.node))
    if not n.br.isStatic: result.add(CountNode(n.br.node))
  of ckAdd:
    if not n.left.isStatic: result.add(CountNode(n.left.node))
    if not n.right.isStatic: result.add(CountNode(n.right.node))
  of ckDecl:
    if not n.init.isStatic: result.add(CountNode(n.init.node))
  of ckRead: result.add(CountNode(n.v.node))
  of ckWrite:
    result.add(CountNode(n.v.node))
    if not n.val.isStatic: result.add(CountNode(n.val.node))
  of ckSeq:
    if not n.a.isStatic: result.add(CountNode(n.a.node))
    if not n.b.isStatic: result.add(CountNode(n.b.node))
  of ckIf:
    if not n.cond.isStatic: result.add(CountNode(n.cond.node))
    if not n.thenB.isStatic: result.add(CountNode(n.thenB.node))
    if not n.elseB.isStatic: result.add(CountNode(n.elseB.node))

proc countCallbacks(): TraversalCallbacks[CountNode] =
  TraversalCallbacks[CountNode](
    children: childNodes,
    key: proc(n: CountNode): string = $n.kind,
    isComposite: proc(n: CountNode): bool = true,
    isBoundary: proc(n: CountNode): bool = false,
    rebuild: proc(n: CountNode; kids: seq[CountNode]): CountNode = n,
    makeRef: proc(x: string): CountNode = CountNode(kind: ckInput, name: x),
    makeLet: proc(x: string; a, b: CountNode): CountNode = a)

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let r = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

when isMainModule:
  let values = @[25, 60000, 40, 45000, 35, 80000, 50, 90000]
  let direct = countProgram(directCount(values))
  doAssert direct.result == 2, "COUNT expected two matching rows"
  let staged = countProgram(stagedCount())
  doAssert not staged.result.isStatic
  let decl = CountNode(staged.cell.node)
  doAssert decl.kind == ckDecl and decl.init.isStatic and decl.init.staticVal == 0

  # Var-bearing residuals are effectful; never feed this tree to insertLets/
  # insertLetsCb unless the DSL has proved it pure.
  let seen = occurrences(CountNode(staged.body.node), countCallbacks())
  doAssert seen.getOrDefault("ckDecl") > 0 and seen.getOrDefault("ckWrite") > 0 and seen.getOrDefault("ckIf") > 0

  let dir = getTempDir() / ("staging-vars-" & $getCurrentProcessId() & "-" &
    $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  var src = emitDecl(staged.cell) & "\n"
  for i in 0 .. 3: src.add("let age" & $i & " = " & $values[i * 2] & "\n")
  for i in 0 .. 3: src.add("let sal" & $i & " = " & $values[i * 2 + 1] & "\n")
  src.add("\n" & emitStmt(staged.body) & "\necho count\n")
  writeFile(source, src)
  doAssert parseInt(compileRun(source, exe, dir)) == direct.result
  removeDir(dir)
  echo "ok: residual vars, Rep[Unit] sequencing, traversal, and COUNT codegen"
