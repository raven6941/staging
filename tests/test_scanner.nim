## Effectful staged scanner over a dynamic string, with runnable residual code.

import staging/framework
import staging/arrays
import staging/genlet
import staging/traversal
import std/[os, osproc, strutils, times, tables]

type
  DirectScanner = object
    text: string
    pos: int
    closed: bool

proc newDirectScanner(text: string): DirectScanner = DirectScanner(text: text)

proc next(s: var DirectScanner; delim: char): string =
  doAssert not s.closed
  let start = s.pos
  var stop = s.pos
  if delim == '\n':
    while stop < s.text.len and s.text[stop] != '\n': inc stop
  else:
    while stop < s.text.len and s.text[stop] != delim: inc stop
  result = s.text[start ..< stop]
  s.pos = stop
  if s.pos < s.text.len and (delim == '\n' or s.text[s.pos] == delim): inc s.pos

proc hasNext(s: DirectScanner): bool = not s.closed and s.pos < s.text.len
proc close(s: var DirectScanner) = s.closed = true

type
  ScannerKind = enum skInput, skNew, skNext, skHasNext, skClose, skVarDecl,
    skVarRead, skVarWrite, skSeq, skWhile, skArrDecl, skArrWrite, skArrRead,
    skArrLen, skAdd, skLt
  ScannerNode = ref object of IRNode
    kind: ScannerKind
    name: string
    text: Rep[string]
    scanner: Rep[int]
    delim: char
    pos: Var[int]
    init: Rep[int]
    left, right: Rep[int]
    cond: Rep[bool]
    a, b: Rep[Unit]
    arr: Arr[string]
    index: Rep[int]
    value: Rep[string]

proc scannerNew(text: Rep[string]): Rep[int] =
  let pos = newVar[int](liftNow(0), proc(init: Rep[int]): IRNode =
    ScannerNode(kind: skVarDecl, name: "scannerPos", init: init))
  dynamic[int](ScannerNode(kind: skNew, text: text, pos: pos))

proc scannerNext(s: Rep[int]; delim: char): Rep[string] =
  dynamic[string](ScannerNode(kind: skNext, scanner: s, delim: delim))

proc scannerHasNext(s: Rep[int]): Rep[bool] =
  dynamic[bool](ScannerNode(kind: skHasNext, scanner: s))

proc scannerClose(s: Rep[int]): Rep[Unit] =
  dynamic[Unit](ScannerNode(kind: skClose, scanner: s))

proc scannerText(s: Rep[int]): Rep[string] = ScannerNode(s.node).text

proc intAdd(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
  proc(x, y: int): int = x + y,
  proc(x, y: Rep[int]): IRNode = ScannerNode(kind: skAdd, left: x, right: y))

proc seqs(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
  proc(a, b: Rep[Unit]): IRNode = ScannerNode(kind: skSeq, a: a, b: b))

proc scannerArrayNew(len: Rep[int]): Arr[string] = newArray[string](len,
  proc(len: Rep[int]): IRNode = ScannerNode(kind: skArrDecl, name: "output", left: len))

proc scannerArrayWrite(a: Arr[string]; i: Rep[int]; x: Rep[string]): Rep[Unit] =
  writeArr[string](a, i, x, proc(a: Arr[string]; i: Rep[int]; x: Rep[string]): IRNode =
    ScannerNode(kind: skArrWrite, arr: a, index: i, value: x))

proc emitInt(r: Rep[int]): string

proc emitChar(c: char): string =
  case c
  of '\n': "'\\n'"
  of '\r': "'\\r'"
  of '\\': "'\\\\'"
  of '\'': "'\\''"
  else: "'" & $c & "'"

proc emitString(r: Rep[string]): string =
  if r.isStatic: return escape(r.staticVal)
  let n = ScannerNode(r.node)
  case n.kind
  of skInput: n.name
  of skNext:
    "scannerNext(" & emitString(scannerText(n.scanner)) & ", scannerPos, " & emitChar(n.delim) & ")"
  of skArrRead: ScannerNode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  else: raise newException(ValueError, "bad string expression: " & $n.kind)

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = ScannerNode(r.node)
  case n.kind
  of skAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of skVarRead: ScannerNode(n.pos.node).name
  of skArrLen: ScannerNode(n.arr.node).name & ".len"
  else: raise newException(ValueError, "bad int expression: " & $n.kind)

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = ScannerNode(r.node)
  case n.kind
  of skHasNext: "scannerPos < " & emitString(scannerText(n.scanner)) & ".len"
  of skLt: "(" & emitInt(n.left) & " < " & emitInt(n.right) & ")"
  else: raise newException(ValueError, "bad bool expression: " & $n.kind)

proc emitStmt(r: Rep[Unit]; indent = ""): string =
  if r.isStatic: return indent & "discard"
  let n = ScannerNode(r.node)
  case n.kind
  of skSeq: emitStmt(n.a, indent) & "\n" & emitStmt(n.b, indent)
  of skWhile: indent & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b, indent & "  ")
  of skArrWrite: indent & ScannerNode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitString(n.value)
  of skVarWrite: indent & ScannerNode(n.pos.node).name & " = " & emitInt(n.left)
  of skClose: indent & "scannerClose()"
  else: raise newException(ValueError, "bad statement: " & $n.kind)

proc emitDecl(v: Var[int]): string = "var " & ScannerNode(v.node).name & " = " & emitInt(ScannerNode(v.node).init)
proc emitDecl(a: Arr[string]): string = "var " & ScannerNode(a.node).name & " = newSeq[string](" & emitInt(ScannerNode(a.node).left) & ")"

proc childNodes(n: ScannerNode): seq[ScannerNode] =
  case n.kind
  of skInput: discard
  of skNew:
    if not n.text.isStatic: result.add(ScannerNode(n.text.node))
  of skNext, skHasNext, skClose: result.add(ScannerNode(n.scanner.node))
  of skVarDecl:
    if not n.init.isStatic: result.add(ScannerNode(n.init.node))
  of skVarRead: result.add(ScannerNode(n.pos.node))
  of skVarWrite:
    result.add(ScannerNode(n.pos.node))
    if not n.left.isStatic: result.add(ScannerNode(n.left.node))
  of skSeq:
    if not n.a.isStatic: result.add(ScannerNode(n.a.node))
    if not n.b.isStatic: result.add(ScannerNode(n.b.node))
  of skWhile:
    if not n.cond.isStatic: result.add(ScannerNode(n.cond.node))
    if not n.b.isStatic: result.add(ScannerNode(n.b.node))
  of skArrDecl:
    if not n.left.isStatic: result.add(ScannerNode(n.left.node))
  of skArrWrite:
    if not n.index.isStatic: result.add(ScannerNode(n.index.node))
    if not n.value.isStatic: result.add(ScannerNode(n.value.node))
    result.add(ScannerNode(n.arr.node))
  of skArrRead:
    if not n.index.isStatic: result.add(ScannerNode(n.index.node))
    result.add(ScannerNode(n.arr.node))
  of skArrLen: result.add(ScannerNode(n.arr.node))
  of skAdd, skLt:
    if not n.left.isStatic: result.add(ScannerNode(n.left.node))
    if not n.right.isStatic: result.add(ScannerNode(n.right.node))

proc scannerCallbacks(): TraversalCallbacks[ScannerNode] =
  TraversalCallbacks[ScannerNode](
    children: childNodes,
    key: proc(n: ScannerNode): string = $n.kind,
    isComposite: proc(n: ScannerNode): bool = true,
    isBoundary: proc(n: ScannerNode): bool = false,
    rebuild: proc(n: ScannerNode; kids: seq[ScannerNode]): ScannerNode = n,
    makeRef: proc(x: string): ScannerNode = ScannerNode(kind: skInput, name: x),
    # No-hoist by construction: the only genlet invocation in this test runs
    # over a tree of effectful nodes, and the test asserts ctx.counter == 0,
    # so makeLet is never invoked with a real hoist here.
    makeLet: proc(x: string; a, b: ScannerNode): ScannerNode = a,
    isPure: proc(n: ScannerNode): bool = n.kind notin {skNew, skNext, skHasNext, skClose, skVarWrite, skArrWrite})

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim compiler not found on PATH"
  let r = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

proc residualSource(csv: string; body: Rep[Unit]; scannerPos, index: Var[int]; output: Arr[string]; count: int): string =
  result = "proc scannerNext(text: string; pos: var int; delim: char): string =\n" &
    "  let start = pos\n  var stop = pos\n  while stop < text.len and text[stop] != delim: inc stop\n" &
    "  result = text[start ..< stop]\n  if stop < text.len: inc stop\n  pos = stop\n\n" &
    "proc scannerClose() = discard\n\n" &
    "let csv = " & escape(csv) & "\n" & emitDecl(scannerPos) & "\n" & emitDecl(index) & "\n" & emitDecl(output) & "\n" &
    emitStmt(body) & "\n"
  for i in 0 ..< count: result.add("echo output[" & $i & "]\n")

proc directFields(csv: string; delims: seq[char]): seq[string] =
  var s = newDirectScanner(csv)
  for d in delims: result.add(s.next(d))
  s.close()

proc stagedFields(csv: string; delims: seq[char]): seq[string] =
  let input = dynamic[string](ScannerNode(kind: skInput, name: "csv"))
  let scanner = scannerNew(input)
  let output = scannerArrayNew(liftNow(delims.len))
  var body = unit()
  for i, d in delims:
    body = seqs(body, scannerArrayWrite(output, liftNow(i), scannerNext(scanner, d)))
  let index = newVar[int](liftNow(0), proc(init: Rep[int]): IRNode =
    ScannerNode(kind: skVarDecl, name: "index", init: init))
  let sourceText = residualSource(csv, seqs(body, scannerClose(scanner)),
    ScannerNode(scanner.node).pos, index, output, delims.len)
  let dir = getTempDir() / ("staging-scanner-fields-" & $getCurrentProcessId() &
    "-" & $int(epochTime() * 1000))
  createDir(dir)
  writeFile(dir / "residual.nim", sourceText)
  result = compileRun(dir / "residual.nim", dir / "residual", dir).splitLines
  removeDir(dir)

when isMainModule:
  let csv = "Name,Value,Flag\nAda,42,true\n"
  var ds = newDirectScanner(csv)
  doAssert ds.hasNext()
  doAssert ds.next(',') == "Name"
  doAssert ds.hasNext()
  ds.close()
  doAssert not ds.hasNext()
  doAssert directFields(csv, @[',']) == @["Name"]
  doAssert directFields(csv, @[',', ',']) == @["Name", "Value"]
  doAssert directFields(csv, @['\n']) == @["Name,Value,Flag"]
  doAssert directFields(csv, @[',', ',', '\n']) == @["Name", "Value", "Flag"]
  doAssert directFields(csv, @[',', ',', '\n', ',']) == @["Name", "Value", "Flag", "Ada"]
  doAssert stagedFields(csv, @[',', ',']) == directFields(csv, @[',', ','])
  doAssert stagedFields(csv, @['\n']) == directFields(csv, @['\n'])
  doAssert stagedFields("solo", @['\n']) == @["solo"]

  let input = dynamic[string](ScannerNode(kind: skInput, name: "csv"))
  let scanner = scannerNew(input)
  let output = scannerArrayNew(liftNow(8))
  var index = newVar[int](liftNow(0), proc(init: Rep[int]): IRNode = ScannerNode(kind: skVarDecl, name: "index", init: init))
  let first = scannerNext(scanner, ',')
  let second = scannerNext(scanner, ',')
  doAssert first.node != second.node
  var two = seqs(scannerArrayWrite(output, liftNow(0), first), scannerArrayWrite(output, liftNow(1), second))
  let cb = scannerCallbacks()
  var ctx = newGenletCtx()
  discard insertLetsCb(ScannerNode(two.node), ctx, cb)
  doAssert ctx.counter == 0
  doAssert isEffectful(ScannerNode(first.node), cb)
  doAssert $ScannerNode(first.node).kind == "skNext" and $ScannerNode(second.node).kind == "skNext"
  doAssert emitStmt(two).count("scannerNext(") == 2

  let loopCsv = "Name,Value,Flag"
  let loopScanner = scannerNew(input)
  var body = unit()
  let loop = smartWhile(proc(): Rep[bool] = scannerHasNext(loopScanner), proc(): Rep[Unit] =
    seqs(scannerArrayWrite(output, readVar[int](index, proc(v: Var[int]): IRNode = ScannerNode(kind: skVarRead, pos: v)), scannerNext(loopScanner, ',')),
      writeVar[int](index, intAdd(readVar[int](index, proc(v: Var[int]): IRNode = ScannerNode(kind: skVarRead, pos: v)), liftNow(1)),
        proc(v: Var[int]; x: Rep[int]): IRNode = ScannerNode(kind: skVarWrite, pos: v, left: x))),
    proc(c: Rep[bool]; b: Rep[Unit]): IRNode = ScannerNode(kind: skWhile, cond: c, b: b))
  body = seqs(loop, scannerClose(loopScanner))
  let text = residualSource(loopCsv, body, ScannerNode(loopScanner.node).pos, index, output, 3)
  let dir = getTempDir() / ("staging-scanner-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  writeFile(dir / "residual.nim", text)
  let got = compileRun(dir / "residual.nim", dir / "residual", dir).splitLines
  doAssert got == @["Name", "Value", "Flag"]
  removeDir(dir)
  echo "ok: effectful staged scanner preserves order and scans dynamic CSV input"
