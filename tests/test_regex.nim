## End-to-end staged Pike/Kernighan regular-expression matcher.
##
## The staged matcher follows the LMS tutorial: the pattern and all pattern
## indices are static, while the input and results are residual.  The
## framework has no implicit statement sequencing, so the matcher threads
## statement/value pairs explicitly.  Star vars are declared hoisted with
## dummy initializers, then initialized at entry because matchStar is
## re-entered.  Loop-carried `start`/`found` and `sstart`/`found`/`failed` are
## explicit framework `Var` cells.

import staging/framework
import std/[os, osproc, strutils, times]

type
  RegexPair[B, S] = object
    stmts: S
    val: B
  RegexCell[T] = ref object
    value: T
  RegexKind = enum rkInput, rkTextLen, rkCharAt, rkCharEq, rkLt, rkAdd,
    rkEqInt, rkEqBool, rkAnd, rkOr, rkNot, rkDeclInt, rkDeclBool,
    rkReadInt, rkReadBool, rkWriteInt, rkWriteBool, rkSeq, rkIf, rkWhile
  RegexNode = ref object of IRNode
    kind: RegexKind
    name: string
    c: char
    left, right: Rep[int]
    bl, br: Rep[bool]
    text: Rep[string]
    index: Rep[int]
    chr: Rep[char]
    initInt: Rep[int]
    initBool: Rep[bool]
    intVar: Var[int]
    boolVar: Var[bool]
    intVal: Rep[int]
    boolVal: Rep[bool]
    a, b: Rep[Unit]
    cond: Rep[bool]
    thenB, elseB: Rep[Unit]
    thenStmts, elseStmts: Rep[Unit]
  RegexSym[T, I, B, S, CI, CB, Ch] = object
    input: proc(name: string): T
    litInt: proc(n: int): I
    litBool: proc(v: bool): B
    lt: proc(a, b: I): B
    add: proc(a, b: I): I
    eqInt: proc(a, b: I): B
    andB: proc(a, b: B): B
    orB: proc(a, b: B): B
    notB: proc(a: B): B
    selectB: proc(c: B, t, e: proc(): RegexPair[B, S]): RegexPair[B, S]
    textLen: proc(t: T): I
    charAt: proc(t: T, i: I): Ch
    charEq: proc(c: char, t: Ch): B
    unit: proc(): S
    ifB: proc(c: B, t, e: proc(): S): S
    whileLoop: proc(c: proc(): B, body: proc(): S): S
    varNewInt: proc(init: I): CI
    varNewBool: proc(init: B): CB
    readInt: proc(v: CI): I
    readBool: proc(v: CB): B
    writeInt: proc(v: CI, x: I): S
    writeBool: proc(v: CB, x: B): S
    seq: proc(a, b: S): S
proc directSym(text: string): RegexSym[string, int, bool, Unit, RegexCell[int], RegexCell[bool], char] =
  RegexSym[string, int, bool, Unit, RegexCell[int], RegexCell[bool], char](
    input: proc(name: string): string = text,
    litInt: proc(n: int): int = n,
    litBool: proc(v: bool): bool = v,
    lt: proc(a, b: int): bool = a < b,
    add: proc(a, b: int): int = a + b,
    eqInt: proc(a, b: int): bool = a == b,
    andB: proc(a, b: bool): bool = a and b,
    orB: proc(a, b: bool): bool = a or b,
    notB: proc(a: bool): bool = not a,
    selectB: proc(c: bool, t, e: proc(): RegexPair[bool, Unit]): RegexPair[bool, Unit] =
      (if c: t() else: e()),
    textLen: proc(t: string): int = t.len,
    charAt: proc(t: string, i: int): char = t[i],
    charEq: proc(c: char, t: char): bool = c == '.' or c == t,
    unit: proc(): Unit = Unit(),
    ifB: proc(c: bool, t, e: proc(): Unit): Unit = (if c: t() else: e()),
    whileLoop: proc(c: proc(): bool, body: proc(): Unit): Unit =
      (while c(): discard body(); Unit()),
    varNewInt: proc(init: int): RegexCell[int] = RegexCell[int](value: init),
    varNewBool: proc(init: bool): RegexCell[bool] = RegexCell[bool](value: init),
    readInt: proc(v: RegexCell[int]): int = v.value,
    readBool: proc(v: RegexCell[bool]): bool = v.value,
    writeInt: proc(v: RegexCell[int], x: int): Unit = (v.value = x; Unit()),
    writeBool: proc(v: RegexCell[bool], x: bool): Unit = (v.value = x; Unit()),
    seq: proc(a, b: Unit): Unit = Unit())

type RegexDeclKind = enum rdkInt, rdkBool
type RegexDecl = ref object
  kind: RegexDeclKind
  name: string
  initInt: Rep[int]
  initBool: Rep[bool]
type RegexStageState = ref object
  nextId: int
  decls: seq[RegexDecl]

proc stagedSym(state: RegexStageState): RegexSym[Rep[string], Rep[int], Rep[bool], Rep[Unit],
    Var[int], Var[bool], Rep[char]] =
  RegexSym[Rep[string], Rep[int], Rep[bool], Rep[Unit], Var[int], Var[bool], Rep[char]](
    input: proc(name: string): Rep[string] = dynamic[string](RegexNode(kind: rkInput, name: name)),
    litInt: proc(n: int): Rep[int] = liftNow(n),
    litBool: proc(v: bool): Rep[bool] = liftNow(v),
    lt: proc(a, b: Rep[int]): Rep[bool] =
      if a.isStatic and b.isStatic: liftNow(a.staticVal < b.staticVal)
      else: dynamic[bool](RegexNode(kind: rkLt, left: a, right: b)),
    add: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x + y,
      proc(x, y: Rep[int]): IRNode = RegexNode(kind: rkAdd, left: x, right: y)),
    eqInt: proc(a, b: Rep[int]): Rep[bool] =
      if a.isStatic and b.isStatic: liftNow(a.staticVal == b.staticVal)
      else: dynamic[bool](RegexNode(kind: rkEqInt, left: a, right: b)),
    andB: proc(a, b: Rep[bool]): Rep[bool] = smartOp[bool](a, b,
      proc(x, y: bool): bool = x and y,
      proc(x, y: Rep[bool]): IRNode = RegexNode(kind: rkAnd, bl: x, br: y)),
    orB: proc(a, b: Rep[bool]): Rep[bool] = smartOp[bool](a, b,
      proc(x, y: bool): bool = x or y,
      proc(x, y: Rep[bool]): IRNode = RegexNode(kind: rkOr, bl: x, br: y)),
    notB: proc(a: Rep[bool]): Rep[bool] = smartOpUni[bool](a,
      proc(x: bool): bool = not x,
      proc(x: Rep[bool]): IRNode = RegexNode(kind: rkNot, bl: x)),
    selectB: proc(c: Rep[bool], t, e: proc(): RegexPair[Rep[bool], Rep[Unit]]): RegexPair[Rep[bool], Rep[Unit]] =
      if c.isStatic: (if c.staticVal: t() else: e())
      else:
        let tp = t()
        let ep = e()
        RegexPair[Rep[bool], Rep[Unit]](
          stmts: unit(),
          val: dynamic[bool](RegexNode(kind: rkIf, cond: c, bl: tp.val, br: ep.val,
            thenStmts: tp.stmts, elseStmts: ep.stmts))),
    textLen: proc(t: Rep[string]): Rep[int] = dynamic[int](RegexNode(kind: rkTextLen, text: t)),
    charAt: proc(t: Rep[string], i: Rep[int]): Rep[char] = dynamic[char](RegexNode(kind: rkCharAt, text: t, index: i)),
    charEq: proc(c: char, t: Rep[char]): Rep[bool] =
      if c == '.': liftNow(true)
      elif t.isStatic: liftNow(c == t.staticVal)
      else: dynamic[bool](RegexNode(kind: rkCharEq, c: c, chr: t)),
    unit: proc(): Rep[Unit] = unit(),
    ifB: proc(c: Rep[bool], t, e: proc(): Rep[Unit]): Rep[Unit] = smartIf[Unit](c, t, e,
      proc(c: Rep[bool], t, e: Rep[Unit]): IRNode = RegexNode(kind: rkIf, cond: c, thenB: t, elseB: e)),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] = smartWhile(c, body,
      proc(c: Rep[bool], b: Rep[Unit]): IRNode = RegexNode(kind: rkWhile, cond: c, b: b)),
    varNewInt: proc(init: Rep[int]): Var[int] = (inc state.nextId; let v = Var[int](node: RegexNode(kind: rkDeclInt, name: "v" & $state.nextId, initInt: init)); state.decls.add(RegexDecl(kind: rdkInt, name: "v" & $state.nextId, initInt: init)); v),
    varNewBool: proc(init: Rep[bool]): Var[bool] = (inc state.nextId; let v = Var[bool](node: RegexNode(kind: rkDeclBool, name: "v" & $state.nextId, initBool: init)); state.decls.add(RegexDecl(kind: rdkBool, name: "v" & $state.nextId, initBool: init)); v),
    readInt: proc(v: Var[int]): Rep[int] = readVar[int](v, proc(v: Var[int]): IRNode = RegexNode(kind: rkReadInt, intVar: v)),
    readBool: proc(v: Var[bool]): Rep[bool] = readVar[bool](v, proc(v: Var[bool]): IRNode = RegexNode(kind: rkReadBool, boolVar: v)),
    writeInt: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x, proc(v: Var[int], x: Rep[int]): IRNode = RegexNode(kind: rkWriteInt, intVar: v, intVal: x)),
    writeBool: proc(v: Var[bool], x: Rep[bool]): Rep[Unit] = writeVar[bool](v, x, proc(v: Var[bool], x: Rep[bool]): IRNode = RegexNode(kind: rkWriteBool, boolVar: v, boolVal: x)),
    seq: proc(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b, proc(a, b: Rep[Unit]): IRNode = RegexNode(kind: rkSeq, a: a, b: b)))

proc matchStar[T, I, B, S, CI, CB, Ch](s: RegexSym[T, I, B, S, CI, CB, Ch], c: char,
    regexp: string, restart: int, text: T, start: I): RegexPair[B, S]

proc matchHere[T, I, B, S, CI, CB, Ch](s: RegexSym[T, I, B, S, CI, CB, Ch], regexp: string,
    restart: int, text: T, start: I): RegexPair[B, S] =
  if restart == regexp.len: RegexPair[B, S](stmts: s.unit(), val: s.litBool(true))
  elif regexp[restart] == '$' and restart + 1 == regexp.len:
    RegexPair[B, S](stmts: s.unit(), val: s.eqInt(start, s.textLen(text)))
  elif restart + 1 < regexp.len and regexp[restart + 1] == '*':
    matchStar(s, regexp[restart], regexp, restart + 2, text, start)
  else:
    s.selectB(s.lt(start, s.textLen(text)),
      proc(): RegexPair[B, S] = s.selectB(s.charEq(regexp[restart], s.charAt(text, start)),
        proc(): RegexPair[B, S] = matchHere(s, regexp, restart + 1, text, s.add(start, s.litInt(1))),
        proc(): RegexPair[B, S] = RegexPair[B, S](stmts: s.unit(), val: s.litBool(false))),
      proc(): RegexPair[B, S] = RegexPair[B, S](stmts: s.unit(), val: s.litBool(false)))

proc matchStar[T, I, B, S, CI, CB, Ch](s: RegexSym[T, I, B, S, CI, CB, Ch], c: char,
    regexp: string, restart: int, text: T, start: I): RegexPair[B, S] =
  let sstart = s.varNewInt(s.litInt(0))
  let found = s.varNewBool(s.litBool(false))
  let failed = s.varNewBool(s.litBool(false))
  let startWrite = s.writeInt(sstart, start)
  let initial = matchHere(s, regexp, restart, text, s.readInt(sstart))
  let entry = s.seq(startWrite,
    s.seq(initial.stmts, s.seq(s.writeBool(found, initial.val),
      s.writeBool(failed, s.litBool(false)))))
  let loop = s.whileLoop(
    proc(): B = s.andB(s.andB(s.notB(s.readBool(failed)), s.notB(s.readBool(found))),
      s.lt(s.readInt(sstart), s.textLen(text))),
    proc(): S =
      let failedWrite = s.writeBool(failed, s.notB(s.charEq(c, s.charAt(text, s.readInt(sstart)))))
      let increment = s.writeInt(sstart, s.add(s.readInt(sstart), s.litInt(1)))
      let inner = matchHere(s, regexp, restart, text, s.readInt(sstart))
      s.seq(
      failedWrite,
      s.seq(increment,
        s.seq(inner.stmts, s.writeBool(found, inner.val))))
  )
  RegexPair[B, S](stmts: s.seq(entry, loop), val: s.andB(s.notB(s.readBool(failed)), s.readBool(found)))

proc regexProgram[T, I, B, S, CI, CB, Ch](s: RegexSym[T, I, B, S, CI, CB, Ch], regexp: string, text: T): RegexPair[B, S] =
  if regexp[0] == '^':
    let p = matchHere(s, regexp, 1, text, s.litInt(0))
    RegexPair[B, S](stmts: p.stmts, val: p.val)
  else:
    let start = s.varNewInt(s.litInt(-1))
    let found = s.varNewBool(s.litBool(false))
    let body = s.whileLoop(
      proc(): B = s.andB(s.notB(s.readBool(found)), s.lt(s.readInt(start), s.textLen(text))),
      proc(): S =
        let increment = s.writeInt(start, s.add(s.readInt(start), s.litInt(1)))
        let p = matchHere(s, regexp, 0, text, s.readInt(start))
        s.seq(increment,
          s.seq(p.stmts, s.writeBool(found, p.val))))
    RegexPair[B, S](stmts: body, val: s.readBool(found))

proc regexMatch[T, I, B, S, CI, CB, Ch](s: RegexSym[T, I, B, S, CI, CB, Ch], regexp: string, text: T): B =
  regexProgram(s, regexp, text).val

proc emitChar(c: char): string =
  case c
  of '\\': "'\\\\'"
  of '\'': "'\\''"
  of '\n': "'\\n'"
  else: "'" & $c & "'"

proc emitText(r: Rep[string]): string

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = RegexNode(r.node)
  case n.kind
  of rkInput: raise newException(ValueError, "not an int expression: " & $n.kind)
  of rkTextLen: emitText(n.text) & ".len"
  of rkCharAt: raise newException(ValueError, "not an int expression: " & $n.kind)
  of rkAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of rkReadInt: RegexNode(Var[int](n.intVar).node).name
  else: raise newException(ValueError, "not an int expression: " & $n.kind)

proc emitText(r: Rep[string]): string =
  if r.isStatic: return "\"\""
  "text"

proc emitCharExpr(r: Rep[char]): string =
  if r.isStatic: return emitChar(r.staticVal)
  let n = RegexNode(r.node)
  doAssert n.kind == rkCharAt
  emitText(n.text) & "[" & emitInt(n.index) & "]"

proc emitStmt(r: Rep[Unit], indent = ""): string

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = RegexNode(r.node)
  case n.kind
  of rkLt: "(" & emitInt(n.left) & " < " & emitInt(n.right) & ")"
  of rkEqInt: "(" & emitInt(n.left) & " == " & emitInt(n.right) & ")"
  of rkEqBool: "(" & emitBool(n.bl) & " == " & emitBool(n.br) & ")"
  of rkAnd: "(" & emitBool(n.bl) & " and " & emitBool(n.br) & ")"
  of rkOr: "(" & emitBool(n.bl) & " or " & emitBool(n.br) & ")"
  of rkNot: "(not " & emitBool(n.bl) & ")"
  of rkIf:
    if n.thenStmts.isStatic and n.elseStmts.isStatic:
      "(if " & emitBool(n.cond) & ": " & emitBool(n.bl) & " else: " & emitBool(n.br) & ")"
    else:
      "(if " & emitBool(n.cond) & ":\n" & emitStmt(n.thenStmts, "  ") & "\n  " & emitBool(n.bl) &
        "\nelse:\n" & emitStmt(n.elseStmts, "  ") & "\n  " & emitBool(n.br) & ")"
  of rkCharEq: "(" & emitChar(n.c) & " == " & emitCharExpr(n.chr) & ")"
  of rkReadBool: RegexNode(Var[bool](n.boolVar).node).name
  else: raise newException(ValueError, "not a bool expression: " & $n.kind)

proc emitStmt(r: Rep[Unit], indent = ""): string =
  if r.isStatic: return indent & "discard"
  let n = RegexNode(r.node)
  case n.kind
  of rkSeq: emitStmt(n.a, indent) & "\n" & emitStmt(n.b, indent)
  of rkWriteInt: indent & RegexNode(Var[int](n.intVar).node).name & " = " & emitInt(n.intVal)
  of rkWriteBool: indent & RegexNode(Var[bool](n.boolVar).node).name & " = " & emitBool(n.boolVal)
  of rkIf: indent & "if " & emitBool(n.cond) & ":\n" & emitStmt(n.thenB, indent & "  ") &
    "\n" & indent & "else:\n" & emitStmt(n.elseB, indent & "  ")
  of rkWhile: indent & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b, indent & "  ")
  else: raise newException(ValueError, "not a statement: " & $n.kind)

proc emitDecl(d: RegexDecl): string =
  if d.kind == rdkInt: "var " & d.name & " = " & emitInt(d.initInt)
  else: "var " & d.name & " = " & emitBool(d.initBool)

proc compileRun(source, exe, dir, input: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim compiler not found on PATH"
  if not fileExists(exe):
    let r = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
      " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
    doAssert r.exitCode == 0, r.output
  let run = execCmdEx(quoteShell(exe) & " " & quoteShell(input), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

type CachedRegex = ref object
  dir, exe: string
  residual: string

proc makeCached(pattern: string): CachedRegex =
  let state = RegexStageState(nextId: 0)
  let p = regexProgram(stagedSym(state), pattern, dynamic[string](RegexNode(kind: rkInput, name: "text")))
  result = CachedRegex(dir: getTempDir() / ("staging-regex-" & $getCurrentProcessId() & "-" & $state.nextId & "-" & $int(epochTime() * 1000)))
  createDir(result.dir)
  result.exe = result.dir / "residual"
  result.residual = emitBool(p.val)
  var src = "import std/os\nlet text = paramStr(1)\n"
  for d in state.decls: src.add(emitDecl(d) & "\n")
  src.add(emitStmt(p.stmts) & "\necho " & result.residual & "\n")
  doAssert "proc " notin src, "handwritten matcher leaked into residual"
  # The input is dynamic by design; argv permits one compile per pattern.
  writeFile(result.dir / "residual.nim", src)

when isMainModule:
  let cases = @[
    ("^hello$", "hello", true), ("^hello$", "hell", false), ("hell", "hello", true),
    ("hell", "hell", true), ("hel*", "he", true), ("hel*$", "hello", false),
    ("hel*", "yo hello", true), ("ab", "hello ab hello", true), ("^ab", "hello ab hello", false),
    ("a*b", "hello aab hello", true), ("^ab*", "abcd", true), ("^ab*", "a", true),
    ("^ab*", "ac", true), ("^ab*", "bac", false), ("^ab*$", "ac", false)]
  for (pattern, text, expected) in cases:
    doAssert regexMatch(directSym(text), pattern, text) == expected
  var cache: seq[(string, CachedRegex)]
  for (pattern, text, expected) in cases:
    var found = false
    var c: CachedRegex
    for item in cache:
      if item[0] == pattern: c = item[1]; found = true
    if not found:
      c = makeCached(pattern); cache.add((pattern, c))
    let stagedValue = parseBool(compileRun(c.dir / "residual.nim", c.exe, c.dir, text))
    doAssert stagedValue == expected, pattern & " / " & text & " got " & $stagedValue
  let hell = makeCached("hell")
  doAssert "while" in readFile(hell.dir / "residual.nim")
  let star = makeCached("hel*")
  doAssert "while" in readFile(star.dir / "residual.nim")
  let anchored = makeCached("^hello$")
  doAssert "while" notin readFile(anchored.dir / "residual.nim")
  for text in ["hello", "hallo"]: doAssert regexMatch(directSym(text), "h.llo", text)
  doAssert not regexMatch(directSym("hllo"), "h.llo", "hllo")
  let wildcardState = RegexStageState(nextId: 0)
  let wildcard = regexMatch(stagedSym(wildcardState), "h.llo", dynamic[string](RegexNode(kind: rkInput, name: "text")))
  discard wildcard
  let wildcardChar = stagedSym(RegexStageState(nextId: 0)).charEq('.', dynamic[char](RegexNode(kind: rkInput, name: "ch")))
  doAssert wildcardChar.isStatic and wildcardChar.staticVal
  echo "ok: regex direct/staged agreement, residual while, wildcard fold, and compile cache"
