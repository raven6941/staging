## Staged subset construction: an NFA becomes mutually recursive residual DFA procs.

import staging/framework
import std/[algorithm, os, osproc, sequtils, strutils, tables, times]

type
  CharSet = enum csChar, csWild
  NFAState = ref object
    id: int
    trans: seq[NTrans]
  NTrans = object
    set: CharSet
    ch: char
    found: bool
    next: NFAState
  RepFun = proc(c: char): DFAState
  DFAState = object
    accepting: bool
    next: RepFun

proc newNfa(id: int): NFAState = NFAState(id: id, trans: @[])
proc stop(): NFAState = newNfa(-1)
proc guard(s: NFAState, set: CharSet, ch: char, found: bool, next: NFAState): NFAState =
  s.trans.add(NTrans(set: set, ch: ch, found: found, next: next)); s
proc trans(s: NFAState, set: CharSet, ch: char, next: NFAState): NFAState =
  guard(s, set, ch, false, next)

proc findAab(): NFAState =
  let s0 = newNfa(0)
  let s1 = newNfa(1)
  let s2 = newNfa(2)
  let done = stop()
  discard guard(s2, csChar, 'B', true, done)
  discard trans(s1, csChar, 'A', s2)
  discard trans(s0, csChar, 'A', s1)
  discard trans(s2, csWild, '\0', s0)
  discard trans(s1, csWild, '\0', s0)
  discard trans(s0, csWild, '\0', s0)
  s0

proc directMatch(start: NFAState, input: string): bool =
  var live = @[start]
  for c in input:
    var next: seq[NFAState]
    var accepted = false
    for state in live:
      for t in state.trans:
        if t.set == csWild or t.ch == c:
          if t.found: accepted = true
          if t.next.id >= 0 and t.next notin next: next.add(t.next)
    if accepted: return true
    live = next
  false

type
  AutoKind = enum akCharInput, akEq, akIf, akState, akApp, akRef, akArg, akDef
  AutoNode = ref object of IRNode
    case kind: AutoKind
    of akCharInput: inputName: string
    of akEq:
      eqChar: char
      eqInput: Rep[char]
    of akIf:
      cond: Rep[bool]
      thenState, elseState: Rep[DFAState]
    of akState:
      accepting: bool
      nextFun: Rep[RepFun]
    of akApp:
      fn: Rep[RepFun]
      arg: Rep[char]
    of akRef: funName: string
    of akArg: discard
    of akDef:
      defName: string
      body: Rep[DFAState]
  AutoState = ref object
    refs: Table[string, Rep[RepFun]]
    defs: seq[AutoNode]
    nextId: int

proc charInput(name: string): Rep[char] = dynamic[char](AutoNode(kind: akCharInput, inputName: name))
proc charEq(c: char, x: Rep[char]): Rep[bool] =
  if x.isStatic: liftNow(x.staticVal == c)
  else: dynamic[bool](AutoNode(kind: akEq, eqChar: c, eqInput: x))

proc stagedFun(state: AutoState, key: string,
              body: proc(c: Rep[char]): Rep[DFAState]): Rep[RepFun] =
  if state.refs.hasKey(key): return state.refs[key]
  let name = "dfa_" & $state.nextId
  inc state.nextId
  let refRep = dynamic[RepFun](AutoNode(kind: akRef, funName: name))
  state.refs[key] = refRep
  discard smartFun[char, DFAState](key, body,
    proc(): Rep[RepFun] = refRep,
    proc(): Rep[char] = dynamic[char](AutoNode(kind: akArg)),
    proc(bodyResult: Rep[DFAState]): IRNode =
      let d = AutoNode(kind: akDef, defName: name, body: bodyResult)
      state.defs.add(d); d)
  refRep

proc stateValue(accepting: bool, f: Rep[RepFun]): Rep[DFAState] =
  dynamic[DFAState](AutoNode(kind: akState, accepting: accepting, nextFun: f))
proc applyFun(f: Rep[RepFun], c: Rep[char]): Rep[DFAState] =
  dynamic[DFAState](AutoNode(kind: akApp, fn: f, arg: c))

proc keyOf(xs: seq[NTrans]): string =
  result = "["
  for t in xs: result.add($t.next.id & ":" & $(if t.set == csWild: '*' else: t.ch) & ":" & $t.found & ";")
  result.add("]")

proc transCmp(a, b: NTrans): int =
  result = cmp(a.set, b.set)
  if result == 0 and a.set == csChar: result = cmp(a.ch, b.ch)
  if result == 0: result = cmp(a.found, b.found)
  if result == 0: result = cmp(a.next.id, b.next.id)

proc canonicalize(xs: seq[NTrans]): seq[NTrans] =
  result = xs
  result.sort(transCmp)
  var unique: seq[NTrans]
  for t in result:
    if unique.len == 0 or transCmp(unique[^1], t) != 0: unique.add(t)
  result = unique

proc knowing(s1, s2: NTrans): bool = s1.set == csWild or
  (s1.set == csChar and s2.set == csChar and s1.ch == s2.ch)
proc knowingNot(s1, s2: NTrans): bool = not (s1.set == csChar and s2.set == csChar and s1.ch == s2.ch)

proc explore(state: AutoState, xs: seq[NTrans], c: Rep[char],
             k: proc(found: bool, next: seq[NTrans]): Rep[DFAState]): Rep[DFAState] =
  if xs.len == 0: return k(false, @[])
  let first = xs[0]
  if first.set == csWild:
    var chars: seq[NTrans]
    var wildNext: seq[NTrans]
    var wildFound = false
    for t in xs:
      if t.set == csWild:
        wildFound = wildFound or t.found
        wildNext.add(t.next.trans)
      else: chars.add(t)
    return explore(state, chars, c, proc(found: bool, next: seq[NTrans]): Rep[DFAState] =
      k(found or wildFound, next & wildNext))
  var rest: seq[NTrans]
  var matchRest: seq[NTrans]
  for t in xs[1..^1]:
    if knowingNot(t, first): rest.add(t)
    if knowing(t, first): matchRest.add(NTrans(set: csWild, ch: '\0', found: t.found, next: t.next))
  if first.set == csChar:
    let yes = explore(state, matchRest, c, proc(found: bool, next: seq[NTrans]): Rep[DFAState] =
      k(found or first.found, next & first.next.trans))
    let no = explore(state, rest, c, k)
    let condition = charEq(first.ch, c)
    if condition.isStatic: return (if condition.staticVal: yes else: no)
    return dynamic[DFAState](AutoNode(kind: akIf, cond: condition, thenState: yes, elseState: no))
  k(false, @[])

proc buildDfa(start: NFAState, state: AutoState): Rep[DFAState] =
  proc makeFun(config: seq[NTrans]): Rep[RepFun]
  proc iterate(accepting: bool, config: seq[NTrans]): Rep[DFAState] =
    let canon = canonicalize(config)
    let key = keyOf(canon)
    stateValue(accepting, makeFun(canon))
  proc makeFun(config: seq[NTrans]): Rep[RepFun] =
    let canon = canonicalize(config)
    let key = keyOf(canon)
    stagedFun(state, key, proc(c: Rep[char]): Rep[DFAState] =
      explore(state, canon, c, proc(found: bool, next: seq[NTrans]): Rep[DFAState] =
        stateValue(found, makeFun(next))))
  var initial: seq[NTrans]
  for t in start.trans: initial.add(t)
  iterate(false, initial)

proc emitChar(c: char): string =
  case c
  of '\\': "'\\\\'"
  of '\'': "'\\''"
  of '\n': "'\\n'"
  else: "'" & $c & "'"

proc emitFun(r: Rep[RepFun]): string
proc emitState(r: Rep[DFAState]): string =
  let n = AutoNode(r.node); doAssert n.kind == akState
  "DFAState(accepting: " & $n.accepting & ", next: " & emitFun(n.nextFun) & ")"
proc emitCharExpr(r: Rep[char]): string =
  if r.isStatic: return emitChar(r.staticVal)
  let n = AutoNode(r.node)
  if n.kind == akArg: return "c"
  doAssert n.kind == akCharInput
  n.inputName
proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = AutoNode(r.node); doAssert n.kind == akEq
  "(" & emitCharExpr(n.eqInput) & " == " & emitChar(n.eqChar) & ")"
proc emitFun(r: Rep[RepFun]): string =
  let n = AutoNode(r.node); doAssert n.kind == akRef
  n.funName
proc emitDfa(r: Rep[DFAState]): string =
  if r.isStatic: return "DFAState(accepting: " & $r.staticVal.accepting & ", next: nil)"
  let n = AutoNode(r.node)
  case n.kind
  of akState: emitState(r)
  of akApp: emitFun(n.fn) & "(" & emitCharExpr(n.arg) & ")"
  of akIf: "(if " & emitBool(n.cond) & ": " & emitDfa(n.thenState) & " else: " & emitDfa(n.elseState) & ")"
  else: raise newException(ValueError, "not a DFA expression: " & $n.kind)

proc compileRun(source, exe, dir, input: string): string =
  let nim = findExe("nim"); doAssert nim.len > 0, "nim compiler not found on PATH"
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe) & " " & quoteShell(input), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

when isMainModule:
  let nfa = findAab()
  let cases = [("", false), ("B", false), ("AAB", true), ("AAC", false),
    ("AACAAB", true), ("AACAABAAC", true), ("AAAB", true)]
  for (text, expected) in cases: doAssert directMatch(nfa, text) == expected
  let stagedState = AutoState(refs: initTable[string, Rep[RepFun]](), defs: @[], nextId: 0)
  let residual = buildDfa(nfa, stagedState)
  doAssert stagedState.defs.len == 3, "unexpected DFA state count: " & $stagedState.defs.len
  doAssert stagedState.defs.mapIt(it.defName).deduplicate.len == stagedState.defs.len
  var source = "import std/os\n\ntype\n  DFAState = object\n    accepting: bool\n    next: proc(c: char): DFAState\n\n"
  for d in stagedState.defs: source.add("proc " & d.defName & "(c: char): DFAState\n\n")
  for d in stagedState.defs: source.add("proc " & d.defName & "(c: char): DFAState =\n  " & emitDfa(d.body) & "\n\n")
  source.add("let initial = " & emitDfa(residual) & "\nvar a = initial\nlet text = paramStr(1)\nvar i = 0\nwhile not a.accepting and i < text.len:\n  a = a.next(text[i]); inc i\necho a.accepting\n")
  doAssert source.count("proc ") == stagedState.defs.len * 2
  doAssert source.contains(stagedState.defs[0].defName & "("), "initial DFA proc is not referenced"
  var bodies: seq[string]
  for d in stagedState.defs:
    let body = emitDfa(d.body)
    bodies.add(body)
    doAssert body.count("'A'") <= 1, "redundant A guard in " & d.defName
  doAssert bodies.deduplicate.len == bodies.len, "DFA states have duplicate residual bodies"
  var backEdge = false
  for d in stagedState.defs[1..^1]:
    if emitDfa(d.body).contains(stagedState.defs[0].defName): backEdge = true
  doAssert backEdge, "a later DFA state must reference the initial state"
  let dir = getTempDir() / ("staging-automata-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let file = dir / "residual.nim"; let exe = dir / "residual"
  writeFile(file, source)
  for (text, expected) in cases:
    doAssert parseBool(compileRun(file, exe, dir, text)) == expected, text
  doAssert source.contains("dfa_0") and source.contains("dfa_1")
  removeDir(dir)
  echo "ok: staged NFA-to-DFA automata matcher"
