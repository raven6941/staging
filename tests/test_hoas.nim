import staging/hoas
import std/[os, osproc, sequtils, strutils, times]

proc buildAAB(): Nfa =
  result = newNfa()
  let s0 = result.newState()
  let s1 = result.newState()
  let s2 = result.newState()
  let acc = result.newState()
  result.define(s0, proc(): seq[NTrans] = @[guard(C('A'), s1), guard(W(), s0)])
  result.define(s1, proc(): seq[NTrans] = @[guard(C('A'), s2)])
  result.define(s2, proc(): seq[NTrans] = @[guard(C('B'), acc, true)])
  result.define(acc, proc(): seq[NTrans] = stop())

proc buildBroken(): Nfa =
  result = newNfa()
  let s0 = result.newState()
  let s1 = result.newState()
  let s2 = result.newState()
  let acc = result.newState()
  result.define(s0, proc(): seq[NTrans] = @[guard(C('A'), s1), guard(W(), s0)])
  result.define(s1, proc(): seq[NTrans] = @[guard(C('A'), s2)])
  result.define(s2, proc(): seq[NTrans] = @[guard(C('C'), acc, true)])
  result.define(acc, proc(): seq[NTrans] = stop())

proc buildAABLiteral(): Nfa =
  result = newNfa()
  let s0 = result.newState()
  let s1 = result.newState()
  let s2 = result.newState()
  let acc = result.newState()
  result.define(s0, proc(): seq[NTrans] = @[guard(C('A'), s1), guard(W(), s0)])
  result.define(s1, proc(): seq[NTrans] = @[guard(C('A'), s2)])
  result.define(s2, proc(): seq[NTrans] = @[guard(C('B'), acc, true)])
  result.define(acc, proc(): seq[NTrans] = stop())

proc directMatches(s: string): bool =
  ## The W self-loop on s0 makes the NFA a substring search for "AAB",
  ## not a suffix check: any occurrence anywhere in s is accepted.
  s.contains("AAB")

proc emitDfa(dfa: Dfa): string =
  result = "const chars = " & $dfa.chars & "\n"
  result.add("const table = [\n")
  for state in dfa.states:
    result.add("  (accepted: " & $state.`out` & ", next: " & $state.next & "),\n")
  result.add("]\n")
  result.add("proc matches(s: string): bool =\n  var state = 0\n")
  result.add("  for c in s:\n    if table[state].accepted: return true\n")
  result.add("    var k = chars.len\n    for i, x in chars:\n      if x == c: k = i\n")
  result.add("    state = table[state].next[k]\n  table[state].accepted\n")

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let built = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert built.exitCode == 0, built.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

when isMainModule:
  let dfa = convertNFAtoDFA(buildAAB())
  doAssert dfa.states.len == 4
  doAssert dfa.states.countIt(it.`out`) == 1
  let cases = ["AAB", "AAC", "AACAAB", "AACAABAAC", "", "B"]
  for input in cases:
    doAssert matches(dfa, input) == directMatches(input)

  let residual = emitDfa(dfa)
  doAssert residual.contains("const table") and residual.contains("next:")
  let dir = getTempDir() / ("staging-hoas-" & $getCurrentProcessId() & "-" &
    $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  writeFile(source, residual & "echo matches(\"AAB\"), \" \", matches(\"AAC\")\n")
  doAssert compileRun(source, exe, dir) == "true false"
  removeDir(dir)

  let dfa2 = convertNFAtoDFA(buildAABLiteral())
  doAssert dfa.states == dfa2.states
  let s0 = StateId(0)
  let s1 = StateId(1)
  let s2 = StateId(2)
  doAssert canonicalKey(@[s2, s1, s0], false) == canonicalKey(@[s0, s2, s1], false)
  doAssert dfa.states[2].next[0] == 2 # {s0,s1,s2} loops to itself on 'A'
  doAssert dfa.states[0].next[1] == 0 # {s0} falls back to itself on 'B'
  doAssert dfa.states[1].next[1] == 0 # {s0,s1} falls back to {s0} on 'B'
  doAssert not matches(convertNFAtoDFA(buildBroken()), "AAB")
  echo "ok: HOAS NFA-to-DFA"
