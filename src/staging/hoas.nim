## NFA-to-DFA staging with HOAS builders and first-order named states.
##
## Decision: HOAS is used only as a builder.  Each explicitly named NFA state
## is defined by a proc evaluated once, immediately, into first-order NTrans
## data; the proc is then discarded and is never compared or stored.  DFA
## configurations are canonical sorted StateId sets plus their incoming found
## flag, and a memo table keyed by that canonical form deduplicates them.
## Evaluation-based closure comparison is rejected because it reruns arbitrary
## Nim code; creation-site tagging loses captured environments; a keyed
## registry alone does not provide subset-construction canonicalization.
##
## The alphabet is one class for every literal C(c) in the NFA plus one final
## ``other`` class.  W matches every class.  The residual is an emitter-agnostic
## first-order DFA table: DfaState.next is indexed by chars (in Dfa.chars order)
## followed by the other class, and matches interprets that table.

import std/[algorithm, tables]

type
  CharSetKind* = enum
    csChar, csWildcard

  CharSet* = object
    kind*: CharSetKind
    value*: char

  StateId* = distinct int

  NTrans* = object
    cs*: CharSet
    found*: bool
    to*: StateId

  Nfa* = ref object
    transitions: seq[seq[NTrans]]
    defined: seq[bool]
    start*: StateId

  DfaState* = object
    `out`*: bool
    next*: seq[int]

  Dfa* = object
    states*: seq[DfaState]
    chars*: seq[char]
    start*: int

proc `==`*(a, b: StateId): bool = int(a) == int(b)

proc C*(c: char): CharSet =
  CharSet(kind: csChar, value: c)

proc W*(): CharSet =
  CharSet(kind: csWildcard)

proc newNfa*(): Nfa =
  Nfa(transitions: @[], defined: @[], start: StateId(0))

proc newState*(nfa: Nfa): StateId =
  let id = StateId(nfa.transitions.len)
  nfa.transitions.add(@[])
  nfa.defined.add(false)
  if nfa.transitions.len == 1:
    nfa.start = id
  id

proc define*(nfa: Nfa; id: StateId; body: proc(): seq[NTrans]) =
  ## Evaluate body exactly once.  Its closure is discarded after this call;
  ## no closure is retained in, or compared by, the NFA representation.
  let i = int(id)
  doAssert i >= 0 and i < nfa.transitions.len
  doAssert not nfa.defined[i]
  nfa.transitions[i] = body()
  nfa.defined[i] = true

proc guard*(cs: CharSet; to: StateId; found = false): NTrans =
  NTrans(cs: cs, found: found, to: to)

proc stop*(): seq[NTrans] = @[]

proc canonicalKey*(states: openArray[StateId]; found: bool): string =
  var sorted: seq[int] = @[]
  for state in states:
    sorted.add(int(state))
  sorted.sort()
  result = if found: "1:" else: "0:"
  for i, state in sorted:
    if i > 0: result.add(',')
    result.add($state)

proc matchesClass(cs: CharSet; c: char): bool =
  cs.kind == csWildcard or cs.value == c

proc convertNFAtoDFA*(nfa: Nfa): Dfa =
  var built = Dfa()
  var chars: seq[char] = @[]
  for body in nfa.transitions:
    for trans in body:
      if trans.cs.kind == csChar and trans.cs.value notin chars:
        chars.add(trans.cs.value)
  chars.sort()
  built.chars = chars
  built.start = 0

  var memo = initTable[string, int]()
  var configurations: seq[(seq[StateId], bool)] = @[]

  proc addConfiguration(states: seq[StateId]; found: bool): int =
    let key = canonicalKey(states, found)
    if memo.hasKey(key):
      return memo[key]
    built.states.add(DfaState(`out`: found, next: newSeq[int](chars.len + 1)))
    let index = built.states.high
    memo[key] = index
    configurations.add((states, found))
    index

  discard addConfiguration(@[nfa.start], false)
  var cursor = 0
  while cursor < configurations.len:
    let (states, found) = configurations[cursor]
    let current = memo[canonicalKey(states, found)]
    if found:
      for classIndex in 0 ..< chars.len + 1:
        built.states[current].next[classIndex] = -1
      inc cursor
      continue
    for classIndex in 0 ..< chars.len + 1:
      var successors: seq[StateId] = @[]
      var successorFound = false
      let input = if classIndex < chars.len: chars[classIndex] else: '\x00'
      for state in states:
        let body = nfa.transitions[int(state)]
        for trans in body:
          if (classIndex == chars.len and trans.cs.kind == csWildcard) or
              (classIndex < chars.len and matchesClass(trans.cs, input)):
            if trans.to notin successors:
              successors.add(trans.to)
            successorFound = successorFound or trans.found
      let nextIndex = addConfiguration(successors, successorFound)
      built.states[current].next[classIndex] = nextIndex
    inc cursor
  result = built

proc matches*(dfa: Dfa; s: string): bool =
  var state = dfa.start
  for c in s:
    if dfa.states[state].`out`:
      return true
    var classIndex = dfa.chars.len
    for i, known in dfa.chars:
      if known == c:
        classIndex = i
        break
    let nextState = dfa.states[state].next[classIndex]
    if nextState < 0:
      return false
    state = nextState
  dfa.states[state].`out`
