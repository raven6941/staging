import std/[algorithm, sequtils, strutils]
import test_query_optc

type
  TokenKind = enum tkEof, tkWord, tkInt, tkString, tkBad, tkStar, tkComma, tkLParen,
    tkRParen, tkEquals, tkLess, tkDelim
  Token = object
    kind: TokenKind
    text: string
    offset: int
  ParseError* = object of ValueError
    offset*, line*, column*: int
    expected*, found*: string

type Parser = object
  input: string
  tokens: seq[Token]
  pos: int
  resolveTable: proc(ident: string): Operator

proc parseError(p: Parser; t: Token; expected: string): ref ParseError =
  new(result)
  result.offset = t.offset
  result.line = p.input[0 ..< t.offset].count('\n') + 1
  let nl = p.input.rfind('\n', 0, max(0, t.offset - 1))
  result.column = t.offset - nl
  result.expected = expected
  result.found = if t.kind == tkEof: "end of input" else: t.text
  result.msg = "parse error at byte " & $result.offset & " (line " & $result.line & ", column " & $result.column & "): expected " & expected & ", found " & result.found

proc addToken(tokens: var seq[Token]; k: TokenKind; text: string; at: int) =
  tokens.add(Token(kind: k, text: text, offset: at))

proc tokenize(s: string): seq[Token] =
  var i = 0
  while i < s.len:
    if s[i] in {' ', '\t', '\n', '\r'}: inc i; continue
    let at = i
    case s[i]
    of ',': addToken(result, tkComma, ",", i); inc i
    of '(' : addToken(result, tkLParen, "(", i); inc i
    of ')' : addToken(result, tkRParen, ")", i); inc i
    of '=' : addToken(result, tkEquals, "=", i); inc i
    of '<' : addToken(result, tkLess, "<", i); inc i
    of '*': addToken(result, tkStar, "*", i); inc i
    of '\'':
      inc i
      let start = i
      while i < s.len and s[i] != '\'': inc i
      if i >= s.len:
        addToken(result, tkBad, "unterminated string", at)
        break
      addToken(result, tkString, s[start ..< i], at); inc i
    of '\\':
      if i + 1 < s.len and s[i + 1] == 't': addToken(result, tkDelim, "\\t", i); i += 2
      else: addToken(result, tkWord, "\\", i); inc i
    else:
      if s[i].isDigit:
        while i < s.len and s[i].isDigit: inc i
        addToken(result, tkInt, s[at ..< i], at)
      else:
        while i < s.len and s[i] notin {' ', '\t', '\n', '\r', ',', '(', ')', '=', '<', '*', '\'', '\\'}: inc i
        addToken(result, tkWord, s[at ..< i], at)
  result.add(Token(kind: tkEof, offset: s.len))

proc current(p: Parser): Token = p.tokens[p.pos]
proc take(p: var Parser): Token = (result = p.current; inc p.pos)
proc want(p: var Parser; kind: TokenKind; text = ""): Token =
  let t = p.current
  if t.kind != kind or (text.len > 0 and t.text != text): raise p.parseError(t, if text.len > 0: text else: $kind)
  result = p.take
proc isWord(p: Parser; s: string): bool = p.current.kind == tkWord and p.current.text == s
proc acceptWord(p: var Parser; s: string): bool =
  if p.isWord(s): discard p.take; return true
  false

proc fieldList(p: var Parser; aliases: bool): tuple[outNames, inNames: seq[string]] =
  while true:
    let n = p.want(tkWord).text
    result.inNames.add(n)
    result.outNames.add(if p.acceptWord("as"): p.want(tkWord).text else: n)
    if p.current.kind != tkComma: break
    discard p.take

proc fieldNames(p: var Parser): seq[string] =
  result.add(p.want(tkWord).text)
  while p.current.kind == tkComma:
    discard p.take; result.add(p.want(tkWord).text)

proc statement(p: var Parser): Operator

proc tableClause(p: var Parser): Operator =
  if p.current.kind == tkLParen:
    discard p.take; result = p.statement; discard p.want(tkRParen); return
  let name = p.want(tkWord).text
  result = p.resolveTable(name)
  if p.acceptWord("schema"):
    let names = p.fieldNames
    result = result.setSchema(names)
  if p.acceptWord("delim"):
    let t = p.current
    if t.kind != tkDelim and t.kind != tkString and t.kind != tkWord: raise p.parseError(t, "delimiter")
    discard p.take
    result = result.setDelim(if t.kind == tkDelim: '\t' else: t.text[0])

proc joinClause(p: var Parser): Operator =
  let nested = p.acceptWord("nestedloops")
  result = p.tableClause
  while p.acceptWord("join"):
    let rhs = p.tableClause
    result = if nested: join(result, rhs) else: hashJoin(result, rhs)

proc refValue(p: var Parser): Ref =
  case p.current.kind
  of tkString: value(p.take.text)
  of tkInt: intValue(parseInt(p.take.text))
  of tkWord: field(p.take.text)
  else: raise p.parseError(p.current, "field, string, or integer")

proc comparison(p: var Parser): Predicate =
  let a = p.refValue
  if p.current.kind == tkEquals:
    discard p.take; result = equals(a, p.refValue)
  elif p.current.kind == tkLess:
    discard p.take; result = lessThan(a, p.refValue)
  else: raise p.parseError(p.current, "= or <")

proc andExpression(p: var Parser): Predicate =
  result = p.comparison
  while p.acceptWord("and"): result = predAnd(result, p.comparison)

proc predicateExpression(p: var Parser): Predicate =
  ## AND binds tighter than OR, matching conventional boolean expression precedence.
  result = p.andExpression
  while p.acceptWord("or"): result = predOr(result, p.andExpression)

proc aggregateKind(p: var Parser): AggKind =
  let t = p.current
  if t.kind != tkWord: raise p.parseError(t, "sum, avg, min, or max")
  case t.text
  of "sum": result = akSum
  of "avg": result = akAvg
  of "min": result = akMin
  of "max": result = akMax
  else: raise p.parseError(t, "sum, avg, min, or max")
  discard p.take

proc isAggregateWord(t: Token): bool =
  t.kind == tkWord and t.text in ["sum", "avg", "min", "max"]

proc statement(p: var Parser): Operator =
  discard p.want(tkWord, "select")
  var outNames, inNames: seq[string]
  if p.current.kind == tkStar: discard p.take
  else:
    (outNames, inNames) = p.fieldList(true)
  discard p.want(tkWord, "from")
  result = p.joinClause
  if p.acceptWord("where"):
    result = filter(p.predicateExpression, result)
  if p.acceptWord("group"):
    discard p.want(tkWord, "by")
    let keys = p.fieldNames
    var kinds: seq[AggKind] = @[]
    var aggs: seq[string] = @[]
    kinds.add(p.aggregateKind)
    aggs.add(p.want(tkWord).text)
    while p.current.kind == tkComma:
      discard p.take
      # A field named sum/avg/min/max is ambiguous here; treat it as a kind,
      # matching the existing positional grammar.
      if p.pos + 1 < p.tokens.len and isAggregateWord(p.tokens[p.pos]) and
          p.tokens[p.pos + 1].kind == tkWord:
        kinds.add(p.aggregateKind)
      else:
        kinds.add(kinds[^1])
      aggs.add(p.want(tkWord).text)
    result = groupKinds(keys, aggs, result, kinds)
  var orderKeys: seq[string] = @[]
  var orderDirs: seq[bool] = @[]
  if p.acceptWord("order"):
    discard p.want(tkWord, "by")
    while true:
      orderKeys.add(p.want(tkWord).text)
      if p.acceptWord("desc"): orderDirs.add(true)
      else:
        discard p.acceptWord("asc")
        orderDirs.add(false)
      if p.current.kind != tkComma: break
      discard p.take
  if outNames.len > 0: result = project(outNames, result, inNames)
  if orderKeys.len > 0: result = orderBy(orderKeys, orderDirs, result)
  if p.acceptWord("limit"): result = limit(parseInt(p.want(tkInt).text), result)

proc parseSql*(sql: string; resolveTable: proc(ident: string): Operator): Operator =
  var p = Parser(input: sql, tokens: tokenize(sql), resolveTable: resolveTable)
  result = p.statement
  if p.current.kind != tkEof: raise p.parseError(p.current, "end of input")

proc expectShape(sql, expected: string; resolveTable: proc(ident: string): Operator) =
  doAssert parseSql(sql, resolveTable).opShape == expected

when isMainModule:
  let csv = "Name,Flag,Value\nAda,yes,10\nBob,no,20\nAda,yes,7\n"
  let stringAggCsv = "Name,Flag,Value\nAda,x,10\nAda,10,11\nAda,9,12\nBob,8,13\n"
  let numericFirstStringAggCsv = "Name,Flag,Value\nAda,10,11\nAda,9,12\nAda,x,15\nBob,8,13\nBob,7,14\n"
  let stringOrderCsv = "Name,Flag,Value\nAda,x,10\nAda,y,11\nBob,z,12\n"
  let emptyCsv = "Name,Flag,Value\n"
  let multiCsv = "Dept,Name,Value\n10,Ada,2\n10,Bob,3\n10,Ada,5\n"
  let gram = "Phrase\tYear\tMatchCount\tVolumeCount\nAuswanderung\t2000\t3\t4\nOther\t2001\t2\t3\n"
  proc resolve(n: string): Operator =
    if n == "?": scan(gram, @["Phrase", "Year", "MatchCount", "VolumeCount"], '\t')
    elif n == "multi.csv": scan(multiCsv, @["Dept", "Name", "Value"])
    elif n == "strings.csv": scan(stringAggCsv, @["Name", "Flag", "Value"])
    elif n == "numeric-first-strings.csv": scan(numericFirstStringAggCsv, @["Name", "Flag", "Value"])
    elif n == "string-order.csv": scan(stringOrderCsv, @["Name", "Flag", "Value"])
    elif n == "empty.csv": scan(emptyCsv, @["Name", "Flag", "Value"])
    else: scan(csv, @["Name", "Flag", "Value"])
  expectShape("select * from t.csv", "Scan(Name,Flag,Value)", resolve)
  expectShape("select Name from t.csv", "Project(Name;Name;Scan(Name,Flag,Value))", resolve)
  expectShape("select Name from t.csv where Flag='yes'", "Project(Name;Name;Filter(Scan(Name,Flag,Value)))", resolve)
  expectShape("select * from nestedloops t.csv join (select Name as Name1 from t.csv)", "Join(Scan(Name,Flag,Value);Project(Name1;Name;Scan(Name,Flag,Value)))", resolve)
  expectShape("select * from t.csv join (select Name from t.csv)", "HashJoin(Scan(Name,Flag,Value);Project(Name;Name;Scan(Name,Flag,Value)))", resolve)
  expectShape("select * from t.csv group by Name sum Value", "Group(Name;sum:Value;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv group by Name,Flag sum Value", "Group(Name,Flag;sum:Value;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv group by Name avg Value", "Group(Name;avg:Value;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv group by Name min Value", "Group(Name;min:Value;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv group by Name max Value", "Group(Name;max:Value;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv group by Name sum Value, min Value", "Group(Name;sum:Value,min:Value;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv order by Value desc", "Sort(Value:desc;Scan(Name,Flag,Value))", resolve)
  expectShape("select * from t.csv limit 2", "Limit(2;Scan(Name,Flag,Value))", resolve)
  let limited = parseSql("select * from t.csv limit 2", resolve)
  doAssert "limitCount" in execOp(limited)
  doAssert runStaged(limited) == directRows(limited).mapIt(it.join(","))
  doAssert runStaged(limited) == @["Ada,yes,10", "Bob,no,20"]
  let limitZero = parseSql("select * from t.csv limit 0", resolve)
  doAssert runStaged(limitZero) == @[]
  doAssert directRows(limitZero).len == 0
  let limitLarge = parseSql("select * from t.csv limit 10", resolve)
  doAssert runStaged(limitLarge) == directRows(limitLarge).mapIt(it.join(","))
  doAssert runStaged(limitLarge) == @["Ada,yes,10", "Bob,no,20", "Ada,yes,7"]
  let topN = parseSql("select * from t.csv order by Value desc limit 2", resolve)
  expectShape("select * from t.csv order by Value desc limit 2", "Limit(2;Sort(Value:desc;Scan(Name,Flag,Value)))", resolve)
  doAssert runStaged(topN) == directRows(topN).mapIt(it.join(","))
  doAssert runStaged(topN) == @["Bob,no,20", "Ada,yes,10"]
  let groupedLimit = parseSql("select * from t.csv group by Name sum Value limit 1", resolve)
  doAssert runStaged(groupedLimit) == directRows(groupedLimit).mapIt(it.join(","))
  doAssert runStaged(groupedLimit).len == 1
  try:
    discard parseSql("select * from t.csv limit nope", resolve)
    doAssert false
  except ParseError: discard
  doAssert runStaged(parseSql("select * from t.csv where Flag='yes'", resolve)) == @["Ada,yes,10", "Ada,yes,7"]
  # Load-bearing: the following assertion fails if the residual Lt branch is
  # stubbed out (verified by stubbing it once, observing the failure, restoring).
  doAssert runStaged(parseSql("select * from t.csv where Value<10", resolve)) == @["Ada,yes,7"]
  # String Lt is lexicographic: 'Ada' < 'Bob', so only the Ada rows match.
  doAssert runStaged(parseSql("select * from t.csv where Name<'Bob'", resolve)) == @["Ada,yes,10", "Ada,yes,7"]
  doAssert directRows(parseSql("select * from t.csv where Name<'Bob'", resolve)) == @[@["Ada", "yes", "10"], @["Ada", "yes", "7"]]
  doAssert runStaged(parseSql("select Name as Name1 from t.csv where Name='Ada' and Value=7", resolve)) == @["Ada"]
  doAssert runStaged(parseSql("select * from t.csv where Name='Ada' or Flag='no'", resolve)) == @["Ada,yes,10", "Bob,no,20", "Ada,yes,7"]
  # AND binds tighter than OR: this selects both Ada rows and Bob's row.
  let mixed = parseSql("select * from t.csv where Name='Ada' or Flag='no' and Value=20", resolve)
  doAssert runStaged(mixed) == @["Ada,yes,10", "Bob,no,20", "Ada,yes,7"]
  doAssert directRows(mixed) == @[@["Ada", "yes", "10"], @["Bob", "no", "20"], @["Ada", "yes", "7"]]
  try:
    discard directRows(parseSql("select * from t.csv where Value='x'", resolve))
    doAssert false
  except AssertionDefect: discard
  try:
    discard execOp(parseSql("select * from t.csv where Name<5", resolve))
    doAssert false
  except AssertionDefect: discard
  doAssert directRows(parseSql("select Name as Name1 from t.csv", resolve)) == @[@["Ada"], @["Bob"], @["Ada"]]
  doAssert directRows(parseSql("select * from nestedloops t.csv join (select Name as Name1 from t.csv)", resolve)).len == 9
  doAssert directRows(parseSql("select * from t.csv join (select Name from t.csv)", resolve)).len == 5
  doAssert sorted(runStaged(parseSql("select * from t.csv group by Name sum Value", resolve))) == sorted(@["Ada,2,17", "Bob,1,20"])
  for kind in [akAvg, akMin, akMax]:
    let kindName = aggName(kind)
    let grouped = parseSql("select * from t.csv group by Name " & kindName & " Value", resolve)
    let staged = sorted(runStaged(grouped))
    let oracle = sorted(directRows(grouped).mapIt(it.join(",")))
    doAssert staged == oracle, kindName & ": " & $staged & " != " & $oracle
    let expected = case kind
      of akAvg: @[
        "Ada,2,8", "Bob,1,20"]
      of akMin: @["Ada,2,7", "Bob,1,20"]
      of akMax: @["Ada,2,10", "Bob,1,20"]
      else: @[]
    doAssert staged == sorted(expected)
  let orderedAverage = parseSql("select * from t.csv group by Name avg Value order by avg_Value", resolve)
  doAssert runStaged(orderedAverage) == directRows(orderedAverage).mapIt(it.join(","))
  doAssert runStaged(orderedAverage) == @["Ada,2,8", "Bob,1,20"]
  try:
    discard runStaged(parseSql("select * from t.csv group by Name sum Flag", resolve))
    doAssert false
  except AssertionDefect: discard
  try:
    discard runStaged(parseSql("select * from t.csv group by Name avg Flag", resolve))
    doAssert false
  except AssertionDefect: discard
  # Regression: the filtered first surviving row must not change the source
  # column kind used by either execution path.
  let numericFirstMin = parseSql("select * from numeric-first-strings.csv group by Name min Flag", resolve)
  doAssert runStaged(numericFirstMin) == @[
    "Ada,3,10", "Bob,2,7"]
  doAssert runStaged(numericFirstMin) == directRows(numericFirstMin).mapIt(it.join(","))
  let numericFirstMax = parseSql("select * from numeric-first-strings.csv group by Name max Flag", resolve)
  doAssert runStaged(numericFirstMax) == @[
    "Ada,3,x", "Bob,2,8"]
  doAssert runStaged(numericFirstMax) == directRows(numericFirstMax).mapIt(it.join(","))
  let orderedNumericFirstMin = parseSql("select * from numeric-first-strings.csv group by Name min Flag order by min_Flag", resolve)
  doAssert runStaged(orderedNumericFirstMin) == directRows(orderedNumericFirstMin).mapIt(it.join(","))
  var stagedFilterRaised = false
  try:
    discard runStaged(parseSql("select * from strings.csv where Flag='10' group by Name sum Flag", resolve))
  except AssertionDefect: stagedFilterRaised = true
  doAssert stagedFilterRaised
  var oracleFilterRaised = false
  try:
    discard directRows(parseSql("select * from strings.csv where Flag='10' group by Name sum Flag", resolve))
  except AssertionDefect: oracleFilterRaised = true
  doAssert oracleFilterRaised
  let emptyQuery = parseSql("select * from empty.csv", resolve)
  doAssert runStaged(emptyQuery) == @[]
  doAssert runStaged(emptyQuery) == directRows(emptyQuery).mapIt(it.join(","))
  for kind in [akMin, akMax]:
    let grouped = parseSql("select * from strings.csv group by Name " & aggName(kind) & " Flag", resolve)
    doAssert sorted(runStaged(grouped)) == sorted(directRows(grouped).mapIt(it.join(",")))
    let expected = if kind == akMin: @[
      "Ada,3,10", "Bob,1,8"] else: @["Ada,3,x", "Bob,1,8"]
    doAssert sorted(runStaged(grouped)) == sorted(expected)
  let mixedString = parseSql("select * from strings.csv group by Name min Value,Flag", resolve)
  doAssert sorted(runStaged(mixedString)) == sorted(directRows(mixedString).mapIt(it.join(",")))
  doAssert sorted(runStaged(mixedString)) == sorted(@["Ada,3,10,10", "Bob,1,13,8"])
  let mixedKinds = parseSql("select * from t.csv group by Name sum Value, min Value", resolve)
  doAssert resultSchema(mixedKinds) == @["Name", "count", "sum_Value", "min_Value"]
  doAssert runStaged(mixedKinds) == directRows(mixedKinds).mapIt(it.join(","))
  doAssert runStaged(mixedKinds) == @["Ada,2,17,7", "Bob,1,20,20"]
  let mixedIntString = parseSql("select * from strings.csv group by Name sum Value, min Flag", resolve)
  doAssert resultSchema(mixedIntString) == @["Name", "count", "sum_Value", "min_Flag"]
  doAssert runStaged(mixedIntString) == directRows(mixedIntString).mapIt(it.join(","))
  doAssert runStaged(mixedIntString) == @["Ada,3,33,10", "Bob,1,13,8"]
  let singleKind = parseSql("select * from t.csv group by Name sum Value", resolve)
  doAssert resultSchema(singleKind) == @["Name", "count", "sum_Value"]
  let orderedQualified = parseSql("select * from t.csv group by Name sum Value order by sum_Value desc", resolve)
  doAssert runStaged(orderedQualified) == directRows(orderedQualified).mapIt(it.join(","))
  doAssert runStaged(orderedQualified) == @["Bob,1,20", "Ada,2,17"]
  let mixedAvgString = parseSql("select * from strings.csv group by Name avg Value, max Flag", resolve)
  doAssert runStaged(mixedAvgString) == directRows(mixedAvgString).mapIt(it.join(","))
  doAssert runStaged(mixedAvgString) == @["Ada,3,11,x", "Bob,1,13,8"]
  try:
    discard runStaged(parseSql("select * from strings.csv group by Name sum Flag, min Value", resolve))
    doAssert false
  except AssertionDefect: discard
  let orderedString = parseSql("select * from string-order.csv group by Name min Flag order by Name desc", resolve)
  doAssert runStaged(orderedString) == directRows(orderedString).mapIt(it.join(","))
  let multiKey = parseSql("select * from multi.csv group by Dept,Name sum Value", resolve)
  doAssert sorted(runStaged(multiKey)) == sorted(directRows(multiKey).mapIt(it.join(",")))
  doAssert sorted(runStaged(multiKey)) == sorted(@["10,Ada,2,7", "10,Bob,1,3"])
  doAssert runStaged(parseSql("select * from ? schema Phrase,Year,MatchCount,VolumeCount delim \\t where Phrase='Auswanderung'", resolve)) == @["Auswanderung,2000,3,4"]
  let orderedValue = parseSql("select * from t.csv order by Value desc", resolve)
  doAssert runStaged(orderedValue) == directRows(orderedValue).mapIt(it.join(","))
  doAssert runStaged(orderedValue) == @["Bob,no,20", "Ada,yes,10", "Ada,yes,7"]
  let orderedMixed = parseSql("select * from t.csv order by Name asc, Value desc", resolve)
  doAssert runStaged(orderedMixed) == directRows(orderedMixed).mapIt(it.join(","))
  doAssert runStaged(orderedMixed) == @["Ada,yes,10", "Ada,yes,7", "Bob,no,20"]
  let orderedDefault = parseSql("select * from t.csv order by Name", resolve)
  doAssert runStaged(orderedDefault) == directRows(orderedDefault).mapIt(it.join(","))
  let groupedCount = parseSql("select * from t.csv group by Name sum Value order by count desc", resolve)
  doAssert runStaged(groupedCount) == directRows(groupedCount).mapIt(it.join(","))
  doAssert runStaged(groupedCount) == @["Ada,2,17", "Bob,1,20"]
  let groupedValue = parseSql("select * from t.csv group by Name sum Value order by sum_Value", resolve)
  doAssert runStaged(groupedValue) == directRows(groupedValue).mapIt(it.join(","))
  doAssert runStaged(groupedValue) == @["Ada,2,17", "Bob,1,20"]
  try:
    discard parseSql("select Name t.csv", resolve)
    doAssert false
  except ParseError as e: doAssert "byte" in e.msg and "from" in e.msg
  try:
    discard parseSql("select * from t.csv where Name='x", resolve)
    doAssert false
  except ParseError as e: doAssert "field, string, or integer" in e.msg
  echo "ok: SQL parser"
