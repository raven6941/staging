import std/[algorithm, strutils]
import test_query_optc

type
  TokenKind = enum tkEof, tkWord, tkInt, tkString, tkBad, tkStar, tkComma, tkLParen,
    tkRParen, tkEquals, tkDelim
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
        while i < s.len and s[i] notin {' ', '\t', '\n', '\r', ',', '(', ')', '=', '*', '\'', '\\'}: inc i
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

proc statement(p: var Parser): Operator =
  discard p.want(tkWord, "select")
  var outNames, inNames: seq[string]
  if p.current.kind == tkStar: discard p.take
  else:
    (outNames, inNames) = p.fieldList(true)
  discard p.want(tkWord, "from")
  result = p.joinClause
  if p.acceptWord("where"):
    let a = p.refValue; discard p.want(tkEquals, "="); let b = p.refValue
    result = filter(equals(a, b), result)
  if p.acceptWord("group"):
    discard p.want(tkWord, "by")
    let keys = p.fieldNames
    if keys.len != 1: raise newException(ValueError, "multi-key group by is unsupported")
    discard p.want(tkWord, "sum")
    let aggs = p.fieldNames
    result = group(keys, aggs, result)
  if outNames.len > 0: result = project(outNames, result, inNames)

proc parseSql*(sql: string; resolveTable: proc(ident: string): Operator): Operator =
  var p = Parser(input: sql, tokens: tokenize(sql), resolveTable: resolveTable)
  result = p.statement
  if p.current.kind != tkEof: raise p.parseError(p.current, "end of input")

proc expectShape(sql, expected: string; resolveTable: proc(ident: string): Operator) =
  doAssert parseSql(sql, resolveTable).opShape == expected

when isMainModule:
  let csv = "Name,Flag,Value\nAda,yes,10\nBob,no,20\nAda,yes,7\n"
  let gram = "Phrase\tYear\tMatchCount\tVolumeCount\nAuswanderung\t2000\t3\t4\nOther\t2001\t2\t3\n"
  proc resolve(n: string): Operator =
    if n == "?": scan(gram, @["Phrase", "Year", "MatchCount", "VolumeCount"], '\t')
    else: scan(csv, @["Name", "Flag", "Value"])
  expectShape("select * from t.csv", "Scan(Name,Flag,Value)", resolve)
  expectShape("select Name from t.csv", "Project(Name;Name;Scan(Name,Flag,Value))", resolve)
  expectShape("select Name from t.csv where Flag='yes'", "Project(Name;Name;Filter(Scan(Name,Flag,Value)))", resolve)
  expectShape("select * from nestedloops t.csv join (select Name as Name1 from t.csv)", "Join(Scan(Name,Flag,Value);Project(Name1;Name;Scan(Name,Flag,Value)))", resolve)
  expectShape("select * from t.csv join (select Name from t.csv)", "HashJoin(Scan(Name,Flag,Value);Project(Name;Name;Scan(Name,Flag,Value)))", resolve)
  expectShape("select * from t.csv group by Name sum Value", "Group(Name;Value;Scan(Name,Flag,Value))", resolve)
  doAssert runStaged(parseSql("select * from t.csv where Flag='yes'", resolve)) == @["Ada,yes,10", "Ada,yes,7"]
  doAssert directRows(parseSql("select Name as Name1 from t.csv", resolve)) == @[@["Ada"], @["Bob"], @["Ada"]]
  doAssert directRows(parseSql("select * from nestedloops t.csv join (select Name as Name1 from t.csv)", resolve)).len == 9
  doAssert directRows(parseSql("select * from t.csv join (select Name from t.csv)", resolve)).len == 5
  doAssert sorted(runStaged(parseSql("select * from t.csv group by Name sum Value", resolve))) == sorted(@["Ada,2,17", "Bob,1,20"])
  doAssert runStaged(parseSql("select * from ? schema Phrase,Year,MatchCount,VolumeCount delim \\t where Phrase='Auswanderung'", resolve)) == @["Auswanderung,2000,3,4"]
  try:
    discard parseSql("select Name t.csv", resolve)
    doAssert false
  except ParseError as e: doAssert "byte" in e.msg and "from" in e.msg
  try:
    discard parseSql("select * from t.csv where Name='x", resolve)
    doAssert false
  except ParseError as e: doAssert "field, string, or integer" in e.msg
  echo "ok: SQL parser"
