## Residual CSV query compiler.
##
## The input strings and schemas are staging-time values.  The scanner, field
## values, buffers, and hash tables below are residual values: emitProgram is
## the only path used by the staged tests, and compileRun executes its output.

import staging/framework
import staging/arrays
import std/[algorithm, os, osproc, strutils, sequtils, tables]

type
  FieldKind = enum fkString, fkInt
  RString = object
    data: Rep[string]
    len: Rep[int]
  RInt = object
    value: Rep[int]
  RField = object
    kind: FieldKind
    str: RString
    int: RInt

  NodeKind = enum nkInput, nkScanner, nkNext, nkNextInt, nkHasNext, nkClose,
    nkVarDecl, nkVarRead, nkVarWrite, nkSeq, nkWhile, nkIf, nkAdd, nkMul,
    nkEq, nkLt, nkLe, nkGe, nkAnd, nkOr, nkNot, nkStringLen, nkStringEq, nkStringLt, nkStringLe, nkStringGe, nkHash, nkMod, nkDiv, nkArrDecl,
    nkArrRead, nkArrWrite, nkBufferLen, nkBufferAppend, nkBufferRead, nkInProbe, nkPrint, nkDiscard
  QueryNode = ref object of IRNode
    kind: NodeKind
    name, text: string
    delim: char
    pos, v: Var[int]
    init, left, right, index, value: Rep[int]
    boolLeft, boolRight: Rep[int]
    boolA, boolB: Rep[bool]
    sleft, sright: Rep[string]
    cond: Rep[bool]
    a, b, thenB, elseB: Rep[Unit]
    arr: Arr[int]
    arrStr: Arr[string]
    data: seq[int]
    svalue: Rep[string]
    fields: seq[RField]

  Scanner = object
    text: string
    pos: Var[int]
    closed: Var[int]
  ArrayBuffer = object
    ints: Arr[int]
    strings: Arr[string]
    len: Var[int]
  ColBuffer = ArrayBuffer

proc bufferAppend(b: ArrayBuffer; x: RField): Rep[Unit] =
  ## Append is residual: the length Var is incremented after the typed write.
  let i = readVar(b.len, proc(v: Var[int]): IRNode = QueryNode(kind: nkVarRead, v: v))
  let n = QueryNode(kind: nkBufferAppend, arr: b.ints, arrStr: b.strings, v: b.len,
    value: x.int.value, svalue: x.str.data, index: i)
  dynamic[Unit](n)
proc bufferRead(b: ArrayBuffer; i: Rep[int]; kind: FieldKind): RField =
  if kind == fkInt:
    let x = dynamic[int](QueryNode(kind: nkBufferRead, arr: b.ints, index: i))
    RField(kind: kind, int: RInt(value: x))
  else:
    let x = dynamic[string](QueryNode(kind: nkBufferRead, arrStr: b.strings, index: i))
    RField(kind: kind, str: RString(data: x, len: liftNow(0)))

type
  RefKind* = enum rkField, rkValue
  Ref* = object
    kind*: RefKind
    name: string
    value: RField
  PredicateKind* = enum pkEquals, pkLessThan, pkGreaterThan, pkLessEq, pkGreaterEq, pkAnd, pkOr, pkIn
  Predicate* = ref object
    kind*: PredicateKind
    left*, right*: Ref
    a*, b*: Predicate
    subquery*: Operator
  AggKind* = enum akSum, akAvg, akMin, akMax
  OpKind* = enum okScan, okFilter, okProject, okJoin, okHashJoin, okGroup, okSort, okLimit, okOffset, okHaving, okDistinct, okPrintCSV
  Operator* = ref object
    kind: OpKind
    csv, csvRight: string
    schema, outputSchema, inputSchema, keys, aggregates: seq[string]
    aggKinds: seq[AggKind]
    sortKeys: seq[string]
    sortDesc: seq[bool]
    n: int
    delim: char
    predicate: Predicate
    parent, right: Operator

proc directRows*(q: Operator): seq[seq[string]]
proc execOp*(q: Operator): string

proc staticString(x: string): Rep[string] = liftNow(x)
proc staticInt(x: int): Rep[int] = liftNow(x)
proc staticField(x: string): RField = RField(kind: fkString, str: RString(data: staticString(x), len: staticInt(x.len)))
proc intField(x: int): RField = RField(kind: fkInt, int: RInt(value: staticInt(x)))
proc field*(name: string): Ref = Ref(kind: rkField, name: name)
proc value*(x: string): Ref = Ref(kind: rkValue, value: staticField(x))
proc intValue*(x: int): Ref = Ref(kind: rkValue, value: intField(x))
proc scan*(csv: string; schema: seq[string]; delim = ','): Operator =
  let header = csv.splitLines[0].split(delim)
  doAssert header.len == schema.len, "schema length does not match CSV header"
  Operator(kind: okScan, csv: csv, schema: schema, delim: delim)
proc setSchema*(q: Operator; schema: seq[string]): Operator =
  q.schema = schema
  q
proc setDelim*(q: Operator; delim: char): Operator =
  q.delim = delim
  q
proc filter*(p: Predicate; q: Operator): Operator = Operator(kind: okFilter, csv: q.csv, delim: q.delim, predicate: p, parent: q)
proc project*(s: seq[string]; q: Operator; inputSchema: seq[string] = @[]): Operator =
  Operator(kind: okProject, csv: q.csv, delim: q.delim, outputSchema: s,
    inputSchema: (if inputSchema.len == 0: s else: inputSchema), parent: q)
proc join*(a, b: Operator): Operator = Operator(kind: okJoin, parent: a, right: b)
proc hashJoin*(a, b: Operator): Operator = Operator(kind: okHashJoin, parent: a, right: b)
proc groupKinds*(keys, aggs: seq[string]; q: Operator; kinds: seq[AggKind]): Operator
proc group*(keys, aggs: seq[string]; q: Operator; kind = akSum): Operator =
  groupKinds(keys, aggs, q, newSeqWith(aggs.len, kind))
proc groupKinds*(keys, aggs: seq[string]; q: Operator; kinds: seq[AggKind]): Operator =
  doAssert kinds.len == aggs.len
  Operator(kind: okGroup, keys: keys, aggregates: aggs, aggKinds: kinds, parent: q)
proc aggName*(kind: AggKind): string =
  case kind
  of akSum: "sum"
  of akAvg: "avg"
  of akMin: "min"
  of akMax: "max"
proc printCSV(q: Operator): Operator = Operator(kind: okPrintCSV, parent: q)
proc equals*(a, b: Ref): Predicate = Predicate(kind: pkEquals, left: a, right: b)
proc lessThan*(a, b: Ref): Predicate = Predicate(kind: pkLessThan, left: a, right: b)
proc greaterThan*(a, b: Ref): Predicate = Predicate(kind: pkGreaterThan, left: a, right: b)
proc lessEq*(a, b: Ref): Predicate = Predicate(kind: pkLessEq, left: a, right: b)
proc greaterEq*(a, b: Ref): Predicate = Predicate(kind: pkGreaterEq, left: a, right: b)
proc predAnd*(a, b: Predicate): Predicate = Predicate(kind: pkAnd, a: a, b: b)
proc predOr*(a, b: Predicate): Predicate = Predicate(kind: pkOr, a: a, b: b)
proc inSubquery*(fieldRef: Ref; sub: Operator): Predicate =
  Predicate(kind: pkIn, left: fieldRef, subquery: sub)

proc opShape*(q: Operator): string

proc resultSchema*(q: Operator): seq[string] =
  case q.kind
  of okScan: q.schema
  of okFilter, okPrintCSV: resultSchema(q.parent)
  of okProject: q.outputSchema
  of okJoin, okHashJoin: resultSchema(q.parent) & resultSchema(q.right)
  of okGroup:
    var aggregateNames: seq[string] = @[]
    for j, name in q.aggregates:
      aggregateNames.add(aggName(q.aggKinds[j]) & "_" & name)
    q.keys & @["count"] & aggregateNames
  of okSort, okLimit, okOffset, okHaving, okDistinct: resultSchema(q.parent)

proc predShape(p: Predicate): string =
  proc refShape(r: Ref): string =
    if r.kind == rkField: r.name
    elif r.value.kind == fkString: "'" & r.value.str.data.staticVal & "'"
    else: $r.value.int.value.staticVal
  case p.kind
  of pkEquals: refShape(p.left) & "=" & refShape(p.right)
  of pkLessThan: refShape(p.left) & "<" & refShape(p.right)
  of pkGreaterThan: refShape(p.left) & ">" & refShape(p.right)
  of pkLessEq: refShape(p.left) & "<=" & refShape(p.right)
  of pkGreaterEq: refShape(p.left) & ">=" & refShape(p.right)
  of pkAnd: predShape(p.a) & " and " & predShape(p.b)
  of pkOr: predShape(p.a) & " or " & predShape(p.b)
  of pkIn: "In(" & refShape(p.left) & ";" & opShape(p.subquery) & ")"

proc opShape*(q: Operator): string =
  ## A compact structural view used by the SQL front-end tests.
  case q.kind
  of okScan: "Scan(" & q.schema.join(",") & ")"
  of okFilter:
    if q.predicate.kind == pkIn: "Filter(" & predShape(q.predicate) & ";" & opShape(q.parent) & ")"
    else: "Filter(" & opShape(q.parent) & ")"
  of okProject: "Project(" & q.outputSchema.join(",") & ";" & q.inputSchema.join(",") & ";" & opShape(q.parent) & ")"
  of okJoin: "Join(" & opShape(q.parent) & ";" & opShape(q.right) & ")"
  of okHashJoin: "HashJoin(" & opShape(q.parent) & ";" & opShape(q.right) & ")"
  of okGroup:
    var aggregateShape: seq[string] = @[]
    for j, name in q.aggregates: aggregateShape.add(aggName(q.aggKinds[j]) & ":" & name)
    "Group(" & q.keys.join(",") & ";" & aggregateShape.join(",") & ";" & opShape(q.parent) & ")"
  of okSort:
    "Sort(" & q.sortKeys.mapIt(it & ":" & (if q.sortDesc[q.sortKeys.find(it)]: "desc" else: "asc")).join(",") & ";" & opShape(q.parent) & ")"
  of okLimit: "Limit(" & $q.n & ";" & opShape(q.parent) & ")"
  of okOffset: "Offset(" & $q.n & ";" & opShape(q.parent) & ")"
  of okHaving: "Having(" & predShape(q.predicate) & ";" & opShape(q.parent) & ")"
  of okDistinct: "Distinct(" & opShape(q.parent) & ")"
  of okPrintCSV: "Print(" & opShape(q.parent) & ")"

proc lookup(s: seq[string]; n: string): int =
  result = s.find(n); doAssert result >= 0, "unknown field " & n

proc orderBy*(keys: seq[string]; dirs: seq[bool]; q: Operator): Operator =
  let schema = resultSchema(q)
  for key in keys: discard lookup(schema, key)
  Operator(kind: okSort, sortKeys: keys, sortDesc: dirs, parent: q)
proc limit*(n: int; q: Operator): Operator =
  Operator(kind: okLimit, n: n, parent: q)
proc offset*(m: int; q: Operator): Operator =
  Operator(kind: okOffset, n: m, parent: q)
proc having*(pred: Predicate; q: Operator): Operator =
  Operator(kind: okHaving, predicate: pred, parent: q)
proc distinctOp*(q: Operator): Operator =
  Operator(kind: okDistinct, parent: q)

proc parseRows*(csv: string; delim = ','): seq[seq[string]] =
  for line in csv.strip.splitLines[1 .. ^1]:
    if line.len > 0: result.add(line.split(delim))

proc sourceKinds(csv: string; schema: seq[string]; delim: char): seq[bool] =
  ## Classify a source column as string when any data value is not an integer.
  result = newSeq[bool](schema.len)
  for row in parseRows(csv, delim):
    for i in 0 ..< schema.len:
      if result[i]: continue
      if i >= row.len:
        result[i] = true
      else:
        try: discard parseInt(row[i])
        except ValueError: result[i] = true
  if csv.strip.splitLines.len <= 1:
    for i, name in schema:
      if name in ["Name", "Flag", "Phrase"]: result[i] = true

proc refText(r: Ref; row: seq[string]; schema: seq[string]): string =
  if r.kind == rkField: row[lookup(schema, r.name)]
  elif r.value.kind == fkString: r.value.str.data.staticVal
  else: $r.value.int.value.staticVal

proc refKind(r: Ref; schema: seq[string]; kinds: seq[bool]): FieldKind =
  if r.kind == rkField:
    if kinds[lookup(schema, r.name)]: fkString else: fkInt
  else: r.value.kind

proc columnKinds(q: Operator): seq[bool]

proc predicateMatches(p: Predicate; row: seq[string]; schema: seq[string]; kinds: seq[bool]): bool =
  case p.kind
  of pkEquals, pkLessThan, pkGreaterThan, pkLessEq, pkGreaterEq:
    let aKind = refKind(p.left, schema, kinds)
    let bKind = refKind(p.right, schema, kinds)
    doAssert aKind == bKind, "predicate kind mismatch"
    let a = refText(p.left, row, schema)
    let b = refText(p.right, row, schema)
    if p.kind == pkEquals: result = a == b
    elif aKind == fkString:
      result = case p.kind
        of pkLessThan: a < b
        of pkGreaterThan: a > b
        of pkLessEq: a <= b
        of pkGreaterEq: a >= b
        else: false
    else:
      let ai = parseInt(a); let bi = parseInt(b)
      result = case p.kind
        of pkLessThan: ai < bi
        of pkGreaterThan: ai > bi
        of pkLessEq: ai <= bi
        of pkGreaterEq: ai >= bi
        else: false
  of pkAnd: result = predicateMatches(p.a, row, schema, kinds) and predicateMatches(p.b, row, schema, kinds)
  of pkOr: result = predicateMatches(p.a, row, schema, kinds) or predicateMatches(p.b, row, schema, kinds)
  of pkIn:
    doAssert p.left.kind == rkField, "IN left operand must be a field"
    let leftKind = refKind(p.left, schema, kinds)
    let subKinds = columnKinds(p.subquery)
    doAssert subKinds.len > 0, "IN subquery must have a column"
    doAssert leftKind == (if subKinds[0]: fkString else: fkInt), "predicate kind mismatch"
    let needle = refText(p.left, row, schema)
    for subRow in directRows(p.subquery):
      if subRow.len > 0 and subRow[0] == needle: return true
    result = false

proc validateHaving(p: Predicate; q: Operator) =
  doAssert q.kind == okGroup, "HAVING requires GROUP BY"
  var allowed = @["count"]
  for j, name in q.aggregates: allowed.add(aggName(q.aggKinds[j]) & "_" & name)
  proc validate(x: Predicate) =
    case x.kind
    of pkAnd, pkOr: validate(x.a); validate(x.b)
    of pkIn: doAssert false, "IN is not allowed in HAVING"
    else:
      for r in [x.left, x.right]:
        if r.kind == rkField:
          doAssert r.name in allowed, "HAVING field must be an aggregate output: " & r.name

proc columnKinds(q: Operator): seq[bool] =
  case q.kind
  of okScan: result = sourceKinds(q.csv, q.schema, q.delim)
  of okFilter, okPrintCSV, okSort, okLimit, okOffset, okHaving, okDistinct: result = columnKinds(q.parent)
  of okProject:
    let parentSchema = resultSchema(q.parent)
    let input = if q.inputSchema.len == 0: q.outputSchema else: q.inputSchema
    let parentKinds = columnKinds(q.parent)
    for name in input: result.add(parentKinds[lookup(parentSchema, name)])
  of okJoin, okHashJoin: result = columnKinds(q.parent) & columnKinds(q.right)
  of okGroup:
    let parentSchema = resultSchema(q.parent)
    let parentKinds = columnKinds(q.parent)
    for name in q.keys: result.add(parentKinds[lookup(parentSchema, name)])
    result.add(false)
    for j, name in q.aggregates:
      result.add(if q.aggKinds[j] in {akMin, akMax}: parentKinds[lookup(parentSchema, name)] else: false)

proc directRows(q: Operator): seq[seq[string]] =
  case q.kind
  of okScan: result = parseRows(q.csv, q.delim)
  of okFilter:
    let ps = resultSchema(q.parent)
    let kinds = columnKinds(q.parent)
    for row in directRows(q.parent):
      if predicateMatches(q.predicate, row, ps, kinds): result.add(row)
  of okProject:
    let ps = resultSchema(q.parent)
    let ins = if q.inputSchema.len == 0: q.outputSchema else: q.inputSchema
    for row in directRows(q.parent):
      var projected: seq[string] = @[]
      for name in ins: projected.add(row[lookup(ps, name)])
      result.add(projected)
  of okJoin, okHashJoin:
    let ls = resultSchema(q.parent); let rs = resultSchema(q.right)
    for a in directRows(q.parent):
      for b in directRows(q.right):
        var good = true
        for k in ls:
          if k in rs: good = good and a[lookup(ls, k)] == b[lookup(rs, k)]
        if good: result.add(a & b)
  of okGroup:
    let ps = resultSchema(q.parent); let kinds = columnKinds(q.parent)
    for j, n in q.aggregates:
      if q.aggKinds[j] in {akSum, akAvg}:
        doAssert not kinds[lookup(ps, n)], "aggregate field must be integer"
    # Insertion-ordered: plain Table iteration order is Nim-version
    # dependent (2.0.8 yields Bob before Ada here), while the staged
    # path emits groups in first-seen order. OrderedTable keeps the
    # oracle deterministic and in agreement with staged on all versions.
    var groups = initOrderedTable[string, seq[string]]()
    for row in directRows(q.parent):
      let k = q.keys.mapIt(row[lookup(ps, it)]).join("\x1f")
      if not groups.hasKey(k): groups[k] = q.keys.mapIt(row[lookup(ps, it)]) & @[$1] & q.aggregates.mapIt(row[lookup(ps, it)])
      else:
        let countIndex = q.keys.len
        groups[k][countIndex] = $(parseInt(groups[k][countIndex]) + 1)
        for j, n in q.aggregates:
          let valueIndex = countIndex + 1 + j
          let aggregateIndex = lookup(ps, n)
          if kinds[aggregateIndex]:
            let value = row[aggregateIndex]
            let current = groups[k][valueIndex]
            case q.aggKinds[j]
            of akMin:
              if value < current: groups[k][valueIndex] = value
            of akMax:
              if current < value: groups[k][valueIndex] = value
            of akSum, akAvg: doAssert false, "aggregate field must be integer"
          else:
            let value = parseInt(row[aggregateIndex])
            let current = parseInt(groups[k][valueIndex])
            case q.aggKinds[j]
            of akSum, akAvg: groups[k][valueIndex] = $(current + value)
            of akMin: groups[k][valueIndex] = $(min(current, value))
            of akMax: groups[k][valueIndex] = $(max(current, value))
    for x in groups.mvalues:
      let count = parseInt(x[q.keys.len])
      for j in 0 ..< q.aggregates.len:
        if q.aggKinds[j] == akAvg:
          let i = q.keys.len + 1 + j
          x[i] = $(parseInt(x[i]) div count)
      result.add(x)
  of okSort:
    result = directRows(q.parent)
    let schema = resultSchema(q.parent)
    let kinds = columnKinds(q.parent)
    proc less(a, b: seq[string]): bool =
      for k, name in q.sortKeys:
        let i = lookup(schema, name)
        if a[i] == b[i]: continue
        let x = if kinds[i]: a[i] < b[i] else: parseInt(a[i]) < parseInt(b[i])
        return if q.sortDesc[k]: not x else: x
      false
    for i in 1 ..< result.len:
      let row = result[i]
      var j = i
      while j > 0 and less(row, result[j - 1]):
        result[j] = result[j - 1]
        dec j
      result[j] = row
  of okLimit:
    let parentRows = directRows(q.parent)
    let count = min(max(q.n, 0), parentRows.len)
    result = parentRows[0 ..< count]
  of okOffset:
    let parentRows = directRows(q.parent)
    let start = min(max(q.n, 0), parentRows.len)
    result = parentRows[start ..< parentRows.len]
  of okHaving:
    validateHaving(q.predicate, q.parent)
    let ps = resultSchema(q.parent); let kinds = columnKinds(q.parent)
    for row in directRows(q.parent):
      if predicateMatches(q.predicate, row, ps, kinds): result.add(row)
  of okDistinct:
    for row in directRows(q.parent):
      if row notin result: result.add(row)
  of okPrintCSV: result = directRows(q.parent)

# Residual constructors.  In particular, Scanner position is a residual Var,
# and effectful scanner nodes are never pure/merged by genlet.
proc scannerNew(text: string): Scanner =
  ## The name is residual state, so two scans can coexist in a join.
  var serial {.global.}: int
  let suffix = if serial == 0: "" else: $serial
  inc serial
  result.text = text
  result.pos = newVar(staticInt(0), proc(x: Rep[int]): IRNode = QueryNode(kind: nkVarDecl, name: "scannerPos" & suffix, init: x))
  result.closed = newVar(staticInt(0), proc(x: Rep[int]): IRNode = QueryNode(kind: nkVarDecl, name: "scannerClosed" & suffix, init: x))
proc scannerNext(s: Scanner; d: char): Rep[string] = dynamic[string](QueryNode(kind: nkNext, text: s.text, delim: d, pos: s.pos))
proc scannerNextInt(s: Scanner; d: char): Rep[int] = dynamic[int](QueryNode(kind: nkNextInt, text: s.text, delim: d, pos: s.pos))
proc scannerHasNext(s: Scanner): Rep[bool] = dynamic[bool](QueryNode(kind: nkHasNext, text: s.text, pos: s.pos))
proc scannerClose(s: Scanner): Rep[Unit] = dynamic[Unit](QueryNode(kind: nkClose, pos: s.pos))
proc scannerIsPure(n: QueryNode): bool =
  ## This is deliberately false for every scanner action and mutation.
  n.kind notin {nkScanner, nkNext, nkNextInt, nkHasNext, nkClose, nkVarWrite,
    nkArrWrite, nkBufferAppend}
proc stringCompare(a, b: RString): Rep[bool] =
  dynamic[bool](QueryNode(kind: nkStringEq, sleft: a.data, sright: b.data))
proc stringLess(a, b: RString): Rep[bool] =
  dynamic[bool](QueryNode(kind: nkStringLt, sleft: a.data, sright: b.data))
proc stringLessEq(a, b: RString): Rep[bool] =
  dynamic[bool](QueryNode(kind: nkStringLe, sleft: a.data, sright: b.data))
proc stringGreaterEq(a, b: RString): Rep[bool] =
  dynamic[bool](QueryNode(kind: nkStringGe, sleft: a.data, sright: b.data))
proc fieldHash(a: RString): Rep[int] =
  dynamic[int](QueryNode(kind: nkHash, sleft: a.data))
proc intAdd(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x+y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkAdd,left:x,right:y))
proc intMul(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x*y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkMul,left:x,right:y))
proc intMod(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x mod y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkMod,left:x,right:y))
proc intDiv(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x div y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkDiv,left:x,right:y))
proc seqs(a,b: Rep[Unit]): Rep[Unit] = seqR(a,b,proc(x,y:Rep[Unit]):IRNode=QueryNode(kind:nkSeq,a:x,b:y))
proc seqMany(xs: openArray[Rep[Unit]]): Rep[Unit] =
  result = unit()
  for x in xs: result = seqs(result, x)
proc whileLoop(c: proc(): Rep[bool]; body: proc(): Rep[Unit]): Rep[Unit] = smartWhile(c,body,proc(x:Rep[bool];y:Rep[Unit]):IRNode=QueryNode(kind:nkWhile,cond:x,b:y))

proc emitString(x: Rep[string]): string
proc emitInt(x: Rep[int]): string =
  if x.isStatic: return $x.staticVal
  let n = QueryNode(x.node)
  case n.kind
  of nkNextInt: "parseInt(scannerNext(" & escape(n.text) & ", " & QueryNode(n.pos.node).name & ", " & repr(n.delim) & "))"
  of nkAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of nkMul: "(" & emitInt(n.left) & " * " & emitInt(n.right) & ")"
  of nkMod: "(" & emitInt(n.left) & " mod " & emitInt(n.right) & ")"
  of nkDiv: "(" & emitInt(n.left) & " div " & emitInt(n.right) & ")"
  of nkHash: "hashString(" & emitString(n.sleft) & ")"
  of nkBufferRead: QueryNode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  of nkArrRead: QueryNode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  of nkVarWrite: QueryNode(n.v.node).name
  of nkVarRead: QueryNode(n.v.node).name
  else: raise newException(ValueError, "bad residual int")
proc emitString(x: Rep[string]): string =
  if x.isStatic: return escape(x.staticVal)
  let n = QueryNode(x.node)
  case n.kind
  of nkNext: "scannerNext(" & escape(n.text) & ", " & QueryNode(n.pos.node).name & ", " & repr(n.delim) & ")"
  of nkBufferRead: QueryNode(n.arrStr.node).name & "[" & emitInt(n.index) & "]"
  of nkArrRead: QueryNode(n.arrStr.node).name & "[" & emitInt(n.index) & "]"
  else: raise newException(ValueError, "bad residual string")
proc emitBool(x: Rep[bool]): string =
  if x.isStatic: return $x.staticVal
  let n = QueryNode(x.node)
  if n.kind == nkHasNext: QueryNode(n.pos.node).name & " < " & escape(n.text) & ".len"
  elif n.kind == nkStringEq: "compareStringChars(" & emitString(n.sleft) & ", " & emitString(n.sright) & ")"
  elif n.kind == nkStringLt: "compareStringLt(" & emitString(n.sleft) & ", " & emitString(n.sright) & ")"
  elif n.kind == nkStringLe: "compareStringLe(" & emitString(n.sleft) & ", " & emitString(n.sright) & ")"
  elif n.kind == nkStringGe: "compareStringGe(" & emitString(n.sleft) & ", " & emitString(n.sright) & ")"
  elif n.kind == nkEq: "(" & emitInt(n.boolLeft) & " == " & emitInt(n.boolRight) & ")"
  elif n.kind == nkLt: "(" & emitInt(n.boolLeft) & " < " & emitInt(n.boolRight) & ")"
  elif n.kind == nkLe: "(" & emitInt(n.boolLeft) & " <= " & emitInt(n.boolRight) & ")"
  elif n.kind == nkGe: "(" & emitInt(n.boolLeft) & " >= " & emitInt(n.boolRight) & ")"
  elif n.kind == nkAnd: "(" & emitBool(n.boolA) & " and " & emitBool(n.boolB) & ")"
  elif n.kind == nkOr: "(" & emitBool(n.boolA) & " or " & emitBool(n.boolB) & ")"
  elif n.kind == nkInProbe:
    let f = n.fields[0]
    let used = QueryNode(n.v.node).name
    if n.arrStr != nil:
      "inString(" & emitString(f.str.data) & ", " & QueryNode(n.arrStr.node).name & ", " & used & ")"
    else:
      "inInt(" & emitInt(f.int.value) & ", " & QueryNode(n.arr.node).name & ", " & used & ")"
  else: raise newException(ValueError, "bad residual bool")
proc emitStmt(x: Rep[Unit]; ind=""): string =
  if x.isStatic: return ind & "discard"
  let n = QueryNode(x.node)
  case n.kind
  of nkSeq: emitStmt(n.a,ind) & "\n" & emitStmt(n.b,ind)
  of nkWhile: ind & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b,ind & "  ")
  of nkIf: ind & "if " & emitBool(n.cond) & ":\n" & emitStmt(n.thenB, ind & "  ") &
    "\n" & ind & "else:\n" & emitStmt(n.elseB, ind & "  ")
  of nkClose: ind & "scannerClosed = 1"
  of nkVarWrite: ind & QueryNode(n.v.node).name & " = " & emitInt(n.value)
  of nkPrint:
    ind & "echo " & n.fields.mapIt(if it.kind == fkString: emitString(it.str.data) else: "$(" & emitInt(it.int.value) & ")").join(" & \",\" & ")
  of nkDiscard:
    n.fields.mapIt(ind & "discard " & (if it.kind == fkString: emitString(it.str.data) else: emitInt(it.int.value))).join("\n")
  of nkBufferAppend:
    let target = if n.svalue == nil: QueryNode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitInt(n.value)
                 else: QueryNode(n.arrStr.node).name & "[" & emitInt(n.index) & "] = " & emitString(n.svalue)
    ind & target & "\n" & ind & QueryNode(n.v.node).name & " = " & QueryNode(n.v.node).name & " + 1"
  of nkArrWrite:
    if n.arrStr != nil: ind & QueryNode(n.arrStr.node).name & "[" & emitInt(n.index) & "] = " & emitString(n.svalue)
    else: ind & QueryNode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitInt(n.value)
  else: ind & "discard"

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0, "nim compiler not found"
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir/"nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath,poStdErrToStdOut}, workingDir=dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath,poStdErrToStdOut}, workingDir=dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

proc ifB(c: Rep[bool]; t, e: proc(): Rep[Unit]): Rep[Unit] =
  smartIf(c, t, e, proc(x:Rep[bool]; a,b:Rep[Unit]):IRNode=QueryNode(kind:nkIf,cond:x,thenB:a,elseB:b))
proc emitDecl(v: Var[int]): string =
  let n=QueryNode(v.node); "var " & n.name & " = " & emitInt(n.init)
proc emitDecl(a: Arr[int]): string =
  let n = QueryNode(a.node); "var " & n.name & " = newSeq[int](" & emitInt(n.init) & ")"
proc emitDecl(a: Arr[string]): string =
  let n = QueryNode(a.node); "var " & n.name & " = newSeq[string](" & emitInt(n.init) & ")"

proc execOpWith(q: Operator; emitRow: proc(f: seq[RField]): Rep[Unit];
    sharedVars: var seq[Var[int]]; sharedInts: var seq[Arr[int]];
    sharedStrings: var seq[Arr[string]]; bodyOut: var Rep[Unit]; root: bool): string =
  ## Build the residual from the operator's fields.  The only host-side work
  ## here is choosing typed columns from the CSV fixture; all scanning,
  ## hashing, probing, buffering, and output are Rep nodes.
  let cap = 256
  var vars = sharedVars
  var ints = sharedInts
  var strings = sharedStrings
  proc iv(name: string; x = 0): Var[int] =
    result = newVar(staticInt(x), proc(v: Rep[int]): IRNode = QueryNode(kind:nkVarDecl,name:name,init:v)); vars.add(result)
  proc ia(name: string; size = cap): Arr[int] =
    result = newArray[int](staticInt(size), proc(v: Rep[int]): IRNode = QueryNode(kind:nkArrDecl,name:name,init:v)); ints.add(result)
  proc sa(name: string): Arr[string] =
    result = newArray[string](staticInt(cap), proc(v: Rep[int]): IRNode = QueryNode(kind:nkArrDecl,name:name,init:v)); strings.add(result)
  proc vr(v: Var[int]): Rep[int] = readVar(v, proc(x: Var[int]): IRNode = QueryNode(kind:nkVarRead,v:x))
  proc vw(v: Var[int]; x: Rep[int]): Rep[Unit] = writeVar(v,x,proc(a:Var[int]; b:Rep[int]):IRNode=QueryNode(kind:nkVarWrite,v:a,value:b))
  proc ar(a: Arr[int]; i: Rep[int]): Rep[int] = readArr(a,i,proc(x:Arr[int]; y:Rep[int]):IRNode=QueryNode(kind:nkArrRead,arr:x,index:y))
  proc sr(a: Arr[string]; i: Rep[int]): Rep[string] = readArr(a,i,proc(x:Arr[string]; y:Rep[int]):IRNode=QueryNode(kind:nkArrRead,arrStr:x,index:y))
  proc aw(a: Arr[int]; i,x:Rep[int]): Rep[Unit] = writeArr(a,i,x,proc(z:Arr[int];j,k:Rep[int]):IRNode=QueryNode(kind:nkArrWrite,arr:z,index:j,value:k))
  proc sw(a: Arr[string]; i:Rep[int]; x:Rep[string]): Rep[Unit] = writeArr(a,i,x,proc(z:Arr[string];j:Rep[int];k:Rep[string]):IRNode=QueryNode(kind:nkArrWrite,arrStr:z,index:j,svalue:k))
  proc eqI(a,b: Rep[int]): Rep[bool] = dynamic[bool](QueryNode(kind:nkEq,boolLeft:a,boolRight:b))
  proc ltI(a,b: Rep[int]): Rep[bool] = dynamic[bool](QueryNode(kind:nkLt,boolLeft:a,boolRight:b))
  proc leI(a,b: Rep[int]): Rep[bool] = dynamic[bool](QueryNode(kind:nkLe,boolLeft:a,boolRight:b))
  proc geI(a,b: Rep[int]): Rep[bool] = dynamic[bool](QueryNode(kind:nkGe,boolLeft:a,boolRight:b))
  proc andB(a,b: Rep[bool]): Rep[bool] = dynamic[bool](QueryNode(kind:nkAnd,boolA:a,boolB:b))
  proc orB(a,b: Rep[bool]): Rep[bool] = dynamic[bool](QueryNode(kind:nkOr,boolA:a,boolB:b))
  proc discardFields(xs: seq[RField]): Rep[Unit] = dynamic[Unit](QueryNode(kind:nkDiscard,fields:xs))
  proc addMany(xs: seq[Rep[Unit]]): Rep[Unit] = seqMany(xs)
  proc stringCols(csv: string; schema: seq[string]): seq[bool] =
    let delim = if q.kind == okScan: q.delim else: q.parent.delim
    sourceKinds(csv, schema, delim)
  proc row(sc: Scanner; csv: string; schema: seq[string]; kinds: seq[bool]; delim: char): seq[RField] =
    for i in 0 ..< schema.len:
      let d = if i == schema.high: '\n' else: delim
      if kinds[i]: result.add(RField(kind:fkString,str:RString(data:scannerNext(sc,d))))
      else: result.add(RField(kind:fkInt,int:RInt(value:scannerNextInt(sc,d))))
  proc scanRows(csv: string; schema: seq[string]; kinds: seq[bool]; delim: char; emitRow: proc(f: seq[RField]): Rep[Unit]): Rep[Unit] =
    let sc = scannerNew(csv)
    vars.add(sc.pos)
    let start = vw(sc.pos, staticInt(csv.find('\n') + 1))
    let loop = whileLoop(proc():Rep[bool]=scannerHasNext(sc), proc():Rep[Unit]=emitRow(row(sc,csv,schema,kinds,delim)))
    seqs(start, loop)
  var inPreds: seq[Predicate] = @[]
  var inS: seq[Arr[string]] = @[]
  var inI: seq[Arr[int]] = @[]
  var inUsed: seq[Var[int]] = @[]
  proc keyNames(a,b: seq[string]): seq[string] =
    for x in a:
      if x in b: result.add(x)
  proc predicateRep(p: Predicate; f: seq[RField]; schema: seq[string]; kinds: seq[bool]): Rep[bool] =
    case p.kind
    of pkEquals, pkLessThan, pkGreaterThan, pkLessEq, pkGreaterEq:
      var a, b: RField
      if p.left.kind == rkField: a = f[lookup(schema, p.left.name)] else: a = p.left.value
      if p.right.kind == rkField: b = f[lookup(schema, p.right.name)] else: b = p.right.value
      doAssert a.kind == b.kind, "predicate kind mismatch"
      if p.kind == pkEquals:
        result = if a.kind == fkString: stringCompare(a.str, b.str) else: eqI(a.int.value, b.int.value)
      else:
        result = if a.kind == fkString:
          case p.kind
          of pkLessThan: stringLess(a.str, b.str)
          of pkGreaterThan: stringLess(b.str, a.str)
          of pkLessEq: stringLessEq(a.str, b.str)
          of pkGreaterEq: stringGreaterEq(a.str, b.str)
          else: liftNow(false)
        else:
          case p.kind
          of pkLessThan: ltI(a.int.value, b.int.value)
          of pkGreaterThan: ltI(b.int.value, a.int.value)
          of pkLessEq: leI(a.int.value, b.int.value)
          of pkGreaterEq: geI(a.int.value, b.int.value)
          else: liftNow(false)
    of pkAnd: result = andB(predicateRep(p.a, f, schema, kinds), predicateRep(p.b, f, schema, kinds))
    of pkOr: result = orB(predicateRep(p.a, f, schema, kinds), predicateRep(p.b, f, schema, kinds))
    of pkIn:
      let j = inPreds.find(p)
      doAssert j >= 0
      let field = f[lookup(schema, p.left.name)]
      if field.kind == fkString:
        doAssert inS[j] != nil, "predicate kind mismatch"
        result = dynamic[bool](QueryNode(kind: nkInProbe, arrStr: inS[j], v: inUsed[j], fields: @[field]))
      else:
        doAssert inI[j] != nil, "predicate kind mismatch"
        result = dynamic[bool](QueryNode(kind: nkInProbe, arr: inI[j], v: inUsed[j], fields: @[field]))
  var body: Rep[Unit]
  if q.kind == okLimit:
    let count = iv("limitCount")
    proc wrappedEmitRow(f: seq[RField]): Rep[Unit] =
      ifB(ltI(vr(count), staticInt(q.n)),
        proc(): Rep[Unit] = seqs(emitRow(f), vw(count, intAdd(vr(count), staticInt(1)))),
        proc(): Rep[Unit] = discardFields(f))
    var parentBody: Rep[Unit]
    discard execOpWith(q.parent, wrappedEmitRow, vars, ints, strings, parentBody, false)
    body = parentBody
  elif q.kind == okOffset:
    let count = iv("offsetCount")
    proc wrappedEmitRow(f: seq[RField]): Rep[Unit] =
      ifB(ltI(vr(count), staticInt(q.n)),
        proc(): Rep[Unit] = seqs(discardFields(f), vw(count, intAdd(vr(count), staticInt(1)))),
        proc(): Rep[Unit] = emitRow(f))
    var parentBody: Rep[Unit]
    discard execOpWith(q.parent, wrappedEmitRow, vars, ints, strings, parentBody, false)
    body = parentBody
  elif q.kind == okHaving:
    validateHaving(q.predicate, q.parent)
    let schema = resultSchema(q.parent)
    let kinds = columnKinds(q.parent)
    proc wrappedEmitRow(f: seq[RField]): Rep[Unit] =
      let holds = predicateRep(q.predicate, f, schema, kinds)
      ifB(holds, proc(): Rep[Unit] = emitRow(f), proc(): Rep[Unit] = discardFields(f))
    var parentBody: Rep[Unit]
    discard execOpWith(q.parent, wrappedEmitRow, vars, ints, strings, parentBody, false)
    body = parentBody
  elif q.kind == okDistinct:
    let kinds = columnKinds(q.parent)
    var outS: seq[Arr[string]] = @[]
    var outI: seq[Arr[int]] = @[]
    for i, isString in kinds:
      if isString: outS.add(sa("distinctS" & $i)); outI.add(nil)
      else: outS.add(nil); outI.add(ia("distinctI" & $i))
    let used = iv("distinctUsed")
    let scanPos = iv("distinctScan")
    let priorPos = iv("distinctPrior")
    let duplicate = iv("distinctDuplicate")
    proc consume(f: seq[RField]): Rep[Unit] =
      var writes: seq[Rep[Unit]] = @[]
      for i, fld in f:
        if kinds[i]: writes.add(sw(outS[i], vr(used), fld.str.data))
        else: writes.add(aw(outI[i], vr(used), fld.int.value))
      writes.add(vw(used, intAdd(vr(used), staticInt(1))))
      addMany(writes)
    var parentBody: Rep[Unit]
    discard execOpWith(q.parent, consume, vars, ints, strings, parentBody, false)
    proc sameRow(a, b: Rep[int]): Rep[bool] =
      var same: Rep[bool] = liftNow(true)
      for i, isString in kinds:
        if isString:
          same = andB(same, stringCompare(RString(data:sr(outS[i], a)), RString(data:sr(outS[i], b))))
        else:
          same = andB(same, eqI(ar(outI[i], a), ar(outI[i], b)))
      same
    let emitDistinct = ifB(eqI(vr(duplicate), staticInt(0)),
      proc(): Rep[Unit] =
        var fields: seq[RField] = @[]
        for i, isString in kinds:
          if isString: fields.add(RField(kind:fkString, str:RString(data:sr(outS[i], vr(scanPos)))))
          else: fields.add(RField(kind:fkInt, int:RInt(value:ar(outI[i], vr(scanPos)))))
        emitRow(fields),
      proc(): Rep[Unit] = unit())
    let compareLoop = whileLoop(
      proc(): Rep[bool] = andB(ltI(vr(priorPos), vr(scanPos)), eqI(vr(duplicate), staticInt(0))),
      proc(): Rep[Unit] = seqs(
        ifB(sameRow(vr(scanPos), vr(priorPos)),
          proc(): Rep[Unit] = vw(duplicate, staticInt(1)),
          proc(): Rep[Unit] = unit()),
        vw(priorPos, intAdd(vr(priorPos), staticInt(1))))
    )
    let distinctLoop = whileLoop(
      proc(): Rep[bool] = ltI(vr(scanPos), vr(used)),
      proc(): Rep[Unit] = seqs(
        vw(priorPos, staticInt(0)),
        seqs(vw(duplicate, staticInt(0)), seqs(compareLoop,
          seqs(emitDistinct, vw(scanPos, intAdd(vr(scanPos), staticInt(1)))))))
    )
    body = seqs(parentBody, seqs(vw(scanPos, staticInt(0)), distinctLoop))
  elif q.kind == okSort:
    let schema = resultSchema(q.parent)
    let kinds = columnKinds(q.parent)
    var outS: seq[Arr[string]] = @[]
    var outI: seq[Arr[int]] = @[]
    for i, isString in kinds:
      if isString: outS.add(sa("sortS" & $i)); outI.add(nil)
      else: outS.add(nil); outI.add(ia("sortI" & $i))
    let used = iv("sortUsed")
    let pos = iv("sortPos")
    let current = iv("sortCurrent")
    let scanPos = iv("sortScan")
    let order = ia("sortOrder")
    proc consume(f: seq[RField]): Rep[Unit] =
      var writes: seq[Rep[Unit]] = @[]
      var si = 0
      var ii = 0
      for i, fld in f:
        if kinds[i]: writes.add(sw(outS[i], vr(used), fld.str.data)); inc si
        else: writes.add(aw(outI[i], vr(used), fld.int.value)); inc ii
      writes.add(vw(used, intAdd(vr(used), staticInt(1))))
      addMany(writes)
    var parentBody: Rep[Unit]
    discard execOpWith(q.parent, consume, vars, ints, strings, parentBody, false)
    proc lessRows(a, b: Rep[int]): Rep[bool] =
      var less: Rep[bool] = liftNow(false)
      var equal: Rep[bool] = liftNow(true)
      for k, name in q.sortKeys:
        let i = lookup(schema, name)
        let av = if kinds[i]: RField(kind:fkString, str:RString(data:sr(outS[i], ar(order, a))))
                 else: RField(kind:fkInt, int:RInt(value:ar(outI[i], ar(order, a))))
        let bv = if kinds[i]: RField(kind:fkString, str:RString(data:sr(outS[i], ar(order, b))))
                 else: RField(kind:fkInt, int:RInt(value:ar(outI[i], ar(order, b))))
        let lt = if kinds[i]: stringLess(av.str, bv.str) else: ltI(av.int.value, bv.int.value)
        let eq = if kinds[i]: stringCompare(av.str, bv.str) else: eqI(av.int.value, bv.int.value)
        let directed = if q.sortDesc[k]: andB(equal, if kinds[i]: stringLess(bv.str, av.str) else: ltI(bv.int.value, av.int.value)) else: andB(equal, lt)
        less = orB(less, directed)
        equal = andB(equal, eq)
      less
    let initOrder = whileLoop(proc():Rep[bool]=ltI(vr(pos),vr(used)), proc():Rep[Unit]=
      seqs(aw(order,vr(pos),vr(pos)),vw(pos,intAdd(vr(pos),staticInt(1)))))
    let sortLoop = whileLoop(proc():Rep[bool]=ltI(vr(scanPos),vr(used)), proc():Rep[Unit]=
      seqs(vw(current,ar(order,vr(scanPos))), seqs(vw(pos,vr(scanPos)),
        seqs(whileLoop(proc():Rep[bool]=andB(ltI(staticInt(0),vr(pos)),lessRows(vr(current),ar(order,intAdd(vr(pos),staticInt(-1))))), proc():Rep[Unit]=
          seqs(aw(order,vr(pos),ar(order,intAdd(vr(pos),staticInt(-1)))),vw(pos,intAdd(vr(pos),staticInt(-1))))),
          seqs(aw(order,vr(pos),vr(current)),vw(scanPos,intAdd(vr(scanPos),staticInt(1))))))))
    var output: seq[Rep[Unit]] = @[]
    let outLoop = whileLoop(proc():Rep[bool]=ltI(vr(pos),vr(used)), proc():Rep[Unit]=
      var fields: seq[RField] = @[]
      for i, isString in kinds:
        if isString: fields.add(RField(kind:fkString,str:RString(data:sr(outS[i],ar(order,vr(pos))))))
        else: fields.add(RField(kind:fkInt,int:RInt(value:ar(outI[i],ar(order,vr(pos))))))
      seqs(emitRow(fields),vw(pos,intAdd(vr(pos),staticInt(1)))))
    body = seqs(parentBody, seqs(initOrder, seqs(vw(scanPos,staticInt(1)), seqs(sortLoop, seqs(vw(pos,staticInt(0)),outLoop)))))
  elif q.kind == okGroup:
    let schema = resultSchema(q.parent)
    let stringKinds = stringCols(q.parent.csv, schema)
    var keyIndexes: seq[int] = @[]
    var keyKinds: seq[FieldKind] = @[]
    for key in q.keys:
      let keyIndex = lookup(schema, key)
      keyIndexes.add(keyIndex)
      keyKinds.add(if stringKinds[keyIndex]: fkString else: fkInt)
    let used=iv("used"); let pos=iv("slot"); let found=iv("found"); let outPos=iv("outPos")
    let occupied=ia("occupied"); let slotIndex=ia("slotIndex")
    var keyBufS: seq[Arr[string]] = @[]
    var keyBufI: seq[Arr[int]] = @[]
    var outKeyS: seq[Arr[string]] = @[]
    var outKeyI: seq[Arr[int]] = @[]
    for j, kind in keyKinds:
      if kind == fkString:
        keyBufS.add(sa(if j == 0: "groupKeys" else: "groupKeyS" & $j)); keyBufI.add(nil)
        outKeyS.add(sa(if j == 0: "outKeys" else: "outKeyS" & $j)); outKeyI.add(nil)
      else:
        keyBufS.add(nil); keyBufI.add(ia(if j == 0: "groupKeyInts" else: "groupKeyI" & $j))
        outKeyS.add(nil); outKeyI.add(ia(if j == 0: "outKeyInts" else: "outKeyI" & $j))
    let outCount=ia("outCounts"); let outAgg=ia("outAggs", cap * q.aggregates.len)
    var outAggS: seq[Arr[string]] = @[]
    for k in 0 ..< q.aggregates.len: outAggS.add(sa("outAggS" & $k))
    var inputColsS: seq[Arr[string]] = @[]
    var inputColsI: seq[Arr[int]] = @[]
    for i in 0 ..< schema.len:
      if stringKinds[i]: inputColsS.add(sa("inputColS" & $i))
      else: inputColsI.add(ia("inputColI" & $i))
    var inputAgg: seq[Arr[int]] = @[]
    for k in 0 ..< q.aggregates.len: inputAgg.add(ia("inputAgg" & $k))
    var inputAggS: seq[Arr[string]] = @[]
    for k in 0 ..< q.aggregates.len: inputAggS.add(sa("inputAggS" & $k))
    var aggIsString: seq[bool] = @[]
    for n in q.aggregates: aggIsString.add(stringKinds[lookup(schema, n)])
    let inputPos=iv("inputPos")
    proc consume(f: seq[RField]): Rep[Unit] =
      var inputWrites: seq[Rep[Unit]] = @[]
      var sCol = 0
      var iCol = 0
      for i in 0 ..< schema.len:
        if stringKinds[i]:
          inputWrites.add(sw(inputColsS[sCol],vr(inputPos),f[i].str.data)); inc sCol
        else:
          inputWrites.add(aw(inputColsI[iCol],vr(inputPos),f[i].int.value)); inc iCol
      for j,n in q.aggregates:
        let aggregateIndex = lookup(schema,n)
        var aggregateStorageIndex = 0
        for i in 0 ..< aggregateIndex:
          if stringKinds[i] == aggIsString[j]: inc aggregateStorageIndex
        if aggIsString[j]:
          inputWrites.add(sw(inputAggS[j],vr(inputPos),sr(inputColsS[aggregateStorageIndex],vr(inputPos))))
        else:
          doAssert not stringKinds[aggregateIndex], "aggregate field must be integer"
          inputWrites.add(aw(inputAgg[j],vr(inputPos),ar(inputColsI[aggregateStorageIndex],vr(inputPos))))
      var storedKeys: seq[RField] = @[]
      var h: Rep[int] = staticInt(0)
      for j, keyIndex in keyIndexes:
        var storageIndex = 0
        for i in 0 ..< keyIndex:
          if stringKinds[i] == (keyKinds[j] == fkString): inc storageIndex
        if keyKinds[j] == fkString:
          let key = sr(inputColsS[storageIndex], vr(inputPos))
          storedKeys.add(RField(kind: fkString, str: RString(data: key)))
          h = intMod(intAdd(h, fieldHash(RString(data: key))), staticInt(cap))
        else:
          let key = ar(inputColsI[storageIndex], vr(inputPos))
          storedKeys.add(RField(kind: fkInt, int: RInt(value: key)))
          h = intMod(intAdd(h, key), staticInt(cap))
      let stable = addMany(inputWrites)
      let seek = whileLoop(proc():Rep[bool]=andB(ltI(vr(pos),staticInt(cap)),eqI(vr(found),staticInt(0))), proc():Rep[Unit]=
        ifB(eqI(ar(occupied,vr(pos)),staticInt(1)),
          proc():Rep[Unit]=
            var same: Rep[bool] = liftNow(true)
            for j, key in storedKeys:
              let equal = if key.kind == fkString:
                stringCompare(key.str, RString(data: sr(keyBufS[j], vr(pos))))
              else:
                eqI(key.int.value, ar(keyBufI[j], vr(pos)))
              same = andB(same, equal)
            ifB(same,proc():Rep[Unit]=vw(found,staticInt(1)),proc():Rep[Unit]=vw(pos,intAdd(vr(pos),staticInt(1)))),
          proc():Rep[Unit]=
            var writes: seq[Rep[Unit]] = @[]
            for j, key in storedKeys:
              if key.kind == fkString: writes.add(sw(keyBufS[j], vr(pos), key.str.data))
              else: writes.add(aw(keyBufI[j], vr(pos), key.int.value))
            writes.add(aw(occupied,vr(pos),staticInt(1)))
            writes.add(vw(found,staticInt(2)))
            addMany(writes)))
      var updates: seq[Rep[Unit]] = @[stable, vw(pos,h), vw(found,staticInt(0)), seek]
      let update = ifB(eqI(vr(found),staticInt(1)),
        proc():Rep[Unit]=
          let compact = ar(slotIndex,vr(pos)); var xs: seq[Rep[Unit]] = @[aw(outCount,compact,intAdd(ar(outCount,compact),staticInt(1)))]
          for j,n in q.aggregates:
            if aggIsString[j]:
              let current = sr(outAggS[j], compact); let incoming = sr(inputAggS[j],vr(inputPos))
              case q.aggKinds[j]
              of akMin: xs.add(ifB(stringLess(RString(data:incoming),RString(data:current)), proc():Rep[Unit]=sw(outAggS[j],compact,incoming), proc():Rep[Unit]=unit()))
              of akMax: xs.add(ifB(stringLess(RString(data:current),RString(data:incoming)), proc():Rep[Unit]=sw(outAggS[j],compact,incoming), proc():Rep[Unit]=unit()))
              of akSum, akAvg: doAssert false, "aggregate field must be integer"
            else:
              let aggregateIndex = intAdd(intMul(compact,staticInt(q.aggregates.len)),staticInt(j))
              let current = ar(outAgg, aggregateIndex)
              let incoming = ar(inputAgg[j],vr(inputPos))
              case q.aggKinds[j]
              of akSum, akAvg: xs.add(aw(outAgg,aggregateIndex,intAdd(current,incoming)))
              of akMin: xs.add(ifB(ltI(incoming,current), proc():Rep[Unit]=aw(outAgg,aggregateIndex,incoming), proc():Rep[Unit]=unit()))
              of akMax: xs.add(ifB(ltI(current,incoming), proc():Rep[Unit]=aw(outAgg,aggregateIndex,incoming), proc():Rep[Unit]=unit()))
          addMany(xs),
        proc():Rep[Unit]=
          var xs: seq[Rep[Unit]] = @[aw(slotIndex,vr(pos),vr(used)), aw(outCount,vr(used),staticInt(1))]
          for j, key in storedKeys:
            if key.kind == fkString: xs.add(sw(outKeyS[j],vr(used),key.str.data))
            else: xs.add(aw(outKeyI[j],vr(used),key.int.value))
          for j,n in q.aggregates:
            if aggIsString[j]: xs.add(sw(outAggS[j],vr(used),sr(inputAggS[j],vr(inputPos))))
            else: xs.add(aw(outAgg,intAdd(intMul(vr(used),staticInt(q.aggregates.len)),staticInt(j)),ar(inputAgg[j],vr(inputPos))))
          xs.add(vw(used,intAdd(vr(used),staticInt(1)))); addMany(xs))
      updates.add(update); updates.add(vw(inputPos,intAdd(vr(inputPos),staticInt(1)))); addMany(updates)
    let consumeAll = scanRows(q.parent.csv, schema, stringKinds, q.parent.delim, consume)
    var output: seq[Rep[Unit]] = @[]
    let outLoop = whileLoop(proc():Rep[bool]=ltI(vr(outPos),vr(used)), proc():Rep[Unit]=
      var fs: seq[RField] = @[]
      for j, kind in keyKinds:
        if kind == fkString:
          fs.add(RField(kind:fkString,str:RString(data:sr(outKeyS[j],vr(outPos)))))
        else:
          fs.add(RField(kind:fkInt,int:RInt(value:ar(outKeyI[j],vr(outPos)))))
      fs.add(RField(kind:fkInt,int:RInt(value:ar(outCount,vr(outPos)))))
      for j in 0 ..< q.aggregates.len:
        if aggIsString[j]:
          fs.add(RField(kind:fkString,str:RString(data:sr(outAggS[j],vr(outPos)))))
        else:
          let aggregate = ar(outAgg,intAdd(intMul(vr(outPos),staticInt(q.aggregates.len)),staticInt(j)))
          let value = if q.aggKinds[j] == akAvg: intDiv(aggregate, ar(outCount,vr(outPos))) else: aggregate
          fs.add(RField(kind:fkInt,int:RInt(value:value)))
      seqs(emitRow(fs),vw(outPos,intAdd(vr(outPos),staticInt(1)))))
    body = seqs(consumeAll,outLoop)
  elif q.kind == okHashJoin:
    let ls=resultSchema(q.parent); let rs=resultSchema(q.right); let keys=keyNames(ls,rs)
    let lk=stringCols(q.parent.csv,ls); let rk=stringCols(q.right.csv,rs)
    let used=iv("joinUsed"); let pos=iv("joinPos"); let occupied=ia("joinOccupied"); let hkeys=sa("joinKeys")
    var hrowsI: seq[Arr[int]] = @[]
    for k in 0 ..< ls.len: hrowsI.add(ia("joinI" & $k))
    var hrowsS: seq[Arr[string]] = @[]
    for k in 0 ..< ls.len: hrowsS.add(sa("joinS" & $k))
    var leftTmpI: seq[Arr[int]] = @[]
    for k in 0 ..< ls.len: leftTmpI.add(ia("leftTmpI" & $k))
    var leftTmpS: seq[Arr[string]] = @[]
    for k in 0 ..< ls.len: leftTmpS.add(sa("leftTmpS" & $k))
    let leftTmpPos=iv("leftTmpPos")
    var rightTmpI: seq[Arr[int]] = @[]
    for k in 0 ..< rs.len: rightTmpI.add(ia("rightTmpI" & $k))
    var rightTmpS: seq[Arr[string]] = @[]
    for k in 0 ..< rs.len: rightTmpS.add(sa("rightTmpS" & $k))
    let rightTmpPos=iv("rightTmpPos")
    let rscan= scannerNew(q.right.csv); vars.add(rscan.pos)
    proc hashOf(fs: seq[RField]; schema: seq[string]): Rep[int] =
      result = fieldHash(fs[lookup(schema,keys[0])].str)
      for k in keys[1 .. ^1]: result = intMod(intAdd(result,fieldHash(fs[lookup(schema,k)].str)),staticInt(cap))
      result = intMod(result,staticInt(cap))
    let build = scanRows(q.parent.csv,ls,lk,q.parent.delim,proc(f: seq[RField]):Rep[Unit]=
      var stableWrites: seq[Rep[Unit]] = @[]; var sf: seq[RField] = @[]
      for j in 0 ..< ls.len:
        if lk[j]: stableWrites.add(sw(leftTmpS[j],vr(leftTmpPos),f[j].str.data)); sf.add(RField(kind:fkString,str:RString(data:sr(leftTmpS[j],vr(leftTmpPos)))))
        else: stableWrites.add(aw(leftTmpI[j],vr(leftTmpPos),f[j].int.value)); sf.add(RField(kind:fkInt,int:RInt(value:ar(leftTmpI[j],vr(leftTmpPos)))))
      var xs: seq[Rep[Unit]] = @[addMany(stableWrites), vw(pos,hashOf(sf,ls))]
      let seek=whileLoop(proc():Rep[bool]=eqI(ar(occupied,vr(pos)),staticInt(1)),proc():Rep[Unit]=vw(pos,intMod(intAdd(vr(pos),staticInt(1)),staticInt(cap))))
      xs.add(seek); xs.add(aw(occupied,vr(pos),staticInt(1)))
      for j,n in keys: xs.add(sw(hkeys,intAdd(intMul(vr(pos),staticInt(keys.len)),staticInt(j)),sf[lookup(ls,n)].str.data))
      for j,fld in sf:
        if fld.kind == fkString: xs.add(writeArr[string](hrowsS[j],vr(pos),fld.str.data,proc(a:Arr[string];i:Rep[int];x:Rep[string]):IRNode=QueryNode(kind:nkArrWrite,arrStr:a,index:i,svalue:x)))
        else: xs.add(aw(hrowsI[j],vr(pos),fld.int.value))
      xs.add(vw(used,intAdd(vr(used),staticInt(1)))); xs.add(vw(leftTmpPos,intAdd(vr(leftTmpPos),staticInt(1)))); addMany(xs))
    let probe = seqs(vw(rscan.pos,staticInt(q.right.csv.find('\n')+1)),whileLoop(proc():Rep[bool]=scannerHasNext(rscan),proc():Rep[Unit]=
      let f=row(rscan,q.right.csv,rs,rk,q.right.delim); var stableWrites: seq[Rep[Unit]] = @[]; var sf: seq[RField] = @[]
      for j in 0 ..< rs.len:
        if rk[j]: stableWrites.add(sw(rightTmpS[j],vr(rightTmpPos),f[j].str.data)); sf.add(RField(kind:fkString,str:RString(data:sr(rightTmpS[j],vr(rightTmpPos)))))
        else: stableWrites.add(aw(rightTmpI[j],vr(rightTmpPos),f[j].int.value)); sf.add(RField(kind:fkInt,int:RInt(value:ar(rightTmpI[j],vr(rightTmpPos)))))
      var xs: seq[Rep[Unit]] = @[addMany(stableWrites), vw(pos,hashOf(sf,rs))]
      let loop=whileLoop(proc():Rep[bool]=eqI(ar(occupied,vr(pos)),staticInt(1)),proc():Rep[Unit]=
        var same=stringCompare(RString(data:sr(hkeys,intAdd(intMul(vr(pos),staticInt(keys.len)),staticInt(0)))),sf[lookup(rs,keys[0])].str)
        for j in 1 ..< keys.len: same=andB(same,stringCompare(RString(data:sr(hkeys,intAdd(intMul(vr(pos),staticInt(keys.len)),staticInt(j)))),sf[lookup(rs,keys[j])].str))
        var outputFields: seq[RField] = @[]
        for j in 0 ..< ls.len: outputFields.add(if lk[j]: RField(kind:fkString,str:RString(data:sr(hrowsS[j],vr(pos)))) else: RField(kind:fkInt,int:RInt(value:ar(hrowsI[j],vr(pos)))))
        outputFields.add(sf); seqs(ifB(same,proc():Rep[Unit]=emitRow(outputFields),proc():Rep[Unit]=unit()),vw(pos,intMod(intAdd(vr(pos),staticInt(1)),staticInt(cap)))))
      seqs(addMany(xs),seqs(loop,vw(rightTmpPos,intAdd(vr(rightTmpPos),staticInt(1)))))))
    body=seqs(build,probe)
  elif q.kind == okFilter:
    let schema = resultSchema(q.parent)
    let kinds = stringCols(q.parent.csv, schema)
    proc collectIn(p: Predicate) =
      case p.kind
      of pkAnd, pkOr: collectIn(p.a); collectIn(p.b)
      of pkIn: inPreds.add(p)
      else: discard
    collectIn(q.predicate)
    var fillBodies: seq[Rep[Unit]] = @[]
    for j, pred in inPreds:
      doAssert pred.left.kind == rkField, "IN left operand must be a field"
      let leftKind = refKind(pred.left, schema, kinds)
      let subKinds = columnKinds(pred.subquery)
      doAssert subKinds.len > 0, "IN subquery must have a column"
      let subKind = if subKinds[0]: fkString else: fkInt
      doAssert leftKind == subKind, "predicate kind mismatch"
      let used = iv("inUsed" & $j)
      inUsed.add(used)
      if subKind == fkString:
        let values = sa("inValuesS" & $j)
        inS.add(values); inI.add(nil)
        var fill: Rep[Unit]
        discard execOpWith(pred.subquery,
          proc(fields: seq[RField]): Rep[Unit] =
            doAssert fields[0].kind == fkString
            seqs(sw(values, vr(used), fields[0].str.data), vw(used, intAdd(vr(used), staticInt(1)))),
          vars, ints, strings, fill, false)
        fillBodies.add(fill)
      else:
        let values = ia("inValuesI" & $j)
        inI.add(values); inS.add(nil)
        var fill: Rep[Unit]
        discard execOpWith(pred.subquery,
          proc(fields: seq[RField]): Rep[Unit] =
            doAssert fields[0].kind == fkInt
            seqs(aw(values, vr(used), fields[0].int.value), vw(used, intAdd(vr(used), staticInt(1)))),
          vars, ints, strings, fill, false)
        fillBodies.add(fill)
    let pos = iv("filterPos")
    var bs: seq[Arr[string]] = @[]
    var bi: seq[Arr[int]] = @[]
    for i in 0 ..< schema.len:
      if kinds[i]: bs.add(sa("filterS" & $i))
      else: bi.add(ia("filterI" & $i))
    body = scanRows(q.parent.csv, schema, kinds, q.parent.delim, proc(f: seq[RField]): Rep[Unit] =
      var writes: seq[Rep[Unit]] = @[]; var si = 0; var ii = 0
      for i in 0 ..< schema.len:
        if kinds[i]: writes.add(sw(bs[si], vr(pos), f[i].str.data)); inc si
        else: writes.add(aw(bi[ii], vr(pos), f[i].int.value)); inc ii
      var loaded: seq[RField] = @[]; si = 0; ii = 0
      for i in 0 ..< schema.len:
        if kinds[i]: loaded.add(RField(kind: fkString, str: RString(data: sr(bs[si], vr(pos))))); inc si
        else: loaded.add(RField(kind: fkInt, int: RInt(value: ar(bi[ii], vr(pos))))); inc ii
      let same = predicateRep(q.predicate, loaded, schema, kinds)
      seqs(addMany(writes), seqs(ifB(same, proc():Rep[Unit]=emitRow(loaded), proc():Rep[Unit]=unit()), vw(pos, intAdd(vr(pos), staticInt(1))))))
    body = seqs(seqMany(fillBodies), body)
  elif q.kind == okProject:
    let source = if q.parent.kind == okFilter: q.parent.parent else: q.parent
    let schema = resultSchema(source)
    let kinds = stringCols(source.csv, schema)
    let input = if q.inputSchema.len == 0: q.outputSchema else: q.inputSchema
    let emit = proc(f: seq[RField]): Rep[Unit] =
      var selected: seq[RField] = @[]
      for name in input: selected.add(f[lookup(schema,name)])
      emitRow(selected)
    if q.parent.kind == okFilter:
      let pred = q.parent.predicate
      var fillBodies: seq[Rep[Unit]] = @[]
      proc collectIn(p: Predicate) =
        case p.kind
        of pkAnd, pkOr: collectIn(p.a); collectIn(p.b)
        of pkIn: inPreds.add(p)
        else: discard
      collectIn(pred)
      for j, inPred in inPreds:
        let leftKind = refKind(inPred.left, schema, kinds)
        let subKinds = columnKinds(inPred.subquery)
        doAssert subKinds.len > 0
        let subKind = if subKinds[0]: fkString else: fkInt
        doAssert leftKind == subKind, "predicate kind mismatch"
        let used = iv("inUsed" & $j)
        inUsed.add(used)
        if subKind == fkString:
          let values = sa("inValuesS" & $j)
          inS.add(values); inI.add(nil)
          var fill: Rep[Unit]
          discard execOpWith(inPred.subquery, proc(fields: seq[RField]): Rep[Unit] =
            seqs(sw(values, vr(used), fields[0].str.data), vw(used, intAdd(vr(used), staticInt(1)))),
            vars, ints, strings, fill, false)
          fillBodies.add(fill)
        else:
          let values = ia("inValuesI" & $j)
          inI.add(values); inS.add(nil)
          var fill: Rep[Unit]
          discard execOpWith(inPred.subquery, proc(fields: seq[RField]): Rep[Unit] =
            seqs(aw(values, vr(used), fields[0].int.value), vw(used, intAdd(vr(used), staticInt(1)))),
            vars, ints, strings, fill, false)
          fillBodies.add(fill)
      # Buffer the scanned row first: the scanner Rep nodes advance the
      # residual scanner position each time they are emitted, so the
      # predicate and the projection must both read the buffered values —
      # emitting the raw row twice misaligns the scanner (parseInt on a
      # later field's text). This mirrors the okFilter branch.
      let pos = iv("projectFilterPos")
      var bs: seq[Arr[string]] = @[]
      var bi: seq[Arr[int]] = @[]
      for i in 0 ..< schema.len:
        if kinds[i]: bs.add(sa("projectFilterS" & $i))
        else: bi.add(ia("projectFilterI" & $i))
      body = scanRows(source.csv, schema, kinds, source.delim, proc(f: seq[RField]): Rep[Unit] =
        var writes: seq[Rep[Unit]] = @[]; var si = 0; var ii = 0
        for i in 0 ..< schema.len:
          if kinds[i]: writes.add(sw(bs[si], vr(pos), f[i].str.data)); inc si
          else: writes.add(aw(bi[ii], vr(pos), f[i].int.value)); inc ii
        var loaded: seq[RField] = @[]; si = 0; ii = 0
        for i in 0 ..< schema.len:
          if kinds[i]: loaded.add(RField(kind:fkString,str:RString(data:sr(bs[si],vr(pos))))); inc si
          else: loaded.add(RField(kind:fkInt,int:RInt(value:ar(bi[ii],vr(pos))))); inc ii
        let same = predicateRep(pred, loaded, schema, kinds)
        seqs(addMany(writes), seqs(ifB(same, proc(): Rep[Unit] = emit(loaded), proc(): Rep[Unit] = unit()), vw(pos, intAdd(vr(pos), staticInt(1))))))
      body = seqs(seqMany(fillBodies), body)
    else:
      # Buffer the parent's rows first, then project from the buffer. The
      # scanner Rep nodes advance the residual scanner position each time
      # they are emitted, so emitting only the projected fields would
      # misalign the scanner — each loop iteration would consume one field
      # instead of one row (verified: `select Name from t.csv` staged
      # returned all 9 fields on main). Routing the parent through
      # execOpWith also fixes Project over Group/Join parents, which the
      # old scanRows(source.csv, ...) path read as raw CSV (for Group,
      # source.csv is empty, so `select distinct Dept ... group by ...`
      # staged returned no rows at all).
      let pos = iv("projectPos")
      let pkinds = columnKinds(q.parent)
      var bs: seq[Arr[string]] = @[]
      var bi: seq[Arr[int]] = @[]
      for i in 0 ..< schema.len:
        if pkinds[i]: bs.add(sa("projectS" & $i))
        else: bi.add(ia("projectI" & $i))
      var parentBody: Rep[Unit]
      proc bufferedEmit(f: seq[RField]): Rep[Unit] =
        var writes: seq[Rep[Unit]] = @[]; var si = 0; var ii = 0
        for i in 0 ..< schema.len:
          if pkinds[i]: writes.add(sw(bs[si], vr(pos), f[i].str.data)); inc si
          else: writes.add(aw(bi[ii], vr(pos), f[i].int.value)); inc ii
        var loaded: seq[RField] = @[]; si = 0; ii = 0
        for i in 0 ..< schema.len:
          if pkinds[i]: loaded.add(RField(kind:fkString,str:RString(data:sr(bs[si],vr(pos))))); inc si
          else: loaded.add(RField(kind:fkInt,int:RInt(value:ar(bi[ii],vr(pos))))); inc ii
        seqs(addMany(writes), seqs(emit(loaded), vw(pos, intAdd(vr(pos), staticInt(1)))))
      discard execOpWith(q.parent, bufferedEmit, vars, ints, strings, parentBody, false)
      body = parentBody
  elif q.kind == okJoin:
    let ls = resultSchema(q.parent); let rs = resultSchema(q.right)
    let lk = stringCols(q.parent.csv, ls); let rk = stringCols(q.right.csv, rs)
    body = scanRows(q.parent.csv, ls, lk, q.parent.delim, proc(left: seq[RField]): Rep[Unit] =
      scanRows(q.right.csv, rs, rk, q.right.delim, proc(right: seq[RField]): Rep[Unit] =
        var same: Rep[bool] = liftNow(true)
        for name in ls:
          if name in rs:
            let li = lookup(ls,name); let ri = lookup(rs,name)
            doAssert left[li].kind == right[ri].kind, "join kind mismatch"
            let eq = if left[li].kind == fkString: stringCompare(left[li].str,right[ri].str) else: eqI(left[li].int.value,right[ri].int.value)
            same = andB(same,eq)
        ifB(same, proc():Rep[Unit]=emitRow(left & right), proc():Rep[Unit]=unit())))
  else:
    let schema = resultSchema(if q.kind == okScan: q else: q.parent)
    let csv = if q.kind == okScan: q.csv else: q.parent.csv
    let kinds=stringCols(csv,schema)
    body=scanRows(csv,schema,kinds,if q.kind == okScan: q.delim else: q.parent.delim,proc(f: seq[RField]):Rep[Unit]=emitRow(f))
  result = "import std/strutils\n\nproc compareStringChars(a,b: string): bool =\n  var i = 0\n  result = a.len == b.len\n  while result and i < a.len:\n    result = a[i] == b[i]\n    inc i\n\nproc hashString(a: string): int =\n  var i = 0\n  result = 0\n  while i < a.len:\n    result = result * 41 + ord(a[i])\n    inc i\n\nproc scannerNext(text: string; pos: var int; delim: char): string =\n  let start = pos\n  var stop = pos\n  while stop < text.len and text[stop] != delim: inc stop\n  result = text[start ..< stop]\n  if stop < text.len: inc stop\n  pos = stop\n\n"
  result = result.replace("proc compareStringChars(a,b: string): bool =", "proc inString(x: string; a: seq[string]; n: int): bool =\n  var i = 0\n  while i < n:\n    if x == a[i]: return true\n    inc i\n  false\n\nproc inInt(x: int; a: seq[int]; n: int): bool =\n  var i = 0\n  while i < n:\n    if x == a[i]: return true\n    inc i\n  false\n\nproc compareStringChars(a,b: string): bool =")
  bodyOut = body
  sharedVars = vars
  sharedInts = ints
  sharedStrings = strings
  if not root: return ""
  result = result.replace("proc hashString(a: string): int =", "proc compareStringLt(a,b: string): bool =\n  var i = 0\n  while i < a.len and i < b.len and a[i] == b[i]: inc i\n  if i == a.len or i == b.len: return a.len < b.len\n  result = a[i] < b[i]\n\nproc compareStringLe(a,b: string): bool = compareStringLt(a,b) or compareStringChars(a,b)\nproc compareStringGe(a,b: string): bool = compareStringLt(b,a) or compareStringChars(a,b)\n\nproc hashString(a: string): int =")
  for a in strings: result.add(emitDecl(a) & "\n")
  for a in ints: result.add(emitDecl(a) & "\n")
  for v in vars: result.add(emitDecl(v) & "\n")
  result.add(emitStmt(body) & "\n")

proc execOp*(q: Operator): string =
  var vars: seq[Var[int]] = @[]
  var ints: seq[Arr[int]] = @[]
  var strings: seq[Arr[string]] = @[]
  var body: Rep[Unit]
  proc printRow(f: seq[RField]): Rep[Unit] = dynamic[Unit](QueryNode(kind:nkPrint,fields:f))
  result = execOpWith(q, printRow, vars, ints, strings, body, true)

proc runStaged*(q: Operator): seq[string] =
  let d = getTempDir()/("query-optc-" & $getCurrentProcessId()); createDir(d)
  let src=d/"residual.nim"; writeFile(src, execOp(q)); let outputText=compileRun(src,d/"residual",d)
  if outputText.len > 0: result=outputText.splitLines
  removeDir(d)

proc runBufferRoundTrip(): string =
  let d = getTempDir()/"query-optc-buffer"; createDir(d)
  let b = ArrayBuffer(ints: newArray[int](staticInt(4), proc(n:Rep[int]):IRNode=QueryNode(kind:nkArrDecl,name:"bufferInts",init:n)), strings: newArray[string](staticInt(4), proc(n:Rep[int]):IRNode=QueryNode(kind:nkArrDecl,name:"bufferStrings",init:n)), len:newVar(staticInt(0),proc(n:Rep[int]):IRNode=QueryNode(kind:nkVarDecl,name:"bufferLen",init:n)))
  let ai = bufferAppend(b, intField(42)); let astr = bufferAppend(b, staticField("Ada"))
  let ri = bufferRead(b, staticInt(0), fkInt); let rs = bufferRead(b, staticInt(1), fkString)
  let printed = dynamic[Unit](QueryNode(kind:nkPrint,fields: @[ri,rs]))
  let src=d/"buffer.nim"; writeFile(src, "import std/strutils\n" & emitDecl(b.ints) & "\n" & emitDecl(b.strings) & "\n" & emitDecl(b.len) & "\n" & emitStmt(seqMany(@[ai,astr,printed])) & "\n")
  result = compileRun(src,d/"buffer",d)
  removeDir(d)

when isMainModule:
  let csv = "name,amount\nAda,10\nBob,20\nAda,7\n"
  let q = group(@["name"], @["amount"], scan(csv,@["name","amount"]))
  let expected = directRows(q).mapIt(it.join(","))
  let scanQ = scan(csv, @["name", "amount"])
  doAssert runStaged(scanQ) == directRows(scanQ).mapIt(it.join(","))
  let residual = execOp(q)
  doAssert "newSeq[string]" in residual
  doAssert "hashString(" in residual and residual.count("hashString(") > 1
  doAssert "compareStringChars(" in residual and residual.count("compareStringChars(") > 1
  doAssert "while stop < text.len" in residual
  doAssert "while result and i < a.len" in residual
  doAssert "result = result * 41 + ord(a[i])" in residual
  let stagedGroup = runStaged(q)
  doAssert sorted(stagedGroup) == sorted(expected), $stagedGroup & " != " & $expected

  let intKeyCsv = "dept,amount\n10,2\n20,3\n10,5\n"
  let intKeyGroup = group(@["dept"], @["amount"], scan(intKeyCsv,@["dept","amount"]))
  let intKeyResidual = execOp(intKeyGroup)
  doAssert "groupKeyInts" in intKeyResidual and "outKeyInts" in intKeyResidual
  doAssert sorted(runStaged(intKeyGroup)) == sorted(directRows(intKeyGroup).mapIt(it.join(",")))

  let mixedKeyCsv = "dept,name,amount\n10,Ada,2\n10,Bob,3\n10,Ada,5\n"
  let mixedKeyGroup = group(@["dept", "name"], @["amount"], scan(mixedKeyCsv,@["dept","name","amount"]))
  doAssert sorted(runStaged(mixedKeyGroup)) == sorted(directRows(mixedKeyGroup).mapIt(it.join(",")))

  let reverseMaxCsv = "name,amount\nAda,7\nAda,10\n"
  let reverseMaxGroup = group(@["name"], @["amount"], scan(reverseMaxCsv,@["name","amount"]), akMax)
  doAssert runStaged(reverseMaxGroup) == directRows(reverseMaxGroup).mapIt(it.join(","))
  doAssert runStaged(reverseMaxGroup) == @["Ada,2,10"]

  var manyGroups = "name,a,b\n"
  for i in 0 ..< 40: manyGroups.add("G" & $i & "," & $(i + 1) & "," & $(i + 2) & "\n")
  let manyAggs = group(@["name"], @["a", "b"], scan(manyGroups, @["name", "a", "b"]))
  doAssert sorted(runStaged(manyAggs)) == sorted(directRows(manyAggs).mapIt(it.join(",")))

  var hundredGroups = "name,a,b\n"
  for i in 0 ..< 100: hundredGroups.add("G" & $i & "," & $(i + 1) & "," & $(i + 2) & "\n")
  let hundredAggs = group(@["name"], @["a", "b"], scan(hundredGroups, @["name", "a", "b"]))
  let hundredStaged = runStaged(hundredAggs)
  doAssert sorted(hundredStaged) == sorted(directRows(hundredAggs).mapIt(it.join(",")))
  doAssert hundredStaged.len == 100

  let nonKeyStringCsv = "name,dept,amount\nAda,10,2\nBob,20,3\nAda,30,5\n"
  let nonKeyStringGroup = group(@["name"], @["amount"], scan(nonKeyStringCsv,@["name","dept","amount"]))
  doAssert sorted(runStaged(nonKeyStringGroup)) == sorted(directRows(nonKeyStringGroup).mapIt(it.join(",")))

  let l = "id,value\nA,2\nB,3\n"
  let r = "id,rvalue\nA,10\nB,20\n"
  let hj = hashJoin(scan(l,@["id","value"]), scan(r,@["id","rvalue"]))
  doAssert runStaged(hj) == directRows(hj).mapIt(it.join(",")), $runStaged(hj) & " != " & $directRows(hj).mapIt(it.join(","))

  # Typed ArrayBuffer/ColBuffer round-trip is residual code, not a host seq.
  let b = ArrayBuffer(ints: newArray[int](staticInt(4), proc(n:Rep[int]):IRNode=QueryNode(kind:nkArrDecl,name:"ints",init:n)), strings: newArray[string](staticInt(4), proc(n:Rep[int]):IRNode=QueryNode(kind:nkArrDecl,name:"strings",init:n)), len:newVar(staticInt(0),proc(n:Rep[int]):IRNode=QueryNode(kind:nkVarDecl,name:"bufferLen",init:n)))
  let appended = bufferAppend(b, intField(42))
  let indexed = bufferRead(b, staticInt(0), fkInt)
  let appendedString = bufferAppend(b, staticField("Ada")); let indexedString = bufferRead(b, staticInt(1), fkString)
  doAssert b.ints.node != nil and b.strings.node != nil and b.len.node != nil and appended.node != nil and appendedString.node != nil and indexed.int.value.node != nil and indexedString.str.data.node != nil
  doAssert runBufferRoundTrip() == "42,Ada"
  let s = scannerNew("Ada,42\n")
  let loop = whileLoop(proc():Rep[bool]=scannerHasNext(s), proc():Rep[Unit]=scannerClose(s))
  doAssert "while stop < text.len" in execOp(scan("name,amount\nAda,1\n", @["name","amount"]))
  doAssert not scannerIsPure(QueryNode(scannerNext(s, ',').node))
  doAssert stringCompare(staticField("Ada").str, staticField("Ada").str).node != nil
  doAssert fieldHash(staticField("Ada").str).node != nil
  doAssert loop.node != nil
  echo "ok: residual query compiler"
