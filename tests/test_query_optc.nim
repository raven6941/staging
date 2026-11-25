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
    nkEq, nkLt, nkAnd, nkNot, nkStringLen, nkStringEq, nkHash, nkMod, nkArrDecl,
    nkArrRead, nkArrWrite, nkBufferLen, nkBufferAppend, nkBufferRead, nkPrint
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
    kind: RefKind
    name: string
    value: RField
  Predicate* = object
    left, right: Ref
  OpKind* = enum okScan, okFilter, okProject, okJoin, okHashJoin, okGroup, okPrintCSV
  Operator* = ref object
    kind: OpKind
    csv, csvRight: string
    schema, outputSchema, inputSchema, keys, aggregates: seq[string]
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
proc group*(keys, aggs: seq[string]; q: Operator): Operator = Operator(kind: okGroup, keys: keys, aggregates: aggs, parent: q)
proc printCSV(q: Operator): Operator = Operator(kind: okPrintCSV, parent: q)
proc equals*(a, b: Ref): Predicate = Predicate(left: a, right: b)

proc resultSchema*(q: Operator): seq[string] =
  case q.kind
  of okScan: q.schema
  of okFilter, okPrintCSV: resultSchema(q.parent)
  of okProject: q.outputSchema
  of okJoin, okHashJoin: resultSchema(q.parent) & resultSchema(q.right)
  of okGroup: q.keys & @["count"] & q.aggregates

proc opShape*(q: Operator): string =
  ## A compact structural view used by the SQL front-end tests.
  case q.kind
  of okScan: "Scan(" & q.schema.join(",") & ")"
  of okFilter: "Filter(" & opShape(q.parent) & ")"
  of okProject: "Project(" & q.outputSchema.join(",") & ";" & q.inputSchema.join(",") & ";" & opShape(q.parent) & ")"
  of okJoin: "Join(" & opShape(q.parent) & ";" & opShape(q.right) & ")"
  of okHashJoin: "HashJoin(" & opShape(q.parent) & ";" & opShape(q.right) & ")"
  of okGroup: "Group(" & q.keys.join(",") & ";" & q.aggregates.join(",") & ";" & opShape(q.parent) & ")"
  of okPrintCSV: "Print(" & opShape(q.parent) & ")"

proc lookup(s: seq[string]; n: string): int =
  result = s.find(n); doAssert result >= 0, "unknown field " & n

proc parseRows*(csv: string; delim = ','): seq[seq[string]] =
  for line in csv.strip.splitLines[1 .. ^1]:
    if line.len > 0: result.add(line.split(delim))

proc refText(r: Ref; row: seq[string]; schema: seq[string]): string =
  if r.kind == rkField: row[lookup(schema, r.name)]
  elif r.value.kind == fkString: r.value.str.data.staticVal
  else: $r.value.int.value.staticVal

proc refKind(r: Ref; schema: seq[string]; kinds: seq[bool]): FieldKind =
  if r.kind == rkField:
    if kinds[lookup(schema, r.name)]: fkString else: fkInt
  else: r.value.kind

proc columnKinds(q: Operator): seq[bool] =
  let schema = resultSchema(q)
  let rows = directRows(q)
  if rows.len == 0: return newSeq[bool](schema.len)
  for cell in rows[0]:
    try: discard parseInt(cell); result.add(false)
    except ValueError: result.add(true)

proc directRows(q: Operator): seq[seq[string]] =
  case q.kind
  of okScan: result = parseRows(q.csv, q.delim)
  of okFilter:
    let ps = resultSchema(q.parent)
    let kinds = columnKinds(q.parent)
    for row in directRows(q.parent):
        let aKind = refKind(q.predicate.left, ps, kinds)
        let bKind = refKind(q.predicate.right, ps, kinds)
        doAssert aKind == bKind, "predicate kind mismatch"
        if refText(q.predicate.left, row, ps) == refText(q.predicate.right, row, ps): result.add(row)
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
    let ps = resultSchema(q.parent); var groups = initTable[string, seq[string]]()
    for row in directRows(q.parent):
      let k = q.keys.mapIt(row[lookup(ps, it)]).join("\x1f")
      if not groups.hasKey(k): groups[k] = q.keys.mapIt(row[lookup(ps, it)]) & @[$1] & q.aggregates.mapIt(row[lookup(ps, it)])
      else:
        groups[k][q.keys.len] = $(parseInt(groups[k][q.keys.len]) + 1)
        for j, n in q.aggregates: groups[k][q.keys.len + 1 + j] = $(parseInt(groups[k][q.keys.len + 1 + j]) + parseInt(row[lookup(ps, n)]))
    for x in groups.values: result.add(x)
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
proc fieldHash(a: RString): Rep[int] =
  dynamic[int](QueryNode(kind: nkHash, sleft: a.data))
proc intAdd(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x+y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkAdd,left:x,right:y))
proc intMul(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x*y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkMul,left:x,right:y))
proc intMod(a, b: Rep[int]): Rep[int] = smartOp[int](a, b, proc(x,y:int):int=x mod y, proc(x,y:Rep[int]):IRNode=QueryNode(kind:nkMod,left:x,right:y))
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
  elif n.kind == nkEq: "(" & emitInt(n.boolLeft) & " == " & emitInt(n.boolRight) & ")"
  elif n.kind == nkLt: "(" & emitInt(n.boolLeft) & " < " & emitInt(n.boolRight) & ")"
  elif n.kind == nkAnd: "(" & emitBool(n.boolA) & " and " & emitBool(n.boolB) & ")"
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

proc execOp(q: Operator): string =
  ## Build the residual from the operator's fields.  The only host-side work
  ## here is choosing typed columns from the CSV fixture; all scanning,
  ## hashing, probing, buffering, and output are Rep nodes.
  let cap = 64
  var vars: seq[Var[int]] = @[]
  var ints: seq[Arr[int]] = @[]
  var strings: seq[Arr[string]] = @[]
  proc iv(name: string; x = 0): Var[int] =
    result = newVar(staticInt(x), proc(v: Rep[int]): IRNode = QueryNode(kind:nkVarDecl,name:name,init:v)); vars.add(result)
  proc ia(name: string): Arr[int] =
    result = newArray[int](staticInt(cap), proc(v: Rep[int]): IRNode = QueryNode(kind:nkArrDecl,name:name,init:v)); ints.add(result)
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
  proc andB(a,b: Rep[bool]): Rep[bool] = dynamic[bool](QueryNode(kind:nkAnd,boolA:a,boolB:b))
  proc pr(xs: seq[RField]): Rep[Unit] = dynamic[Unit](QueryNode(kind:nkPrint,fields:xs))
  proc addMany(xs: seq[Rep[Unit]]): Rep[Unit] = seqMany(xs)
  proc firstData(csv: string; col: int; delim: char): string = csv.strip.splitLines[1].split(delim)[col]
  proc stringCols(csv: string; schema: seq[string]): seq[bool] =
    let delim = if q.kind == okScan: q.delim else: q.parent.delim
    for i in 0 ..< schema.len:
      try: discard parseInt(firstData(csv, i, delim)); result.add(false)
      except ValueError: result.add(true)
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
  proc keyNames(a,b: seq[string]): seq[string] =
    for x in a:
      if x in b: result.add(x)
  var body: Rep[Unit]
  if q.kind == okGroup:
    let schema = resultSchema(q.parent)
    let stringKinds = stringCols(q.parent.csv, schema)
    let keyIndex = lookup(schema, q.keys[0])
    let keyKind = if stringKinds[keyIndex]: fkString else: fkInt
    let used=iv("used"); let pos=iv("slot"); let found=iv("found"); let outPos=iv("outPos")
    let occupied=ia("occupied"); let slotIndex=ia("slotIndex")
    let keyBufS=sa("groupKeys"); let keyBufI=ia("groupKeyInts")
    let outKeyS=sa("outKeys"); let outKeyI=ia("outKeyInts")
    let outCount=ia("outCounts"); let outSum=ia("outSums")
    var inputColsS: seq[Arr[string]] = @[]
    var inputColsI: seq[Arr[int]] = @[]
    for i in 0 ..< schema.len:
      if stringKinds[i]: inputColsS.add(sa("inputColS" & $i))
      else: inputColsI.add(ia("inputColI" & $i))
    var keyStorageIndex = 0
    for i in 0 ..< keyIndex:
      if stringKinds[i] == (keyKind == fkString): inc keyStorageIndex
    var inputAgg: seq[Arr[int]] = @[]
    for k in 0 ..< q.aggregates.len: inputAgg.add(ia("inputAgg" & $k))
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
          if not stringKinds[i]: inc aggregateStorageIndex
        inputWrites.add(aw(inputAgg[j],vr(inputPos),ar(inputColsI[aggregateStorageIndex],vr(inputPos))))
      var h: Rep[int]
      var stringKey: Rep[string]
      var intKey: Rep[int]
      if keyKind == fkString:
        stringKey = sr(inputColsS[keyStorageIndex],vr(inputPos))
        h = intMod(fieldHash(RString(data: stringKey)), staticInt(cap))
      else:
        intKey = ar(inputColsI[keyStorageIndex],vr(inputPos))
        h = intMod(intKey, staticInt(cap))
      let stable = addMany(inputWrites)
      let seek = whileLoop(proc():Rep[bool]=andB(ltI(vr(pos),staticInt(cap)),eqI(vr(found),staticInt(0))), proc():Rep[Unit]=
        ifB(eqI(ar(occupied,vr(pos)),staticInt(1)),
          proc():Rep[Unit]=
            if keyKind == fkString:
              ifB(stringCompare(RString(data: stringKey),RString(data:sr(keyBufS,vr(pos)))),proc():Rep[Unit]=vw(found,staticInt(1)),proc():Rep[Unit]=vw(pos,intAdd(vr(pos),staticInt(1))))
            else:
              ifB(eqI(intKey,ar(keyBufI,vr(pos))),proc():Rep[Unit]=vw(found,staticInt(1)),proc():Rep[Unit]=vw(pos,intAdd(vr(pos),staticInt(1)))),
          proc():Rep[Unit]=
            if keyKind == fkString:
              seqs(sw(keyBufS,vr(pos),stringKey),seqs(aw(occupied,vr(pos),staticInt(1)),vw(found,staticInt(2))))
            else:
              seqs(aw(keyBufI,vr(pos),intKey),seqs(aw(occupied,vr(pos),staticInt(1)),vw(found,staticInt(2))))))
      var updates: seq[Rep[Unit]] = @[stable, vw(pos,h), vw(found,staticInt(0)), seek]
      let update = ifB(eqI(vr(found),staticInt(1)),
        proc():Rep[Unit]=
          let compact = ar(slotIndex,vr(pos)); var xs: seq[Rep[Unit]] = @[aw(outCount,compact,intAdd(ar(outCount,compact),staticInt(1)))]
          for j,n in q.aggregates: xs.add(aw(outSum,intAdd(intMul(compact,staticInt(q.aggregates.len)),staticInt(j)),intAdd(ar(outSum,intAdd(intMul(compact,staticInt(q.aggregates.len)),staticInt(j))),ar(inputAgg[j],vr(inputPos)))))
          addMany(xs),
        proc():Rep[Unit]=
          var xs: seq[Rep[Unit]] = @[aw(slotIndex,vr(pos),vr(used)), aw(outCount,vr(used),staticInt(1))]
          if keyKind == fkString: xs.add(sw(outKeyS,vr(used),stringKey))
          else: xs.add(aw(outKeyI,vr(used),intKey))
          for j,n in q.aggregates: xs.add(aw(outSum,intAdd(intMul(vr(used),staticInt(q.aggregates.len)),staticInt(j)),ar(inputAgg[j],vr(inputPos))))
          xs.add(vw(used,intAdd(vr(used),staticInt(1)))); addMany(xs))
      updates.add(update); updates.add(vw(inputPos,intAdd(vr(inputPos),staticInt(1)))); addMany(updates)
    let consumeAll = scanRows(q.parent.csv, schema, stringKinds, q.parent.delim, consume)
    var output: seq[Rep[Unit]] = @[]
    let outLoop = whileLoop(proc():Rep[bool]=ltI(vr(outPos),vr(used)), proc():Rep[Unit]=
      var fs: seq[RField] = @[]
      if keyKind == fkString:
        fs.add(RField(kind:fkString,str:RString(data:sr(outKeyS,vr(outPos)))))
      else:
        fs.add(RField(kind:fkInt,int:RInt(value:ar(outKeyI,vr(outPos)))))
      fs.add(RField(kind:fkInt,int:RInt(value:ar(outCount,vr(outPos)))))
      for j in 0 ..< q.aggregates.len: fs.add(RField(kind:fkInt,int:RInt(value:ar(outSum,intAdd(intMul(vr(outPos),staticInt(q.aggregates.len)),staticInt(j))))))
      seqs(pr(fs),vw(outPos,intAdd(vr(outPos),staticInt(1)))))
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
        outputFields.add(sf); seqs(ifB(same,proc():Rep[Unit]=pr(outputFields),proc():Rep[Unit]=unit()),vw(pos,intMod(intAdd(vr(pos),staticInt(1)),staticInt(cap)))))
      seqs(addMany(xs),seqs(loop,vw(rightTmpPos,intAdd(vr(rightTmpPos),staticInt(1)))))))
    body=seqs(build,probe)
  elif q.kind == okFilter:
    let schema = resultSchema(q.parent)
    let kinds = stringCols(q.parent.csv, schema)
    let leftKind = if q.predicate.left.kind == rkField: (if kinds[lookup(schema,q.predicate.left.name)]: fkString else: fkInt) else: q.predicate.left.value.kind
    let rightKind = if q.predicate.right.kind == rkField: (if kinds[lookup(schema,q.predicate.right.name)]: fkString else: fkInt) else: q.predicate.right.value.kind
    doAssert leftKind == rightKind, "predicate kind mismatch"
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
      var a, b: RField
      if q.predicate.left.kind == rkField: a = loaded[lookup(schema,q.predicate.left.name)] else: a = q.predicate.left.value
      if q.predicate.right.kind == rkField: b = loaded[lookup(schema,q.predicate.right.name)] else: b = q.predicate.right.value
      let same = if leftKind == fkString: stringCompare(a.str,b.str) else: eqI(a.int.value,b.int.value)
      seqs(addMany(writes), seqs(ifB(same, proc():Rep[Unit]=pr(loaded), proc():Rep[Unit]=unit()), vw(pos, intAdd(vr(pos), staticInt(1))))))
  elif q.kind == okProject:
    let source = if q.parent.kind == okFilter: q.parent.parent else: q.parent
    let schema = resultSchema(source)
    let kinds = stringCols(source.csv, schema)
    let input = if q.inputSchema.len == 0: q.outputSchema else: q.inputSchema
    let emit = proc(f: seq[RField]): Rep[Unit] =
      var selected: seq[RField] = @[]
      for name in input: selected.add(f[lookup(schema,name)])
      pr(selected)
    if q.parent.kind == okFilter:
      let pred = q.parent.predicate
      let leftKind = if pred.left.kind == rkField: (if kinds[lookup(schema,pred.left.name)]: fkString else: fkInt) else: pred.left.value.kind
      let rightKind = if pred.right.kind == rkField: (if kinds[lookup(schema,pred.right.name)]: fkString else: fkInt) else: pred.right.value.kind
      doAssert leftKind == rightKind, "predicate kind mismatch"
      body = scanRows(source.csv, schema, kinds, source.delim, proc(f: seq[RField]): Rep[Unit] =
        var a, b: RField
        if pred.left.kind == rkField: a = f[lookup(schema,pred.left.name)] else: a = pred.left.value
        if pred.right.kind == rkField: b = f[lookup(schema,pred.right.name)] else: b = pred.right.value
        let same = if leftKind == fkString: stringCompare(a.str,b.str) else: eqI(a.int.value,b.int.value)
        ifB(same, proc(): Rep[Unit] = emit(f), proc(): Rep[Unit] = unit()))
    else:
      body = scanRows(source.csv, schema, kinds, source.delim, emit)
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
        ifB(same, proc():Rep[Unit]=pr(left & right), proc():Rep[Unit]=unit())))
  else:
    let schema = resultSchema(if q.kind == okScan: q else: q.parent)
    let csv = if q.kind == okScan: q.csv else: q.parent.csv
    let kinds=stringCols(csv,schema)
    body=scanRows(csv,schema,kinds,if q.kind == okScan: q.delim else: q.parent.delim,proc(f: seq[RField]):Rep[Unit]=pr(f))
  result = "import std/strutils\n\nproc compareStringChars(a,b: string): bool =\n  var i = 0\n  result = a.len == b.len\n  while result and i < a.len:\n    result = a[i] == b[i]\n    inc i\n\nproc hashString(a: string): int =\n  var i = 0\n  result = 0\n  while i < a.len:\n    result = result * 41 + ord(a[i])\n    inc i\n\nproc scannerNext(text: string; pos: var int; delim: char): string =\n  let start = pos\n  var stop = pos\n  while stop < text.len and text[stop] != delim: inc stop\n  result = text[start ..< stop]\n  if stop < text.len: inc stop\n  pos = stop\n\n"
  for a in strings: result.add(emitDecl(a) & "\n")
  for a in ints: result.add(emitDecl(a) & "\n")
  for v in vars: result.add(emitDecl(v) & "\n")
  result.add(emitStmt(body) & "\n")

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
