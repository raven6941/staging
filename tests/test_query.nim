## Staged Scan/Filter/Project over a static-schema, in-memory integer table.

import staging/framework
import staging/arrays
import std/[algorithm, os, osproc, strutils, times, sequtils]

type
  RefKind = enum rkField, rkValue
  Ref = object
    kind: RefKind
    name: string
    value: int
  Predicate = object
    left, right: Ref
  OpKind = enum okScan, okFilter, okProject, okJoin, okHashJoin, okGroup, okPrintCSV
  Operator[T] = ref object
    kind: OpKind
    table: T
    schema, outputSchema, keys, aggregates: seq[string]
    source: int
    predicate: Predicate
    parent, right: Operator[T]

  Table[A] = object
    data: A
    schema: seq[string]
    rows, width: int

  QueryNodeKind = enum qkInput, qkAdd, qkMul, qkMod, qkLt, qkEq, qkAnd, qkNot, qkArrDecl,
    qkArrRead, qkArrWrite, qkVarDecl, qkVarRead, qkVarWrite, qkSeq,
    qkIf, qkWhile
  QueryNode = ref object of IRNode
    kind: QueryNodeKind
    name: string
    left, right, index, value, init: Rep[int]
    cond: Rep[bool]
    boolLeft, boolRight: Rep[int]
    boolA, boolB: Rep[bool]
    boolCond: Rep[bool]
    arr: Arr[int]
    v: Var[int]
    thenB, elseB, a, b: Rep[Unit]
    data: seq[int]

  QuerySym[I, B, S, C, A] = object
    lit: proc(x: int): I
    add, mul, modulo: proc(x, y: I): I
    lt, eq: proc(x, y: I): B
    andB: proc(x, y: B): B
    notB: proc(x: B): B
    unit: proc(): S
    seq: proc(x, y: S): S
    ifB: proc(c: B, t, e: proc(): S): S
    whileLoop: proc(c: proc(): B, body: proc(): S): S
    varNew: proc(x: I): C
    varRead: proc(v: C): I
    varWrite: proc(v: C, x: I): S
    arrNew: proc(n: I, data: seq[int]): A
    arrRead: proc(a: A, i: I): I
    arrWrite: proc(a: A, i, x: I): S

  QueryPlan[S, C, A] = object
    body: S
    output: A
    count: C
    index: C
    table, rightTable: Table[A]
    vars: seq[C]
    arrays: seq[A]

var stagedVars: seq[Var[int]] = @[]
var stagedArrays: seq[Arr[int]] = @[]

proc field(name: string): Ref = Ref(kind: rkField, name: name)
proc value(x: int): Ref = Ref(kind: rkValue, value: x)
proc equals(a, b: Ref): Predicate = Predicate(left: a, right: b)

proc scan[T](table: T, schema: seq[string]): Operator[T] =
  Operator[T](kind: okScan, table: table, schema: schema)
proc scan[T](table: T, schema: seq[string], source: int): Operator[T] =
  Operator[T](kind: okScan, table: table, schema: schema, source: source)
proc filter[T](p: Predicate, parent: Operator[T]): Operator[T] =
  Operator[T](kind: okFilter, predicate: p, parent: parent)
proc project[T](schema: seq[string], parent: Operator[T]): Operator[T] =
  Operator[T](kind: okProject, outputSchema: schema, parent: parent)
proc printCSV[T](parent: Operator[T]): Operator[T] =
  Operator[T](kind: okPrintCSV, parent: parent)
proc join[T](left, right: Operator[T]): Operator[T] =
  Operator[T](kind: okJoin, parent: left, right: right)
proc hashJoin[T](left, right: Operator[T]): Operator[T] =
  Operator[T](kind: okHashJoin, parent: left, right: right)
proc group[T](keys, aggregates: seq[string], parent: Operator[T]): Operator[T] =
  Operator[T](kind: okGroup, keys: keys, aggregates: aggregates, parent: parent)

proc resultSchema[T](o: Operator[T]): seq[string] =
  case o.kind
  of okScan: o.schema
  of okFilter, okPrintCSV: resultSchema(o.parent)
  of okProject: o.outputSchema
  of okJoin, okHashJoin: resultSchema(o.parent) & resultSchema(o.right)
  of okGroup: o.keys & @["count"] & o.aggregates

proc lookup(schema: seq[string], name: string): int =
  let i = schema.find(name)
  doAssert i >= 0, "unknown field " & name
  i

proc evalRef[I, B, S, C, A](s: QuerySym[I, B, S, C, A], r: Ref,
    rec: tuple[fields: seq[I], schema: seq[string]]): I =
  if r.kind == rkField: rec.fields[lookup(rec.schema, r.name)] else: s.lit(r.value)

proc evalPred[I, B, S, C, A](s: QuerySym[I, B, S, C, A], p: Predicate,
    rec: tuple[fields: seq[I], schema: seq[string]]): B =
  s.eq(evalRef(s, p.left, rec), evalRef(s, p.right, rec))

proc shared(a, b: seq[string]): seq[string] =
  for x in a:
    if x in b: result.add(x)

proc execOp[I, B, S, C, A](s: QuerySym[I, B, S, C, A], o: Operator[A],
    tables: seq[Table[A]], yld: proc(fields: seq[I], schema: seq[string]): S): S =
  case o.kind
  of okScan:
    let table = tables[o.source]
    let row = s.varNew(s.lit(0))
    let body = s.seq(
      (block:
        var fields: seq[I] = @[]
        for col in 0 ..< table.width:
          let offset = s.add(s.mul(s.varRead(row), s.lit(table.width)), s.lit(col))
          fields.add(s.arrRead(table.data, offset))
        yld(fields, table.schema)),
      s.varWrite(row, s.add(s.varRead(row), s.lit(1))))
    s.seq(s.varWrite(row, s.lit(0)),
      s.whileLoop(proc(): B = s.lt(s.varRead(row), s.lit(table.rows)), proc(): S = body))
  of okFilter:
    execOp(s, o.parent, tables, proc(fields: seq[I], schema: seq[string]): S =
      s.ifB(s.evalPred(o.predicate, (fields: fields, schema: schema)),
        proc(): S = yld(fields, schema), proc(): S = s.unit()))
  of okProject:
    execOp(s, o.parent, tables, proc(fields: seq[I], schema: seq[string]): S =
      (block:
        var selected: seq[I] = @[]
        for name in o.outputSchema: selected.add(fields[lookup(schema, name)])
        yld(selected, o.outputSchema)))
  of okJoin, okHashJoin:
    let keys = shared(resultSchema(o.parent), resultSchema(o.right))
    if o.kind == okJoin or keys.len == 0:
      execOp(s, o.parent, tables, proc(f: seq[I], sc: seq[string]): S =
        execOp(s, o.right, tables, proc(g: seq[I], tc: seq[string]): S =
          var c: B
          if keys.len == 0: c = s.eq(s.lit(0), s.lit(0))
          else:
            c = s.eq(f[lookup(sc, keys[0])], g[lookup(tc, keys[0])])
            for k in keys[1 .. ^1]: c = s.andB(c, s.eq(f[lookup(sc, k)], g[lookup(tc, k)]))
          s.ifB(c, proc(): S = yld(f & g, sc & tc), proc(): S = s.unit())))
    else:
      # Residual open-addressed hash table (HashMapBuffer): one slot per
      # left row, key columns + full row stored in residual arrays; only
      # the schema-derived column positions are static. Duplicate keys
      # occupy consecutive slots via linear probing, so the probe phase
      # scans all matching slots.
      let hsize = 256
      let leftWidth = resultSchema(o.parent).len
      let htable = s.arrNew(s.lit(hsize), @[]) # -1 empty, 1 occupied
      let hkeys = s.arrNew(s.lit(hsize * keys.len), @[])
      let hrows = s.arrNew(s.lit(hsize * leftWidth), @[])
      let slot = s.varNew(s.lit(0))
      var init = s.unit()
      for i in 0 ..< hsize:
        init = s.seq(init, s.arrWrite(htable, s.lit(i), s.lit(-1)))
      proc hashOf(row: seq[I], sc: seq[string]): I =
        var h = s.modulo(row[lookup(sc, keys[0])], s.lit(hsize))
        for j in 1 ..< keys.len:
          h = s.modulo(s.add(h, row[lookup(sc, keys[j])]), s.lit(hsize))
        h
      proc advanceSlot(): S =
        s.varWrite(slot, s.modulo(s.add(s.varRead(slot), s.lit(1)), s.lit(hsize)))
      let build = execOp(s, o.parent, tables, proc(f: seq[I], sc: seq[string]): S =
        var insert = s.seq(s.varWrite(slot, hashOf(f, sc)),
          s.whileLoop(proc(): B = s.eq(s.arrRead(htable, s.varRead(slot)), s.lit(1)),
            proc(): S = advanceSlot()))
        insert = s.seq(insert, s.arrWrite(htable, s.varRead(slot), s.lit(1)))
        for j, name in keys:
          insert = s.seq(insert, s.arrWrite(hkeys,
            s.add(s.mul(s.varRead(slot), s.lit(keys.len)), s.lit(j)), f[lookup(sc, name)]))
        for j in 0 ..< leftWidth:
          insert = s.seq(insert, s.arrWrite(hrows,
            s.add(s.mul(s.varRead(slot), s.lit(leftWidth)), s.lit(j)), f[j]))
        insert)
      let probePhase = execOp(s, o.right, tables, proc(g: seq[I], tc: seq[string]): S =
        var probeBody = s.varWrite(slot, hashOf(g, tc))
        let scanSlots = s.whileLoop(proc(): B = s.eq(s.arrRead(htable, s.varRead(slot)), s.lit(1)),
          proc(): S =
            var same = s.eq(s.arrRead(hkeys, s.mul(s.varRead(slot), s.lit(keys.len))),
              g[lookup(tc, keys[0])])
            for j in 1 ..< keys.len:
              same = s.andB(same, s.eq(s.arrRead(hkeys,
                s.add(s.mul(s.varRead(slot), s.lit(keys.len)), s.lit(j))),
                g[lookup(tc, keys[j])]))
            var leftRow: seq[I] = @[]
            for j in 0 ..< leftWidth:
              leftRow.add(s.arrRead(hrows,
                s.add(s.mul(s.varRead(slot), s.lit(leftWidth)), s.lit(j))))
            s.seq(s.ifB(same, proc(): S = yld(leftRow & g, resultSchema(o.parent) & tc),
              proc(): S = s.unit()), advanceSlot()))
        s.seq(probeBody, scanSlots))
      s.seq(init, s.seq(build, probePhase))
  of okGroup:
    let cap = 256
    let used = s.varNew(s.lit(0))
    let pos = s.varNew(s.lit(0))
    let found = s.varNew(s.lit(0))
    let keyData = s.arrNew(s.lit(cap * o.keys.len), @[])
    let countData = s.arrNew(s.lit(cap), @[])
    let sumData = s.arrNew(s.lit(cap * o.aggregates.len), @[])
    var init = s.unit()
    let consume = execOp(s, o.parent, tables, proc(f: seq[I], sc: seq[string]): S =
      var start = s.seq(s.varWrite(pos, s.lit(0)), s.varWrite(found, s.lit(0)))
      var seek = s.whileLoop(proc(): B = s.andB(s.lt(s.varRead(pos), s.varRead(used)),
          s.eq(s.varRead(found), s.lit(0))), proc(): S =
        var same: B
        if o.keys.len == 0: same = s.eq(s.lit(0), s.lit(0))
        else:
          same = s.eq(s.arrRead(keyData, s.add(s.mul(s.varRead(pos), s.lit(o.keys.len)), s.lit(0))), f[lookup(sc, o.keys[0])])
          for j in 1 ..< o.keys.len:
            same = s.andB(same, s.eq(s.arrRead(keyData, s.add(s.mul(s.varRead(pos), s.lit(o.keys.len)), s.lit(j))), f[lookup(sc, o.keys[j])]))
        s.ifB(same, proc(): S = s.varWrite(found, s.lit(1)),
          proc(): S = s.varWrite(pos, s.add(s.varRead(pos), s.lit(1)))))
      var update = s.ifB(s.eq(s.varRead(found), s.lit(1)),
        proc(): S =
          var w = s.arrWrite(countData, s.varRead(pos), s.add(s.arrRead(countData, s.varRead(pos)), s.lit(1)))
          for j, name in o.aggregates:
            w = s.seq(w, s.arrWrite(sumData, s.add(s.mul(s.varRead(pos), s.lit(o.aggregates.len)), s.lit(j)),
              s.add(s.arrRead(sumData, s.add(s.mul(s.varRead(pos), s.lit(o.aggregates.len)), s.lit(j))), f[lookup(sc, name)])))
          w,
        proc(): S =
          var w = s.unit()
          for j, name in o.keys: w = s.seq(w, s.arrWrite(keyData, s.add(s.mul(s.varRead(used), s.lit(o.keys.len)), s.lit(j)), f[lookup(sc, name)]))
          for j, name in o.aggregates: w = s.seq(w, s.arrWrite(sumData, s.add(s.mul(s.varRead(used), s.lit(o.aggregates.len)), s.lit(j)), f[lookup(sc, name)]))
          w = s.seq(w, s.arrWrite(countData, s.varRead(used), s.lit(1)))
          w = s.seq(w, s.varWrite(used, s.add(s.varRead(used), s.lit(1))))
          w)
      s.seq(start, s.seq(seek, update)))
    let outPos = s.varNew(s.lit(0))
    let outputLoop = s.whileLoop(proc(): B = s.lt(s.varRead(outPos), s.varRead(used)), proc(): S =
      var vals: seq[I] = @[]
      for j in 0 ..< o.keys.len: vals.add(s.arrRead(keyData, s.add(s.mul(s.varRead(outPos), s.lit(o.keys.len)), s.lit(j))))
      vals.add(s.arrRead(countData, s.varRead(outPos)))
      for j in 0 ..< o.aggregates.len: vals.add(s.arrRead(sumData, s.add(s.mul(s.varRead(outPos), s.lit(o.aggregates.len)), s.lit(j))))
      s.seq(yld(vals, o.keys & @["count"] & o.aggregates), s.varWrite(outPos, s.add(s.varRead(outPos), s.lit(1)))))
    s.seq(consume, outputLoop)
  of okPrintCSV:
    execOp(s, o.parent, tables, yld)

proc runPlan[I, B, S, C, A](s: QuerySym[I, B, S, C, A], q: Operator[A],
    table, rightTable: Table[A]): QueryPlan[S, C, A] =
  let output = s.arrNew(s.lit((table.rows + rightTable.rows + 1) * resultSchema(q).len * 8), @[])
  let count = s.varNew(s.lit(0))
  let index = s.varNew(s.lit(0))
  var tables = @[table]
  if rightTable.width > 0:
    QueryNode(rightTable.data.node).name = "inputRight"
    tables.add(rightTable)
  let body = execOp(s, printCSV(q), tables,
    proc(fields: seq[I], schema: seq[string]): S =
      (block:
        var writes = s.unit()
        var first = true
        for j, x in fields:
          let w = s.arrWrite(output, s.add(s.varRead(count), s.lit(j)), x)
          if first:
            writes = w
            first = false
          else:
            writes = s.seq(writes, w)
        s.seq(writes, s.varWrite(count, s.add(s.varRead(count), s.lit(fields.len))))))
  QueryPlan[S, C, A](body: body, output: output, count: count, index: index, table: table, rightTable: rightTable,
    vars: stagedVars, arrays: stagedArrays)

proc runPlan[I, B, S, C, A](s: QuerySym[I, B, S, C, A], q: Operator[A],
    table: Table[A]): QueryPlan[S, C, A] =
  runPlan(s, q, table, Table[A](width: 0))

proc directRows(q: Operator[seq[seq[int]]]): seq[seq[int]] =
  case q.kind
  of okScan: result = q.table
  of okFilter:
    for row in directRows(q.parent):
      let schema = resultSchema(q.parent)
      let left = if q.predicate.left.kind == rkField:
        row[lookup(schema, q.predicate.left.name)] else: q.predicate.left.value
      let right = if q.predicate.right.kind == rkField:
        row[lookup(schema, q.predicate.right.name)] else: q.predicate.right.value
      if left == right: result.add(@row)
  of okProject:
    let parentSchema = resultSchema(q.parent)
    for row in directRows(q.parent):
      result.add(q.outputSchema.mapIt(row[lookup(parentSchema, it)]))
  of okJoin, okHashJoin:
    let ls = resultSchema(q.parent); let rs = resultSchema(q.right)
    for a in directRows(q.parent):
      for b in directRows(q.right):
        var good = true
        for k in shared(ls, rs): good = good and a[lookup(ls, k)] == b[lookup(rs, k)]
        if good: result.add(a & b)
  of okGroup:
    let ps = resultSchema(q.parent); let ks = q.keys
    var groups: seq[seq[int]] = @[]
    for row in directRows(q.parent):
      let key = ks.mapIt(row[lookup(ps, it)])
      var i = groups.mapIt(it[0 ..< ks.len]).find(key)
      if i < 0:
        groups.add(key & @[1] & q.aggregates.mapIt(row[lookup(ps, it)]))
      else:
        groups[i][ks.len] += 1
        for j, name in q.aggregates: groups[i][ks.len + 1 + j] += row[lookup(ps, name)]
    result = groups
  of okPrintCSV: result = directRows(q.parent)

proc directTable(values: seq[seq[int]], schema: seq[string]): Table[seq[seq[int]]] =
  Table[seq[seq[int]]](data: values, schema: schema, rows: values.len, width: schema.len)

proc flatten(rows: seq[seq[int]]): seq[int] =
  for row in rows:
    for x in row: result.add(x)

proc stagedOperator(q: Operator[seq[seq[int]]], table: Table[Arr[int]]; rightTable: Table[Arr[int]] = Table[Arr[int]]()): Operator[Arr[int]] =
  case q.kind
  of okScan: scan(if q.source == 0: table.data else: rightTable.data,
      if q.source == 0: table.schema else: rightTable.schema, q.source)
  of okFilter: filter(q.predicate, stagedOperator(q.parent, table, rightTable))
  of okProject: project(q.outputSchema, stagedOperator(q.parent, table, rightTable))
  of okJoin: join(stagedOperator(q.parent, table, rightTable), stagedOperator(q.right, table, rightTable))
  of okHashJoin: hashJoin(stagedOperator(q.parent, table, rightTable), stagedOperator(q.right, table, rightTable))
  of okGroup: group(q.keys, q.aggregates, stagedOperator(q.parent, table, rightTable))
  of okPrintCSV: printCSV(stagedOperator(q.parent, table, rightTable))

proc stagedTable(values: seq[seq[int]], schema: seq[string]): Table[Arr[int]] =
  var flat: seq[int] = @[]
  for row in values: flat.add(row)
  let arr = Arr[int](node: QueryNode(kind: qkInput, name: "input", data: flat))
  Table[Arr[int]](data: arr, schema: schema, rows: values.len, width: schema.len)

proc stagedSym(): QuerySym[Rep[int], Rep[bool], Rep[Unit], Var[int], Arr[int]] =
  var varNumber = 0
  var arrayNumber = 0
  stagedVars = @[]
  stagedArrays = @[]
  QuerySym[Rep[int], Rep[bool], Rep[Unit], Var[int], Arr[int]](
    lit: proc(x: int): Rep[int] = liftNow(x),
    add: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y, proc(a, b: int): int = a + b,
      proc(a, b: Rep[int]): IRNode = QueryNode(kind: qkAdd, left: a, right: b)),
    mul: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y, proc(a, b: int): int = a * b,
      proc(a, b: Rep[int]): IRNode = QueryNode(kind: qkMul, left: a, right: b)),
    modulo: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y, proc(a, b: int): int = a mod b,
      proc(a, b: Rep[int]): IRNode = QueryNode(kind: qkMod, left: a, right: b)),
    lt: proc(x, y: Rep[int]): Rep[bool] =
      (if x.isStatic and y.isStatic: liftNow(x.staticVal < y.staticVal)
       else: dynamic[bool](QueryNode(kind: qkLt, boolLeft: x, boolRight: y))),
    eq: proc(x, y: Rep[int]): Rep[bool] =
      (if x.isStatic and y.isStatic: liftNow(x.staticVal == y.staticVal)
       else: dynamic[bool](QueryNode(kind: qkEq, boolLeft: x, boolRight: y))),
    andB: proc(x, y: Rep[bool]): Rep[bool] =
      (if x.isStatic: (if x.staticVal: y else: liftNow(false))
       elif y.isStatic: (if y.staticVal: x else: liftNow(false))
       else: dynamic[bool](QueryNode(kind: qkAnd, boolA: x, boolB: y))),
    notB: proc(x: Rep[bool]): Rep[bool] = (if x.isStatic: liftNow(not x.staticVal)
      else: dynamic[bool](QueryNode(kind: qkNot, boolA: x))),
    unit: proc(): Rep[Unit] = unit(),
    seq: proc(x, y: Rep[Unit]): Rep[Unit] = seqR(x, y,
      proc(a, b: Rep[Unit]): IRNode = QueryNode(kind: qkSeq, a: a, b: b)),
    ifB: proc(c: Rep[bool], t, e: proc(): Rep[Unit]): Rep[Unit] = smartIf(c, t, e,
      proc(c: Rep[bool], a, b: Rep[Unit]): IRNode = QueryNode(kind: qkIf, boolCond: c, thenB: a, elseB: b)),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] = smartWhile(c, body,
      proc(c: Rep[bool], b: Rep[Unit]): IRNode = QueryNode(kind: qkWhile, cond: c, b: b)),
    varNew: proc(x: Rep[int]): Var[int] =
      (inc varNumber; result = newVar(x,
        proc(x: Rep[int]): IRNode = QueryNode(kind: qkVarDecl, name: "v" & $varNumber, init: x)); stagedVars.add(result)),
    varRead: proc(v: Var[int]): Rep[int] = readVar(v,
      proc(v: Var[int]): IRNode = QueryNode(kind: qkVarRead, v: v)),
    varWrite: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar(v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = QueryNode(kind: qkVarWrite, v: v, value: x)),
    arrNew: proc(n: Rep[int], data: seq[int]): Arr[int] = (inc arrayNumber; result = newArray[int](n,
      proc(n: Rep[int]): IRNode = QueryNode(kind: qkArrDecl,
        name: (if data.len > 0: "input" elif arrayNumber == 1: "output" else: "array" & $arrayNumber), init: n, data: data)); stagedArrays.add(result)),
    arrRead: proc(a: Arr[int], i: Rep[int]): Rep[int] = readArr[int](a, i,
      proc(a: Arr[int], i: Rep[int]): IRNode = QueryNode(kind: qkArrRead, arr: a, index: i)),
    arrWrite: proc(a: Arr[int], i, x: Rep[int]): Rep[Unit] = writeArr[int](a, i, x,
      proc(a: Arr[int], i, x: Rep[int]): IRNode = QueryNode(kind: qkArrWrite, arr: a, index: i, value: x)))

proc emitInt(x: Rep[int]): string =
  if x.isStatic: return $x.staticVal
  let n = QueryNode(x.node)
  case n.kind
  of qkAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of qkMul: "(" & emitInt(n.left) & " * " & emitInt(n.right) & ")"
  of qkMod: "(" & emitInt(n.left) & " mod " & emitInt(n.right) & ")"
  of qkArrRead: QueryNode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  of qkVarRead: QueryNode(n.v.node).name
  else: raise newException(ValueError, "bad int node")

proc emitBool(x: Rep[bool]): string =
  if x.isStatic: return $x.staticVal
  let n = QueryNode(x.node)
  case n.kind
  of qkEq, qkLt:
    let op = if n.kind == qkEq: " == " else: " < "
    "(" & emitInt(n.boolLeft) & op & emitInt(n.boolRight) & ")"
  of qkAnd: "(" & emitBool(n.boolA) & " and " & emitBool(n.boolB) & ")"
  of qkNot: "(not " & emitBool(n.boolA) & ")"
  else: raise newException(ValueError, "bad bool node")

proc emitStmt(x: Rep[Unit], ind = ""): string =
  if x.isStatic: return ind & "discard"
  let n = QueryNode(x.node)
  case n.kind
  of qkSeq: emitStmt(n.a, ind) & "\n" & emitStmt(n.b, ind)
  of qkIf: ind & "if " & emitBool(n.boolCond) & ":\n" & emitStmt(n.thenB, ind & "  ") &
    "\n" & ind & "else:\n" & emitStmt(n.elseB, ind & "  ")
  of qkWhile: ind & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.b, ind & "  ")
  of qkVarWrite: ind & QueryNode(n.v.node).name & " = " & emitInt(n.value)
  of qkArrWrite: ind & QueryNode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitInt(n.value)
  else: raise newException(ValueError, "bad statement node")

proc emitDecl(v: Var[int]): string =
  let n = QueryNode(v.node); "var " & n.name & " = " & emitInt(n.init)
proc emitDecl(a: Arr[int]): string =
  let n = QueryNode(a.node)
  if n.kind == qkInput: "var " & n.name & " = " & $n.data
  else: "var " & n.name & " = newSeq[int](" & emitInt(n.init) & ")"
proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim"); doAssert nim.len > 0
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

proc runStaged(plan: QueryPlan[Rep[Unit], Var[int], Arr[int]]): seq[int] =
  let dir = getTempDir() / ("query-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"; let exe = dir / "residual"
  let count = QueryNode(plan.count.node).name
  var declarations = emitDecl(plan.table.data) & "\n"
  if plan.rightTable.width > 0: declarations.add(emitDecl(plan.rightTable.data) & "\n")
  declarations.add(emitDecl(plan.output) & "\n")
  for a in plan.arrays:
    if QueryNode(a.node).kind != qkInput and QueryNode(a.node).name != QueryNode(plan.output.node).name:
      declarations.add(emitDecl(a) & "\n")
  for v in plan.vars: declarations.add(emitDecl(v) & "\n")
  writeFile(source, declarations & emitStmt(plan.body) &
    "\nfor i in 0 ..< " & count & ": echo output[i]\n")
  let text = compileRun(source, exe, dir)
  removeDir(dir)
  if text.len > 0: result = text.splitWhitespace.map(parseInt)

when isMainModule:
  let schema = @["id", "age", "score"]
  let values = @[@[1, 20, 7], @[2, 30, 4], @[3, 20, 9], @[4, 40, 1], @[5, 30, 8], @[6, 20, 2]]
  let base = scan(directTable(values, schema).data, schema)
  let qs = @[base, filter(equals(field("age"), value(20)), base),
    project(@["score", "id"], filter(equals(field("age"), value(30)), base)),
    project(@["score"], base), filter(equals(field("score"), value(99)), base)]
  doAssert directRows(qs[3]).len == 6 and directRows(qs[3])[0].len == 1
  doAssert directRows(qs[4]).len == 0
  for q in qs:
    let expected = directRows(q)
    let ss = stagedSym(); let table = stagedTable(values, schema)
    let stagedQ = stagedOperator(q, table)
    let plan = runPlan(ss, stagedQ, table)
    let text = emitStmt(plan.body)
    let got = runStaged(plan)
    doAssert got == flatten(expected), "got=" & $got & " expected=" & $flatten(expected)
    doAssert text.count("while") == 1
    if q.kind == okFilter or (q.kind == okProject and q.parent.kind == okFilter):
      doAssert "if" in text
    for name in schema: doAssert name notin text
  let projectionTable = stagedTable(values, schema)
  let projection = project(@["score", "id"], scan(projectionTable.data, schema))
  let projectionText = emitStmt(runPlan(stagedSym(), projection, projectionTable).body)
  doAssert "input[((v1 * 3) + 1)]" notin projectionText, projectionText
  doAssert "+ 2" in projectionText and "+ 0" in projectionText
  doAssert "while" in projectionText
  let leftSchema = @["id", "lv", "amount"]
  let rightSchema = @["id", "rv"]
  let leftValues = @[@[1, 10, 3], @[1, 11, 4], @[2, 20, 5], @[9, 90, 1]]
  let rightValues = @[@[1, 100], @[1, 101], @[2, 200], @[7, 700]]
  let leftQ = scan(leftValues, leftSchema, 0)
  let rightQ = scan(rightValues, rightSchema, 1)
  let jq = join(leftQ, rightQ)
  let hq = hashJoin(leftQ, rightQ)
  let gq = group(@["id"], @["amount"], leftQ)
  let lt = stagedTable(leftValues, leftSchema)
  let rt = stagedTable(rightValues, rightSchema)
  for q in [jq, hq]:
    let expected = directRows(q)
    let plan = runPlan(stagedSym(), stagedOperator(q, lt, rt), lt, rt)
    let residual = emitStmt(plan.body)
    let got = runStaged(plan)
    # HashJoin emits probe-major order (right row outer), the nested-loop
    # join emits left-major order; both are the same multiset of rows.
    let width = resultSchema(q).len
    proc asRows(flat: seq[int]): seq[seq[int]] =
      for i in countup(0, flat.len - 1, width): result.add(flat[i ..< i + width])
    doAssert sorted(asRows(got).mapIt($it)) == sorted(asRows(flatten(expected)).mapIt($it)),
      "join got=" & $got & " expected=" & $flatten(expected) & " residual=" & residual
    doAssert residual.count("while") >= 2
    for name in leftSchema & rightSchema: doAssert name notin residual
    if q.kind == okHashJoin:
      doAssert "array" in residual
      doAssert residual.count("while") >= 2
  let groupExpected = directRows(gq)
  let groupPlan = runPlan(stagedSym(), stagedOperator(gq, lt), lt)
  let groupResidual = emitStmt(groupPlan.body)
  doAssert runStaged(groupPlan) == flatten(groupExpected)
  doAssert groupResidual.count("while") >= 3
  for name in leftSchema: doAssert name notin groupResidual
  doAssert "array" in groupResidual or "array" in emitDecl(groupPlan.output)
  let emptyRight = scan(@[@[8, 800]], rightSchema, 1)
  let emptyJoin = join(leftQ, emptyRight)
  doAssert directRows(emptyJoin).len == 0
  let emptyPlan = runPlan(stagedSym(), stagedOperator(emptyJoin, lt, stagedTable(@[@[8, 800]], rightSchema)), lt,
    stagedTable(@[@[8, 800]], rightSchema))
  doAssert runStaged(emptyPlan).len == 0
  echo "ok: staged query compiler"
