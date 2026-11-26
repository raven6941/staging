import staging/framework
import staging/traversal
import std/[os, osproc, strutils, tables, times]

type
  Person = object
    name: string
    age: int
  Couple = object
    her, him: string
  PeopleDB = object
    people: seq[Person]
    couples: seq[Couple]
  DptRow = object
    dpt: Rep[string]
  EmpRow = object
    dpt, emp: Rep[string]
  TaskRow = object
    emp, tsk: Rep[string]
  OrgDpt = object
    dpt: string
  OrgEmp = object
    dpt, emp: string
  OrgTask = object
    emp, tsk: string
  OrgDB = object
    departments: seq[OrgDpt]
    employees: seq[OrgEmp]
    tasks: seq[OrgTask]
  EmptyRow = object
  NameRow = object
    name: Rep[string]
  PersonRow = object
    name: Rep[string]
    age: Rep[int]
  ListKind = enum lkEmpty, lkYield, lkConcat, lkIf
  ListNode[T] = ref object of IRNode
    kind: ListKind
    elem: Rep[T]
    left, right: Rep[seq[T]]
    cond: Rep[bool]
    thenB, elseB: Rep[seq[T]]
  DatabaseNode = ref object of IRNode
    name: string
  TableNode = ref object of IRNode
    db: string
    table: string
  RowNode = ref object of IRNode
    binder: string
  FieldNode = ref object of IRNode
    binder, field: string
  NameValueNode = ref object of IRNode
    name: Rep[string]
  DptValueNode = ref object of IRNode
    dpt: Rep[string]
  ExistsNode[T] = ref object of IRNode
    source: Rep[seq[T]]
  ScalarKind = enum skEq, skLt, skLe, skGt, skGe, skAnd, skOr, skNot, skAdd, skSub
  ScalarNode[T] = ref object of IRNode
    kind: ScalarKind
    left, right: Rep[T]
  FunRecord[B] = object
    binder: string
    body: Rep[seq[B]]
  DBForBase = ref object of IRNode
    ## Non-generic base so the boundary/binder queries cover every
    ## DBForNode[B] instantiation without enumerating them.
    binder: string
  DBForNode[B] = ref object of DBForBase
    sourceDb, table: string
    body: Rep[seq[B]]
    ff: FunRecord[B]
  PredicateKind = enum pkAbove, pkBelow, pkAnd, pkOr, pkNot
  Predicate = ref object
    case kind: PredicateKind
    of pkAbove, pkBelow: a: int
    of pkAnd, pkOr: leftPred, rightPred: Predicate
    of pkNot: operand: Predicate

var funCounter = 0

proc emptyList[T](): Rep[seq[T]] = dynamic[seq[T]](ListNode[T](kind: lkEmpty))
proc yieldList[T](x: Rep[T]): Rep[seq[T]] =
  dynamic[seq[T]](ListNode[T](kind: lkYield, elem: x))
proc concatList[T](a, b: Rep[seq[T]]): Rep[seq[T]] =
  dynamic[seq[T]](ListNode[T](kind: lkConcat, left: a, right: b))

proc listIf[T](c: Rep[bool], t, e: Rep[seq[T]]): Rep[seq[T]] =
  if c.isStatic: (if c.staticVal: t else: e)
  else: dynamic[seq[T]](ListNode[T](kind: lkIf, cond: c, thenB: t, elseB: e))

proc database[T](name: string): Rep[T] = dynamic[T](DatabaseNode(name: name))

proc table[T, D](db: Rep[D], name: string): Rep[seq[T]] =
  dynamic[seq[T]](TableNode(db: DatabaseNode(db.node).name, table: name))

proc people(db: Rep[PeopleDB]): Rep[seq[PersonRow]] = table[PersonRow, PeopleDB](db, "people")

proc departments(db: Rep[OrgDB]): Rep[seq[DptRow]] = table[DptRow, OrgDB](db, "departments")
proc employees(db: Rep[OrgDB]): Rep[seq[EmpRow]] = table[EmpRow, OrgDB](db, "employees")
proc tasks(db: Rep[OrgDB]): Rep[seq[TaskRow]] = table[TaskRow, OrgDB](db, "tasks")

proc rowField[T](x: Rep[PersonRow], name: string): Rep[T] =
  if x.isStatic: raise newException(ValueError, "static row field")
  let r = RowNode(x.node)
  dynamic[T](FieldNode(binder: r.binder, field: name))

proc nameOf(x: Rep[PersonRow]): Rep[string] = rowField[string](x, "name")
proc ageOf(x: Rep[PersonRow]): Rep[int] = rowField[int](x, "age")
proc nameValue(x: Rep[string]): Rep[NameRow] = dynamic[NameRow](NameValueNode(name: x))
proc orgField[A, T](x: Rep[A], name: string): Rep[T] =
  dynamic[T](FieldNode(binder: RowNode(x.node).binder, field: name))
proc dptOf(x: Rep[DptRow]): Rep[string] = orgField[DptRow, string](x, "dpt")
proc empDptOf(x: Rep[EmpRow]): Rep[string] = orgField[EmpRow, string](x, "dpt")
proc empOf(x: Rep[EmpRow]): Rep[string] = orgField[EmpRow, string](x, "emp")
proc taskEmpOf(x: Rep[TaskRow]): Rep[string] = orgField[TaskRow, string](x, "emp")
proc taskNameOf(x: Rep[TaskRow]): Rep[string] = orgField[TaskRow, string](x, "tsk")
proc dptValue(x: Rep[string]): Rep[DptRow] = dynamic[DptRow](DptValueNode(dpt: x))

proc exists[T](xs: Rep[seq[T]]): Rep[bool] =
  if xs.node of ListNode[T] and ListNode[T](xs.node).kind == lkEmpty: liftNow(false)
  else: dynamic[bool](ExistsNode[T](source: xs))
proc emptyRow(): Rep[EmptyRow] = dynamic[EmptyRow](RowNode(binder: "empty"))

proc eqR[T](a, b: Rep[T]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal == b.staticVal)
  else: dynamic[bool](ScalarNode[T](kind: skEq, left: a, right: b))
proc ltR(a, b: Rep[int]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal < b.staticVal)
  else: dynamic[bool](ScalarNode[int](kind: skLt, left: a, right: b))
proc leR(a, b: Rep[int]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal <= b.staticVal)
  else: dynamic[bool](ScalarNode[int](kind: skLe, left: a, right: b))
proc gtR(a, b: Rep[int]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal > b.staticVal)
  else: dynamic[bool](ScalarNode[int](kind: skGt, left: a, right: b))
proc andR(a, b: Rep[bool]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal and b.staticVal)
  else: dynamic[bool](ScalarNode[bool](kind: skAnd, left: a, right: b))
proc orR(a, b: Rep[bool]): Rep[bool] =
  if a.isStatic and b.isStatic: liftNow(a.staticVal or b.staticVal)
  else: dynamic[bool](ScalarNode[bool](kind: skOr, left: a, right: b))
proc notR(a: Rep[bool]): Rep[bool] =
  if a.isStatic: liftNow(not a.staticVal)
  else: dynamic[bool](ScalarNode[bool](kind: skNot, left: a, right: liftNow(true)))

proc Above(a: int): Predicate = Predicate(kind: pkAbove, a: a)
proc Below(a: int): Predicate = Predicate(kind: pkBelow, a: a)
proc And(t, u: Predicate): Predicate = Predicate(kind: pkAnd, leftPred: t, rightPred: u)
proc Or(t, u: Predicate): Predicate = Predicate(kind: pkOr, leftPred: t, rightPred: u)
proc Not(t: Predicate): Predicate = Predicate(kind: pkNot, operand: t)

proc P(t: Predicate): proc(x: Rep[int]): Rep[bool] {.closure.} =
  result = proc(x: Rep[int]): Rep[bool] {.closure.} =
    case t.kind
    of pkAbove: leR(liftNow(t.a), x)
    of pkBelow: ltR(x, liftNow(t.a))
    of pkAnd: andR(P(t.leftPred)(x), P(t.rightPred)(x))
    of pkOr: orR(P(t.leftPred)(x), P(t.rightPred)(x))
    of pkNot: notR(P(t.operand)(x))

proc ifThenElseList[T](c: Rep[bool], t, e: Rep[seq[T]]): Rep[seq[T]] =
  let tn = ListNode[T](t.node); let en = ListNode[T](e.node)
  if tn.kind == lkEmpty and en.kind == lkEmpty: return emptyList[T]()
  if tn.kind == lkConcat and en.kind == lkEmpty:
    return concatList(ifThenElseList(c, tn.left, emptyList[T]()),
      ifThenElseList(c, tn.right, emptyList[T]()))
  if tn.kind == lkIf and en.kind == lkEmpty:
    return listIf(andR(c, tn.cond), tn.thenB, emptyList[T]())
  if t.node of DBForNode[T] and en.kind == lkEmpty:
    let dn = DBForNode[T](t.node)
    return dynamic[seq[T]](DBForNode[T](sourceDb: dn.sourceDb, table: dn.table,
      binder: dn.binder, body: listIf(c, dn.body, emptyList[T]()),
      ff: FunRecord[T](binder: dn.binder, body: listIf(c, dn.body, emptyList[T]()))))
  dynamic[seq[T]](ListNode[T](kind: lkIf, cond: c, thenB: t, elseB: e))

proc dbfor[A, B](l: Rep[seq[A]], f: proc(x: Rep[A]): Rep[seq[B]] {.closure.}): Rep[seq[B]]

proc mapListBody[A, B](body: Rep[seq[A]], f: proc(x: Rep[A]): Rep[seq[B]] {.closure.}): Rep[seq[B]] =
  # A bare DBFor body flattens through dbfor (the tutorial's for-over-for
  # case); without this the ListNode cast below raises ObjectConversionDefect
  # on e.g. a flatMap whose body is itself a sub-query.
  if body.node of DBForNode[A]: return dbfor(body, f)
  let n = ListNode[A](body.node)
  case n.kind
  of lkEmpty: emptyList[B]()
  of lkYield: f(n.elem)
  of lkConcat: concatList(mapListBody(n.left, f), mapListBody(n.right, f))
  of lkIf: listIf(n.cond, mapListBody(n.thenB, f), mapListBody(n.elseB, f))

proc dbfor[A, B](l: Rep[seq[A]], f: proc(x: Rep[A]): Rep[seq[B]] {.closure.}): Rep[seq[B]] =
  if l.node of ListNode[A]:
    let n = ListNode[A](l.node)
    case n.kind
    of lkEmpty: return emptyList[B]()
    of lkYield: return f(n.elem)
    of lkIf:
      # The tutorial's IfThen extractor matches if-then with an empty else
      # only; a non-empty else cannot normalize and must not be dropped.
      if n.elseB.node of ListNode[B] and ListNode[B](n.elseB.node).kind == lkEmpty:
        return listIf(n.cond, dbfor(n.thenB, f), emptyList[B]())
      raise newException(ValueError, "cannot normalize for expression")
    of lkConcat: return concatList(dbfor(n.left, f), dbfor(n.right, f))
  if l.node of DBForNode[A]:
    let d = DBForNode[A](l.node)
    let body = mapListBody(d.body, f)
    if body.node of ListNode[B] and ListNode[B](body.node).kind == lkEmpty:
      return emptyList[B]()
    return dynamic[seq[B]](DBForNode[B](sourceDb: d.sourceDb, table: d.table,
      binder: d.binder, body: body, ff: FunRecord[B](binder: d.binder, body: body)))
  if l.node of TableNode:
    let t = TableNode(l.node)
    inc funCounter
    let binder = dynamic[A](RowNode(binder: "row" & $(funCounter + 1)))
    let body = f(binder)
    if body.node of ListNode[B] and ListNode[B](body.node).kind == lkEmpty:
      return emptyList[B]()
    let ff = FunRecord[B](binder: RowNode(binder.node).binder, body: body)
    return dynamic[seq[B]](DBForNode[B](sourceDb: t.db,
      table: t.table, binder: ff.binder, body: body, ff: ff))
  raise newException(ValueError, "cannot normalize for expression")

proc listFlatMap[A, B](l: Rep[seq[A]], f: proc(x: Rep[A]): Rep[seq[B]] {.closure.}): Rep[seq[B]] = dbfor(l, f)
proc listMap[A, B](l: Rep[seq[A]], f: proc(x: Rep[A]): Rep[B] {.closure.}): Rep[seq[B]] =
  dbfor(l, proc(x: Rep[A]): Rep[seq[B]] = yieldList(f(x)))
proc listFilter[A](l: Rep[seq[A]], f: proc(x: Rep[A]): Rep[bool] {.closure.}): Rep[seq[A]] =
  dbfor(l, proc(x: Rep[A]): Rep[seq[A]] = listIf(f(x), yieldList(x), emptyList[A]()))

let db = database[PeopleDB]("db")
proc satisfies(p: proc(x: Rep[int]): Rep[bool] {.closure.}): Rep[seq[NameRow]] =
  listMap(listFilter(people(db), proc(x: Rep[PersonRow]): Rep[bool] {.closure.} = p(ageOf(x))),
    proc(x: Rep[PersonRow]): Rep[NameRow] {.closure.} = nameValue(nameOf(x)))

proc range(db: Rep[PeopleDB], a, b: Rep[int]): Rep[seq[NameRow]] =
  listMap(listFilter(people(db), proc(x: Rep[PersonRow]): Rep[bool] {.closure.} = andR(leR(a, ageOf(x)), ltR(ageOf(x), b))),
    proc(x: Rep[PersonRow]): Rep[NameRow] {.closure.} = nameValue(nameOf(x)))
proc ageFromName(db: Rep[PeopleDB], s: Rep[string]): Rep[seq[int]] =
  listMap(listFilter(people(db), proc(x: Rep[PersonRow]): Rep[bool] {.closure.} = eqR(nameOf(x), s)),
    proc(x: Rep[PersonRow]): Rep[int] {.closure.} = ageOf(x))
proc rangeFromNames(db: Rep[PeopleDB], s, t: Rep[string]): Rep[seq[NameRow]] =
  listFlatMap(ageFromName(db, s), proc(a: Rep[int]): Rep[seq[NameRow]] {.closure.} =
    listFlatMap(ageFromName(db, t), proc(b: Rep[int]): Rep[seq[NameRow]] {.closure.} = range(db, a, b)))

let org = database[OrgDB]("org")
proc taskMatches(e: Rep[EmpRow], u: Rep[string]): Rep[bool] =
  exists(listMap(listFilter(tasks(org), proc(t: Rep[TaskRow]): Rep[bool] {.closure.} =
    andR(eqR(empOf(e), taskEmpOf(t)), eqR(taskNameOf(t), u))),
    proc(t: Rep[TaskRow]): Rep[EmptyRow] {.closure.} = emptyRow()))
proc employeeMatches(d: Rep[DptRow], u: Rep[string]): Rep[bool] =
  exists(listMap(listFilter(employees(org), proc(e: Rep[EmpRow]): Rep[bool] {.closure.} =
    andR(eqR(dptOf(d), empDptOf(e)), notR(taskMatches(e, u)))),
    proc(e: Rep[EmpRow]): Rep[EmptyRow] {.closure.} = emptyRow()))
proc expertise(u: Rep[string]): Rep[seq[DptRow]] =
  listMap(listFilter(departments(org), proc(d: Rep[DptRow]): Rep[bool] {.closure.} =
    notR(employeeMatches(d, u))),
  proc(d: Rep[DptRow]): Rep[DptRow] {.closure.} = dptValue(dptOf(d)))

proc emitInt(r: Rep[int]): string
proc emitString(r: Rep[string]): string
proc emitBool(r: Rep[bool]): string
proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  if r.node of FieldNode: return FieldNode(r.node).binder & ".age"
  let n = ScalarNode[int](r.node)
  case n.kind
  of skAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of skSub: "(" & emitInt(n.left) & " - " & emitInt(n.right) & ")"
  else: raise newException(ValueError, "bad int node")
proc emitString(r: Rep[string]): string =
  if r.isStatic: return "\"" & r.staticVal & "\""
  let f = FieldNode(r.node)
  f.binder & "." & f.field
proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return (if r.staticVal: "true" else: "false")
  if r.node of ScalarNode[int]:
    let n = ScalarNode[int](r.node)
    let op = case n.kind
      of skLt: " < "
      of skLe: " <= "
      of skGt: " > "
      of skGe: " >= "
      else: ""
    if op.len > 0: return "(" & emitInt(n.left) & op & emitInt(n.right) & ")"
  if r.node of ScalarNode[string]:
    return "(" & emitString(ScalarNode[string](r.node).left) & " == " & emitString(ScalarNode[string](r.node).right) & ")"
  let n = ScalarNode[bool](r.node)
  case n.kind
  of skAnd: "(" & emitBool(n.left) & " and " & emitBool(n.right) & ")"
  of skOr: "(" & emitBool(n.left) & " or " & emitBool(n.right) & ")"
  of skNot: "(not " & emitBool(n.left) & ")"
  else: raise newException(ValueError, "bad bool node")

var existsCounter = 0

proc emitBoolHoisted(r: Rep[bool], indent: string): tuple[pre, expr: string]
proc emitEmpty(r: Rep[seq[EmptyRow]], indent: string, flag: string): string =
  if r.node of DBForNode[EmptyRow]:
    let n = DBForNode[EmptyRow](r.node)
    return indent & "for " & n.binder & " in org." & n.table & ":\n" &
      emitEmpty(n.body, indent & "  ", flag)
  let n = ListNode[EmptyRow](r.node)
  case n.kind
  of lkEmpty: ""
  of lkYield: indent & flag & " = true\n"
  of lkConcat: emitEmpty(n.left, indent, flag) & emitEmpty(n.right, indent, flag)
  of lkIf:
    let c = emitBoolHoisted(n.cond, indent)
    c.pre & indent & "if " & c.expr & ":\n" & emitEmpty(n.thenB, indent & "  ", flag)

proc emitBoolHoisted(r: Rep[bool], indent: string): tuple[pre, expr: string] =
  if r.node of ExistsNode[EmptyRow]:
    inc existsCounter
    let flag = "exists" & $existsCounter
    let e = ExistsNode[EmptyRow](r.node)
    return (indent & "var " & flag & " = false\n" & emitEmpty(e.source, indent, flag), flag)
  if r.node of ScalarNode[string] or r.node of ScalarNode[int]:
    return ("", emitBool(r))
  if r.node of ScalarNode[bool]:
    let n = ScalarNode[bool](r.node)
    case n.kind
    of skAnd, skOr:
      let a = emitBoolHoisted(n.left, indent)
      let b = emitBoolHoisted(n.right, indent)
      return (a.pre & b.pre, "(" & a.expr & (if n.kind == skAnd: " and " else: " or ") & b.expr & ")")
    of skNot:
      let a = emitBoolHoisted(n.left, indent)
      return (a.pre, "(not " & a.expr & ")")
    else: discard
  ("", emitBool(r))

proc emitNames(r: Rep[seq[NameRow]], outName, indent: string): string
proc emitInts(r: Rep[seq[int]], outName, indent: string): string
proc emitDpts(r: Rep[seq[DptRow]], outName, indent: string): string
proc emitNames(r: Rep[seq[NameRow]], outName, indent: string): string =
  if r.isStatic: return ""
  if r.node of DBForNode[NameRow]:
    let n = DBForNode[NameRow](r.node)
    return indent & "for " & n.binder & " in db." & n.table & ":\n" & emitNames(n.body, outName, indent & "  ")
  let n = ListNode[NameRow](r.node)
  case n.kind
  of lkEmpty: ""
  of lkYield: indent & outName & ".add(NameRow(name: " & emitString(NameValueNode(n.elem.node).name) & "))\n"
  of lkConcat: emitNames(n.left, outName, indent) & emitNames(n.right, outName, indent)
  of lkIf:
    let c = emitBoolHoisted(n.cond, indent)
    c.pre & indent & "if " & c.expr & ":\n" & emitNames(n.thenB, outName, indent & "  ")
proc emitInts(r: Rep[seq[int]], outName, indent: string): string =
  if r.node of DBForNode[int]:
    let n = DBForNode[int](r.node)
    return indent & "for " & n.binder & " in db." & n.table & ":\n" & emitInts(n.body, outName, indent & "  ")
  let n = ListNode[int](r.node)
  case n.kind
  of lkEmpty: ""
  of lkYield: indent & outName & ".add(" & emitInt(n.elem) & ")\n"
  of lkConcat: emitInts(n.left, outName, indent) & emitInts(n.right, outName, indent)
  of lkIf:
    let c = emitBoolHoisted(n.cond, indent)
    c.pre & indent & "if " & c.expr & ":\n" & emitInts(n.thenB, outName, indent & "  ")

proc emitDpts(r: Rep[seq[DptRow]], outName, indent: string): string =
  if r.node of DBForNode[DptRow]:
    let n = DBForNode[DptRow](r.node)
    return indent & "for " & n.binder & " in org." & n.table & ":\n" & emitDpts(n.body, outName, indent & "  ")
  let n = ListNode[DptRow](r.node)
  case n.kind
  of lkEmpty: ""
  of lkYield: indent & outName & ".add(DptRow(dpt: " & emitString(DptValueNode(n.elem.node).dpt) & "))\n"
  of lkConcat: emitDpts(n.left, outName, indent) & emitDpts(n.right, outName, indent)
  of lkIf:
    let c = emitBoolHoisted(n.cond, indent)
    c.pre & indent & "if " & c.expr & ":\n" & emitDpts(n.thenB, outName, indent & "  ")

proc oracleRange(db: PeopleDB, a, b: int): seq[string] =
  for p in db.people:
    if a <= p.age and p.age < b: result.add(p.name)
proc oracleAge(db: PeopleDB, s: string): seq[int] =
  for p in db.people:
    if p.name == s: result.add(p.age)
proc oracleRangeNames(db: PeopleDB, s, t: string): seq[string] =
  for a in oracleAge(db, s):
    for b in oracleAge(db, t): result.add(oracleRange(db, a, b))
proc oracleSatisfies(db: PeopleDB, pred: proc(age: int): bool): seq[string] =
  for p in db.people:
    if pred(p.age): result.add(p.name)

proc compileRun(src: string): string =
  let dir = getTempDir() / ("linq-" & $epochTime().int)
  createDir(dir); let path = dir / "main.nim"; let exe = dir / "main"
  writeFile(path, src)
  let c = execCmdEx(quoteShell(findExe("nim")) & " c --hints:off --nimcache:" & quoteShell(dir / "cache") & " --out:" & quoteShell(exe) & " " & quoteShell(path), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

proc linqChildren(n: IRNode): seq[IRNode] =
  ## Child IR nodes for the traversal callbacks. A DBFor child is listed
  ## via its reified body; field projections are leaves.
  if n of DBForNode[NameRow]:
    let d = DBForNode[NameRow](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of DBForNode[int]:
    let d = DBForNode[int](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of DBForNode[PersonRow]:
    let d = DBForNode[PersonRow](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of DBForNode[DptRow]:
    let d = DBForNode[DptRow](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of DBForNode[EmpRow]:
    let d = DBForNode[EmpRow](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of DBForNode[TaskRow]:
    let d = DBForNode[TaskRow](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of DBForNode[EmptyRow]:
    let d = DBForNode[EmptyRow](n)
    if not d.body.isStatic: result.add(d.body.node)
  elif n of ListNode[NameRow]:
    let l = ListNode[NameRow](n)
    case l.kind
    of lkEmpty: discard
    of lkYield:
      if not l.elem.isStatic: result.add(l.elem.node)
    of lkConcat:
      if not l.left.isStatic: result.add(l.left.node)
      if not l.right.isStatic: result.add(l.right.node)
    of lkIf:
      if not l.cond.isStatic: result.add(l.cond.node)
      if not l.thenB.isStatic: result.add(l.thenB.node)
      if not l.elseB.isStatic: result.add(l.elseB.node)
  elif n of ListNode[int]:
    let l = ListNode[int](n)
    case l.kind
    of lkEmpty: discard
    of lkYield:
      if not l.elem.isStatic: result.add(l.elem.node)
    of lkConcat:
      if not l.left.isStatic: result.add(l.left.node)
      if not l.right.isStatic: result.add(l.right.node)
    of lkIf:
      if not l.cond.isStatic: result.add(l.cond.node)
      if not l.thenB.isStatic: result.add(l.thenB.node)
      if not l.elseB.isStatic: result.add(l.elseB.node)
  elif n of ListNode[DptRow]:
    let l = ListNode[DptRow](n)
    case l.kind
    of lkEmpty: discard
    of lkYield:
      if not l.elem.isStatic: result.add(l.elem.node)
    of lkConcat:
      if not l.left.isStatic: result.add(l.left.node)
      if not l.right.isStatic: result.add(l.right.node)
    of lkIf:
      if not l.cond.isStatic: result.add(l.cond.node)
      if not l.thenB.isStatic: result.add(l.thenB.node)
  elif n of NameValueNode:
    let v = NameValueNode(n)
    if not v.name.isStatic: result.add(v.name.node)
  elif n of DptValueNode:
    let v = DptValueNode(n)
    if not v.dpt.isStatic: result.add(v.dpt.node)
  elif n of ExistsNode[EmptyRow]:
    let e = ExistsNode[EmptyRow](n)
    if not e.source.isStatic: result.add(e.source.node)
  elif n of ScalarNode[string]:
    let s = ScalarNode[string](n)
    if not s.left.isStatic: result.add(s.left.node)
    if not s.right.isStatic: result.add(s.right.node)
  elif n of ScalarNode[int]:
    let s = ScalarNode[int](n)
    if not s.left.isStatic: result.add(s.left.node)
    if not s.right.isStatic: result.add(s.right.node)
  elif n of ScalarNode[bool]:
    let s = ScalarNode[bool](n)
    if not s.left.isStatic: result.add(s.left.node)
    if not s.right.isStatic: result.add(s.right.node)
  elif n of TableNode:
    discard

proc linqCallbacks(): TraversalCallbacks[IRNode] =
  ## A DBFor node is a traversal boundary with its row binder, and is
  ## effectful unconditionally (it reads a database table).
  TraversalCallbacks[IRNode](
    children: linqChildren,
    key: proc(n: IRNode): string =
      if n of FieldNode: "field" else: "other",
    isComposite: proc(n: IRNode): bool = n of FieldNode,
    isBoundary: proc(n: IRNode): bool = n of DBForBase,
    binders: proc(n: IRNode): seq[string] =
      if n of DBForBase: @[DBForBase(n).binder] else: @[],
    isPure: proc(n: IRNode): bool = not (n of DBForBase))

proc linqCallbacksOpen(): TraversalCallbacks[IRNode] =
  ## Same callbacks with the boundary open and no effect marking: the
  ## control for the boundary test below.
  var cb = linqCallbacks()
  cb.isBoundary = proc(n: IRNode): bool = false
  cb.isPure = nil
  cb

when isMainModule:
  let data = PeopleDB(people: @[Person(name: "Alex", age: 60), Person(name: "Bert", age: 55), Person(name: "Cora", age: 33), Person(name: "Drew", age: 31), Person(name: "Edna", age: 21), Person(name: "Fred", age: 60)], couples: @[Couple(her: "Alex", him: "Bert"), Couple(her: "Cora", him: "Drew")])
  let orgData = OrgDB(
    departments: @[OrgDpt(dpt: "Product"), OrgDpt(dpt: "Quality"), OrgDpt(dpt: "Research"), OrgDpt(dpt: "Sales")],
    employees: @[OrgEmp(dpt: "Product", emp: "Alex"), OrgEmp(dpt: "Product", emp: "Bert"), OrgEmp(dpt: "Research", emp: "Cora"), OrgEmp(dpt: "Research", emp: "Drew"), OrgEmp(dpt: "Research", emp: "Edna"), OrgEmp(dpt: "Sales", emp: "Fred")],
    tasks: @[OrgTask(emp: "Alex", tsk: "build"), OrgTask(emp: "Bert", tsk: "build"), OrgTask(emp: "Cora", tsk: "abstract"), OrgTask(emp: "Cora", tsk: "build"), OrgTask(emp: "Cora", tsk: "design"), OrgTask(emp: "Drew", tsk: "abstract"), OrgTask(emp: "Drew", tsk: "design"), OrgTask(emp: "Edna", tsk: "abstract"), OrgTask(emp: "Edna", tsk: "call"), OrgTask(emp: "Edna", tsk: "design"), OrgTask(emp: "Fred", tsk: "call")])
  let q = rangeFromNames(db, liftNow("Edna"), liftNow("Bert"))
  doAssert oracleRangeNames(data, "Edna", "Bert") == @["Cora", "Drew", "Edna"]
  let source = "type Person = object\n  name: string\n  age: int\ntype NameRow = object\n  name: string\ntype DB = object\n  people: seq[Person]\nlet db = DB(people: @[Person(name: \"Alex\", age: 60), Person(name: \"Bert\", age: 55), Person(name: \"Cora\", age: 33), Person(name: \"Drew\", age: 31), Person(name: \"Edna\", age: 21), Person(name: \"Fred\", age: 60)])\nvar results: seq[NameRow] = @[]\n" & emitNames(q, "results", "") & "for x in results: echo x.name\n"
  doAssert compileRun(source) == "Cora\nDrew\nEdna"
  let t0 = And(Above(30), Below(40))
  let thirtySomethings3 = satisfies(P(t0))
  let t1 = Not(Or(Below(30), Above(40)))
  let thirtySomethings4 = satisfies(P(t1))
  let aboveFifty = satisfies(P(Above(50)))
  let nestedPredicate = satisfies(P(Or(Above(55), Below(25))))
  proc runNames(q: Rep[seq[NameRow]]): string =
    let src = "type Person = object\n  name: string\n  age: int\ntype NameRow = object\n  name: string\ntype DB = object\n  people: seq[Person]\nlet db = DB(people: @[Person(name: \"Alex\", age: 60), Person(name: \"Bert\", age: 55), Person(name: \"Cora\", age: 33), Person(name: \"Drew\", age: 31), Person(name: \"Edna\", age: 21), Person(name: \"Fred\", age: 60)])\nvar results: seq[NameRow] = @[]\n" & emitNames(q, "results", "") & "for x in results: echo x.name\n"
    compileRun(src)
  doAssert runNames(thirtySomethings3) == oracleSatisfies(data, proc(age: int): bool = 30 <= age and age < 40).join("\n")
  doAssert runNames(thirtySomethings4) == oracleSatisfies(data, proc(age: int): bool = not (age < 30 or age >= 40)).join("\n")
  doAssert runNames(aboveFifty) == oracleSatisfies(data, proc(age: int): bool = age >= 50).join("\n")
  doAssert runNames(nestedPredicate) == oracleSatisfies(data, proc(age: int): bool = age >= 55 or age < 25).join("\n")
  let predicateResidual = emitNames(aboveFifty, "results", "")
  doAssert predicateResidual.contains("for") and predicateResidual.contains("<=")
  doAssert "Predicate" notin predicateResidual and "P(" notin predicateResidual
  let thirty = range(db, liftNow(30), liftNow(40))
  doAssert thirty.node of DBForNode[NameRow]
  doAssert emitNames(thirty, "out", "").contains("for")
  let ages = ageFromName(db, liftNow("Cora")); doAssert ages.node of DBForNode[int]
  let nobody = ageFromName(db, liftNow("Nobody")); doAssert nobody.node of DBForNode[int]
  let emptyResult = dbfor(emptyList[PersonRow](), proc(x: Rep[PersonRow]): Rep[seq[NameRow]] = yieldList(nameValue(nameOf(x))))
  doAssert ListNode[NameRow](emptyResult.node).kind == lkEmpty
  let yielded = dbfor(yieldList(dynamic[PersonRow](RowNode(binder: "y"))),
    proc(x: Rep[PersonRow]): Rep[seq[int]] = yieldList(ageOf(x)))
  doAssert yielded.node of ListNode[int]
  let distributed = dbfor(concatList(people(db), people(db)),
    proc(x: Rep[PersonRow]): Rep[seq[int]] = yieldList(ageOf(x)))
  doAssert ListNode[int](distributed.node).kind == lkConcat
  let flattened = dbfor(dbfor(people(db),
    proc(x: Rep[PersonRow]): Rep[seq[PersonRow]] = yieldList(x)),
    proc(x: Rep[PersonRow]): Rep[seq[int]] = yieldList(ageOf(x)))
  doAssert flattened.node of DBForNode[int]
  let ifEmpty = ifThenElseList[int](liftNow(false), emptyList[int](), emptyList[int]())
  doAssert ListNode[int](ifEmpty.node).kind == lkEmpty
  let filtered = listFilter(people(db), proc(x: Rep[PersonRow]): Rep[bool] {.closure.} = gtR(ageOf(x), liftNow(50)))
  let mapped = listMap(filtered, proc(x: Rep[PersonRow]): Rep[NameRow] {.closure.} = nameValue(nameOf(x)))
  doAssert mapped.node of DBForNode[NameRow]
  var raised = false
  try: discard dbfor(dynamic[seq[int]](ScalarNode[int](kind: skAdd)), proc(x: Rep[int]): Rep[seq[int]] = yieldList(x))
  except ValueError: raised = true
  doAssert raised
  # dbfor over if-then-yield-else-yield is a staging-time error: the
  # tutorial's IfThen extractor matches an empty else only, so the else
  # branch must not be silently dropped.
  let dynCond = dynamic[bool](ScalarNode[bool](kind: skEq, left: liftNow(true), right: liftNow(true)))
  let ifBoth = listIf(dynCond, yieldList(liftNow(1)), yieldList(liftNow(2)))
  var raisedIf = false
  try: discard dbfor(ifBoth, proc(x: Rep[int]): Rep[seq[int]] = yieldList(x))
  except ValueError: raisedIf = true
  doAssert raisedIf
  # A flatMap body that is itself a DBFor flattens (for-over-for) instead
  # of crashing on the ListNode cast.
  let nested = dbfor(dbfor(people(db), proc(x: Rep[PersonRow]): Rep[seq[int]] = ageFromName(db, nameOf(x))),
    proc(a: Rep[int]): Rep[seq[int]] = yieldList(a))
  doAssert nested.node of DBForNode[int]
  doAssert emitInts(nested, "out", "").contains("for")
  # The DBFor node is a traversal boundary with its row binder, and is
  # effectful unconditionally. The boundary hides the body: no field
  # projection inside it is counted, while the same walk with the
  # boundary open counts them.
  var cb = linqCallbacks()
  doAssert cb.isBoundary(q.node)
  doAssert cb.binders(q.node) == @[DBForNode[NameRow](q.node).binder]
  doAssert isEffectful(q.node, cb)
  let wrapped = concatList(q, q)
  doAssert occurrences(wrapped.node, cb).getOrDefault("field") == 0
  doAssert occurrences(wrapped.node, linqCallbacksOpen()).getOrDefault("field") > 0
  let orgSource = "type DptRow = object\n  dpt: string\ntype EmpRow = object\n  dpt, emp: string\ntype TaskRow = object\n  emp, tsk: string\ntype Org = object\n  departments: seq[DptRow]\n  employees: seq[EmpRow]\n  tasks: seq[TaskRow]\nlet org = Org(departments: @[DptRow(dpt: \"Product\"), DptRow(dpt: \"Quality\"), DptRow(dpt: \"Research\"), DptRow(dpt: \"Sales\")], employees: @[EmpRow(dpt: \"Product\", emp: \"Alex\"), EmpRow(dpt: \"Product\", emp: \"Bert\"), EmpRow(dpt: \"Research\", emp: \"Cora\"), EmpRow(dpt: \"Research\", emp: \"Drew\"), EmpRow(dpt: \"Research\", emp: \"Edna\"), EmpRow(dpt: \"Sales\", emp: \"Fred\")], tasks: @[TaskRow(emp: \"Alex\", tsk: \"build\"), TaskRow(emp: \"Bert\", tsk: \"build\"), TaskRow(emp: \"Cora\", tsk: \"abstract\"), TaskRow(emp: \"Cora\", tsk: \"build\"), TaskRow(emp: \"Cora\", tsk: \"design\"), TaskRow(emp: \"Drew\", tsk: \"abstract\"), TaskRow(emp: \"Drew\", tsk: \"design\"), TaskRow(emp: \"Edna\", tsk: \"abstract\"), TaskRow(emp: \"Edna\", tsk: \"call\"), TaskRow(emp: \"Edna\", tsk: \"design\"), TaskRow(emp: \"Fred\", tsk: \"call\")])\nvar results: seq[DptRow] = @[]\n" & emitDpts(expertise(liftNow("abstract")), "results", "") & "for x in results: echo x.dpt\n"
  doAssert compileRun(orgSource) == "Quality\nResearch"
  let buildResult = compileRun(orgSource.replace("== \"abstract\"", "== \"build\""))
  doAssert buildResult == "Product\nQuality"
  doAssert compileRun(orgSource.replace("== \"abstract\"", "== \"call\"")) == "Quality\nSales"
  let orgResidual = emitDpts(expertise(liftNow("abstract")), "results", "")
  doAssert orgResidual.contains("var exists") and orgResidual.contains("for")
  doAssert "exists(" notin orgResidual and "materialize" notin orgResidual
  let orgWrapped = concatList(expertise(liftNow("abstract")), expertise(liftNow("build")))
  doAssert occurrences(orgWrapped.node, cb).getOrDefault("field") == 0
  doAssert occurrences(orgWrapped.node, linqCallbacksOpen()).getOrDefault("field") > 0
  echo "ok: linq staged database comprehensions, normalization, effects, and residual execution"
