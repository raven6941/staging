## TPCH-Q1-shaped fused filter/group/sum over struct-of-arrays columns.

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times]

type
  Kind = enum tkInput, tkLen
  Node = ref object of IRNode
    kind: Kind
    name: string
    intData: seq[int]
    floatData: seq[float]
    sourceInt: Arr[int]
    sourceFloat: Arr[float]

  ColumnarTable = object
    returnflag, shipdate: Arr[int]
    quantity: Arr[float]
    comment: Arr[int] # present in the source table, but not needed by this query

  PrunedTable = object
    returnflag, shipdate: Arr[int]
    quantity: Arr[float]

  Query = object
    table: ColumnarTable
    boundary: int

proc inputInt(name: string, data: seq[int]): Arr[int] =
  Arr[int](node: Node(kind: tkInput, name: name, intData: data))

proc inputFloat(name: string, data: seq[float]): Arr[float] =
  Arr[float](node: Node(kind: tkInput, name: name, floatData: data))

proc columnLength(a: Arr[int]): Rep[int] = lenArr[int](a,
  proc(x: Arr[int]): IRNode = Node(kind: tkLen, sourceInt: x))

proc pruneColumns(q: Query): PrunedTable =
  ## The projection is performed while staging.  The residual emitter only
  ## receives this pruned view, so an unused source column cannot leak into it.
  PrunedTable(returnflag: q.table.returnflag, shipdate: q.table.shipdate,
    quantity: q.table.quantity)

proc emitIntColumn(a: Arr[int]): string =
  let n = Node(a.node)
  doAssert n.kind == tkInput
  n.name

proc emitFloatColumn(a: Arr[float]): string =
  let n = Node(a.node)
  doAssert n.kind == tkInput
  n.name

proc emitResidual(q: Query): string =
  let t = pruneColumns(q)
  let flags = emitIntColumn(t.returnflag)
  let dates = emitIntColumn(t.shipdate)
  let quantities = emitFloatColumn(t.quantity)
  let n = columnLength(t.returnflag)
  doAssert n.isStatic == false # the residual gets its length from a column
  let lengthText = emitIntColumn(t.returnflag) # all SoA columns have equal length
  result = "var " & flags & ": seq[int] = " & $Node(t.returnflag.node).intData & "\n"
  result &= "var " & dates & ": seq[int] = " & $Node(t.shipdate.node).intData & "\n"
  result &= "var " & quantities & ": seq[float] = " & $Node(t.quantity.node).floatData & "\n"
  result &= "var positions = newSeq[int](32)\n"
  result &= "var groupKeys = newSeq[int](32)\n"
  result &= "var sums = newSeq[float](32)\n"
  result &= "var used = 0\n"
  result &= "var i = 0\n"
  result &= "while i < len(" & lengthText & "):\n"
  result &= "  if " & dates & "[i] <= " & $q.boundary & ":\n"
  result &= "    let key = " & flags & "[i]\n"
  result &= "    var position = positions[key]\n"
  result &= "    if position == 0:\n"
  result &= "      position = used + 1\n"
  result &= "      positions[key] = position\n"
  result &= "      groupKeys[used] = key\n"
  result &= "      used += 1\n"
  result &= "    sums[position - 1] += " & quantities & "[i]\n"
  result &= "  i += 1\n"
  result &= "echo used\n"
  result &= "for j in 0 ..< used:\n"
  result &= "  echo groupKeys[j], \" \", sums[j]"

proc compileRun(src, exe, dir: string): string =
  let nim = findExe("nim")
  doAssert nim.len > 0
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

type GroupResult = object
  key: int
  sum: float

proc direct(q: Query): seq[GroupResult] =
  var positions = newSeq[int](32)
  let flags = Node(q.table.returnflag.node).intData
  let dates = Node(q.table.shipdate.node).intData
  let quantities = Node(q.table.quantity.node).floatData
  let rows = flags.len
  for i in 0 ..< rows:
    if dates[i] <= q.boundary:
      let key = flags[i]
      if positions[key] == 0:
        positions[key] = result.len + 1
        result.add(GroupResult(key: key, sum: 0.0))
      result[positions[key] - 1].sum += quantities[i]

proc runAndCheck(q: Query, expected: seq[GroupResult], prefix: string) =
  let text = emitResidual(q)
  doAssert text.count("while") == 1
  doAssert text.count("newSeq") == 3 # only the residual hash table columns
  doAssert "comment" notin text
  doAssert "filtered" notin text
  doAssert "row" notin text
  let dir = getTempDir() / (prefix & "-" & $getCurrentProcessId() & "-" &
    $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"
  let exe = dir / "residual"
  writeFile(source, text)
  let lines = compileRun(source, exe, dir).splitLines
  doAssert parseInt(lines[0]) == expected.len
  for i in 0 ..< expected.len:
    let fields = lines[i + 1].splitWhitespace
    doAssert parseInt(fields[0]) == expected[i].key
    doAssert parseFloat(fields[1]) == expected[i].sum
  removeDir(dir)

when isMainModule:
  let table = ColumnarTable(
    returnflag: inputInt("returnflag", @[0, 1, 0, 2, 1, 3]),
    shipdate: inputInt("shipdate", @[10, 11, 10, 9, 12, 10]),
    quantity: inputFloat("quantity", @[1.5, 2.0, 3.5, 4.0, 9.0, 6.0]),
    comment: inputInt("comment", @[99, 98, 97, 96, 95, 94]))
  let q = Query(table: table, boundary: 10)
  let pruned = pruneColumns(q)
  doAssert Node(pruned.returnflag.node).name == "returnflag"
  doAssert Node(pruned.shipdate.node).name == "shipdate"
  doAssert Node(pruned.quantity.node).name == "quantity"
  runAndCheck(q, direct(q), "tpch-q1")
  doAssert direct(q).len == 3
  doAssert direct(q)[0].key == 0 and direct(q)[0].sum == 5.0 # boundary rows included
  doAssert direct(q)[1].key == 2 and direct(q)[1].sum == 4.0 # single-row group
  doAssert direct(q)[2].key == 3 and direct(q)[2].sum == 6.0

  # The boundary row (date 10) is included, key 3 is a single-row group, and
  # key 1 is emptied by the filter in this second query.
  let boundary = Query(table: table, boundary: 9)
  let expected = direct(boundary)
  doAssert expected.len == 1
  doAssert expected[0].key == 2
  runAndCheck(boundary, expected, "tpch-q1-boundary")

  echo "ok: tpch q1 fused group sum"
