import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times, sequtils]

type
  ShonanKind = enum skInput, skLit, skAdd, skMul, skEq, skLt, skDecl, skRead,
    skWrite, skSeq, skIf, skWhile, skArrDecl, skArrRead, skArrWrite
  ShonanNode = ref object of IRNode
    kind: ShonanKind
    name: string
    i1, i2: Rep[int]
    b: Rep[bool]
    value: Rep[int]
    init: Rep[int]
    v: Var[int]
    a, z, thenB, elseB: Rep[Unit]
    arr: Arr[int]
    index: Rep[int]
  ShonanSym[I, B, S, C, A] = object
    lit: proc(x: int): I
    add, mul: proc(x, y: I): I
    eq, lt: proc(x, y: I): B
    unit: proc(): S
    seq: proc(x, y: S): S
    ifB: proc(c: B, t, e: proc(): S): S
    whileLoop: proc(c: proc(): B, body: proc(): S): S
    varNew: proc(x: I): C
    varRead: proc(v: C): I
    varWrite: proc(v: C, x: I): S
    arrNew: proc(n: I): A
    arrRead: proc(a: A, i: I): I
    arrWrite: proc(a: A, i, x: I): S
  ShonanProgram[S, C, A] = object
    body: S
    output: A
    vars: seq[C]

proc directSym(): ShonanSym[int, bool, Unit, ref int, ref seq[int]] =
  result = ShonanSym[int, bool, Unit, ref int, ref seq[int]](
    lit: proc(x: int): int = x,
    add: proc(x, y: int): int = x + y,
    mul: proc(x, y: int): int = x * y,
    eq: proc(x, y: int): bool = x == y,
    lt: proc(x, y: int): bool = x < y,
    unit: proc(): Unit = Unit(),
    seq: proc(x, y: Unit): Unit = Unit(),
    ifB: proc(c: bool, t, e: proc(): Unit): Unit = (if c: t() else: e()),
    whileLoop: proc(c: proc(): bool, body: proc(): Unit): Unit =
      (while c(): discard body(); Unit()),
    varNew: proc(x: int): ref int = (new(result); result[] = x),
    varRead: proc(v: ref int): int = v[],
    varWrite: proc(v: ref int, x: int): Unit = (v[] = x; Unit()),
    arrNew: proc(n: int): ref seq[int] = (new(result); result[] = newSeq[int](n)),
    arrRead: proc(a: ref seq[int], i: int): int = a[][i],
    arrWrite: proc(a: ref seq[int], i, x: int): Unit = (a[][i] = x; Unit()))

proc stagedSym(): ShonanSym[Rep[int], Rep[bool], Rep[Unit], Var[int], Arr[int]] =
  ShonanSym[Rep[int], Rep[bool], Rep[Unit], Var[int], Arr[int]](
    lit: proc(x: int): Rep[int] = liftNow(x),
    add: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y,
      proc(a, b: int): int = a + b,
      proc(a, b: Rep[int]): IRNode = ShonanNode(kind: skAdd, i1: a, i2: b)),
    mul: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y,
      proc(a, b: int): int = a * b,
      proc(a, b: Rep[int]): IRNode = ShonanNode(kind: skMul, i1: a, i2: b)),
    eq: proc(x, y: Rep[int]): Rep[bool] =
      (if x.isStatic and y.isStatic: liftNow(x.staticVal == y.staticVal)
       else: dynamic[bool](ShonanNode(kind: skEq, i1: x, i2: y))),
    lt: proc(x, y: Rep[int]): Rep[bool] =
      (if x.isStatic and y.isStatic: liftNow(x.staticVal < y.staticVal)
       else: dynamic[bool](ShonanNode(kind: skLt, i1: x, i2: y))),
    unit: proc(): Rep[Unit] = unit(),
    seq: proc(x, y: Rep[Unit]): Rep[Unit] = seqR(x, y,
      proc(a, b: Rep[Unit]): IRNode = ShonanNode(kind: skSeq, a: a, z: b)),
    ifB: proc(c: Rep[bool], t, e: proc(): Rep[Unit]): Rep[Unit] = smartIf[Unit](c, t, e,
      proc(c: Rep[bool], a, b: Rep[Unit]): IRNode = ShonanNode(kind: skIf, b: c, thenB: a, elseB: b)),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] = smartWhile(c, body,
      proc(c: Rep[bool], b: Rep[Unit]): IRNode = ShonanNode(kind: skWhile, b: c, z: b)),
    varNew: proc(x: Rep[int]): Var[int] = newVar[int](x,
      proc(x: Rep[int]): IRNode = ShonanNode(kind: skDecl, name: "j", init: x)),
    varRead: proc(v: Var[int]): Rep[int] = readVar[int](v,
      proc(v: Var[int]): IRNode = ShonanNode(kind: skRead, v: v)),
    varWrite: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = ShonanNode(kind: skWrite, v: v, value: x)),
    arrNew: proc(n: Rep[int]): Arr[int] = newArray[int](n,
      proc(n: Rep[int]): IRNode = ShonanNode(kind: skArrDecl, name: "result", init: n)),
    arrRead: proc(a: Arr[int], i: Rep[int]): Rep[int] = readArr[int](a, i,
      proc(a: Arr[int], i: Rep[int]): IRNode = ShonanNode(kind: skArrRead, arr: a, index: i)),
    arrWrite: proc(a: Arr[int], i, x: Rep[int]): Rep[Unit] = writeArr[int](a, i, x,
      proc(a: Arr[int], i, x: Rep[int]): IRNode = ShonanNode(kind: skArrWrite, arr: a, index: i, value: x)))

proc unrollIf[I, B, S, C, A](s: ShonanSym[I, B, S, C, A], dense: bool, r: HSlice[int, int],
    body: proc(j: I): S, vars: var seq[C]): S

proc matrixVectorProd[I, B, S, C, A](s: ShonanSym[I, B, S, C, A], matrix: seq[seq[int]], v: A,
    useUnroll = false): ShonanProgram[S, C, A] =
  let output = s.arrNew(s.lit(matrix.len))
  var whole = s.unit()
  var vars: seq[C] = @[]
  for i in 0 ..< matrix.len:
    let nz = (block:
      var xs: seq[int] = @[]
      for j, x in matrix[i]:
        if x != 0: xs.add(j)
      xs)
    let dense = nz.len >= 3
    proc term(j: I): S =
      when I is Rep[int]:
        if j.isStatic:
          let col = j.staticVal
          if matrix[i][col] == 0: return s.unit()
          return s.arrWrite(output, s.lit(i), s.add(s.arrRead(output, s.lit(i)),
            s.mul(s.lit(matrix[i][col]), s.arrRead(v, s.lit(col)))))
        var terms = s.unit()
        for col in nz:
          let c = col
          terms = s.seq(terms, s.ifB(s.eq(j, s.lit(c)), proc(): S =
            s.arrWrite(output, s.lit(i), s.add(s.arrRead(output, s.lit(i)),
              s.mul(s.lit(matrix[i][c]), s.arrRead(v, j)))), proc(): S = s.unit()))
        terms
      else:
        if matrix[i][j] == 0: return s.unit()
        return s.arrWrite(output, s.lit(i), s.add(s.arrRead(output, s.lit(i)),
          s.mul(s.lit(matrix[i][j]), s.arrRead(v, s.lit(j)))))
    let part = if useUnroll:
      unrollIf(s, dense, 0 ..< matrix[i].len, term, vars)
    else:
      if dense:
        let j = s.varNew(s.lit(0)); vars.add(j)
        s.whileLoop(proc(): B = s.lt(s.varRead(j), s.lit(matrix[i].len)), proc(): S =
          s.seq(term(s.varRead(j)), s.varWrite(j, s.add(s.varRead(j), s.lit(1)))))
      else:
        unrollIf(s, false, 0 ..< matrix[i].len, term, vars)
    whole = s.seq(whole, part)
  ShonanProgram[S, C, A](body: whole, output: output, vars: vars)

proc unrollIf[I, B, S, C, A](s: ShonanSym[I, B, S, C, A], dense: bool, r: HSlice[int, int],
    body: proc(j: I): S, vars: var seq[C]): S =
  if dense:
    let j = s.varNew(s.lit(r.a)); vars.add(j)
    s.whileLoop(proc(): B = s.lt(s.varRead(j), s.lit(r.b + 1)), proc(): S =
      s.seq(body(s.varRead(j)), s.varWrite(j, s.add(s.varRead(j), s.lit(1)))))
  else:
    var acc = s.unit()
    for j in r.a .. r.b: acc = s.seq(acc, body(s.lit(j)))
    acc

proc emitInt(x: Rep[int]): string =
  if x.isStatic: return $x.staticVal
  let n = ShonanNode(x.node)
  case n.kind
  of skAdd: "(" & emitInt(n.i1) & " + " & emitInt(n.i2) & ")"
  of skMul: "(" & emitInt(n.i1) & " * " & emitInt(n.i2) & ")"
  of skRead: ShonanNode(n.v.node).name
  of skArrRead: ShonanNode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  else: raise newException(ValueError, "bad integer node")

proc emitBool(x: Rep[bool]): string =
  if x.isStatic: return $x.staticVal
  let n = ShonanNode(x.node)
  let op = if n.kind == skEq: " == " else: " < "
  doAssert n.kind in {skEq, skLt}
  "(" & emitInt(n.i1) & op & emitInt(n.i2) & ")"

proc emitStmt(x: Rep[Unit], ind = ""): string =
  if x.isStatic: return ind & "discard"
  let n = ShonanNode(x.node)
  case n.kind
  of skSeq: emitStmt(n.a, ind) & "\n" & emitStmt(n.z, ind)
  of skWhile: ind & "while " & emitBool(n.b) & ":\n" & emitStmt(n.z, ind & "  ")
  of skIf: ind & "if " & emitBool(n.b) & ":\n" & emitStmt(n.thenB, ind & "  ") & "\n" & ind & "else:\n" & emitStmt(n.elseB, ind & "  ")
  of skWrite: ind & ShonanNode(n.v.node).name & " = " & emitInt(n.value)
  of skArrWrite: ind & ShonanNode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitInt(n.value)
  else: raise newException(ValueError, "bad statement node")

proc emitDecl(v: Var[int]): string =
  let n = ShonanNode(v.node); "var " & n.name & " = " & emitInt(n.init)
proc emitArr(a: Arr[int]): string =
  let n = ShonanNode(a.node); "var " & n.name & " = newSeq[int](" & emitInt(n.init) & ")"
proc compileRun(src, exe, dir: string): string =
  let nim = findExe("nim"); doAssert nim.len > 0
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

proc direct(matrix: seq[seq[int]], v: seq[int]): seq[int] =
  result = newSeq[int](matrix.len)
  for i, row in matrix:
    for j, x in row: result[i] += x * v[j]

when isMainModule:
  let matrix = @[@[1, 1, 1, 1, 1], @[0, 0, 0, 0, 0], @[0, 0, 1, 0, 0], @[0, 0, 0, 0, 0], @[0, 0, 1, 0, 1]]
  let vectors = @[@[1, 1, 1, 1, 1], @[2, -1, 3, -2, 4], @[-3, 0, 2, 7, -1]]
  let d = directSym()
  for v in vectors:
    let a = d.arrNew(v.len)
    for i, x in v: discard d.arrWrite(a, d.lit(i), d.lit(x))
    let got = matrixVectorProd(d, matrix, a).output
    let expected = direct(matrix, v)
    for i in 0 ..< expected.len:
      if got[][i] != expected[i]: echo "mismatch ", v, " got ", got[], " expected ", expected
      doAssert got[][i] == expected[i]
  doAssert matrix[1].countIt(it != 0) == 0 and matrix[3].countIt(it != 0) == 0
  doAssert matrix[0].countIt(it != 0) >= 3 and matrix[2].countIt(it != 0) < 3
  let input = Arr[int](node: ShonanNode(kind: skInput, name: "input"))
  let explicit = matrixVectorProd(stagedSym(), matrix, input)
  let abstracted = matrixVectorProd(stagedSym(), matrix, input, true)
  let explicitText = emitStmt(explicit.body)
  let abstractedText = emitStmt(abstracted.body)
  doAssert explicitText == abstractedText
  doAssert explicit.vars.len == 1 and abstracted.vars.len == 1
  doAssert "while" in explicitText and explicitText.count("while") == 1
  doAssert "input" in explicitText and "result" in emitArr(explicit.output)
  doAssert "input[2]" in explicitText and "matrix" notin explicitText
  doAssert "matrix" notin explicitText
  doAssert "result[1]" notin explicitText and "result[3]" notin explicitText
  doAssert matrixVectorProd(stagedSym(), @[@[0, 0]], input).body.isStatic
  doAssert "while" notin emitStmt(matrixVectorProd(stagedSym(), @[@[4]], input).body)
  let secondMatrix = @[@[2, 0, 0], @[0, -3, 0], @[0, 0, 0]]
  let secondVector = @[4, -2, 9]
  let secondDirect = directSym()
  let secondInput = secondDirect.arrNew(secondVector.len)
  for i, x in secondVector: discard secondDirect.arrWrite(secondInput, secondDirect.lit(i), secondDirect.lit(x))
  let secondGot = matrixVectorProd(secondDirect, secondMatrix, secondInput).output
  let secondExpected = direct(secondMatrix, secondVector)
  for i, x in secondExpected: doAssert secondGot[][i] == x
  let secondResidual = matrixVectorProd(stagedSym(), secondMatrix, input, true)
  doAssert "while" notin emitStmt(secondResidual.body)
  let dir = getTempDir() / ("shonan-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let source = dir / "residual.nim"; let exe = dir / "residual"
  for v in vectors:
    writeFile(source, "var input = @[" & v.mapIt($it).join(", ") & "]\n" & emitArr(explicit.output) & "\n" &
      emitDecl(explicit.vars[0]) & "\n" & explicitText & "\nfor x in result: echo x\n")
    let output = compileRun(source, exe, dir).splitWhitespace
    let expected = direct(matrix, v)
    for i, x in expected: doAssert parseInt(output[i]) == x
  removeDir(dir)
  echo "ok: shonan HMM"
