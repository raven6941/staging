## Arrays are cells, not pure Rep[seq[T]] values: this test deliberately
## checks that a write followed by a read observes mutation.

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times]

type
  DArr = ref object
    values: seq[int]
  ArrayKind = enum akInput, akAdd, akSub, akMul, akLe, akDecl, akRead, akWrite,
    akLen, akVarDecl, akVarRead, akVarWrite, akSeq, akWhile
  ArrayNode = ref object of IRNode
    kind: ArrayKind
    left, right: Rep[int]
    cond: Rep[bool]
    init: Rep[int]
    name: string
    arr: Arr[int]
    index, value: Rep[int]
    v: Var[int]
    a, b: Rep[Unit]
    body: Rep[Unit]

  ArraySym[I, B, S, C, A] = object
    lit: proc(n: int): I
    add, sub, mul: proc(a, b: I): I
    le: proc(a, b: I): B
    unit: proc(): S
    seq: proc(a, b: S): S
    whileLoop: proc(c: proc(): B, body: proc(): S): S
    varNew: proc(init: I): C
    varRead: proc(v: C): I
    varWrite: proc(v: C, x: I): S
    arrayNew: proc(len: I): A
    arrayRead: proc(a: A, i: I): I
    arrayWrite: proc(a: A, i, x: I): S
    arrayLen: proc(a: A): I

  StencilProgram[I, S, C, A] = object
    input, output: A
    index: C
    body: S

proc directArraySym(): ArraySym[int, bool, Unit, ref int, DArr] =
  ArraySym[int, bool, Unit, ref int, DArr](
    lit: proc(n: int): int = n,
    add: proc(a, b: int): int = a + b,
    sub: proc(a, b: int): int = a - b,
    mul: proc(a, b: int): int = a * b,
    le: proc(a, b: int): bool = a <= b,
    unit: proc(): Unit = Unit(),
    seq: proc(a, b: Unit): Unit = Unit(),
    whileLoop: proc(c: proc(): bool, body: proc(): Unit): Unit =
      (while c(): discard body(); Unit()),
    varNew: proc(init: int): ref int = (new(result); result[] = init),
    varRead: proc(v: ref int): int = v[],
    varWrite: proc(v: ref int, x: int): Unit = (v[] = x; Unit()),
    arrayNew: proc(len: int): DArr = DArr(values: newSeq[int](len)),
    arrayRead: proc(a: DArr, i: int): int = a.values[i],
    arrayWrite: proc(a: DArr, i, x: int): Unit = (a.values[i] = x; Unit()),
    arrayLen: proc(a: DArr): int = a.values.len)

proc stagedArraySym(): ArraySym[Rep[int], Rep[bool], Rep[Unit], Var[int], Arr[int]] =
  var varNumber = 0
  var arrayNumber = 0
  result = ArraySym[Rep[int], Rep[bool], Rep[Unit], Var[int], Arr[int]](
    lit: proc(n: int): Rep[int] = liftNow(n),
    add: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x + y,
      proc(x, y: Rep[int]): IRNode = ArrayNode(kind: akAdd, left: x, right: y)),
    sub: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x - y,
      proc(x, y: Rep[int]): IRNode = ArrayNode(kind: akSub, left: x, right: y)),
    mul: proc(a, b: Rep[int]): Rep[int] = smartOp[int](a, b,
      proc(x, y: int): int = x * y,
      proc(x, y: Rep[int]): IRNode = ArrayNode(kind: akMul, left: x, right: y)),
    le: proc(a, b: Rep[int]): Rep[bool] =
      (if a.isStatic and b.isStatic: liftNow(a.staticVal <= b.staticVal)
       else: dynamic[bool](ArrayNode(kind: akLe, left: a, right: b))),
    unit: proc(): Rep[Unit] = unit(),
    seq: proc(a, b: Rep[Unit]): Rep[Unit] = seqR(a, b,
      proc(a, b: Rep[Unit]): IRNode = ArrayNode(kind: akSeq, a: a, b: b)),
    whileLoop: proc(c: proc(): Rep[bool], body: proc(): Rep[Unit]): Rep[Unit] =
      smartWhile(c, body, proc(c: Rep[bool], b: Rep[Unit]): IRNode =
        ArrayNode(kind: akWhile, cond: c, body: b)),
    varNew: proc(init: Rep[int]): Var[int] =
      (inc varNumber; newVar[int](init, proc(init: Rep[int]): IRNode =
        ArrayNode(kind: akVarDecl, name: (if varNumber == 1: "j" else: "tmp"), init: init))),
    varRead: proc(v: Var[int]): Rep[int] = readVar[int](v,
      proc(v: Var[int]): IRNode = ArrayNode(kind: akVarRead, v: v)),
    varWrite: proc(v: Var[int], x: Rep[int]): Rep[Unit] = writeVar[int](v, x,
      proc(v: Var[int], x: Rep[int]): IRNode = ArrayNode(kind: akVarWrite, v: v, value: x)),
    arrayNew: proc(len: Rep[int]): Arr[int] =
      (inc arrayNumber; newArray[int](len,
        proc(len: Rep[int]): IRNode = ArrayNode(kind: akDecl,
          name: (if arrayNumber == 1: "input" else: "output"), left: len))),
    arrayRead: proc(a: Arr[int], i: Rep[int]): Rep[int] = readArr[int](a, i,
      proc(a: Arr[int], i: Rep[int]): IRNode = ArrayNode(kind: akRead, arr: a, index: i)),
    arrayWrite: proc(a: Arr[int], i, x: Rep[int]): Rep[Unit] = writeArr[int](a, i, x,
      proc(a: Arr[int], i, x: Rep[int]): IRNode = ArrayNode(kind: akWrite, arr: a, index: i, value: x)),
    arrayLen: proc(a: Arr[int]): Rep[int] = lenArr[int](a,
      proc(a: Arr[int]): IRNode = ArrayNode(kind: akLen, arr: a)))

proc stencilB[I, B, S, C, A](s: ArraySym[I, B, S, C, A], a: A, j: I): I =
  let w1mm = s.mul(s.arrayRead(a, s.sub(j, s.lit(2))), s.arrayRead(a, s.sub(j, s.lit(1))))
  let w1m = s.mul(s.arrayRead(a, s.sub(j, s.lit(1))), s.arrayRead(a, j))
  let w1 = s.mul(s.arrayRead(a, j), s.arrayRead(a, s.add(j, s.lit(1))))
  let w1p = s.mul(s.arrayRead(a, s.add(j, s.lit(1))), s.arrayRead(a, s.add(j, s.lit(2))))
  let wmPrev = s.sub(s.sub(s.arrayRead(a, s.sub(j, s.lit(1))), w1m), w1mm)
  let wm = s.sub(s.sub(s.arrayRead(a, j), w1), w1m)
  let wmp = s.sub(s.sub(s.arrayRead(a, s.add(j, s.lit(1))), w1p), w1)
  let w2m = s.mul(wmPrev, wm)
  let w2 = s.mul(wm, wmp)
  s.add(s.sub(wm, w2), w2m)

proc stencilProgram[I, B, S, C, A](s: ArraySym[I, B, S, C, A], input: A): StencilProgram[I, S, C, A] =
  let n = s.arrayLen(input)
  let output = s.arrayNew(n)
  let j = s.varNew(s.lit(2))
  let loop = s.whileLoop(
    proc(): B = s.le(s.varRead(j), s.sub(n, s.lit(3))),
    proc(): S = s.seq(s.arrayWrite(output, s.varRead(j), stencilB(s, input, s.varRead(j))),
      s.varWrite(j, s.add(s.varRead(j), s.lit(1)))))
  StencilProgram[I, S, C, A](input: input, output: output, index: j, body: loop)

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n = ArrayNode(r.node)
  case n.kind
  of akInput: "n"
  of akAdd: "(" & emitInt(n.left) & " + " & emitInt(n.right) & ")"
  of akSub: "(" & emitInt(n.left) & " - " & emitInt(n.right) & ")"
  of akMul: "(" & emitInt(n.left) & " * " & emitInt(n.right) & ")"
  of akRead: ArrayNode(n.arr.node).name & "[" & emitInt(n.index) & "]"
  of akLen: "len(" & ArrayNode(n.arr.node).name & ")"
  of akVarRead: ArrayNode(n.v.node).name
  else: raise newException(ValueError, "not an int expression")

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = ArrayNode(r.node)
  doAssert n.kind == akLe
  "(" & emitInt(n.left) & " <= " & emitInt(n.right) & ")"

proc emitStmt(r: Rep[Unit], indent = ""): string =
  if r.isStatic: return indent & "discard"
  let n = ArrayNode(r.node)
  case n.kind
  of akSeq: emitStmt(n.a, indent) & "\n" & emitStmt(n.b, indent)
  of akWhile: indent & "while " & emitBool(n.cond) & ":\n" & emitStmt(n.body, indent & "  ")
  of akWrite: indent & ArrayNode(n.arr.node).name & "[" & emitInt(n.index) & "] = " & emitInt(n.value)
  of akVarWrite: indent & ArrayNode(n.v.node).name & " = " & emitInt(n.value)
  else: raise newException(ValueError, "not a statement")

proc emitDecl(a: Arr[int]): string =
  let n = ArrayNode(a.node)
  "var " & n.name & " = newSeq[int](" & emitInt(n.left) & ")"

proc emitDecl(v: Var[int]): string =
  let n = ArrayNode(v.node)
  "var " & n.name & " = " & emitInt(n.init)

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let r = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

when isMainModule:
  let ss = stagedArraySym()
  let stagedInput = ss.arrayNew(dynamic[int](ArrayNode(kind: akInput)))
  let staged = stencilProgram(ss, stagedInput)
  doAssert not ArrayNode(staged.output.node).left.isStatic
  let loopNode = ArrayNode(staged.body.node)
  doAssert loopNode.kind == akWhile and not loopNode.cond.isStatic

  for n in [4, 5, 6, 8]:
    var input = DArr(values: newSeq[int](n))
    for i in 0 ..< n: input.values[i] = i + 2
    let direct = stencilProgram(directArraySym(), input)
    let dir = getTempDir() / ("staging-arrays-" & $getCurrentProcessId() & "-" & $n & "-" & $int(epochTime() * 1000))
    createDir(dir)
    let source = dir / "residual.nim"
    let exe = dir / "residual"
    var src = "let n = " & $n & "\n" & emitDecl(stagedInput) & "\n" &
      emitDecl(staged.output) & "\n" & emitDecl(staged.index) & "\n"
    for i, x in input.values: src.add("input[" & $i & "] = " & $x & "\n")
    src.add("\n" & emitStmt(staged.body) & "\n")
    if n >= 5:
      for i in 2 .. n - 3: src.add("echo output[" & $i & "]\n")
    writeFile(source, src)
    let got = compileRun(source, exe, dir).splitLines
    if n >= 5:
      for i in 2 .. n - 3: doAssert parseInt(got[i - 2]) == direct.output.values[i]
    removeDir(dir)

  # Mutation semantics: a write followed by a read sees the new slot value.
  let mut = ss.arrayNew(liftNow(2))
  let write = ss.arrayWrite(mut, liftNow(0), liftNow(41))
  let read = ss.arrayRead(mut, liftNow(0))
  let other = ss.arrayRead(mut, liftNow(1))
  doAssert not write.isStatic and not read.isStatic
  doAssert ArrayNode(mut.node).kind == akDecl
  doAssert ArrayNode(read.node).kind == akRead
  let mutDir = getTempDir() / ("staging-arrays-mutation-" & $getCurrentProcessId())
  createDir(mutDir)
  let mutSource = mutDir / "residual.nim"
  let mutExe = mutDir / "residual"
  writeFile(mutSource, emitDecl(mut) & "\n" & emitStmt(write) & "\n" &
    "echo " & emitInt(read) & "\n" & "echo " & emitInt(other) & "\n")
  let mutGot = compileRun(mutSource, mutExe, mutDir).splitLines
  doAssert mutGot == @["41", "0"]
  removeDir(mutDir)

  let staticLen = newArray[int](liftNow(3), proc(len: Rep[int]): IRNode = ArrayNode(kind: akDecl, left: len))
  doAssert staticLen.node != nil
  echo "ok: dynamic array stencil, mutation, and static-length cells"
