## Sequential OptiML-style Stream core.
##
## This is deliberately Nim-specific: samples are flat seq/Arr cells and the
## scalar distance is abs(a - b), rather than OptiML's dimensional dist.
## The two row passes (find, then count) remain separate; there is no parallel
## DeliteOpForeach and no loop-fusion pass here. Note the apprx set always
## contains the row's self-index (distance 0 < apprxWidth), so a literally
## empty apprx set cannot occur; case 2 is the nearest form (only the
## self-index matches).

import staging/framework
import staging/arrays
import std/[os, osproc, strutils, times]

type
  RowInfo = object
    chunk, row: int
  StreamBox[A] = object
    data: A
    rows, cols, chunkSize: int
  StreamKind = enum skInputF, skInputA, skLitI, skLitF, skAddI, skSubI,
    skMulI, skSubF, skAbsF, skLtI, skLtF, skEqI, skDecl, skRead, skWrite,
    skSeq, skIf, skWhile, skArrDecl, skArrRead, skArrWrite,
    skStream, skChunkRow, skRowElem
  StreamNode = ref object of IRNode
    kind: StreamKind
    name: string
    i1, i2: Rep[int]
    f1, f2: Rep[float]
    b: Rep[bool]
    initI: Rep[int]
    initF: Rep[float]
    v: Var[int]
    iv: Rep[int]
    a, z: Rep[Unit]
    thenB, elseB: Rep[Unit]
    arrI: Arr[int]
    arrF: Arr[float]
    index: Rep[int]
    valueI: Rep[int]
    valueF: Rep[float]
    row: Rep[RowInfo]
    streamData: Arr[float]
    chunk, rowIndex: Rep[int]
  StreamSym[I, F, B, S, C, A, D, R, ST] = object
    litI: proc(x: int): I
    litF: proc(x: float): F
    addI, subI: proc(x, y: I): I
    subF: proc(x, y: F): F
    absF: proc(x: F): F
    ltI: proc(x, y: I): B
    ltF: proc(x, y: F): B
    eqI: proc(x, y: I): B
    unit: proc(): S
    seq: proc(x, y: S): S
    ifB: proc(c: B, t, e: proc(): S): S
    whileLoop: proc(c: proc(): B, body: proc(): S): S
    varNew: proc(x: I): C
    varRead: proc(v: C): I
    varWrite: proc(v: C, x: I): S
    arrReadI: proc(a: D, i: I): I
    arrWriteI: proc(a: D, i, x: I): S
    arrReadF: proc(a: A, i: I): F
    streamNew: proc(data: A): ST
    rows: proc(st: ST, body: proc(r: R): S): S
    rowAt: proc(r: R, j: I): F
    rowIndex: proc(r: R): I
    inputF: proc(name: string): A
    inputI: proc(name: string): D
  StreamProgram[S, C, D] = object
    body: S
    result: D
    chunk, row: C

proc directRows(st: StreamBox[seq[float]], body: proc(r: RowInfo): Unit): Unit =
  for c in 0 ..< 3:
    for r in 0 ..< 2:
      discard body(RowInfo(chunk: c, row: r))
  Unit()

proc directExpected(data: seq[float], initial: seq[int]): seq[int] =
  result = initial
  for i in 0 ..< 6:
    if result[i] == 0:
      var count = 0
      for j in 0 ..< 6:
        if abs(data[i * 6] - data[i * 6 + j]) < 3: inc count
      for j in 0 ..< 6:
        if abs(data[i * 6] - data[i * 6 + j]) < 1.5: result[j] = count

proc directSym(data: seq[float], widths: (float, float), densities: seq[int]):
    StreamSym[int, float, bool, Unit, ref int, seq[float], seq[int], RowInfo,
      StreamBox[seq[float]]] =
  StreamSym[int, float, bool, Unit, ref int, seq[float], seq[int], RowInfo,
    StreamBox[seq[float]]](
    litI: proc(x: int): int = x, litF: proc(x: float): float = x,
    addI: proc(x, y: int): int = x + y, subI: proc(x, y: int): int = x - y,
    subF: proc(x, y: float): float = x - y,
    absF: proc(x: float): float = abs(x), ltI: proc(x, y: int): bool = x < y,
    ltF: proc(x, y: float): bool = x < y, eqI: proc(x, y: int): bool = x == y,
    unit: proc(): Unit = Unit(), seq: proc(x, y: Unit): Unit = Unit(),
    ifB: proc(c: bool, t, e: proc(): Unit): Unit = (if c: t() else: e()),
    whileLoop: proc(c: proc(): bool, body: proc(): Unit): Unit =
      (while c(): discard body(); Unit()),
    varNew: proc(x: int): ref int = (new(result); result[] = x),
    varRead: proc(v: ref int): int = v[],
    varWrite: proc(v: ref int, x: int): Unit = (v[] = x; Unit()),
    arrReadI: proc(a: seq[int], i: int): int = a[i],
    arrWriteI: proc(a: seq[int], i, x: int): Unit = (discard; Unit()),
    arrReadF: proc(a: seq[float], i: int): float = a[i],
    streamNew: proc(d: seq[float]): StreamBox[seq[float]] =
      StreamBox[seq[float]](data: d, rows: 6, cols: 6, chunkSize: 2),
    rows: directRows,
    rowAt: proc(r: RowInfo, j: int): float = data[((r.chunk * 2 + r.row) * 6) + j],
    rowIndex: proc(r: RowInfo): int = r.chunk * 2 + r.row,
    inputF: proc(name: string): seq[float] = data,
    inputI: proc(name: string): seq[int] = densities)

proc stagedSym(): StreamSym[Rep[int], Rep[float], Rep[bool], Rep[Unit], Var[int],
    Arr[float], Arr[int], Rep[RowInfo], StreamBox[Arr[float]]] =
  var vn = 0
  let chunkV = newVar[int](liftNow(0), proc(x: Rep[int]): IRNode = StreamNode(kind: skDecl, name: "chunk", initI: x))
  let rowV = newVar[int](liftNow(0), proc(x: Rep[int]): IRNode = StreamNode(kind: skDecl, name: "row", initI: x))
  StreamSym[Rep[int], Rep[float], Rep[bool], Rep[Unit], Var[int], Arr[float],
    Arr[int], Rep[RowInfo], StreamBox[Arr[float]]](
    litI: proc(x: int): Rep[int] = liftNow(x), litF: proc(x: float): Rep[float] = liftNow(x),
    addI: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y, proc(a,b:int):int=a+b,
      proc(a,b:Rep[int]):IRNode=StreamNode(kind:skAddI,i1:a,i2:b)),
    subI: proc(x, y: Rep[int]): Rep[int] = smartOp[int](x, y, proc(a,b:int):int=a-b,
      proc(a,b:Rep[int]):IRNode=StreamNode(kind:skSubI,i1:a,i2:b)),
    subF: proc(x, y: Rep[float]): Rep[float] = smartOp[float](x, y, proc(a,b:float):float=a-b,
      proc(a,b:Rep[float]):IRNode=StreamNode(kind:skSubF,f1:a,f2:b)),
    absF: proc(x: Rep[float]): Rep[float] = smartOpUni[float](x, proc(a:float):float=abs(a),
      proc(a:Rep[float]):IRNode=StreamNode(kind:skAbsF,f1:a)),
    ltI: proc(x,y:Rep[int]):Rep[bool] = (if x.isStatic and y.isStatic: liftNow(x.staticVal<y.staticVal) else: dynamic[bool](StreamNode(kind:skLtI,i1:x,i2:y))),
    ltF: proc(x,y:Rep[float]):Rep[bool] = dynamic[bool](StreamNode(kind:skLtF,f1:x,f2:y)),
    eqI: proc(x,y:Rep[int]):Rep[bool] = dynamic[bool](StreamNode(kind:skEqI,i1:x,i2:y)),
    unit: proc():Rep[Unit]=unit(), seq: proc(x,y:Rep[Unit]):Rep[Unit]=seqR(x,y,proc(a,b:Rep[Unit]):IRNode=StreamNode(kind:skSeq,a:a,z:b)),
    ifB: proc(c:Rep[bool],t,e:proc():Rep[Unit]):Rep[Unit]=smartIf[Unit](c,t,e,proc(c:Rep[bool],a,b:Rep[Unit]):IRNode=StreamNode(kind:skIf,b:c,thenB:a,elseB:b)),
    whileLoop: proc(c:proc():Rep[bool],body:proc():Rep[Unit]):Rep[Unit]=smartWhile(c,body,proc(c:Rep[bool],b:Rep[Unit]):IRNode=StreamNode(kind:skWhile,b:c,z:b)),
    varNew: proc(x:Rep[int]):Var[int]=(inc vn; newVar[int](x,proc(x:Rep[int]):IRNode=StreamNode(kind:skDecl,name:"v" & $vn,initI:x))),
    varRead: proc(v:Var[int]):Rep[int]=readVar[int](v,proc(v:Var[int]):IRNode=StreamNode(kind:skRead,v:v)),
    varWrite: proc(v:Var[int],x:Rep[int]):Rep[Unit]=writeVar[int](v,x,proc(v:Var[int],x:Rep[int]):IRNode=StreamNode(kind:skWrite,v:v,iv:x)),
    arrReadI: proc(a:Arr[int],i:Rep[int]):Rep[int]=readArr[int](a,i,proc(a:Arr[int],i:Rep[int]):IRNode=StreamNode(kind:skArrRead,arrI:a,index:i)),
    arrWriteI: proc(a:Arr[int],i,x:Rep[int]):Rep[Unit]=writeArr[int](a,i,x,proc(a:Arr[int],i,x:Rep[int]):IRNode=StreamNode(kind:skArrWrite,arrI:a,index:i,valueI:x)),
    arrReadF: proc(a:Arr[float],i:Rep[int]):Rep[float]=readArr[float](a,i,proc(a:Arr[float],i:Rep[int]):IRNode=StreamNode(kind:skArrRead,arrF:a,index:i)),
    streamNew: proc(d:Arr[float]):StreamBox[Arr[float]]=StreamBox[Arr[float]](data:d,rows:6,cols:6,chunkSize:2),
    rows: proc(st:StreamBox[Arr[float]],body:proc(r:Rep[RowInfo]):Rep[Unit]):Rep[Unit]=
      (let rnode = dynamic[RowInfo](StreamNode(kind:skChunkRow,streamData:st.data,chunk:dynamic[int](StreamNode(kind:skRead,v:chunkV)),rowIndex:dynamic[int](StreamNode(kind:skRead,v:rowV))));
       let inner = smartWhile(proc():Rep[bool]=dynamic[bool](StreamNode(kind:skLtI,i1:dynamic[int](StreamNode(kind:skRead,v:rowV)),i2:liftNow(st.chunkSize))),
         proc():Rep[Unit]=seqR(body(rnode),writeVar[int](rowV,smartOp[int](dynamic[int](StreamNode(kind:skRead,v:rowV)),liftNow(1),proc(a,b:int):int=a+b,proc(a,b:Rep[int]):IRNode=StreamNode(kind:skAddI,i1:a,i2:b)),proc(v:Var[int],x:Rep[int]):IRNode=StreamNode(kind:skWrite,v:v,iv:x)),proc(a,b:Rep[Unit]):IRNode=StreamNode(kind:skSeq,a:a,z:b)),
         proc(c:Rep[bool],b:Rep[Unit]):IRNode=StreamNode(kind:skWhile,b:c,z:b));
       let outer = smartWhile(proc():Rep[bool]=dynamic[bool](StreamNode(kind:skLtI,i1:dynamic[int](StreamNode(kind:skRead,v:chunkV)),i2:liftNow(3))),
         proc():Rep[Unit]=seqR(writeVar[int](rowV,liftNow(0),proc(v:Var[int],x:Rep[int]):IRNode=StreamNode(kind:skWrite,v:v,iv:x)),seqR(inner,writeVar[int](chunkV,smartOp[int](dynamic[int](StreamNode(kind:skRead,v:chunkV)),liftNow(1),proc(a,b:int):int=a+b,proc(a,b:Rep[int]):IRNode=StreamNode(kind:skAddI,i1:a,i2:b)),proc(v:Var[int],x:Rep[int]):IRNode=StreamNode(kind:skWrite,v:v,iv:x)),proc(a,b:Rep[Unit]):IRNode=StreamNode(kind:skSeq,a:a,z:b)),proc(a,b:Rep[Unit]):IRNode=StreamNode(kind:skSeq,a:a,z:b)),proc(c:Rep[bool],b:Rep[Unit]):IRNode=StreamNode(kind:skWhile,b:c,z:b)); outer),
    rowAt: proc(r:Rep[RowInfo],j:Rep[int]):Rep[float] =
      (let n=StreamNode(r.node); doAssert n.kind==skChunkRow; dynamic[float](StreamNode(kind:skRowElem,streamData:n.streamData,chunk:n.chunk,rowIndex:n.rowIndex,i1:j))),
    rowIndex: proc(r:Rep[RowInfo]):Rep[int] =
      # Row index is chunk * chunkSize + row, NOT chunk + row: the
      # multiply must be its own node, or the emitted index silently
      # reads the wrong densities entry (caught by case 3 below).
      let n = StreamNode(r.node)
      let chunk2 = smartOp[int](n.chunk, liftNow(2), proc(a, b: int): int = a * b,
        proc(a, b: Rep[int]): IRNode = StreamNode(kind: skMulI, i1: a, i2: b))
      smartOp[int](chunk2, n.rowIndex, proc(a, b: int): int = a + b,
        proc(a, b: Rep[int]): IRNode = StreamNode(kind: skAddI, i1: a, i2: b)),
    inputF: proc(name:string):Arr[float]=Arr[float](node:StreamNode(kind:skInputF,name:name)),
    inputI: proc(name:string):Arr[int]=Arr[int](node:StreamNode(kind:skInputA,name:name)))

proc densityProgram[I,F,B,S,C,A,D,R,ST](s: StreamSym[I,F,B,S,C,A,D,R,ST]): StreamProgram[S,C,D] =
  let data = s.inputF("data")
  let dens = s.inputI("densities")
  let st = s.streamNew(data)
  let aw = s.litF(1.5)
  let kw = s.litF(3.0)
  let body = s.rows(st, proc(row: R): S =
    let i = s.rowIndex(row)
    s.ifB(s.eqI(s.arrReadI(dens, i), s.litI(0)), proc(): S =
      let count = s.varNew(s.litI(0)); let j = s.varNew(s.litI(0))
      let countLoop = s.whileLoop(proc(): B = s.ltI(s.varRead(j), s.litI(6)), proc(): S =
        let d = s.absF(s.subF(s.rowAt(row, s.litI(0)), s.rowAt(row, s.varRead(j))))
        s.seq(s.ifB(s.ltF(d, kw), proc(): S = s.varWrite(count, s.addI(s.varRead(count), s.litI(1))), proc(): S = s.unit()), s.varWrite(j, s.addI(s.varRead(j), s.litI(1)))))
      let k = s.varNew(s.litI(0))
      let updateLoop = s.whileLoop(proc(): B = s.ltI(s.varRead(k), s.litI(6)), proc(): S =
        let d = s.absF(s.subF(s.rowAt(row, s.litI(0)), s.rowAt(row, s.varRead(k))))
        s.seq(s.ifB(s.ltF(d, aw), proc(): S = s.arrWriteI(dens, s.varRead(k), s.varRead(count)), proc(): S = s.unit()), s.varWrite(k, s.addI(s.varRead(k), s.litI(1)))))
      # The row body is built once at staging time, so count/j/k are ONE
      # residual var each, shared by every row iteration: reset them at
      # the top of the body. (The direct Sym calls this proc per row and
      # gets fresh refs, so the resets are no-ops there.) Without the
      # resets, j/k stay 6 after the first row and later rows do nothing
      # — masked in cases 0-2 because every row writes the same values.
      let reset = s.seq(s.varWrite(count, s.litI(0)),
        s.seq(s.varWrite(j, s.litI(0)), s.varWrite(k, s.litI(0))))
      s.seq(reset, s.seq(countLoop, updateLoop)), proc(): S = s.unit()))
  StreamProgram[S,C,D](body: body, result: dens, chunk: s.varNew(s.litI(0)), row: s.varNew(s.litI(0)))

proc emitInt(r: Rep[int]): string =
  if r.isStatic: return $r.staticVal
  let n=StreamNode(r.node)
  case n.kind
  of skAddI: "("&emitInt(n.i1)&" + "&emitInt(n.i2)&")"
  of skSubI: "("&emitInt(n.i1)&" - "&emitInt(n.i2)&")"
  of skMulI: "("&emitInt(n.i1)&" * "&emitInt(n.i2)&")"
  of skRead: StreamNode(n.v.node).name
  of skInputA: n.name
  of skArrRead: StreamNode(n.arrI.node).name&"["&emitInt(n.index)&"]"
  else: raise newException(ValueError,"bad int")

proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let n=StreamNode(r.node)
  case n.kind
  of skSubF: "("&emitFloat(n.f1)&" - "&emitFloat(n.f2)&")"
  of skAbsF: "abs("&emitFloat(n.f1)&")"
  of skArrRead: StreamNode(n.arrF.node).name&"["&emitInt(n.index)&"]"
  of skRowElem: ""&StreamNode(n.streamData.node).name&"[(("&emitInt(n.chunk)&" * 2 + "&emitInt(n.rowIndex)&") * 6) + "&emitInt(n.i1)&"]"
  else: raise newException(ValueError,"bad float")

proc emitBool(r: Rep[bool]): string =
  let n=StreamNode(r.node)
  case n.kind
  of skLtI: "("&emitInt(n.i1)&" < "&emitInt(n.i2)&")"
  of skLtF: "("&emitFloat(n.f1)&" < "&emitFloat(n.f2)&")"
  of skEqI: "("&emitInt(n.i1)&" == "&emitInt(n.i2)&")"
  else: raise newException(ValueError,"bad bool")

proc emitStmt(r: Rep[Unit], ind=""): string =
  if r.isStatic: return ind&"discard"
  let n=StreamNode(r.node)
  case n.kind
  of skSeq: emitStmt(n.a,ind)&"\n"&emitStmt(n.z,ind)
  of skWhile: ind&"while "&emitBool(n.b)&":\n"&emitStmt(n.z,ind&"  ")
  of skIf: ind&"if "&emitBool(n.b)&":\n"&emitStmt(n.thenB,ind&"  ")&"\n"&ind&"else:\n"&emitStmt(n.elseB,ind&"  ")
  of skWrite: ind&StreamNode(n.v.node).name&" = "&emitInt(n.iv)
  of skArrWrite: ind&StreamNode(n.arrI.node).name&"["&emitInt(n.index)&"] = "&emitInt(n.valueI)
  else: raise newException(ValueError,"bad stmt")

proc compileRun(src, exe, dir: string): string =
  let n=findExe("nim"); let c=execCmdEx(quoteShell(n)&" c --hints:off --nimcache:"&quoteShell(dir/"nimcache")&" --out:"&quoteShell(exe)&" "&quoteShell(src),{poUsePath,poStdErrToStdOut},workingDir=dir)
  doAssert c.exitCode==0,c.output
  let r=execCmdEx(quoteShell(exe),{poUsePath,poStdErrToStdOut},workingDir=dir); doAssert r.exitCode==0,r.output; r.output.strip

when isMainModule:
  # Load-bearing negative check: without StreamChunkRow -> StreamRow rewrite,
  # emitted row access would be a row-object accessor rather than this index.
  let ss=stagedSym(); let p=densityProgram(ss); let text=emitStmt(p.body)
  doAssert "while" in text and text.count("while")>=2
  doAssert "[((" in text and "StreamRow(" notin text
  # Row index must be chunk * chunkSize + row: the old rowIndex built an
  # skAddI node for a*2+b, which emitted "(chunk + row)" and read the wrong
  # densities entry in the skip check (case 3 distinguishes the two).
  doAssert "((chunk * 2) + row)" in text
  doAssert "(chunk + row)" notin text
  let ds = @[0.0,1.0,2.0,10.0,11.0,12.0,20.0,21.0,22.0,30.0,31.0,32.0,40.0,41.0,42.0,50.0,51.0,52.0,60.0,61.0,62.0,70.0,71.0,72.0,80.0,81.0,82.0,90.0,91.0,92.0,100.0,101.0,102.0,110.0,111.0,112.0,120.0,121.0,122.0]
  for caseNo in 0 .. 3:
    var input = ds
    var initial = newSeq[int](6)
    if caseNo == 1: initial = @[0, 7, 0, 0, 0, 0]
    if caseNo == 2:
      for x in 0 ..< input.len:
        input[x] = float(x * 100)
    if caseNo == 3:
      # Distinguishing dataset: per-row counts differ, and row 2's update
      # is the only write to densities[2] after row 0. With the old
      # "(chunk + row)" index, row 2 was skipped (it read densities[1] = 9)
      # and rows 3/4 were skipped too, giving [1, 9, 0, 0, 0, 0] instead
      # of the direct [1, 3, 3, 0, 0, 0].
      input = @[0.0, 1.5, 1.6, 1.7, 1.8, 1.9,
                100.0, 101.0, 102.0, 103.0, 104.0, 105.0,
                200.0, 200.5, 201.0, 210.0, 211.0, 212.0,
                300.0, 310.0, 320.0, 330.0, 340.0, 350.0,
                400.0, 410.0, 420.0, 430.0, 440.0, 450.0,
                500.0, 510.0, 520.0, 530.0, 540.0, 550.0]
      initial = @[0, 9, 0, 0, 0, 0]
    let expected = directExpected(input, initial)
    let dir=getTempDir()/("stream-" & $getCurrentProcessId() & "-" & $int(epochTime()*1000) & "-" & $caseNo); createDir(dir)
    let src=dir/"residual.nim"; let exe=dir/"residual"; writeFile(src,"import std/math\nvar data = " & $input & "\nvar densities = " & $initial & "\nvar chunk = 0\nvar row = 0\nvar v1=0\nvar v2=0\nvar v3=0\nvar v4=0\nvar v5=0\n" & text & "\nfor x in densities: stdout.write($x & \" \" )\n")
    let got = compileRun(src,exe,dir).splitWhitespace
    for i in 0 ..< 6: doAssert parseInt(got[i]) == expected[i]
    removeDir(dir)
  echo "ok: sequential stream chunks, row rewrite, and codegen"

