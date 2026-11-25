## Small staged expression-language compiler demo.
##
## The object language is tagless-final, while the staged interpreter uses the
## framework only for binding-time decisions.  Its residual Block IR is local
## to this demo, deliberately keeping the framework's IRNode opaque.

import staging/framework
import std/[os, osproc, strutils, times]

type
  Base[I, B] = object
    lit: proc(x: int): I
    boolLit: proc(x: bool): B

  Arith[I, B] = object
    add: proc(x, y: I): I
    mul: proc(x, y: I): I
    greater: proc(x, y: I): B

  IfThenElse[I, B] = object
    ifThen: proc(c: B, yes, no: proc(): I): I

  ArithSym[I, B] = object
    base: Base[I, B]
    arith: Arith[I, B]
    ite: IfThenElse[I, B]
    variable: proc(name: string): I

  Exp = ref object of RootObj
  ConstExp = ref object of Exp
    value: int
  BoolConstExp = ref object of Exp
    value: bool
  InputExp = ref object of Exp
    name: string
  Sym = ref object of Exp
    id: int

  DefKind = enum dkAdd, dkMul, dkGreater, dkIf
  Block = object
    stms: seq[Stm]
    result: Exp
  Def = ref object
    kind: DefKind
    left, right: Exp
    cond: Exp
    thenBlock, elseBlock: Block
  Stm = object
    sym: Sym
    rhs: Def
  Residual = ref object of IRNode
    exp: Exp

  ReifyContext = ref object
    nextId: int
    blocks: seq[Block]

proc constExp(x: int): Exp = ConstExp(value: x)
proc boolConstExp(x: bool): Exp = BoolConstExp(value: x)
proc inputExp(name: string): Exp = InputExp(name: name)

proc repExp[T](r: Rep[T]): Exp =
  if r.isStatic:
    when T is int:
      return constExp(r.staticVal)
    elif T is bool:
      return boolConstExp(r.staticVal)
  Residual(r.node).exp

proc reflectDef(ctx: ReifyContext, d: Def): Sym =
  let s = Sym(id: ctx.nextId)
  inc ctx.nextId
  ctx.blocks[^1].stms.add(Stm(sym: s, rhs: d))
  s

proc reifyBlock(ctx: ReifyContext, body: proc(): Rep[int]): Block =
  ctx.blocks.add(Block(stms: @[]))
  let value = body()
  ctx.blocks[^1].result = repExp(value)
  ctx.blocks.pop()

proc repFromExp(e: Exp): Rep[int] =
  if e of ConstExp: return liftNow(ConstExp(e).value)
  dynamic[int](Residual(exp: e))

proc residual(ctx: ReifyContext, d: Def): Rep[int] =
  dynamic[int](Residual(exp: reflectDef(ctx, d)))

proc residualBool(ctx: ReifyContext, d: Def): Rep[bool] =
  dynamic[bool](Residual(exp: reflectDef(ctx, d)))

proc addStaged(ctx: ReifyContext, a, b: Rep[int]): Rep[int] =
  if a.isStatic and a.staticVal == 0: return b
  if b.isStatic and b.staticVal == 0: return a
  smartOp[int](a, b,
    proc(x, y: int): int = x + y,
    proc(x, y: Rep[int]): IRNode =
      Residual(exp: reflectDef(ctx, Def(kind: dkAdd, left: repExp(x), right: repExp(y)))))

proc mulStaged(ctx: ReifyContext, a, b: Rep[int]): Rep[int] =
  if a.isStatic and a.staticVal == 0: return liftNow(0)
  if b.isStatic and b.staticVal == 0: return liftNow(0)
  if a.isStatic and a.staticVal == 1: return b
  if b.isStatic and b.staticVal == 1: return a
  smartOp[int](a, b,
    proc(x, y: int): int = x * y,
    proc(x, y: Rep[int]): IRNode =
      Residual(exp: reflectDef(ctx, Def(kind: dkMul, left: repExp(x), right: repExp(y)))))

proc greaterStaged(ctx: ReifyContext, a, b: Rep[int]): Rep[bool] =
  if a.isStatic and b.isStatic: return liftNow(a.staticVal > b.staticVal)
  residualBool(ctx, Def(kind: dkGreater, left: repExp(a), right: repExp(b)))

proc ifStaged(ctx: ReifyContext, c: Rep[bool], yes, no: proc(): Rep[int]): Rep[int] =
  var thenBlock, elseBlock: Block
  let stagedYes = proc(): Rep[int] =
    thenBlock = reifyBlock(ctx, yes)
    repFromExp(thenBlock.result)
  let stagedNo = proc(): Rep[int] =
    elseBlock = reifyBlock(ctx, no)
    repFromExp(elseBlock.result)
  smartIf[int](c, stagedYes, stagedNo,
    proc(cond: Rep[bool], thenValue, elseValue: Rep[int]): IRNode =
      Residual(exp: reflectDef(ctx, Def(kind: dkIf, cond: repExp(cond),
        thenBlock: thenBlock, elseBlock: elseBlock))))

proc stagedSym(ctx: ReifyContext): ArithSym[Rep[int], Rep[bool]] =
  ArithSym[Rep[int], Rep[bool]](
    base: Base[Rep[int], Rep[bool]](
      lit: proc(x: int): Rep[int] = liftNow(x),
      boolLit: proc(x: bool): Rep[bool] = liftNow(x)),
    arith: Arith[Rep[int], Rep[bool]](
      add: proc(x, y: Rep[int]): Rep[int] = addStaged(ctx, x, y),
      mul: proc(x, y: Rep[int]): Rep[int] = mulStaged(ctx, x, y),
      greater: proc(x, y: Rep[int]): Rep[bool] = greaterStaged(ctx, x, y)),
    ite: IfThenElse[Rep[int], Rep[bool]](
      ifThen: proc(c: Rep[bool], yes, no: proc(): Rep[int]): Rep[int] =
        ifStaged(ctx, c, yes, no)),
    variable: proc(name: string): Rep[int] = dynamic[int](Residual(exp: inputExp(name))))

proc directSym(x: int): ArithSym[int, bool] =
  ArithSym[int, bool](
    base: Base[int, bool](lit: proc(n: int): int = n,
                          boolLit: proc(b: bool): bool = b),
    arith: Arith[int, bool](add: proc(a, b: int): int = a + b,
                            mul: proc(a, b: int): int = a * b,
                            greater: proc(a, b: int): bool = a > b),
    ite: IfThenElse[int, bool](ifThen: proc(c: bool, yes, no: proc(): int): int =
      if c: yes() else: no()),
    variable: proc(name: string): int =
      if name == "x": x else: raise newException(ValueError, "unbound: " & name))

proc sample[S, B](s: ArithSym[S, B]): S =
  ## x > 2 ? ((x * 2) + 1) : ((x + 0) + (2 * 3))
  s.ite.ifThen(s.arith.greater(s.variable("x"), s.base.lit(2)),
    proc(): S = s.arith.add(s.arith.mul(s.variable("x"), s.base.lit(2)), s.base.lit(1)),
    proc(): S = s.arith.add(s.arith.add(s.variable("x"), s.base.lit(0)),
                             s.arith.mul(s.base.lit(2), s.base.lit(3))))

proc literal[S, B](s: ArithSym[S, B]): S = s.base.lit(7)

proc nested[S, B](s: ArithSym[S, B]): S =
  s.arith.add(s.arith.mul(s.base.lit(2), s.base.lit(3)),
              s.arith.add(s.base.lit(4), s.base.lit(5)))

proc staticConditional[S, B](s: ArithSym[S, B]): S =
  s.ite.ifThen(s.base.boolLit(true),
    proc(): S = s.base.lit(8),
    proc(): S = s.base.lit(99))

proc emitExp(e: Exp): string
proc emitDef(d: Def): string
proc emitBlock(b: Block): string =
  result = "(block:\n"
  for stm in b.stms:
    result.add("  let s" & $stm.sym.id & " = " & emitDef(stm.rhs) & "\n")
  result.add("  " & emitExp(b.result) & "\n)")

proc emitExp(e: Exp): string =
  if e of ConstExp: return $ConstExp(e).value
  if e of BoolConstExp: return if BoolConstExp(e).value: "true" else: "false"
  if e of InputExp: return InputExp(e).name
  if e of Sym: return "s" & $Sym(e).id
  raise newException(ValueError, "unexpected non-atomic expression")

proc emitDef(d: Def): string =
  case d.kind
  of dkAdd: "(" & emitExp(d.left) & " + " & emitExp(d.right) & ")"
  of dkMul: "(" & emitExp(d.left) & " * " & emitExp(d.right) & ")"
  of dkGreater: "(" & emitExp(d.left) & " > " & emitExp(d.right) & ")"
  of dkIf: "(if " & emitExp(d.cond) & ": " & emitBlock(d.thenBlock) &
           " else: " & emitBlock(d.elseBlock) & ")"

proc emitProgram(b: Block, x: int): string =
  "let x = " & $x & "\nlet answer = " & emitBlock(b) & "\necho answer\n"

proc runEmitted(b: Block, x: int): int =
  let stamp = $int(epochTime())
  let source = getTempDir() / ("staging_compiler_" & stamp & ".nim")
  writeFile(source, emitProgram(b, x))
  let (output, code) = execCmdEx("export PATH=\"$HOME/.nimble/bin:$PATH\"; nim c -r --nimcache:/tmp/nimcache-emitted-compiler92 --hints:off " & quoteShell(source))
  removeFile(source)
  doAssert code == 0, output
  parseInt(output.strip().splitLines()[^1])

when isMainModule:
  let d = directSym(5)
  doAssert literal(d) == 7
  doAssert nested(d) == 15
  doAssert staticConditional(d) == 8
  doAssert sample(d) == 11
  let ctx = ReifyContext(nextId: 0, blocks: @[])
  let staged = stagedSym(ctx)
  let topBlock = reifyBlock(ctx, proc(): Rep[int] = sample(staged))
  doAssert topBlock.stms.len == 2
  doAssert topBlock.stms[1].rhs.kind == dkIf
  doAssert topBlock.stms[1].rhs.thenBlock.stms.len == 2
  doAssert topBlock.stms[1].rhs.elseBlock.stms.len == 1
  doAssert topBlock.stms[1].rhs.elseBlock.stms[0].rhs.kind == dkAdd
  doAssert topBlock.stms[1].rhs.elseBlock.stms[0].rhs.right of ConstExp
  doAssert runEmitted(topBlock, 5) == sample(d)

  let matrixCtx = ReifyContext(nextId: 0, blocks: @[])
  let matrixSym = stagedSym(matrixCtx)
  let matrixBlock = reifyBlock(matrixCtx, proc(): Rep[int] = nested(matrixSym))
  doAssert matrixBlock.stms.len == 0
  doAssert ConstExp(matrixBlock.result).value == nested(d)
  let branchBlock = reifyBlock(matrixCtx, proc(): Rep[int] = staticConditional(matrixSym))
  doAssert branchBlock.stms.len == 0
  doAssert ConstExp(branchBlock.result).value == staticConditional(d)

  let staticCtx = ReifyContext(nextId: 0, blocks: @[])
  let staticSym = stagedSym(staticCtx)
  let staticBlock = reifyBlock(staticCtx, proc(): Rep[int] =
    staticSym.arith.add(staticSym.base.lit(2), staticSym.base.lit(3)))
  doAssert staticBlock.stms.len == 0
  doAssert ConstExp(staticBlock.result).value == 5
  echo "ok: direct/staged compiler, Block reification, local folding, and emitter"
