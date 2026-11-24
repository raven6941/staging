## Staged Complex numbers over the structs facility (04_atwork, lines ~1059-1230).
##
## Two forms of the tutorial's example:
## - Static-pair form: `Complex` as a staging-time pair of `Rep[Double]`
##   (Prod2 from staging/structs), with `+`/`*` per the tutorial formulas and
##   scalar-times, so `c1 + 5 * c2` residualizes to plain `Double` arithmetic
##   with no `Complex` object. A dynamic condition cannot select between two
##   static pairs directly, so the conditional uses the tutorial's explicit
##   split: one residual `if` per field.
## - Struct form: `Rep[Complex]` built through a residual struct node
##   (`struct`/`field` in the tutorial's ComplexStructExp sense): construction
##   and `re`/`im` projection go through the node, `+`/`*` are defined on the
##   interface, and `if test c1 else c2` works directly on the dynamic type.
##   Field access pattern-matches a static value (the tutorial's `field`
##   behaviour): a static `Rep[Complex]` projects its stored fields, a
##   dynamic one emits a residual projection.
##
## Out of scope: `Vector[Complex]` as a VectorOps element type (#50's
## boundary stands); Delite machinery. The FFT butterfly already exercised
## in test_structs.nim is not redone here.

import staging/framework
import staging/structs
import std/[math, os, osproc, sequtils, strutils, times]

type
  Complex = Prod2[float, float]
  DirectComplex = object
    re, im: float
  CplxKind = enum
    ckInput, ckBoolInput, ckAdd, ckSub, ckMul, ckIfF,
    ckStruct, ckRe, ckIm, ckIfC
  ComplexNode = ref object of IRNode
    kind: CplxKind
    name: string
    left, right: Rep[float]
    cond: Rep[bool]
    thenF, elseF: Rep[float]
    re, im: Rep[float]
    cplx: Rep[Complex]
    thenC, elseC: Rep[Complex]

proc addR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x + y,
  proc(x, y: Rep[float]): IRNode = ComplexNode(kind: ckAdd, left: x, right: y))
proc subR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x - y,
  proc(x, y: Rep[float]): IRNode = ComplexNode(kind: ckSub, left: x, right: y))
proc mulR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x * y,
  proc(x, y: Rep[float]): IRNode = ComplexNode(kind: ckMul, left: x, right: y))

# --- Static-pair form ---

proc cplx(re, im: Rep[float]): Complex = prod2(re, im)
proc cadd(a, b: Complex): Complex = mapProd2(a, b, addR, addR)
proc cmul(a, b: Complex): Complex =
  ## Tutorial formula: (ar*br - ai*bi, ar*bi + ai*br).
  prod2(subR(mulR(a.fst, b.fst), mulR(a.snd, b.snd)),
        addR(mulR(a.fst, b.snd), mulR(a.snd, b.fst)))
proc scalarMul(s: Rep[float], c: Complex): Complex =
  prod2(mulR(s, c.fst), mulR(s, c.snd))
proc cplxIf(test: Rep[bool], a, b: Complex): Complex =
  ## Tutorial's explicit split: one residual `if` per field.
  prod2(smartIf[float](test, proc(): Rep[float] = a.fst,
                       proc(): Rep[float] = b.fst,
                       proc(c: Rep[bool], t, e: Rep[float]): IRNode =
                         ComplexNode(kind: ckIfF, cond: c, thenF: t, elseF: e)),
        smartIf[float](test, proc(): Rep[float] = a.snd,
                       proc(): Rep[float] = b.snd,
                       proc(c: Rep[bool], t, e: Rep[float]): IRNode =
                         ComplexNode(kind: ckIfF, cond: c, thenF: t, elseF: e)))

# --- Struct form: Rep[Complex] ---

proc structCplx(re, im: Rep[float]): Rep[Complex] =
  ## Fully static fields fold to a static struct (the tutorial's `field`
  ## pattern-match on a Struct creation then sees the stored fields).
  if re.isStatic and im.isStatic: liftNow(prod2(re, im))
  else: dynamic[Complex](ComplexNode(kind: ckStruct, re: re, im: im))
proc reOf(c: Rep[Complex]): Rep[float] =
  ## `field` behaviour: a static struct projects its stored field; a dynamic
  ## one emits a residual projection.
  if c.isStatic: c.staticVal.fst
  else: dynamic[float](ComplexNode(kind: ckRe, cplx: c))
proc imOf(c: Rep[Complex]): Rep[float] =
  if c.isStatic: c.staticVal.snd
  else: dynamic[float](ComplexNode(kind: ckIm, cplx: c))
proc caddS(a, b: Rep[Complex]): Rep[Complex] =
  structCplx(addR(reOf(a), reOf(b)), addR(imOf(a), imOf(b)))
proc cmulS(a, b: Rep[Complex]): Rep[Complex] =
  structCplx(subR(mulR(reOf(a), reOf(b)), mulR(imOf(a), imOf(b))),
             addR(mulR(reOf(a), imOf(b)), mulR(imOf(a), reOf(b))))
proc cplxIfS(test: Rep[bool], a, b: Rep[Complex]): Rep[Complex] =
  ## Fully dynamic DSL type: the conditional works directly, no manual split.
  smartIf[Complex](test, proc(): Rep[Complex] = a, proc(): Rep[Complex] = b,
    proc(c: Rep[bool], t, e: Rep[Complex]): IRNode =
      ComplexNode(kind: ckIfC, cond: c, thenC: t, elseC: e))

# --- Direct execution ---

proc `+`(a, b: DirectComplex): DirectComplex =
  DirectComplex(re: a.re + b.re, im: a.im + b.im)
proc `*`(a, b: DirectComplex): DirectComplex =
  DirectComplex(re: a.re * b.re - a.im * b.im,
                im: a.re * b.im + a.im * b.re)

# --- Emitters ---

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  ComplexNode(r.node).name

proc emitFloat(r: Rep[float]): string
  ## Forward declaration: float emission projects through struct values,
  ## and struct emission needs float emission.

proc emitCplx(r: Rep[Complex]): string =
  if r.isStatic:
    return "Complex(re: " & emitFloat(r.staticVal.fst) &
      ", im: " & emitFloat(r.staticVal.snd) & ")"
  let node = ComplexNode(r.node)
  case node.kind
  of ckStruct:
    "Complex(re: " & emitFloat(node.re) & ", im: " & emitFloat(node.im) & ")"
  of ckIfC:
    "(if " & emitBool(node.cond) & ": " & emitCplx(node.thenC) &
      " else: " & emitCplx(node.elseC) & ")"
  else: raise newException(ValueError, "bad complex expression: " & $node.kind)

proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let node = ComplexNode(r.node)
  case node.kind
  of ckInput: node.name
  of ckAdd: "(" & emitFloat(node.left) & " + " & emitFloat(node.right) & ")"
  of ckSub: "(" & emitFloat(node.left) & " - " & emitFloat(node.right) & ")"
  of ckMul: "(" & emitFloat(node.left) & " * " & emitFloat(node.right) & ")"
  of ckIfF: "(if " & emitBool(node.cond) & ": " & emitFloat(node.thenF) &
              " else: " & emitFloat(node.elseF) & ")"
  of ckRe: emitCplx(node.cplx) & ".re"
  of ckIm: emitCplx(node.cplx) & ".im"
  else: raise newException(ValueError, "bad float expression: " & $node.kind)

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let built = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert built.exitCode == 0, built.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

proc checkClose(got: seq[float], want: DirectComplex) =
  doAssert got.len == 2
  doAssert abs(got[0] - want.re) < 1e-9, $got & " vs re=" & $want.re & " im=" & $want.im
  doAssert abs(got[1] - want.im) < 1e-9, $got & " vs re=" & $want.re & " im=" & $want.im

when isMainModule:
  let xre = dynamic[float](ComplexNode(kind: ckInput, name: "xre"))
  let xim = dynamic[float](ComplexNode(kind: ckInput, name: "xim"))
  let yre = dynamic[float](ComplexNode(kind: ckInput, name: "yre"))
  let yim = dynamic[float](ComplexNode(kind: ckInput, name: "yim"))
  let test = dynamic[bool](ComplexNode(kind: ckBoolInput, name: "test"))
  let x = cplx(xre, xim)
  let y = cplx(yre, yim)

  # Static folding: fully static operands fold to static fields.
  let folded = cmul(cplx(liftNow(1.0), liftNow(2.0)),
                    cplx(liftNow(3.0), liftNow(4.0)))
  doAssert folded.fst.isStatic and folded.fst.staticVal == -5.0
  doAssert folded.snd.isStatic and folded.snd.staticVal == 10.0

  type Case = tuple[x, y: DirectComplex]
  let cases: array[2, Case] = [
    (DirectComplex(re: 1.0, im: 2.0), DirectComplex(re: 3.0, im: -1.0)),
    (DirectComplex(re: 0.0, im: -2.5), DirectComplex(re: -1.5, im: 0.0))]
  let dir = getTempDir() / ("staging-complex-" & $getCurrentProcessId() & "-" &
    $int(epochTime() * 1000))
  createDir(dir)
  for c in cases:
    let cx = DirectComplex(re: c.x.re, im: c.x.im)
    let cy = DirectComplex(re: c.y.re, im: c.y.im)
    let directAdd = cx + cy
    let directMul = cx * cy
    let directScaled = cx + DirectComplex(re: 5.0 * cy.re, im: 5.0 * cy.im)

    # Static-pair form: residual is plain Double arithmetic, no Complex.
    let stagedAdd = cadd(x, y)
    let stagedMul = cmul(x, y)
    let stagedScaled = cadd(x, scalarMul(liftNow(5.0), y))
    let pairSrc = "let xre = " & $cx.re & "\nlet xim = " & $cx.im & "\n" &
      "let yre = " & $cy.re & "\nlet yim = " & $cy.im & "\n" &
      "let addRe = " & emitFloat(stagedAdd.fst) & "\n" &
      "let addIm = " & emitFloat(stagedAdd.snd) & "\n" &
      "let mulRe = " & emitFloat(stagedMul.fst) & "\n" &
      "let mulIm = " & emitFloat(stagedMul.snd) & "\n" &
      "let scaledRe = " & emitFloat(stagedScaled.fst) & "\n" &
      "let scaledIm = " & emitFloat(stagedScaled.snd) & "\n" &
      "echo addRe, \" \", addIm\n" &
      "echo mulRe, \" \", mulIm\n" &
      "echo scaledRe, \" \", scaledIm\n"
    doAssert "Complex" notin pairSrc
    doAssert "object" notin pairSrc
    let pairSource = dir / "pair.nim"
    let pairExe = dir / "pair"
    writeFile(pairSource, pairSrc)
    let pairLines = compileRun(pairSource, pairExe, dir).splitLines
    checkClose(pairLines[0].splitWhitespace.map(parseFloat), directAdd)
    checkClose(pairLines[1].splitWhitespace.map(parseFloat), directMul)
    checkClose(pairLines[2].splitWhitespace.map(parseFloat), directScaled)

    # Conditional split: both branches of `test`.
    let split = cplxIf(test, x, y)
    for flag in [true, false]:
      let splitSrc = "let xre = " & $cx.re & "\nlet xim = " & $cx.im & "\n" &
        "let yre = " & $cy.re & "\nlet yim = " & $cy.im & "\n" &
        "let test = " & $flag & "\n" &
        "let outRe = " & emitFloat(split.fst) & "\n" &
        "let outIm = " & emitFloat(split.snd) & "\n" &
        "echo outRe, \" \", outIm\n"
      doAssert "Complex" notin splitSrc
      let splitSource = dir / "split.nim"
      let splitExe = dir / "split"
      writeFile(splitSource, splitSrc)
      checkClose(compileRun(splitSource, splitExe, dir).splitWhitespace.map(parseFloat),
                 if flag: cx else: cy)

    # Struct form: Rep[Complex] with +/* and a direct conditional.
    let sx = structCplx(xre, xim)
    let sy = structCplx(yre, yim)
    let structAdd = caddS(sx, sy)
    let structMul = cmulS(sx, sy)
    let structIf = cplxIfS(test, sx, sy)
    doAssert not structAdd.isStatic and not structMul.isStatic
    # Field projection of a static struct returns the stored field.
    doAssert reOf(structCplx(liftNow(1.0), liftNow(2.0))).isStatic
    doAssert imOf(structCplx(liftNow(1.0), liftNow(2.0))).staticVal == 2.0
    let structSrc = "type Complex = object\n  re, im: float\n" &
      "let xre = " & $cx.re & "\nlet xim = " & $cx.im & "\n" &
      "let yre = " & $cy.re & "\nlet yim = " & $cy.im & "\n" &
      "let addOut = " & emitCplx(structAdd) & "\n" &
      "let mulOut = " & emitCplx(structMul) & "\n" &
      "echo addOut.re, \" \", addOut.im\n" &
      "echo mulOut.re, \" \", mulOut.im\n"
    let structSource = dir / "struct.nim"
    let structExe = dir / "struct"
    writeFile(structSource, structSrc)
    let structLines = compileRun(structSource, structExe, dir).splitLines
    checkClose(structLines[0].splitWhitespace.map(parseFloat), directAdd)
    checkClose(structLines[1].splitWhitespace.map(parseFloat), directMul)
    for flag in [true, false]:
      let ifSrc = "type Complex = object\n  re, im: float\n" &
        "let xre = " & $cx.re & "\nlet xim = " & $cx.im & "\n" &
        "let yre = " & $cy.re & "\nlet yim = " & $cy.im & "\n" &
        "let test = " & $flag & "\n" &
        "let outC = " & emitCplx(structIf) & "\n" &
        "echo outC.re, \" \", outC.im\n"
      let ifSource = dir / "structif.nim"
      let ifExe = dir / "structif"
      writeFile(ifSource, ifSrc)
      checkClose(compileRun(ifSource, ifExe, dir).splitWhitespace.map(parseFloat),
                 if flag: cx else: cy)
    # Projecting through the conditional selects per branch too.
    for flag in [true, false]:
      let projSrc = "type Complex = object\n  re, im: float\n" &
        "let xre = " & $cx.re & "\nlet xim = " & $cx.im & "\n" &
        "let yre = " & $cy.re & "\nlet yim = " & $cy.im & "\n" &
        "let test = " & $flag & "\n" &
        "let outRe = " & emitFloat(reOf(structIf)) & "\n" &
        "let outIm = " & emitFloat(imOf(structIf)) & "\n" &
        "echo outRe, \" \", outIm\n"
      let projSource = dir / "structproj.nim"
      let projExe = dir / "structproj"
      writeFile(projSource, projSrc)
      checkClose(compileRun(projSource, projExe, dir).splitWhitespace.map(parseFloat),
                 if flag: cx else: cy)
  removeDir(dir)
  echo "ok: staged Complex numbers"
