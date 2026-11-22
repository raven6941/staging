import staging/framework
import staging/structs
import std/[math, os, osproc, sequtils, strutils, times]

type
  Complex = Prod2[float, float]
  DirectComplex = object
    re, im: float
  ComplexNodeKind = enum cnInput, cnAdd, cnSub, cnMul
  ComplexNode = ref object of IRNode
    kind: ComplexNodeKind
    left, right: Rep[float]
    name: string

proc addR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x + y,
  proc(x, y: Rep[float]): IRNode = ComplexNode(kind: cnAdd, left: x, right: y))

proc subR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x - y,
  proc(x, y: Rep[float]): IRNode = ComplexNode(kind: cnSub, left: x, right: y))

proc mulR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x * y,
  proc(x, y: Rep[float]): IRNode = ComplexNode(kind: cnMul, left: x, right: y))

proc cadd(a, b: Complex): Complex = mapProd2(a, b, addR, addR)
proc csub(a, b: Complex): Complex = mapProd2(a, b, subR, subR)

proc cmul(a, b: Complex): Complex =
  ## The port's Complex multiplication: (ar*br-ai*bi, ar*bi+ai*br).
  prod2(subR(mulR(a.fst, b.fst), mulR(a.snd, b.snd)),
        addR(mulR(a.fst, b.snd), mulR(a.snd, b.fst)))

proc omega(k, n: int): Complex =
  ## The port's twiddle: angle -2*pi*k/N, fields static (k, n staging-time-known).
  let angle = -2.0 * PI * float(k) / float(n)
  prod2(liftNow(cos(angle)), liftNow(sin(angle)))

proc butterfly(x, y: Complex, k, n: int): (Complex, Complex) =
  let z = cmul(omega(k, n), y)
  (cadd(x, z), csub(x, z))

proc directButterfly(x, y: DirectComplex, k, n: int): (DirectComplex, DirectComplex) =
  let angle = -2.0 * PI * float(k) / float(n)
  let wr = cos(angle); let wi = sin(angle)
  let z = DirectComplex(re: wr * y.re - wi * y.im,
                        im: wr * y.im + wi * y.re)
  (DirectComplex(re: x.re + z.re, im: x.im + z.im),
   DirectComplex(re: x.re - z.re, im: x.im - z.im))

proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let node = ComplexNode(r.node)
  case node.kind
  of cnInput: node.name
  of cnAdd: "(" & emitFloat(node.left) & " + " & emitFloat(node.right) & ")"
  of cnSub: "(" & emitFloat(node.left) & " - " & emitFloat(node.right) & ")"
  of cnMul: "(" & emitFloat(node.left) & " * " & emitFloat(node.right) & ")"

proc emitComplex(c: Complex): string =
  "Complex(re: " & emitFloat(c.fst) & ", im: " & emitFloat(c.snd) & ")"

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let built = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert built.exitCode == 0, built.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

when isMainModule:
  let xre = dynamic[float](ComplexNode(kind: cnInput, name: "xre"))
  let xim = dynamic[float](ComplexNode(kind: cnInput, name: "xim"))
  let yre = dynamic[float](ComplexNode(kind: cnInput, name: "yre"))
  let yim = dynamic[float](ComplexNode(kind: cnInput, name: "yim"))
  let x = prod2(xre, xim)
  let y = prod2(yre, yim)
  let staged = butterfly(x, y, 1, 4)
  let w = omega(1, 4)
  doAssert w.fst.isStatic and w.snd.isStatic
  doAssert not staged[0].fst.isStatic and not staged[0].snd.isStatic
  doAssert not staged[1].fst.isStatic and not staged[1].snd.isStatic
  doAssert x.fst.node == xre.node
  doAssert x.fst.node == prod2(x.fst, x.snd).fst.node
  let emitted = emitComplex(staged[0])
  doAssert emitted.contains("Complex(re:")

  let staticResult = butterfly(prod2(liftNow(1.0), liftNow(2.0)),
                               prod2(liftNow(3.0), liftNow(4.0)), 2, 8)
  doAssert staticResult[0].fst.isStatic and staticResult[0].snd.isStatic
  doAssert staticResult[1].fst.isStatic and staticResult[1].snd.isStatic

  type Case = tuple[x, y: array[2, float], k, n: int]
  let cases: array[3, Case] = [
    ([1.0, 2.0], [3.0, -1.0], 1, 4),
    ([-2.5, 0.75], [1.25, 3.5], 2, 8),
    ([4.0, -3.0], [-0.5, 2.0], 3, 16)]
  let dir = getTempDir() / ("staging-structs-" & $getCurrentProcessId() & "-" &
    $int(epochTime() * 1000))
  createDir(dir)
  for c in cases:
    let caseX = prod2(xre, xim)
    let caseY = prod2(yre, yim)
    let caseStaged = butterfly(caseX, caseY, c.k, c.n)
    let direct = directButterfly(DirectComplex(re: c.x[0], im: c.x[1]),
                                 DirectComplex(re: c.y[0], im: c.y[1]), c.k, c.n)
    let source = dir / "residual.nim"
    let exe = dir / "residual"
    let src = "type Complex = object\n  re, im: float\n" &
      "let xre = " & $c.x[0] & "\nlet xim = " & $c.x[1] & "\n" &
      "let yre = " & $c.y[0] & "\nlet yim = " & $c.y[1] & "\n" &
      "let out0 = " & emitComplex(caseStaged[0]) & "\n" &
      "let out1 = " & emitComplex(caseStaged[1]) & "\n" &
      "echo out0.re, \" \", out0.im, \" \", out1.re, \" \", out1.im\n"
    writeFile(source, src)
    let got = compileRun(source, exe, dir).splitWhitespace.map(parseFloat)
    doAssert abs(got[0] - direct[0].re) < 1e-9
    doAssert abs(got[1] - direct[0].im) < 1e-9
    doAssert abs(got[2] - direct[1].re) < 1e-9
    doAssert abs(got[3] - direct[1].im) < 1e-9
  removeDir(dir)
  echo "ok: pure product FFT butterfly"
