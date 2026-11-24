## Staged tagged unions over the structs vocabulary.

import staging/framework
import staging/structs
import std/[math, os, osproc, sequtils, strutils, times]

type
  ClassTag = enum ctCartesian, ctPolar
  Complex = object
    re, im, r, phi: Rep[float]
    clzz: Rep[ClassTag]
  DirectComplex = object
    re, im: float
  UnionKind = enum ukInput, ukBoolInput, ukAdd, ukMul, ukSub, ukIfF,
    ukStruct, ukRe, ukIm, ukR, ukPhi, ukClzz, ukIfTag, ukCos, ukSin, ukDispatch
  UnionNode = ref object of IRNode
    kind: UnionKind
    name: string
    left, right: Rep[float]
    cond: Rep[bool]
    thenF, elseF: Rep[float]
    re, im, r, phi: Rep[float]
    clzz: Rep[ClassTag]
    thenTag, elseTag: Rep[ClassTag]
    cplx, thenC, elseC: Rep[Complex]

proc addR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x + y,
  proc(x, y: Rep[float]): IRNode = UnionNode(kind: ukAdd, left: x, right: y))
proc mulR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x * y,
  proc(x, y: Rep[float]): IRNode = UnionNode(kind: ukMul, left: x, right: y))
proc subR(a, b: Rep[float]): Rep[float] = smartOp[float](a, b,
  proc(x, y: float): float = x - y,
  proc(x, y: Rep[float]): IRNode = UnionNode(kind: ukSub, left: x, right: y))

proc structC(re, im, r, phi: Rep[float], tag: Rep[ClassTag]): Rep[Complex] =
  let fields = prod2(re, im)
  if re.isStatic and im.isStatic and r.isStatic and phi.isStatic and tag.isStatic:
    liftNow(Complex(re: fields.fst, im: fields.snd, r: r, phi: phi, clzz: tag))
  else:
    dynamic[Complex](UnionNode(kind: ukStruct, re: re, im: im, r: r,
      phi: phi, clzz: tag))

proc cartesian(re, im: Rep[float]): Rep[Complex] =
  structC(re, im, liftNow(0.0), liftNow(0.0), liftNow(ctCartesian))
proc polar(r, phi: Rep[float]): Rep[Complex] =
  structC(liftNow(0.0), liftNow(0.0), r, phi, liftNow(ctPolar))

proc reOf(c: Rep[Complex]): Rep[float] =
  if c.isStatic: c.staticVal.re else: dynamic[float](UnionNode(kind: ukRe, cplx: c))
proc imOf(c: Rep[Complex]): Rep[float] =
  if c.isStatic: c.staticVal.im else: dynamic[float](UnionNode(kind: ukIm, cplx: c))
proc rOf(c: Rep[Complex]): Rep[float] =
  if c.isStatic: c.staticVal.r else: dynamic[float](UnionNode(kind: ukR, cplx: c))
proc phiOf(c: Rep[Complex]): Rep[float] =
  if c.isStatic: c.staticVal.phi else: dynamic[float](UnionNode(kind: ukPhi, cplx: c))
proc tagOf(c: Rep[Complex]): Rep[ClassTag] =
  if c.isStatic: c.staticVal.clzz
  else:
    let n = UnionNode(c.node)
    if n.kind == ukStruct and n.clzz.isStatic: n.clzz
    else: dynamic[ClassTag](UnionNode(kind: ukClzz, cplx: c))

proc unionIf(test: Rep[bool], a, b: Rep[Complex]): Rep[Complex] =
  let re = smartIf[float](test, proc(): Rep[float] = reOf(a), proc(): Rep[float] = reOf(b),
    proc(c: Rep[bool], t, e: Rep[float]): IRNode = UnionNode(kind: ukIfF, cond: c, thenF: t, elseF: e))
  let im = smartIf[float](test, proc(): Rep[float] = imOf(a), proc(): Rep[float] = imOf(b),
    proc(c: Rep[bool], t, e: Rep[float]): IRNode = UnionNode(kind: ukIfF, cond: c, thenF: t, elseF: e))
  let r = smartIf[float](test, proc(): Rep[float] = rOf(a), proc(): Rep[float] = rOf(b),
    proc(c: Rep[bool], t, e: Rep[float]): IRNode = UnionNode(kind: ukIfF, cond: c, thenF: t, elseF: e))
  let phi = smartIf[float](test, proc(): Rep[float] = phiOf(a), proc(): Rep[float] = phiOf(b),
    proc(c: Rep[bool], t, e: Rep[float]): IRNode = UnionNode(kind: ukIfF, cond: c, thenF: t, elseF: e))
  let tag = smartIf[ClassTag](test, proc(): Rep[ClassTag] = tagOf(a), proc(): Rep[ClassTag] = tagOf(b),
    proc(c: Rep[bool], t, e: Rep[ClassTag]): IRNode = UnionNode(kind: ukIfTag, cond: c, thenTag: t, elseTag: e))
  structC(re, im, r, phi, tag)

proc toCartesian(c: Rep[Complex]): Rep[Complex] =
  if tagOf(c).isStatic:
    if tagOf(c).staticVal == ctCartesian: c
    else: cartesian(mulR(rOf(c), smartOpUni[float](phiOf(c), cos,
      proc(x: Rep[float]): IRNode = UnionNode(kind: ukCos, left: x))),
      mulR(rOf(c), smartOpUni[float](phiOf(c), sin,
        proc(x: Rep[float]): IRNode = UnionNode(kind: ukSin, left: x))))
  else:
    dynamic[Complex](UnionNode(kind: ukDispatch, cplx: c))

proc emitCplx(r: Rep[Complex]): string
proc emitBool(r: Rep[bool]): string =
  if r.isStatic: $r.staticVal else: UnionNode(r.node).name
proc emitFloat(r: Rep[float]): string
proc emitTag(r: Rep[ClassTag]): string =
  if r.isStatic: (if r.staticVal == ctCartesian: "ctCartesian" else: "ctPolar")
  else:
    let n = UnionNode(r.node)
    case n.kind
    of ukClzz: emitCplx(n.cplx) & ".clzz"
    of ukIfTag: "(if " & emitBool(n.cond) & ": " & emitTag(n.thenTag) & " else: " & emitTag(n.elseTag) & ")"
    else: raise newException(ValueError, "bad tag node")
proc emitCplx(r: Rep[Complex]): string =
  if r.isStatic:
    return "Complex(re: " & emitFloat(r.staticVal.re) & ", im: " & emitFloat(r.staticVal.im) &
      ", r: " & emitFloat(r.staticVal.r) & ", phi: " & emitFloat(r.staticVal.phi) & ")"
  let n = UnionNode(r.node)
  case n.kind
  of ukStruct:
    var s = "Complex(re: " & emitFloat(n.re) & ", im: " & emitFloat(n.im) &
      ", r: " & emitFloat(n.r) & ", phi: " & emitFloat(n.phi)
    if not n.clzz.isStatic: s &= ", clzz: " & emitTag(n.clzz)
    s & ")"
  of ukDispatch:
    "(if " & emitTag(tagOf(n.cplx)) &
      " == ctCartesian: " & emitCplx(n.cplx) & " else: " &
      emitCplx(cartesian(mulR(rOf(n.cplx), smartOpUni[float](phiOf(n.cplx), cos,
        proc(x: Rep[float]): IRNode = UnionNode(kind: ukCos, left: x))),
        mulR(rOf(n.cplx), smartOpUni[float](phiOf(n.cplx), sin,
          proc(x: Rep[float]): IRNode = UnionNode(kind: ukSin, left: x))))) & ")"
  else: raise newException(ValueError, "bad complex node")
proc emitFloat(r: Rep[float]): string =
  if r.isStatic: return $r.staticVal
  let n = UnionNode(r.node)
  case n.kind
  of ukInput: n.name
  of ukAdd: "(" & emitFloat(n.left) & " + " & emitFloat(n.right) & ")"
  of ukSub: "(" & emitFloat(n.left) & " - " & emitFloat(n.right) & ")"
  of ukMul: "(" & emitFloat(n.left) & " * " & emitFloat(n.right) & ")"
  of ukCos: "cos(" & emitFloat(n.left) & ")"
  of ukSin: "sin(" & emitFloat(n.left) & ")"
  of ukIfF: "(if " & emitBool(n.cond) & ": " & emitFloat(n.thenF) & " else: " & emitFloat(n.elseF) & ")"
  of ukRe: emitCplx(n.cplx) & ".re"
  of ukIm: emitCplx(n.cplx) & ".im"
  of ukR: emitCplx(n.cplx) & ".r"
  of ukPhi: emitCplx(n.cplx) & ".phi"
  else: raise newException(ValueError, "bad float node")

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let b = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") &
    " --out:" & quoteShell(exe) & " " & quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert b.exitCode == 0, b.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

proc check(got: seq[float], want: DirectComplex) =
  doAssert got.len == 2
  doAssert abs(got[0] - want.re) < 1e-8, $got
  doAssert abs(got[1] - want.im) < 1e-8, $got

when isMainModule:
  let xr = dynamic[float](UnionNode(kind: ukInput, name: "xr"))
  let xi = dynamic[float](UnionNode(kind: ukInput, name: "xi"))
  let pr = dynamic[float](UnionNode(kind: ukInput, name: "pr"))
  let pp = dynamic[float](UnionNode(kind: ukInput, name: "pp"))
  let test = dynamic[bool](UnionNode(kind: ukBoolInput, name: "test"))
  let c = cartesian(xr, xi)
  let p = polar(pr, pp)
  let dir = getTempDir() / ("staging-union-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  let typePlain = "import std/math\n\ntype Complex = object\n  re, im, r, phi: float\n"
  let typeTagged = "type ClassTag = enum ctCartesian, ctPolar\n" & typePlain & "  clzz: ClassTag\n"
  for vals in [(1.0, -2.0, 0.0, 0.0), (0.0, -2.5, 2.0, 0.5)]:
    let expectedC = DirectComplex(re: vals[0], im: vals[1])
    let expectedP = DirectComplex(re: vals[2] * cos(vals[3]), im: vals[2] * sin(vals[3]))
    let programs = [toCartesian(c), toCartesian(p)]
    for i, program in programs:
      let src = (if i == 0: typePlain else: typeTagged) & "let xr = " & $vals[0] & "\nlet xi = " & $vals[1] &
        "\nlet pr = " & $vals[2] & "\nlet pp = " & $vals[3] & "\nlet resultC = " & emitCplx(program) &
        "\necho resultC.re, \" \", resultC.im\n"
      let f = dir / ("dispatch" & $i & ".nim"); writeFile(f, src)
      check(compileRun(f, dir / ("dispatch" & $i), dir).splitWhitespace.map(parseFloat), if i == 0: expectedC else: expectedP)
    let split = unionIf(test, c, p)
    for flag in [true, false]:
      let result = toCartesian(split)
      let src = typeTagged & "let xr = " & $vals[0] & "\nlet xi = " & $vals[1] & "\nlet pr = " & $vals[2] &
        "\nlet pp = " & $vals[3] & "\nlet test = " & $flag & "\nlet resultC = " & emitCplx(result) & "\necho resultC.re, \" \", resultC.im\n"
      let f = dir / ("branch" & $flag & ".nim"); writeFile(f, src)
      check(compileRun(f, dir / ("branch" & $flag), dir).splitWhitespace.map(parseFloat), if flag: expectedC else: expectedP)
  doAssert "clzz" notin emitCplx(toCartesian(c))
  doAssert "clzz" notin emitCplx(c)
  removeDir(dir)
  echo "ok: staged tagged union Complex"
