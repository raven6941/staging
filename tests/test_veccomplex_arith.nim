## Vector[Complex] arithmetic over the mixed Cartesian/Polar SoA.

import test_soa_mixed
import std/[math, os, osproc, sequtils, strutils, times]

proc compileRun(source, exe, dir: string): string =
  let nim = findExe("nim")
  let built = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " &
    quoteShell(source), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert built.exitCode == 0, built.output
  let run = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert run.exitCode == 0, run.output
  run.output.strip

proc cartesian(x: Complex): Complex =
  if x.clzz == ctCartesian: x
  else: Complex(re: x.r * cos(x.theta), im: x.r * sin(x.theta),
    r: 0.0, theta: 0.0, clzz: ctCartesian)
proc directAdd(a, b: Complex): Complex =
  let x = cartesian(a); let y = cartesian(b)
  Complex(re: x.re + y.re, im: x.im + y.im, r: 0.0, theta: 0.0, clzz: ctCartesian)
proc directScale(s: float, a: Complex): Complex =
  let x = cartesian(a)
  Complex(re: s * x.re, im: s * x.im, r: 0.0, theta: 0.0, clzz: ctCartesian)

proc checkOutput(got: seq[float], expected: seq[Complex]) =
  doAssert got.len == expected.len * 2
  for i, x in expected:
    doAssert abs(got[2 * i] - x.re) < 1e-8
    doAssert abs(got[2 * i + 1] - x.im) < 1e-8

proc makeVector(prefix: string, values: seq[Complex]): VectorComplex =
  var re, im, radius, theta: seq[float]
  var tags: seq[ClassTag]
  for x in values:
    re.add(x.re); im.add(x.im); radius.add(x.r); theta.add(x.theta); tags.add(x.clzz)
  mixedVector(inputF(prefix & "Re", re), inputF(prefix & "Im", im),
    inputF(prefix & "R", radius), inputF(prefix & "Theta", theta),
    inputTag(prefix & "Tag", tags))

when isMainModule:
  let dir = getTempDir() / ("staging-veccomplex-arith-" & $getCurrentProcessId() &
    "-" & $int(epochTime() * 1000))
  createDir(dir)

  let cartA = @[Complex(re: 1.0, im: -2.0, clzz: ctCartesian),
                 Complex(re: 3.5, im: 4.0, clzz: ctCartesian)]
  let cartB = @[Complex(re: -0.5, im: 2.25, clzz: ctCartesian),
                 Complex(re: 1.5, im: -1.0, clzz: ctCartesian)]
  let cartText = emitArithmeticProgram(makeVector("cartA", cartA), makeVector("cartB", cartB), 0.0, true)
  # Cartesian-only add is specialized before emission: r/theta/tag are dead.
  doAssert "var cartAR =" notin cartText and "var cartATheta =" notin cartText
  doAssert "var cartATag =" notin cartText and "var cartBR =" notin cartText
  let cartSource = dir / "cart.nim"
  writeFile(cartSource, cartText)
  checkOutput(compileRun(cartSource, dir / "cart", dir).splitWhitespace.map(parseFloat),
    zip(cartA, cartB).mapIt(directAdd(it[0], it[1])))

  let polarA = @[Complex(r: 2.0, theta: 0.5, clzz: ctPolar),
                  Complex(r: 1.25, theta: -0.75, clzz: ctPolar)]
  let polarB = @[Complex(r: 0.75, theta: -0.25, clzz: ctPolar),
                  Complex(r: 2.5, theta: 0.2, clzz: ctPolar)]
  let polarText = emitArithmeticProgram(makeVector("polarA", polarA), makeVector("polarB", polarB), 0.0, true)
  let polarSource = dir / "polar.nim"
  writeFile(polarSource, polarText)
  checkOutput(compileRun(polarSource, dir / "polar", dir).splitWhitespace.map(parseFloat),
    zip(polarA, polarB).mapIt(directAdd(it[0], it[1])))

  let mixedA = @[Complex(re: 1.0, im: -2.0, clzz: ctCartesian),
                  Complex(r: 2.0, theta: 0.5, clzz: ctPolar),
                  Complex(re: 3.5, im: 4.0, clzz: ctCartesian),
                  Complex(r: 1.25, theta: -0.75, clzz: ctPolar)]
  let mixedB = @[Complex(r: 0.75, theta: -0.25, clzz: ctPolar),
                  Complex(re: -1.5, im: 0.5, clzz: ctCartesian),
                  Complex(r: 2.5, theta: 0.2, clzz: ctPolar),
                  Complex(re: 0.25, im: -1.0, clzz: ctCartesian)]
  let mixedText = emitArithmeticProgram(makeVector("mixedA", mixedA), makeVector("mixedB", mixedB), 0.0, true)
  doAssert "var mixedAR =" in mixedText and "var mixedATheta =" in mixedText and "var mixedATag =" in mixedText
  let mixedSource = dir / "mixed.nim"
  writeFile(mixedSource, mixedText)
  checkOutput(compileRun(mixedSource, dir / "mixed", dir).splitWhitespace.map(parseFloat),
    zip(mixedA, mixedB).mapIt(directAdd(it[0], it[1])))

  let scalar = 2.25
  let scalarText = emitArithmeticProgram(makeVector("scale", mixedA), makeVector("unused", mixedA), scalar, false)
  doAssert "var scaleR =" in scalarText and "var scaleTag =" in scalarText
  doAssert "unusedRe" notin scalarText
  let scalarSource = dir / "scalar.nim"
  writeFile(scalarSource, scalarText)
  checkOutput(compileRun(scalarSource, dir / "scalar", dir).splitWhitespace.map(parseFloat),
    mixedA.mapIt(directScale(scalar, it)))

  removeDir(dir)
  echo "ok: Vector[Complex] arithmetic over mixed SoA"
