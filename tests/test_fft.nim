import staging/framework
import staging/structs
import staging/arrays
import std/[math, os, osproc, sequtils, strutils, times]

type
  Complex = Prod2[float, float]
  K = enum kInput, kRead, kWrite, kAdd, kSub, kMul, kCos, kSin
  N = ref object of IRNode
    kind: K
    name: string
    left, right: Rep[float]
    a, b: Rep[Unit]
    arr: Arr[float]
    index: Rep[int]
    value: Rep[float]

proc rawSub(a, b: Rep[float]): Rep[float] =
  dynamic[float](N(kind: kSub, left: a, right: b))

proc addR(a, b: Rep[float]): Rep[float]
proc subR(a, b: Rep[float]): Rep[float]

proc addR(a, b: Rep[float]): Rep[float] =
  # ArithExpOptFFT: x + (0 - y) -> x - y.
  if not a.isStatic and not b.isStatic:
    let right = N(b.node)
    if right.kind == kSub and right.left.isStatic and right.left.staticVal == 0.0:
      return subR(a, right.right)
  smartOp[float](a, b,
    proc(x, y: float): float = x + y,
    proc(x, y: Rep[float]): IRNode = N(kind: kAdd, left: x, right: y))

proc subR(a, b: Rep[float]): Rep[float] =
  # ArithExpOptFFT: x - (0 - y) -> x + y.
  if not a.isStatic and not b.isStatic:
    let right = N(b.node)
    if right.kind == kSub and right.left.isStatic and right.left.staticVal == 0.0:
      return addR(a, right.right)
  smartOp[float](a, b,
    proc(x, y: float): float = x - y,
    proc(x, y: Rep[float]): IRNode = N(kind: kSub, left: x, right: y))

proc mulR(a, b: Rep[float]): Rep[float] =
  # ArithExpOptFFT: x * -1 -> 0 - x (both operand orders).
  if not a.isStatic and b.isStatic and b.staticVal == -1.0:
    return rawSub(liftNow(0.0), a)
  if a.isStatic and a.staticVal == -1.0 and not b.isStatic:
    return rawSub(liftNow(0.0), b)
  smartOp[float](a, b,
    proc(x, y: float): float = x * y,
    proc(x, y: Rep[float]): IRNode = N(kind: kMul, left: x, right: y))

proc cosR(x: Rep[float]): Rep[float] =
  # TrigExpOptFFT: cos of a half-integer multiple of pi is exactly zero.
  smartOpUni[float](x,
    proc(v: float): float =
      let q = 2.0 * v / PI
      if abs(q - round(q)) < 1e-12 and (int(round(q)) mod 2) != 0: 0.0 else: cos(v),
    proc(v: Rep[float]): IRNode = N(kind: kCos, left: v))

proc sinR(x: Rep[float]): Rep[float] =
  smartOpUni[float](x,
    proc(v: float): float = sin(v),
    proc(v: Rep[float]): IRNode = N(kind: kSin, left: v))

proc cadd(a, b: Complex): Complex = mapProd2(a, b, addR, addR)
proc csub(a, b: Complex): Complex = mapProd2(a, b, subR, subR)
proc cmul(a, b: Complex): Complex =
  prod2(subR(mulR(a.fst, b.fst), mulR(a.snd, b.snd)),
        addR(mulR(a.fst, b.snd), mulR(a.snd, b.fst)))

proc omega(k, n: int): Complex =
  let angle = -2.0 * PI * float(k) / float(n)
  prod2(cosR(liftNow(angle)), sinR(liftNow(angle)))

proc butterfly(x, y: Complex, k, n: int): (Complex, Complex) =
  let z = cmul(omega(k, n), y)
  (cadd(x, z), csub(x, z))

proc fft(xs: seq[Complex]): seq[Complex] =
  if xs.len == 1: return xs
  let half = xs.len div 2
  var even, odd: seq[Complex]
  for i in 0 ..< half:
    even.add(xs[2 * i]); odd.add(xs[2 * i + 1])
  let left = fft(even)
  let right = fft(odd)
  # Each butterfly is staged once; its two outputs go to the two halves.
  var first, second: seq[Complex]
  for k in 0 ..< half:
    let pair = butterfly(left[k], right[k], k, xs.len)
    first.add(pair[0])
    second.add(pair[1])
  result = first & second

proc rf(a: Arr[float], i: Rep[int]): Rep[float] = readArr[float](a, i,
  proc(x: Arr[float], j: Rep[int]): IRNode = N(kind: kRead, arr: x, index: j))
proc wf(a: Arr[float], i: Rep[int], v: Rep[float]): Rep[Unit] = writeArr[float](a, i, v,
  proc(x: Arr[float], j: Rep[int], value: Rep[float]): IRNode =
    N(kind: kWrite, arr: x, index: j, value: value))
# The fixed-size codelet shape: a dynamic flat input and a residual output array.
proc FFTC(input: Arr[float], n: int): tuple[body: Rep[Unit], output: Arr[float]] =
  let output = newArray[float](liftNow(n), proc(x: Rep[int]): IRNode =
    N(kind: kInput, name: "output"))
  var values: seq[Complex]
  for i in 0 ..< n div 2:
    values.add(prod2(rf(input, liftNow(2 * i)), rf(input, liftNow(2 * i + 1))))
  let transformed = fft(values)
  var body: Rep[Unit]
  for i, c in transformed:
    let pair = seqR(wf(output, liftNow(2 * i), c.fst),
                    wf(output, liftNow(2 * i + 1), c.snd),
                    proc(x, y: Rep[Unit]): IRNode = N(kind: kWrite, a: x, b: y))
    body = if body.isNil: pair else: seqR(body, pair,
      proc(x, y: Rep[Unit]): IRNode = N(kind: kWrite, a: x, b: y))
  (body, output)

proc ei(x: Rep[int]): string = $x.staticVal
proc ef(x: Rep[float]): string =
  if x.isStatic: return $x.staticVal
  let n = N(x.node)
  case n.kind
  of kRead: N(n.arr.node).name & "[" & ei(n.index) & "]"
  of kAdd: "(" & ef(n.left) & " + " & ef(n.right) & ")"
  of kSub: "(" & ef(n.left) & " - " & ef(n.right) & ")"
  of kMul: "(" & ef(n.left) & " * " & ef(n.right) & ")"
  of kCos: "cos(" & ef(n.left) & ")"
  of kSin: "sin(" & ef(n.left) & ")"
  else: raise newException(ValueError, "bad float node")
proc es(x: Rep[Unit]): string =
  if x.isNil or x.isStatic: return "discard"
  let n = N(x.node)
  if n.a != nil and n.b != nil:
    return es(n.a) & "\n" & es(n.b)
  N(n.arr.node).name & "[" & ei(n.index) & "] = " & ef(n.value)

proc compileRun(source, exe, dir: string): string =
  let r = execCmdEx(quoteShell(findExe("nim")) & " c --hints:off --nimcache:" &
    quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(source),
    {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  let q = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert q.exitCode == 0, q.output
  q.output.strip

proc direct(a: seq[float]): seq[float] =
  let n = a.len div 2
  result = newSeq[float](a.len)
  for k in 0 ..< n:
    var re, im = 0.0
    for j in 0 ..< n:
      let angle = -2.0 * PI * float(k * j) / float(n)
      re += a[2 * j] * cos(angle) - a[2 * j + 1] * sin(angle)
      im += a[2 * j] * sin(angle) + a[2 * j + 1] * cos(angle)
    result[2 * k] = re; result[2 * k + 1] = im

when isMainModule:
  let input = Arr[float](node: N(kind: kInput, name: "input"))
  # The x * -1 -> 0 - x rewrite with the static -1 on the right (the order
  # cmul's twiddle products never exercise): must rewrite, not emit * -1.0.
  let negated = ef(mulR(rf(input, liftNow(0)), liftNow(-1.0)))
  doAssert negated == "(0.0 - input[0])", negated
  let p = FFTC(input, 8)
  let text = es(p.body)
  doAssert "* -1.0" notin text and "*-1.0" notin text and "-1.0 *" notin text
  doAssert "cos(" notin text and "sin(" notin text
  let dir = getTempDir() / ("staging-fft-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(dir)
  for a in [@[1.0, 0.0, 1.0, 0.0, 2.0, 0.0, 2.0, 0.0],
            @[1.0, 0.5, -2.0, 1.0, 3.0, -1.0, 0.25, 2.0, -1.0, 0.0, 2.0, 1.5, 4.0, -0.5, -3.0, 2.0]]:
    let n = a.len
    let code = FFTC(input, n)
    let residual = es(code.body)
    doAssert "cos(" notin residual and "sin(" notin residual
    let source = dir / ("residual" & $n & ".nim")
    let vals = a.mapIt($it).join(", ")
    var src = "var input = @[" & vals & "]\nvar output = newSeq[float](input.len)\n" & residual & "\n"
    for i in 0 ..< a.len: src.add("echo output[" & $i & "]\n")
    writeFile(source, src)
    let got = compileRun(source, dir / ("residual" & $n), dir).splitWhitespace.map(parseFloat)
    let want = direct(a)
    if n == 8:
      let expected = @[6.0, 0.0, -1.0, 1.0, 0.0, 0.0, -1.0, -1.0]
      for i in 0 ..< expected.len: doAssert abs(got[i] - expected[i]) < 1e-8
    for i in 0 ..< a.len: doAssert abs(got[i] - want[i]) < 1e-8, $i & " got=" & $got[i] & " want=" & $want[i]
  removeDir(dir)
  echo "ok: staged FFT over Complex arrays"
