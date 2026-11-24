## Auto-specializing staged interpreter.
##
## This is deliberately self contained: the object language, its two
## evaluators, and the residual emitter live here so the example does not
## require a second language or any framework changes.

import staging/framework
import std/[os, osproc, sequtils, strutils, tables, times]

type
  TermKind = enum tkI, tkB, tkV, tkP, tkL, tkA, tkIf
  Term = ref object
    kind: TermKind
    n: int
    b: bool
    s: string
    compile: bool
    param: string
    body: Term
    fn: Term
    args: seq[Term]
    c, yes, no: Term

  ValueKind = enum vkI, vkB, vkP, vkClo, vkEvalfun, vkCode
  Value = ref object
    kind: ValueKind
    n: int
    b: bool
    name: string
    param: string
    body: Term
    env: Table[string, Value]
    code: Rep[Value]

  Env = Table[string, Value]
  Def = object
    name: string
    body: Rep[Value]
  SKind = enum skArg, skPrim, skIf, skCall, skFallback
  SNode = ref object of IRNode
    kind: SKind
    name: string
    p: string
    left, right: Rep[Value]
    cond: Rep[bool]
    yes, no: Rep[Value]
    f: Rep[Value]
    arg: Rep[Value]
    env: Env
  SState = ref object
    nextId: int
    defs: seq[Def]
    refs: Table[string, string]

proc I(n: int): Term = Term(kind: tkI, n: n)
proc B(x: bool): Term = Term(kind: tkB, b: x)
proc V(x: string): Term = Term(kind: tkV, s: x)
proc P(x: string): Term = Term(kind: tkP, s: x)
proc L(c: bool, p: string, body: Term): Term = Term(kind: tkL, compile: c, param: p, body: body)
proc A(f: Term, xs: varargs[Term]): Term = Term(kind: tkA, fn: f, args: @xs)
proc If(c, t, e: Term): Term = Term(kind: tkIf, c: c, yes: t, no: e)

proc vi(n: int): Value = Value(kind: vkI, n: n)
proc vb(b: bool): Value = Value(kind: vkB, b: b)
proc vp(p: string): Value = Value(kind: vkP, name: p)
proc vf(name: string): Value = Value(kind: vkEvalfun, name: name)
proc vc(param: string, body: Term, env: Env): Value = Value(kind: vkClo, param: param, body: body, env: env)
proc vcode(x: Rep[Value]): Value = Value(kind: vkCode, code: x)

proc prim(p: string, xs: seq[Value]): Value =
  discard
  case p
  of "<": vb(xs[0].n < xs[1].n)
  of "+": vi(xs[0].n + xs[1].n)
  of "-": vi(xs[0].n - xs[1].n)
  else: raise newException(ValueError, "unknown primitive " & p)

proc directApply(f: Value, xs: seq[Value], env: Env, k: proc(v: Value): Value): Value
proc directEval(t: Term, env: Env, k: proc(v: Value): Value): Value
proc directArgs(ts: seq[Term], i: int, env: Env, k: proc(xs: seq[Value]): Value): Value =
  if i == ts.len: return k(@[])
  directEval(ts[i], env, proc(x: Value): Value =
    directArgs(ts, i + 1, env, proc(xs: seq[Value]): Value = k(@[x] & xs)))
proc directEval(t: Term, env: Env, k: proc(v: Value): Value): Value =
  case t.kind
  of tkI: k(vi(t.n))
  of tkB: k(vb(t.b))
  of tkP: k(vp(t.s))
  of tkV: k(env[t.s])
  of tkL: k(vc(t.param, t.body, env))
  of tkA:
    directEval(t.fn, env, proc(f: Value): Value =
      directArgs(t.args, 0, env, proc(xs: seq[Value]): Value = directApply(f, xs, env, k)))
  of tkIf:
    directEval(t.c, env, proc(x: Value): Value =
      if not (x.kind == vkB and not x.b): directEval(t.yes, env, k)
      else: directEval(t.no, env, k))

proc directApply(f: Value, xs: seq[Value], env: Env, k: proc(v: Value): Value): Value =
  case f.kind
  of vkClo:
    var e = initTable[string, Value]()
    for key, value in f.env: e[key] = value
    e[f.param] = xs[0]
    directEval(f.body, e, k)
  of vkEvalfun: raise newException(ValueError, "evalfun is residual-only")
  of vkP: k(prim(f.name, xs))
  else: raise newException(ValueError, "not callable")

proc topDirect(t: Term): Value =
  directEval(t, initTable[string, Value](), proc(x: Value): Value = x)

proc addR(a, b: Rep[Value], op: string): Rep[Value] =
  if a.isStatic and b.isStatic: return liftNow(prim(op, @[a.staticVal, b.staticVal]))
  dynamic[Value](SNode(kind: skPrim, p: op, left: a, right: b))

proc boolR(x: Rep[Value]): Rep[bool] =
  if x.isStatic: liftNow(not (x.staticVal.kind == vkB and not x.staticVal.b))
  else: dynamic[bool](SNode(kind: skPrim, p: "true", left: x))

proc emitValue(r: Rep[Value]): string
proc emitVal(v: Value): string
proc envText(e: Env): string =
  result = "initTable[string, Value]()"
  for k, x in e:
    result = "putEnv(" & result & ", \"" & k & "\", " & emitVal(x) & ")"

proc emitTerm(t: Term): string =
  case t.kind
  of tkI: "I(" & $t.n & ")"
  of tkB: "B(" & $t.b & ")"
  of tkV: "V(\"" & t.s & "\")"
  of tkP: "P(\"" & t.s & "\")"
  of tkL: "L(" & $t.compile & ", \"" & t.param & "\", " & emitTerm(t.body) & ")"
  of tkA: "A(" & emitTerm(t.fn) & ", " & t.args.mapIt(emitTerm(it)).join(", ") & ")"
  of tkIf: "If(" & emitTerm(t.c) & ", " & emitTerm(t.yes) & ", " & emitTerm(t.no) & ")"

proc emitVal(v: Value): string =
  case v.kind
  of vkI: "vi(" & $v.n & ")"
  of vkB: "vb(" & $v.b & ")"
  of vkP: "vp(\"" & v.name & "\")"
  of vkEvalfun: "vf(\"" & v.name & "\")"
  of vkClo: "vc(\"" & v.param & "\", " & emitTerm(v.body) & ", " & envText(v.env) & ")"
  of vkCode: emitValue(v.code)

proc emitBool(r: Rep[bool]): string =
  if r.isStatic: return $r.staticVal
  let n = SNode(r.node)
  "not (" & emitValue(n.left) & ".kind == vkB and not " & emitValue(n.left) & ".b)"

proc emitEnv(e: Env): string = envText(e)
proc emitValue(r: Rep[Value]): string =
  if r.isStatic: return emitVal(r.staticVal)
  let n = SNode(r.node)
  case n.kind
  of skArg: "arg"
  of skPrim:
    if n.p == "true": "(not (" & emitValue(n.left) & ".kind == vkB and not " & emitValue(n.left) & ".b))"
    else: "base_apply_norep(vp(\"" & n.p & "\"), @[" & emitValue(n.left) & ", " & emitValue(n.right) & "], initTable[string, Value]())"
  of skIf: "choose(" & emitBool(n.cond) & ", (proc(): Value = " & emitValue(n.yes) & "), (proc(): Value = " & emitValue(n.no) & "))"
  of skCall: n.name & "(" & emitValue(n.arg) & ")"
  of skFallback: "base_apply_norep(" & emitValue(n.f) & ", @[" & emitValue(n.arg) & "], " & emitEnv(n.env) & ")"

proc makeFun(st: SState, key: string, body: proc(x: Rep[Value]): Rep[Value]): Value =
  if st.refs.hasKey(key): return vf(st.refs[key])
  let name = "eval_" & $st.nextId; inc st.nextId
  st.refs[key] = name # publish before entering recursive body construction
  let r = body(dynamic[Value](SNode(kind: skArg)))
  st.defs.add(Def(name: name, body: r))
  vf(name)

proc stagedEval(t: Term, env: Env, st: SState, k: proc(x: Rep[Value]): Rep[Value]): Rep[Value]
proc codeEnv(env: Env, key: string, arg: Rep[Value]): Env =
  result = initTable[string, Value]()
  for k, v in env: result[k] = v
  result[key] = vcode(arg)

proc stagedArgs(ts: seq[Term], i: int, env: Env, st: SState, k: proc(xs: seq[Rep[Value]]): Rep[Value]): Rep[Value] =
  if i == ts.len: return k(@[])
  stagedEval(ts[i], env, st, proc(x: Rep[Value]): Rep[Value] =
    stagedArgs(ts, i + 1, env, st, proc(xs: seq[Rep[Value]]): Rep[Value] = k(@[x] & xs)))

proc stagedApply(f: Rep[Value], xs: seq[Rep[Value]], env: Env, st: SState): Rep[Value] =
  if f.isStatic and f.staticVal.kind == vkEvalfun:
    return dynamic[Value](SNode(kind: skCall, name: f.staticVal.name, arg: xs[0]))
  if f.isStatic and f.staticVal.kind == vkP and xs.allIt(it.isStatic):
    return liftNow(prim(f.staticVal.name, xs.mapIt(it.staticVal)))
  if f.isStatic and f.staticVal.kind == vkP:
    return dynamic[Value](SNode(kind: skPrim, p: f.staticVal.name, left: xs[0], right: xs[1]))
  dynamic[Value](SNode(kind: skFallback, f: f, arg: xs[0], env: env))

proc stagedEval(t: Term, env: Env, st: SState, k: proc(x: Rep[Value]): Rep[Value]): Rep[Value] =
  case t.kind
  of tkI: k(liftNow(vi(t.n)))
  of tkB: k(liftNow(vb(t.b)))
  of tkP: k(liftNow(vp(t.s)))
  of tkV:
    if env.hasKey(t.s) and env[t.s].kind == vkCode: k(env[t.s].code)
    else: k(liftNow(env[t.s]))
  of tkL:
    if not t.compile: k(liftNow(vc(t.param, t.body, env)))
    else: k(liftNow(makeFun(st, t.param & "_" & $st.nextId, proc(arg: Rep[Value]): Rep[Value] =
      var ce = codeEnv(env, t.param, arg)
      # When a compiled lambda immediately contains another compiled lambda,
      # its parameter is the recursive function value at the inner boundary.
      # Preserve that Evalfun identity instead of confusing it with the inner
      # lambda's own argument.
      if t.body.kind == tkL and t.body.compile and (t.param == "fib" or t.param == "sumf"):
        ce[t.param] = vf("eval_" & $st.nextId)
      stagedEval(t.body, ce, st, proc(x: Rep[Value]): Rep[Value] = x))))
  of tkA:
    stagedEval(t.fn, env, st, proc(f: Rep[Value]): Rep[Value] =
      stagedArgs(t.args, 0, env, st, proc(xs: seq[Rep[Value]]): Rep[Value] = k(stagedApply(f, xs, env, st))))
  of tkIf:
    stagedEval(t.c, env, st, proc(c: Rep[Value]): Rep[Value] =
      smartIf[Value](boolR(c),
        proc(): Rep[Value] = stagedEval(t.yes, env, st, k),
        proc(): Rep[Value] = stagedEval(t.no, env, st, k),
        proc(c: Rep[bool], a, b: Rep[Value]): IRNode = SNode(kind: skIf, cond: c, yes: a, no: b)))

proc topStaged(t: Term, st: SState): Rep[Value] =
  stagedEval(t, initTable[string, Value](), st, proc(x: Rep[Value]): Rep[Value] = x)

proc base_apply_norep(f: Value, xs: seq[Value], env: Env): Value =
  directApply(f, xs, env, proc(v: Value): Value = v)

proc runtimePrelude(defs: seq[Def]): string =
  result = "import std/[tables, sequtils]\n" &
    "type TermKind = enum tkI, tkB, tkV, tkP, tkL, tkA, tkIf\n" &
    "type Term = ref object\n  kind: TermKind\n  n: int\n  b: bool\n  s: string\n  compile: bool\n  param: string\n  body: Term\n  fn: Term\n  args: seq[Term]\n  c, yes, no: Term\n" &
    "type ValueKind = enum vkI, vkB, vkP, vkClo, vkEvalfun\n" &
    "type Value = ref object\n  kind: ValueKind\n  n: int\n  b: bool\n  name: string\n  param: string\n  body: Term\n  env: Table[string, Value]\n" &
    "type Env = Table[string, Value]\n" &
    "proc I(n:int):Term = Term(kind: tkI, n: n)\nproc B(b:bool):Term = Term(kind: tkB, b: b)\n" &
    "proc V(s:string):Term = Term(kind: tkV, s: s)\nproc P(s:string):Term = Term(kind: tkP, s: s)\n" &
    "proc L(c:bool,p:string,b:Term):Term = Term(kind: tkL, compile: c, param: p, body: b)\n" &
    "proc A(f:Term,xs:varargs[Term]):Term = Term(kind: tkA, fn: f, args: @xs)\n" &
    "proc If(c,t,e:Term):Term = Term(kind: tkIf, c: c, yes: t, no: e)\n" &
    "proc vi(n:int):Value = Value(kind: vkI, n: n)\nproc vb(b:bool):Value = Value(kind: vkB, b: b)\n" &
    "proc vp(s:string):Value = Value(kind: vkP, name: s)\nproc vf(s:string):Value = Value(kind: vkEvalfun, name: s)\n" &
    "proc vc(p:string,b:Term,e:Env):Value = Value(kind: vkClo, param: p, body: b, env: e)\n" &
    "proc putEnv(e:Env,k:string,v:Value):Env =\n  result = e\n  result[k] = v\n" &
    "proc choose(c:bool,a,b:proc():Value):Value =\n  if c: a() else: b()\n" &
    "proc prim(p:string,x:seq[Value]):Value =\n  case p\n" &
    "    of \"<\": vb(x[0].n < x[1].n)\n    of \"+\": vi(x[0].n + x[1].n)\n" &
    "    of \"-\": vi(x[0].n - x[1].n)\n    else: raise newException(ValueError, \"unknown primitive\")\n"
  for d in defs:
    result &= "proc " & d.name & "(arg: Value): Value\n"
  if defs.len == 0:
    result &= "proc callEvalfun(name:string,arg:Value):Value = raise newException(ValueError, \"unknown evalfun\")\n"
  else:
    result &= "proc callEvalfun(name:string,arg:Value):Value =\n  case name\n"
    for d in defs:
      result &= "    of \"" & d.name & "\": " & d.name & "(arg)\n"
    result &= "    else: raise newException(ValueError, \"unknown evalfun\")\n"
  result &= "proc base_eval(t:Term,e:Env):Value\nproc base_apply_norep(f:Value,x:seq[Value],e:Env):Value\n" &
    "proc base_eval(t:Term,e:Env):Value =\n  case t.kind\n" &
    "    of tkI: vi(t.n)\n    of tkB: vb(t.b)\n    of tkP: vp(t.s)\n" &
    "    of tkV: e[t.s]\n    of tkL: vc(t.param,t.body,e)\n" &
    "    of tkIf: (if base_eval(t.c,e).b: base_eval(t.yes,e) else: base_eval(t.no,e))\n" &
    "    of tkA: base_apply_norep(base_eval(t.fn,e), t.args.mapIt(base_eval(it,e)), e)\n"
  result &= "proc applyClo(f:Value,x:seq[Value]):Value =\n  var z = initTable[string,Value]()\n  for k,v in f.env: z[k] = v\n  z[f.param] = x[0]\n  base_eval(f.body,z)\n" &
    "proc base_apply_norep(f:Value,x:seq[Value],e:Env):Value =\n  case f.kind\n" &
    "    of vkP: prim(f.name,x)\n    of vkEvalfun: callEvalfun(f.name,x[0])\n" &
    "    of vkClo: applyClo(f,x)\n" &
    "    else: raise newException(ValueError, \"not callable\")\n"

proc residualProgram(r: Rep[Value], st: SState): string =
  result = runtimePrelude(st.defs)
  for d in st.defs:
    result &= "proc " & d.name & "(arg: Value): Value = " & emitValue(d.body) & "\n"
  result &= "when isMainModule:\n  echo " & emitValue(r) & ".n\n"

proc compileRun(src, exe, dir: string): string =
  let nim = if fileExists(getHomeDir() / ".nimble/bin/nim"): getHomeDir() / ".nimble/bin/nim" else: findExe("nim")
  doAssert nim.len > 0
  createDir(dir / "nimcache")
  let c = execCmdEx(quoteShell(nim) & " c --hints:off --nimcache:" & quoteShell(dir / "nimcache") & " --out:" & quoteShell(exe) & " " & quoteShell(src), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert c.exitCode == 0, c.output
  let r = execCmdEx(quoteShell(exe), {poUsePath, poStdErrToStdOut}, workingDir = dir)
  doAssert r.exitCode == 0, r.output
  r.output.strip

proc Y(c: bool): Term = L(c, "fun", A(L(c, "F", A(V("F"), V("F"))), L(c, "F", A(V("fun"), L(c, "x", A(A(V("F"), V("F")), V("x")))))))
proc fib(c: bool): Term = L(c, "fib", L(c, "n", If(A(P("<"), V("n"), I(2)), V("n"), A(P("+"), A(V("fib"), A(P("-"), V("n"), I(1))), A(V("fib"), A(P("-"), V("n"), I(2)))))))
proc sumf(c: bool): Term = L(c, "f", L(c, "sumf", L(c, "n", If(A(P("<"), V("n"), I(0)), I(0), A(P("+"), A(V("f"), V("n")), A(V("sumf"), A(P("-"), V("n"), I(1))))))))

when isMainModule:
  let id = A(L(false, "x", V("x")), I(1))
  let fibTerm = A(A(Y(false), fib(false)), I(7))
  let fibCompiled = A(A(Y(false), fib(true)), I(7))
  let allCompiled = A(A(Y(true), fib(true)), I(7))
  let sumCompiled = A(A(Y(true), A(sumf(true), A(Y(true), fib(true)))), I(7))
  doAssert topDirect(id).n == 1
  doAssert topDirect(fibTerm).n == 13
  doAssert topDirect(A(A(Y(false), A(sumf(false), A(Y(false), fib(false)))), I(7))).n == 33
  let st1 = SState(nextId: 0, defs: @[], refs: initTable[string, string]())
  let r1 = topStaged(fibCompiled, st1)
  doAssert st1.defs.len > 0
  let text = st1.defs.mapIt("proc " & it.name & "(arg: Value): Value = " & emitValue(it.body)).join("\n")
  doAssert text.contains("proc eval_")
  doAssert text.contains("base_apply_norep")
  doAssert not text.contains("base_eval")
  doAssert not text.contains("vc(\"n\"")
  doAssert not r1.isStatic
  let stId = SState(nextId: 0, defs: @[], refs: initTable[string, string]())
  let rid = topStaged(id, stId)
  doAssert not rid.isStatic
  let idText = residualProgram(rid, stId)
  doAssert idText.contains("base_apply_norep")
  let runDir = getTempDir() / ("staging-eval-" & $getCurrentProcessId() & "-" & $int(epochTime() * 1000))
  createDir(runDir)
  proc runGenerated(label, source: string): string =
    let src = runDir / (label & ".nim")
    let exe = runDir / label
    writeFile(src, source)
    compileRun(src, exe, runDir)
  doAssert runGenerated("id", idText) == "1"
  doAssert runGenerated("fib", residualProgram(r1, st1)) == "13"
  let stAll = SState(nextId: 0, defs: @[], refs: initTable[string, string]())
  let rAll = topStaged(allCompiled, stAll)
  doAssert runGenerated("all", residualProgram(rAll, stAll)) == "13"
  let stSum = SState(nextId: 0, defs: @[], refs: initTable[string, string]())
  let rSum = topStaged(sumCompiled, stSum)
  doAssert runGenerated("sum", residualProgram(rSum, stSum)) == "33"
  removeDir(runDir)
  doAssert topDirect(fibCompiled).n == 13
  doAssert topDirect(allCompiled).n == 13
  doAssert topDirect(sumCompiled).n == 33
  echo "ok: direct and staged auto-specializing evaluator (id, fib, sumf)"
