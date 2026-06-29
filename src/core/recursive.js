// Primitive recursive and μ-recursive functions as expression trees, with an evaluator that traces
// every call, plus Ackermann's function with a call trace and a growth table.
//
// Building blocks: Z (zero, any number of arguments), S (successor), P(i,n) (the i-th of n arguments),
// C(f; g1, …, gm) (composition: f(g1(x̄), …, gm(x̄))), R(f, g) (primitive recursion on the last argument:
// h(x̄, 0) = f(x̄), h(x̄, y+1) = g(x̄, y, h(x̄, y))), M(f) (unbounded search: the least y with f(x̄, y) = 0).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  // ---------- parsing ----------
  function parseExpr(src) {
    let i = 0;
    const s = src.replace(/\s+/g, '');
    const fail = (m) => { throw new Error(`${m} at position ${i} of ${src}`); };
    const eat = (c) => { if (s[i] !== c) fail(`expected ${c}`); i++; };
    const num = () => { const m = /^\d+/.exec(s.slice(i)); if (!m) fail('expected a number'); i += m[0].length; return +m[0]; };
    const expr = () => {
      const m = /^[A-Za-z_][\w']*/.exec(s.slice(i));
      if (!m) fail('expected a function');
      const w = m[0]; i += w.length;
      if (w === 'Z') return { t: 'Z' };
      if (w === 'S') return { t: 'S' };
      if (w === 'P') { eat('('); const a = num(); eat(','); const b = num(); eat(')'); if (a < 1 || a > b) fail(`P(${a},${b}) needs 1 ≤ i ≤ n`); return { t: 'P', i: a, n: b }; }
      if (w === 'C' && s[i] === '(') { eat('('); const f = expr(); eat(';'); const gs = [expr()]; while (s[i] === ',') { i++; gs.push(expr()); } eat(')'); return { t: 'C', f, gs }; }
      if (w === 'R' && s[i] === '(') { eat('('); const f = expr(); eat(','); const g = expr(); eat(')'); return { t: 'R', f, g }; }
      if (w === 'M' && s[i] === '(') { eat('('); const f = expr(); eat(')'); return { t: 'M', f }; }
      return { t: 'N', name: w };
    };
    const e = expr();
    if (i !== s.length) fail('unexpected text');
    return e;
  }

  // Parse `name = expr` lines into an environment (later lines may use earlier names).
  function parseDefs(text, env0 = {}) {
    const env = Object.assign({}, env0), errors = [];
    String(text).split('\n').forEach((line0, ln) => {
      const line = line0.replace(/\/\/.*$/, '').trim();
      if (!line) return;
      const m = /^([A-Za-z_][\w']*)\s*=\s*(.+)$/.exec(line);
      if (!m) { errors.push({ line: ln + 1, msg: 'expected  name = expression' }); return; }
      try { const e = parseExpr(m[2]); const a = arity(e, env); env[m[1]] = { name: m[1], expr: e, arity: a, text: m[2].trim() }; }
      catch (err) { errors.push({ line: ln + 1, msg: err.message }); }
    });
    return { env, errors };
  }

  // Arity of an expression: a number, or null for "any" (Z, and compositions built only from it).
  function arity(e, env) {
    switch (e.t) {
      case 'Z': return null;
      case 'S': return 1;
      case 'P': return e.n;
      case 'N': { if (!env[e.name]) throw new Error(`unknown function ${e.name}`); return env[e.name].arity; }
      case 'C': {
        const af = arity(e.f, env);
        if (af != null && af !== e.gs.length) throw new Error(`${toText(e.f)} takes ${af} argument${af === 1 ? '' : 's'} but is given ${e.gs.length}`);
        let a = null;
        for (const g of e.gs) { const ag = arity(g, env); if (ag != null) { if (a != null && a !== ag) throw new Error(`the inner functions of ${toText(e)} disagree on their number of arguments`); a = ag; } }
        return a;
      }
      case 'R': {
        const af = arity(e.f, env), ag = arity(e.g, env);
        if (af != null && ag != null && ag !== af + 2) throw new Error(`in ${toText(e)} the step function needs ${af + 2} arguments`);
        if (af == null && ag == null) return null;
        return af != null ? af + 1 : ag - 1;
      }
      case 'M': { const af = arity(e.f, env); if (af === 0) throw new Error('M needs a function of at least one argument'); return af == null ? null : af - 1; }
    }
    throw new Error('bad expression');
  }

  function toText(e) {
    switch (e.t) {
      case 'Z': return 'Z';
      case 'S': return 'S';
      case 'P': return `P(${e.i},${e.n})`;
      case 'N': return e.name;
      case 'C': return `C(${toText(e.f)}; ${e.gs.map(toText).join(', ')})`;
      case 'R': return `R(${toText(e.f)}, ${toText(e.g)})`;
      case 'M': return `M(${toText(e.f)})`;
    }
  }

  // ---------- evaluation ----------
  class Limit extends Error {}
  // Evaluate with a call budget. Every call of a named function (and every basic step) is traced with
  // its depth, so the call tree can be drawn. verdict: value | limit (budget spent; perhaps undefined).
  function evaluate(e0, args, env = {}, opts = {}) {
    const e = typeof e0 === 'string' ? (env[e0] ? env[e0].expr : parseExpr(e0)) : e0;
    const maxCalls = opts.maxCalls || 200000, maxSearch = opts.maxSearch || 10000, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 3000, detail = opts.detail || 'named';
    const trace = [];
    let calls = 0;
    const label = (x) => (x.t === 'N' ? x.name : toText(x));
    const note = (s) => { if (wantTrace && trace.length < traceLimit) trace.push(s); };
    const ev = (x, a, d) => {
      if (++calls > maxCalls) throw new Limit();
      const show = detail === 'all' || x.t === 'N' || x.t === 'M' || d === 0;
      if (show) note({ kind: 'call', say: `${label(x)}(${a.join(', ')})`, fn: label(x), args: a.slice(), depth: d });
      let v;
      switch (x.t) {
        case 'Z': v = 0; break;
        case 'S': v = a[0] + 1; break;
        case 'P': v = a[x.i - 1]; break;
        case 'N': v = ev(env[x.name].expr, a, d + 1); break;
        case 'C': { const inner = x.gs.map((g) => ev(g, a, d + 1)); v = ev(x.f, inner, d + 1); break; }
        case 'R': {
          const xs = a.slice(0, -1), y = a[a.length - 1];
          v = ev(x.f, xs, d + 1);
          for (let k = 0; k < y; k++) v = ev(x.g, xs.concat([k, v]), d + 1);
          break;
        }
        case 'M': {
          let y = 0;
          for (;; y++) {
            if (y >= maxSearch) throw new Limit();
            const r = ev(x.f, a.concat([y]), d + 1);
            note({ kind: 'search', say: `Try y = ${y}: ${toText(x.f)}(${a.concat([y]).join(', ')}) = ${r}${r === 0 ? ', found' : ', not 0'}.`, y, value: r, depth: d });
            if (r === 0) break;
          }
          v = y; break;
        }
      }
      if (show) note({ kind: 'return', say: `${label(x)}(${a.join(', ')}) = ${v}`, fn: label(x), args: a.slice(), value: v, depth: d });
      return v;
    };
    try {
      const value = ev(e, args, 0);
      return { verdict: 'value', value, calls, trace };
    } catch (err) {
      if (!(err instanceof Limit)) throw err;
      note({ kind: 'limit', say: `Gave up after ${calls} calls: the search may never end (the function may be undefined here).` });
      return { verdict: 'limit', value: null, calls, trace };
    }
  }

  // A library of definitions; each line may use the names above it.
  const LIBRARY = `
add = R(P(1,1), C(S; P(3,3)))
mult = R(Z, C(add; P(1,3), P(3,3)))
pred = R(Z, P(1,2))
monus = R(P(1,1), C(pred; P(3,3)))
exp = R(C(S; Z), C(mult; P(1,3), P(3,3)))
fact = R(C(S; Z), C(mult; C(S; P(1,2)), P(2,2)))
sg = R(Z, C(S; Z))
nsg = R(C(S; Z), Z)
absdiff = C(add; monus, C(monus; P(2,2), P(1,2)))
eq = C(nsg; absdiff)
lt = C(sg; C(monus; P(2,2), P(1,2)))
min = C(monus; P(1,2), C(monus; P(1,2), P(2,2)))
max = C(add; P(2,2), C(monus; P(1,2), P(2,2)))
double = C(add; P(1,1), P(1,1))
tri = R(Z, C(add; C(S; P(1,2)), P(2,2)))
div = M(C(nsg; C(lt; P(1,3), C(mult; C(S; P(3,3)), P(2,3)))))
isqrt = M(C(nsg; C(lt; P(1,2), C(mult; C(S; P(2,2)), C(S; P(2,2))))))
log2 = M(C(nsg; C(lt; P(1,2), C(exp; C(S; C(S; Z)), C(S; P(2,2))))))
`;
  const ORACLES = {
    add: (x, y) => x + y, mult: (x, y) => x * y, pred: (x) => Math.max(0, x - 1), monus: (x, y) => Math.max(0, x - y),
    exp: (x, y) => x ** y, fact: (n) => { let f = 1; for (let i = 2; i <= n; i++) f *= i; return f; }, sg: (x) => (x ? 1 : 0), nsg: (x) => (x ? 0 : 1),
    absdiff: (x, y) => Math.abs(x - y), eq: (x, y) => (x === y ? 1 : 0), lt: (x, y) => (x < y ? 1 : 0), min: Math.min, max: Math.max,
    double: (x) => 2 * x, tri: (n) => (n * (n + 1)) / 2,
    div: (x, y) => (y === 0 ? undefined : Math.floor(x / y)), isqrt: (x) => Math.floor(Math.sqrt(x)), log2: (x) => (x === 0 ? 0 : Math.floor(Math.log2(x))),
  };
  let libEnv = null;
  const library = () => { if (!libEnv) { const r = parseDefs(LIBRARY); if (r.errors.length) throw new Error(JSON.stringify(r.errors)); libEnv = r.env; } return libEnv; };

  // ---------- Ackermann ----------
  // A(0, n) = n + 1, A(m+1, 0) = A(m, 1), A(m+1, n+1) = A(m, A(m+1, n)). Evaluated with an explicit
  // stack so deep recursion cannot overflow; every call is counted and (up to a limit) traced.
  function ackermann(m, n, opts = {}) {
    const maxCalls = opts.maxCalls || 5e6, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 2000;
    const trace = [], stack = [m];
    let cur = n, calls = 0, maxDepth = 0;
    while (stack.length) {
      const mm = stack.pop();
      if (++calls > maxCalls) return { verdict: 'limit', value: null, calls, maxDepth, trace };
      maxDepth = Math.max(maxDepth, stack.length + 1);
      if (wantTrace && trace.length < traceLimit) trace.push({ kind: 'call', say: `A(${mm}, ${cur})`, m: mm, n: cur, depth: stack.length });
      if (mm === 0) cur = cur + 1;
      else if (cur === 0) { stack.push(mm - 1); cur = 1; }
      else { stack.push(mm - 1); stack.push(mm); cur = cur - 1; }
    }
    trace.push({ kind: 'value', say: `A(${m}, ${n}) = ${cur} after ${calls} calls.`, value: cur, calls });
    return { verdict: 'value', value: cur, calls, maxDepth, trace };
  }
  // Closed forms per row, used where computing is hopeless; values beyond 2^53 are given as text.
  function ackFormula(m, n) {
    if (m === 0) return { value: n + 1, text: `${n} + 1` };
    if (m === 1) return { value: n + 2, text: `${n} + 2` };
    if (m === 2) return { value: 2 * n + 3, text: `2·${n} + 3` };
    if (m === 3) return n + 3 <= 52 ? { value: 2 ** (n + 3) - 3, text: `2^${n + 3} − 3` } : { value: null, text: `2^${n + 3} − 3` };
    if (m === 4) { const tower = n + 3; const v = tower <= 4 ? [0, 0, 4, 16, 65536][tower] : null; return { value: v != null ? v - 3 : null, text: `2↑↑${tower} − 3 (a tower of ${tower} twos, minus 3)` }; }
    return { value: null, text: `beyond any tower: A(${m}, ${n})` };
  }
  function ackTable(maxM = 4, maxN = 5, budget = 3e6) {
    const rows = [];
    for (let m = 0; m <= maxM; m++) {
      const row = [];
      for (let n = 0; n <= maxN; n++) {
        const f = ackFormula(m, n);
        const r = f.value != null && f.value < 5000 ? ackermann(m, n, { trace: false, maxCalls: budget }) : { verdict: 'limit' };
        row.push({ m, n, value: r.verdict === 'value' ? r.value : f.value, calls: r.verdict === 'value' ? r.calls : null, formula: f.text, computed: r.verdict === 'value' });
      }
      rows.push(row);
    }
    return rows;
  }

  T.rec = { parseExpr, parseDefs, arity, toText, evaluate, library, LIBRARY, ORACLES, ackermann, ackFormula, ackTable };
})();
