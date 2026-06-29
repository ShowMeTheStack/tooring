// Lambda calculus as a side door into computability: parsing, capture-avoiding substitution,
// normal-order (leftmost-outermost) reduction traced step by step, and Church numerals.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  const V = (n) => ({ t: 'var', n }), L = (v, b) => ({ t: 'lam', v, b }), A = (f, a) => ({ t: 'app', f, a });

  // Grammar: term := λx y. term | app ; app := atom atom* ; atom := name | number | ( term ).
  // λ may be written \ ; a number k is the Church numeral for k; names in env are expanded.
  function parse(src, env = DEFS) {
    const toks = [], re = /\s*(λ|\\|\.|\(|\)|[A-Za-z_][\w']*|\d+)/y;
    let m, pos = 0;
    while (pos < src.length) {
      if (/^\s*$/.test(src.slice(pos))) break;
      re.lastIndex = pos; m = re.exec(src);
      if (!m) throw new Error(`cannot read "${src.slice(pos, pos + 8)}"`);
      toks.push(m[1]); pos = re.lastIndex;
    }
    let i = 0;
    const term = (bound) => {
      if (toks[i] === 'λ' || toks[i] === '\\') {
        i++;
        const vs = [];
        while (toks[i] && toks[i] !== '.') { if (!/^[A-Za-z_]/.test(toks[i])) throw new Error('expected a variable after λ'); vs.push(toks[i++]); }
        if (toks[i] !== '.' || !vs.length) throw new Error('expected λx. body');
        i++;
        const nb = new Set(bound); vs.forEach((v) => nb.add(v));
        let b = term(nb);
        for (let k = vs.length - 1; k >= 0; k--) b = L(vs[k], b);
        return b;
      }
      let f = atom(bound);
      while (i < toks.length && toks[i] !== ')') f = A(f, (toks[i] === 'λ' || toks[i] === '\\') ? term(bound) : atom(bound));
      return f;
    };
    const atom = (bound) => {
      const t = toks[i++];
      if (t === '(') { const x = term(bound); if (toks[i++] !== ')') throw new Error('missing )'); return x; }
      if (t == null || t === ')' || t === '.') throw new Error('expected a term');
      if (/^\d+$/.test(t)) return church(+t);
      if (!bound.has(t) && env && env[t]) return parse(env[t], env);
      return V(t);
    };
    const r = term(new Set());
    if (i !== toks.length) throw new Error('unexpected ' + toks[i]);
    return r;
  }

  function show(e) {
    if (e.t === 'var') return e.n;
    if (e.t === 'lam') { const vs = []; let b = e; while (b.t === 'lam') { vs.push(b.v); b = b.b; } return `λ${vs.join(' ')}. ${show(b)}`; }
    const f = e.f.t === 'lam' ? `(${show(e.f)})` : show(e.f);
    const a = e.a.t === 'var' ? show(e.a) : `(${show(e.a)})`;
    return f + ' ' + a;
  }

  function free(e, out = new Set()) {
    if (e.t === 'var') out.add(e.n);
    else if (e.t === 'lam') { const s = free(e.b); s.delete(e.v); s.forEach((x) => out.add(x)); }
    else { free(e.f, out); free(e.a, out); }
    return out;
  }
  const fresh = (v, avoid) => { let n = v; while (avoid.has(n)) n += "'"; return n; };

  // e[x := s], renaming bound variables that would capture a free variable of s
  function subst(e, x, s, fs = free(s)) {
    if (e.t === 'var') return e.n === x ? s : e;
    if (e.t === 'app') return A(subst(e.f, x, s, fs), subst(e.a, x, s, fs));
    if (e.v === x) return e;
    if (fs.has(e.v) && free(e.b).has(x)) {
      const nv = fresh(e.v, new Set([...fs, ...free(e.b)]));
      return L(nv, subst(subst(e.b, e.v, V(nv)), x, s, fs));
    }
    return L(e.v, subst(e.b, x, s, fs));
  }

  // One normal-order step: the leftmost-outermost redex. Returns {term, path} or null in normal form.
  function step(e, path = []) {
    if (e.t === 'app') {
      if (e.f.t === 'lam') return { term: subst(e.f.b, e.f.v, e.a), path, redex: e };
      const f = step(e.f, path.concat('f'));
      if (f) return { term: A(f.term, e.a), path: f.path, redex: f.redex };
      const a = step(e.a, path.concat('a'));
      if (a) return { term: A(e.f, a.term), path: a.path, redex: a.redex };
      return null;
    }
    if (e.t === 'lam') { const b = step(e.b, path.concat('b')); return b && { term: L(e.v, b.term), path: b.path, redex: b.redex }; }
    return null;
  }

  const size = (e) => (e.t === 'var' ? 1 : e.t === 'lam' ? 1 + size(e.b) : 1 + size(e.f) + size(e.a));

  // Reduce to normal form (or stop at maxSteps / maxSize). verdict: normal | limit.
  function normalize(e0, opts = {}) {
    let e = typeof e0 === 'string' ? parse(e0, opts.env || DEFS) : e0;
    const maxSteps = opts.maxSteps || 2000, maxSize = opts.maxSize || 20000, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 500;
    const trace = [{ kind: 'start', say: `Start from ${show(e)}.`, term: show(e) }];
    let steps = 0;
    while (true) {
      const r = step(e);
      if (!r) { trace.push({ kind: 'normal', say: `No redex is left: the normal form is ${show(e)}.`, term: show(e), steps }); return { verdict: 'normal', term: e, text: show(e), steps, trace }; }
      if (steps >= maxSteps || size(r.term) > maxSize) { trace.push({ kind: 'limit', say: `Still reducing after ${steps} steps: there may be no normal form.`, steps }); return { verdict: 'limit', term: e, text: show(e), steps, trace }; }
      steps++;
      if (wantTrace && trace.length < traceLimit) trace.push({ kind: 'beta', say: `Reduce the leftmost outermost redex (${show(r.redex.f)}) applied to ${show(r.redex.a)}: put ${show(r.redex.a)} in for ${r.redex.f.v}.`, before: show(e), after: show(r.term), redex: show(r.redex), path: r.path, step: steps });
      e = r.term;
    }
  }

  // de Bruijn form for alpha-equivalence
  function debruijn(e, ctx = []) {
    if (e.t === 'var') { const i = ctx.lastIndexOf(e.n); return i < 0 ? 'free:' + e.n : String(ctx.length - 1 - i); }
    if (e.t === 'lam') return 'λ' + debruijn(e.b, ctx.concat(e.v));
    return '(' + debruijn(e.f, ctx) + ' ' + debruijn(e.a, ctx) + ')';
  }
  const alphaEq = (a, b) => debruijn(a) === debruijn(b);

  function church(n) { let b = V('x'); for (let i = 0; i < n; i++) b = A(V('f'), b); return L('f', L('x', b)); }
  // the number k if e is λf. λx. f (f … (f x)), else null
  function unchurch(e) {
    if (e.t !== 'lam' || e.b.t !== 'lam') return null;
    const f = e.v, x = e.b.v;
    if (f === x) return null;
    let b = e.b.b, k = 0;
    while (b.t === 'app' && b.f.t === 'var' && b.f.n === f) { b = b.a; k++; }
    return b.t === 'var' && b.n === x ? k : null;
  }
  function unbool(e) { if (alphaEq(e, parse('λt f. t', {}))) return true; if (alphaEq(e, parse('λt f. f', {}))) return false; return null; }

  // Named terms, written with each other's names; numbers are Church numerals.
  const DEFS = {
    I: 'λx. x', K: 'λx y. x', KI: 'λx y. y', S: 'λx y z. x z (y z)',
    TRUE: 'λt f. t', FALSE: 'λt f. f', IF: 'λb t f. b t f', NOT: 'λb. b FALSE TRUE', AND: 'λp q. p q p', OR: 'λp q. p p q',
    SUCC: 'λn f x. f (n f x)', PLUS: 'λm n f x. m f (n f x)', MULT: 'λm n f. m (n f)', POW: 'λb e. e (MULT b) 1',
    PRED: 'λn f x. n (λg h. h (g f)) (λu. x) (λu. u)', SUB: 'λm n. n PRED m', ISZERO: 'λn. n (λz. FALSE) TRUE',
    LEQ: 'λm n. ISZERO (SUB m n)', EQ: 'λm n. AND (LEQ m n) (LEQ n m)',
    PAIR: 'λa b s. s a b', FST: 'λp. p TRUE', SND: 'λp. p FALSE',
    Y: 'λf. (λx. f (x x)) (λx. f (x x))', OMEGA: '(λx. x x) (λx. x x)',
    FACT: 'Y (λr n. IF (ISZERO n) 1 (MULT n (r (PRED n))))',
  };

  T.lambda = { parse, show, free, subst, step, normalize, church, unchurch, unbool, alphaEq, debruijn, size, DEFS };
})();
