// Regular expressions: a parser with a friendly syntax, a printer with minimal parentheses,
// simplification by named rules, and every construction between regexes and automata (Thompson,
// Glushkov, Brzozowski derivatives, state elimination, Kleene's table), each with a trace.
//
// Syntax (decided once, used everywhere):
//   a b c ...  any other single character is a symbol; whitespace is ignored (write "\ " for a space)
//   r|s        union                     rs   concatenation (juxtaposition)
//   r*         zero or more              r+   one or more        r?  zero or one
//   ( )        grouping; () alone is ε   ε or \e  the empty string   ∅ or \0  the empty language
//   [abc] [a-d] [^ab]  character classes ([^…] and . need the alphabet)   \x  the character x itself
// Precedence: postfix operators bind tightest, then concatenation, then union.
// With { plus: 'union' } the + sign means union instead (the blackboard habit a+b); postfix one-or-more
// is then unavailable and the printer writes r r* and (ε+r) for r+ and r?.
//
// AST nodes: { t: 'empty' } { t: 'eps' } { t: 'sym', c } { t: 'alt', a, b } { t: 'cat', a, b }
//            { t: 'star', x } { t: 'plus', x } { t: 'opt', x }
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const RE = T.RE = {};
  const FA = T.FA;
  const chars = (w) => Array.from(w);
  const showW = (w) => (w === '' ? 'ε' : w);

  // ---------------------------------------------------------------- nodes

  const EMPTY = { t: 'empty' }, EPSN = { t: 'eps' };
  const N = RE.node = {
    empty: () => EMPTY, eps: () => EPSN, sym: (c) => ({ t: 'sym', c }),
    alt: (a, b) => ({ t: 'alt', a, b }), cat: (a, b) => ({ t: 'cat', a, b }),
    star: (x) => ({ t: 'star', x }), plus: (x) => ({ t: 'plus', x }), opt: (x) => ({ t: 'opt', x }),
  };
  const unary = (r) => r.t === 'star' || r.t === 'plus' || r.t === 'opt';

  // ---------------------------------------------------------------- parser

  function RegexError(msg, pos) { const e = new Error(msg); e.pos = pos; e.name = 'RegexError'; return e; }
  const META = new Set(['|', '(', ')', '*', '?', '+', '[', ']', '.', '\\', 'ε', '∅']);

  RE.parse = function (src, opts = {}) {
    const s = chars(String(src)), unionPlus = opts.plus === 'union';
    let i = 0;
    const skip = () => { while (i < s.length && /\s/.test(s[i])) i++; };
    const peek = () => { skip(); return s[i]; };
    const isUnion = (c) => c === '|' || (unionPlus && c === '+');
    const unionSign = unionPlus ? '+' : '|';
    const alphaNeeded = (what) => { if (!opts.alphabet) throw RegexError(`${what} needs the alphabet to be known.`, i); return opts.alphabet; };

    function alt() {
      let left = cat();
      while (isUnion(peek())) { i++; left = N.alt(left, cat()); }
      return left;
    }
    function cat() {
      const items = [];
      const at = (skip(), i);
      for (;;) {
        const c = peek();
        if (c === undefined || c === ')' || isUnion(c)) break;
        items.push(post());
      }
      if (!items.length) {
        const c = s[i];
        if (c === undefined) throw RegexError(at === 0 ? 'The expression is empty: write ε for the empty string.' : `Something is missing after ${unionSign} at the end: write ε for the empty string.`, at);
        if (c === ')') throw RegexError('Nothing before ")": write ε for the empty string.', at);
        throw RegexError(`Nothing before ${c}: each side of ${unionSign} needs an expression (write ε for the empty string).`, at);
      }
      return items.reduce((x, y) => N.cat(x, y));
    }
    function post() {
      let x = atom();
      for (;;) {
        const c = peek();
        if (c === '*') { i++; x = N.star(x); }
        else if (c === '?') { i++; x = N.opt(x); }
        else if (c === '+' && !unionPlus) { i++; x = N.plus(x); }
        else return x;
      }
    }
    function escaped() {
      const c = s[i + 1];
      if (c === undefined) throw RegexError('A backslash at the end has nothing to escape.', i);
      i += 2;
      if (c === 'e') return EPSN;
      if (c === '0') return EMPTY;
      if (c === 'n') return N.sym('\n');
      if (c === 't') return N.sym('\t');
      return N.sym(c);
    }
    function atom() {
      const c = peek(), at = i;
      if (c === '(') {
        i++;
        if (peek() === ')') { i++; return EPSN; }
        const r = alt();
        if (peek() !== ')') throw RegexError(`The parenthesis opened at ${at + 1} is never closed.`, at);
        i++;
        return r;
      }
      if (c === ')') throw RegexError('This ")" has no matching "(".', at);
      if (c === '*' || c === '?' || c === '+') throw RegexError(`${c} has nothing to repeat: put it after a symbol or a group.`, at);
      if (c === ']') throw RegexError('This "]" has no matching "[".', at);
      if (c === 'ε') { i++; return EPSN; }
      if (c === '∅') { i++; return EMPTY; }
      if (c === '\\') return escaped();
      if (c === '.') { i++; const A = alphaNeeded('"." (any symbol)'); return altOf(A.map(N.sym)); }
      if (c === '[') return klass();
      i++;
      return N.sym(c);
    }
    function klass() {
      const at = i;
      i++;
      let neg = false;
      if (s[i] === '^') { neg = true; i++; }
      const set = [];
      const one = () => {
        if (s[i] === '\\') { const c = s[i + 1]; if (c === undefined) throw RegexError('A backslash at the end has nothing to escape.', i); i += 2; return c === 'n' ? '\n' : c === 't' ? '\t' : c; }
        return s[i++];
      };
      while (i < s.length && s[i] !== ']') {
        const a = one();
        if (s[i] === '-' && s[i + 1] !== undefined && s[i + 1] !== ']') {
          i++;
          const b = one(), lo = a.codePointAt(0), hi = b.codePointAt(0);
          if (hi < lo) throw RegexError(`The range ${a}-${b} runs backwards.`, at);
          if (hi - lo > 2000) throw RegexError(`The range ${a}-${b} is too large.`, at);
          for (let k = lo; k <= hi; k++) set.push(String.fromCodePoint(k));
        } else set.push(a);
      }
      if (s[i] !== ']') throw RegexError(`The class opened at ${at + 1} is never closed with "]".`, at);
      i++;
      let syms = [...new Set(set)];
      if (neg) { const A = alphaNeeded('A negated class [^…]'); syms = A.filter((a) => !syms.includes(a)); }
      return altOf(syms.map(N.sym));
    }
    const r = alt();
    if (peek() !== undefined) {
      if (s[i] === ')') throw RegexError('This ")" has no matching "(".', i);
      throw RegexError(`Unexpected ${s[i]}.`, i);
    }
    return r;
  };
  // Parse without throwing: { ok, ast } or { ok: false, error, pos }.
  RE.check = function (src, opts) {
    try { return { ok: true, ast: RE.parse(src, opts) }; } catch (e) { if (e.name !== 'RegexError') throw e; return { ok: false, error: e.message, pos: e.pos }; }
  };
  const ast = (r, opts) => (typeof r === 'string' ? RE.parse(r, opts) : r);
  RE.ast = ast;
  function altOf(list) { return list.length ? list.reduce((x, y) => N.alt(x, y)) : EMPTY; }
  function catOf(list) { return list.length ? list.reduce((x, y) => N.cat(x, y)) : EPSN; }

  // ---------------------------------------------------------------- printer

  const PREC = { alt: 1, cat: 2, star: 3, plus: 3, opt: 3, sym: 4, eps: 4, empty: 4 };
  RE.show = function (r, opts = {}) {
    r = ast(r, opts);
    const U = opts.plus === 'union';
    const symStr = (c) => (c === ' ' ? '\\ ' : c === '\n' ? '\\n' : c === '\t' ? '\\t' : META.has(c) || /\s/.test(c) ? '\\' + c : c);
    const go = (r, ctx) => {
      if (U && r.t === 'plus') return go(N.cat(r.x, N.star(r.x)), ctx);
      if (U && r.t === 'opt') return go(N.alt(EPSN, r.x), ctx);
      let out;
      switch (r.t) {
        case 'empty': return '∅';
        case 'eps': return 'ε';
        case 'sym': return symStr(r.c);
        case 'alt': out = go(r.a, 1) + (U ? '+' : '|') + go(r.b, 1); break;
        case 'cat': out = go(r.a, 2) + go(r.b, 2); break;
        case 'star': out = go(r.x, 3) + '*'; break;
        case 'plus': out = go(r.x, 3) + '+'; break;
        case 'opt': out = go(r.x, 3) + '?'; break;
        default: throw new Error('unknown node ' + r.t);
      }
      return PREC[r.t] < ctx ? '(' + out + ')' : out;
    };
    return go(r, 0);
  };
  const key = (r) => RE.show(r);
  RE.size = function size(r) { return r.t === 'alt' || r.t === 'cat' ? 1 + size(r.a) + size(r.b) : unary(r) ? 1 + size(r.x) : 1; };
  RE.alphabet = function (r) {
    const out = new Set();
    const go = (r) => { if (r.t === 'sym') out.add(r.c); else if (r.t === 'alt' || r.t === 'cat') { go(r.a); go(r.b); } else if (unary(r)) go(r.x); };
    go(ast(r));
    return [...out].sort();
  };
  const nullable = RE.nullable = function nullable(r) {
    switch (r.t) {
      case 'eps': case 'star': case 'opt': return true;
      case 'empty': case 'sym': return false;
      case 'alt': return nullable(r.a) || nullable(r.b);
      case 'cat': return nullable(r.a) && nullable(r.b);
      case 'plus': return nullable(r.x);
    }
    return false;
  };
  // Does the language contain no string at all? (Purely syntactic, and exact.)
  const isVoid = RE.isEmptyLang = function isVoid(r) {
    switch (r.t) {
      case 'empty': return true;
      case 'alt': return isVoid(r.a) && isVoid(r.b);
      case 'cat': return isVoid(r.a) || isVoid(r.b);
      case 'plus': return isVoid(r.x);
      default: return false;
    }
  };

  // ---------------------------------------------------------------- canonical form (for derivatives)

  const altItems = (r) => (r.t === 'alt' ? [...altItems(r.a), ...altItems(r.b)] : [r]);
  const catItems = (r) => (r.t === 'cat' ? [...catItems(r.a), ...catItems(r.b)] : [r]);
  // Union with associativity, commutativity and idempotence applied (flattened, sorted, deduplicated)
  // and ∅ dropped: with these, the derivatives of a regex are finitely many.
  function mkAlt(list) {
    const m = new Map();
    for (const r of list.flatMap(altItems)) if (r.t !== 'empty') m.set(key(r), r);
    const xs = [...m.keys()].sort().map((k) => m.get(k));
    return xs.length ? xs.reduceRight((acc, x) => N.alt(x, acc)) : EMPTY;
  }
  function mkCat(a, b) {
    if (a.t === 'empty' || b.t === 'empty') return EMPTY;
    if (a.t === 'eps') return b;
    if (b.t === 'eps') return a;
    if (a.t === 'cat') return mkCat(a.a, mkCat(a.b, b));
    return N.cat(a, b);
  }
  function mkStar(x) {
    if (x.t === 'empty' || x.t === 'eps') return EPSN;
    if (x.t === 'star') return x;
    if (x.t === 'plus' || x.t === 'opt') return N.star(x.x);
    return N.star(x);
  }
  RE.canon = function canon(r) {
    switch (r.t) {
      case 'alt': return mkAlt([canon(r.a), canon(r.b)]);
      case 'cat': return mkCat(canon(r.a), canon(r.b));
      case 'star': return mkStar(canon(r.x));
      case 'plus': { const x = canon(r.x); return x.t === 'empty' ? EMPTY : x.t === 'eps' ? EPSN : x.t === 'star' ? x : N.plus(x); }
      case 'opt': { const x = canon(r.x); return x.t === 'empty' || x.t === 'eps' ? EPSN : nullable(x) ? x : N.opt(x); }
      default: return r;
    }
  };

  // ---------------------------------------------------------------- derivatives

  // The derivative of r by c: the strings w with cw in L(r). raw = true skips simplification, to show
  // what the rules produce before tidying.
  RE.derivative = function derivative(r, c, raw) {
    const A = raw ? (l) => altOf(l) : mkAlt, C = raw ? N.cat : mkCat, S = raw ? N.star : mkStar;
    const d = (r) => {
      switch (r.t) {
        case 'empty': case 'eps': return EMPTY;
        case 'sym': return r.c === c ? EPSN : EMPTY;
        case 'alt': return A([d(r.a), d(r.b)]);
        case 'cat': return nullable(r.a) ? A([C(d(r.a), r.b), d(r.b)]) : C(d(r.a), r.b);
        case 'star': return C(d(r.x), r);
        case 'plus': return C(d(r.x), S(r.x));
        case 'opt': return d(r.x);
      }
      throw new Error('unknown node ' + r.t);
    };
    return d(ast(r));
  };
  RE.derivativeWord = (r, w) => chars(w).reduce((x, c) => RE.canon(RE.derivative(x, c)), RE.canon(ast(r)));

  // A DFA whose states are the (canonical) derivatives of r; a state accepts when its regex is nullable.
  // The trace names each derivative before and after simplification.
  RE.derivativeDFA = function (r, opts = {}) {
    r = ast(r, opts);
    const sigma = (opts.alphabet || RE.alphabet(r)).slice().sort(), max = opts.maxStates || 400;
    const r0 = RE.canon(r), names = new Map(), labels = {}, order = [], trace = [], trans = [];
    const add = (x) => { const k = key(x); if (names.has(k)) return [names.get(k), false]; const n = 'd' + names.size; names.set(k, n); labels[n] = k; order.push(x); return [n, true]; };
    add(r0);
    trace.push({ kind: 'state-new', state: 'd0', regex: key(r0), accepting: nullable(r0), say: `Start with the expression itself, d0 = ${key(r0)}${nullable(r0) ? ' (accepting: it matches ε)' : ''}.` });
    for (let i = 0; i < order.length; i++) {
      const x = order[i], from = 'd' + i;
      for (const c of sigma) {
        const rawD = RE.derivative(x, c, true), simp = RE.canon(rawD);
        const [n, fresh] = add(simp);
        if (names.size > max) throw new Error(`More than ${max} derivatives: the expression is too large to explore.`);
        trans.push({ from, sym: c, to: n });
        trace.push({ kind: 'derivative', from, sym: c, raw: key(rawD), regex: key(simp), to: n, fresh, accepting: nullable(simp),
          say: `∂${c}(${key(x)}) = ${key(rawD)}${key(rawD) !== key(simp) ? `, which simplifies to ${key(simp)}` : ''}${fresh ? ` — new state ${n}${nullable(simp) ? ', accepting' : ''}` : ` = ${n}`}.` });
      }
    }
    const fa = FA.make({ states: order.map((_, i) => 'd' + i), alphabet: sigma, start: 'd0', accept: order.map((x, i) => (nullable(x) ? 'd' + i : null)).filter(Boolean), trans });
    trace.push({ kind: 'done', say: `${order.length} distinct derivative${order.length === 1 ? '' : 's'}: the DFA has that many states.` });
    return { fa, labels, trace };
  };

  // ---------------------------------------------------------------- matching

  // Match by derivatives: after each symbol, the expression for "what may still follow".
  RE.match = function (r, w, opts = {}) {
    r = ast(r, opts);
    if (opts.method === 'nfa') { const m = RE.thompson(r, opts).fa; const run = FA.run(m, w); return { matched: run.accepted, trace: run.trace, fa: m }; }
    let cur = RE.canon(r);
    const trace = [{ kind: 'start', regex: key(cur), pos: 0, say: `To match ${showW(w)} against ${key(cur)}, take one derivative per symbol.` }];
    const s = chars(w);
    for (let i = 0; i < s.length; i++) {
      cur = RE.canon(RE.derivative(cur, s[i]));
      trace.push({ kind: 'step', sym: s[i], pos: i + 1, regex: key(cur), say: cur.t === 'empty' ? `After ${s[i]} the derivative is ∅: no completion can match.` : `After ${s[i]}, what remains to match is ${key(cur)}.` });
      if (cur.t === 'empty') break;
    }
    const matched = nullable(cur);
    trace.push({ kind: 'end', matched, say: matched ? `${key(cur)} matches ε, so ${showW(w)} matches.` : `${showW(w)} does not match${cur.t === 'empty' ? '' : `: ${key(cur)} does not match ε`}.` });
    return { matched, trace };
  };
  RE.test = (r, w, opts) => RE.matcher(r, opts)(w);
  // A fast membership function (Thompson's NFA, determinised lazily as strings arrive).
  RE.matcher = function (r, opts = {}) {
    r = ast(r, opts);
    return FA.acceptor(RE.thompson(r, opts).fa);
  };

  // ---------------------------------------------------------------- Thompson

  // Each node becomes a fragment with one start and one accepting state, glued with ε-moves. States
  // are numbered in creation order. Each fragment is traced with the states and moves it adds.
  RE.thompson = function (r, opts = {}) {
    r = ast(r, opts);
    let n = 0;
    const trans = [], trace = [], states = [];
    const fresh = () => { const q = 's' + n++; states.push(q); return q; };
    const E = (from, to, sym = '') => { const e = { from, sym, to }; trans.push(e); return e; };
    const go = (r) => {
      const t0 = trans.length;
      let f;
      switch (r.t) {
        case 'empty': { const s = fresh(), a = fresh(); f = { s, a }; break; }
        case 'eps': { const s = fresh(), a = fresh(); E(s, a); f = { s, a }; break; }
        case 'sym': { const s = fresh(), a = fresh(); E(s, a, r.c); f = { s, a }; break; }
        case 'alt': { const x = go(r.a), y = go(r.b), s = fresh(), a = fresh(); E(s, x.s); E(s, y.s); E(x.a, a); E(y.a, a); f = { s, a, parts: [x, y] }; break; }
        case 'cat': { const x = go(r.a), y = go(r.b); E(x.a, y.s); f = { s: x.s, a: y.a, parts: [x, y] }; break; }
        case 'star': { const x = go(r.x), s = fresh(), a = fresh(); E(s, x.s); E(s, a); E(x.a, x.s); E(x.a, a); f = { s, a, parts: [x] }; break; }
        case 'plus': { const x = go(r.x), s = fresh(), a = fresh(); E(s, x.s); E(x.a, x.s); E(x.a, a); f = { s, a, parts: [x] }; break; }
        case 'opt': { const x = go(r.x), s = fresh(), a = fresh(); E(s, x.s); E(s, a); E(x.a, a); f = { s, a, parts: [x] }; break; }
      }
      const added = trans.slice(t0);
      const what = { empty: 'two states and no move: nothing gets through', eps: 'an ε-move', sym: `one move on ${r.c}`, alt: 'a new start that branches by ε to both, and ε-moves from both ends to a new accepting state',
        cat: 'an ε-move from the end of the first to the start of the second', star: 'ε-moves to enter, skip, loop back and leave', plus: 'ε-moves to enter, loop back and leave (no skip: at least once)', opt: 'ε-moves to enter or skip' }[r.t];
      trace.push({ kind: 'fragment', node: r.t, regex: key(r), start: f.s, accept: f.a, edges: added, parts: (f.parts || []).map((p) => ({ start: p.s, accept: p.a })), say: `${key(r)}: ${what} (start ${f.s}, end ${f.a}).` });
      return f;
    };
    const f = go(r);
    const alphabet = [...new Set([...(opts.alphabet || []), ...RE.alphabet(r)])].sort();
    return { fa: FA.make({ states, alphabet, start: f.s, accept: [f.a], trans }), trace };
  };

  // ---------------------------------------------------------------- Glushkov (position automaton)

  // Number the symbol occurrences (positions); the automaton has one state per position plus a start,
  // with no ε-moves. Moves come from first(r) (from the start) and follow(p) (from position p).
  RE.glushkov = function (r, opts = {}) {
    r = ast(r, opts);
    const pos = [], trace = [];
    const lin = (r) => {
      switch (r.t) {
        case 'sym': { pos.push(r.c); return { t: 'pos', c: r.c, i: pos.length }; }
        case 'alt': case 'cat': return { t: r.t, a: lin(r.a), b: lin(r.b) };
        case 'star': case 'plus': case 'opt': return { t: r.t, x: lin(r.x) };
        default: return r;
      }
    };
    const L = lin(r);
    const name = (i) => pos[i - 1] + i;
    trace.push({ kind: 'positions', positions: pos.map((c, i) => name(i + 1)), say: `Number the symbol occurrences: ${pos.map((c, i) => name(i + 1)).join(', ') || 'none'}.` });
    const nul = (r) => nullable(back(r));
    function back(r) { return r.t === 'pos' ? N.sym(r.c) : r.t === 'alt' || r.t === 'cat' ? { t: r.t, a: back(r.a), b: back(r.b) } : unary(r) ? { t: r.t, x: back(r.x) } : r; }
    const first = (r) => {
      switch (r.t) {
        case 'pos': return [r.i];
        case 'alt': return [...first(r.a), ...first(r.b)];
        case 'cat': return nul(r.a) ? [...first(r.a), ...first(r.b)] : first(r.a);
        case 'star': case 'plus': case 'opt': return first(r.x);
        default: return [];
      }
    };
    const last = (r) => {
      switch (r.t) {
        case 'pos': return [r.i];
        case 'alt': return [...last(r.a), ...last(r.b)];
        case 'cat': return nul(r.b) ? [...last(r.a), ...last(r.b)] : last(r.b);
        case 'star': case 'plus': case 'opt': return last(r.x);
        default: return [];
      }
    };
    const follow = pos.map(() => new Set());
    const fol = (r) => {
      switch (r.t) {
        case 'alt': fol(r.a); fol(r.b); break;
        case 'cat': fol(r.a); fol(r.b); for (const p of last(r.a)) for (const q of first(r.b)) follow[p - 1].add(q); break;
        case 'star': case 'plus': fol(r.x); for (const p of last(r.x)) for (const q of first(r.x)) follow[p - 1].add(q); break;
        case 'opt': fol(r.x); break;
      }
    };
    fol(L);
    const F = [...new Set(first(L))].sort((a, b) => a - b), La = [...new Set(last(L))].sort((a, b) => a - b), nl = nullable(r);
    trace.push({ kind: 'first', set: F.map(name), say: `first = {${F.map(name).join(', ')}}: positions that can begin a word.` });
    trace.push({ kind: 'last', set: La.map(name), nullable: nl, say: `last = {${La.map(name).join(', ')}}: positions that can end a word${nl ? '; the expression matches ε, so the start state accepts too' : ''}.` });
    pos.forEach((_, i) => {
      const f = [...follow[i]].sort((a, b) => a - b);
      trace.push({ kind: 'follow', position: name(i + 1), set: f.map(name), say: `follow(${name(i + 1)}) = {${f.map(name).join(', ')}}.` });
    });
    const trans = [];
    for (const q of F) trans.push({ from: 'i', sym: pos[q - 1], to: name(q) });
    pos.forEach((_, i) => { for (const q of [...follow[i]].sort((a, b) => a - b)) trans.push({ from: name(i + 1), sym: pos[q - 1], to: name(q) }); });
    const states = ['i', ...pos.map((_, i) => name(i + 1))];
    const alphabet = [...new Set([...(opts.alphabet || []), ...pos])].sort();
    const fa = FA.make({ states, alphabet, start: 'i', accept: [...(nl ? ['i'] : []), ...La.map(name)], trans });
    trace.push({ kind: 'done', say: `The position automaton has ${states.length} states and no ε-moves; a move into position p always reads p's symbol.` });
    return { fa, trace };
  };

  // ---------------------------------------------------------------- simplification

  // Syntactic inclusion: true only when L(x) ⊆ L(y) is certain from the shapes (never a false yes).
  function sub(x, y) {
    if (key(x) === key(y) || x.t === 'empty') return true;
    if (x.t === 'eps' && nullable(y)) return true;
    if (x.t === 'alt') return sub(x.a, y) && sub(x.b, y);
    if (y.t === 'alt' && altItems(y).some((z) => sub(x, z))) return true;
    if (y.t === 'star') {
      if (sub(x, y.x)) return true;
      if (unary(x) && sub(x.x, y.x)) return true;
      if (x.t === 'cat') return catItems(x).every((z) => sub(z, y));
      if (unary(x) && sub(x.x, y)) return true;
    }
    if (y.t === 'plus' && (sub(x, y.x) || (x.t === 'plus' && sub(x.x, y.x)))) return true;
    if (y.t === 'opt' && sub(x, y.x)) return true;
    return false;
  }
  RE.syntacticSubset = sub;

  // Each rule maps a node to a simpler one, or null when it does not apply.
  function rules(post) {
    const R = [
      ['r|∅ = r', (r) => r.t === 'alt' && (r.a.t === 'empty' || r.b.t === 'empty') ? (r.a.t === 'empty' ? r.b : r.a) : null],
      ['r∅ = ∅r = ∅', (r) => r.t === 'cat' && (isVoid(r.a) || isVoid(r.b)) ? EMPTY : null],
      ['rε = εr = r', (r) => r.t === 'cat' && (r.a.t === 'eps' || r.b.t === 'eps') ? (r.a.t === 'eps' ? r.b : r.a) : null],
      ['∅* = ε* = ε', (r) => r.t === 'star' && (r.x.t === 'eps' || r.x.t === 'empty') ? EPSN : null],
      ['ε+ = ε? = ε', (r) => (r.t === 'plus' || r.t === 'opt') && r.x.t === 'eps' ? EPSN : null],
      ['∅+ = ∅', (r) => r.t === 'plus' && r.x.t === 'empty' ? EMPTY : null],
      ['∅? = ε', (r) => r.t === 'opt' && r.x.t === 'empty' ? EPSN : null],
      ['(r*)* = r*', (r) => r.t === 'star' && unary(r.x) ? N.star(r.x.x) : null],
      ['(r*)+ = (r*)? = r*', (r) => (r.t === 'plus' || r.t === 'opt') && r.x.t === 'star' ? r.x : null],
      ['(r+)+ = r+', (r) => r.t === 'plus' && r.x.t === 'plus' ? r.x : null],
      ['(r?)? = r?', (r) => r.t === 'opt' && r.x.t === 'opt' ? r.x : null],
      ['(r+)? = (r?)+ = r*', (r) => (r.t === 'opt' && r.x.t === 'plus') || (r.t === 'plus' && r.x.t === 'opt') ? N.star(r.x.x) : null],
      ['r? = r when r matches ε', (r) => r.t === 'opt' && nullable(r.x) ? r.x : null],
      ['r|r = r', (r) => {
        if (r.t !== 'alt') return null;
        const xs = altItems(r), seen = new Set(), out = xs.filter((x) => { const k = key(x); if (seen.has(k)) return false; seen.add(k); return true; });
        return out.length < xs.length ? altOf(out) : null;
      }],
      ['r|s = s when r ⊆ s', (r) => {
        if (r.t !== 'alt') return null;
        const xs = altItems(r);
        for (let i = 0; i < xs.length; i++) for (let j = 0; j < xs.length; j++) if (i !== j && key(xs[i]) !== key(xs[j]) && sub(xs[i], xs[j])) return altOf(xs.filter((_, k) => k !== i));
        return null;
      }],
      ['(ε|r)* = r*', (r) => {
        if (r.t !== 'star' || r.x.t !== 'alt') return null;
        const xs = altItems(r.x), ys = xs.filter((x) => x.t !== 'eps');
        return ys.length < xs.length ? N.star(altOf(ys)) : null;
      }],
      ['(r|s*)* = (r|s)*', (r) => {
        if (r.t !== 'star' || r.x.t !== 'alt') return null;
        const xs = altItems(r.x);
        return xs.some(unary) ? N.star(altOf(xs.map((x) => (unary(x) ? x.x : x)))) : null;
      }],
      ['(r*s*)* = (r|s)*', (r) => {
        if (r.t !== 'star' || r.x.t !== 'cat') return null;
        const xs = catItems(r.x);
        return xs.every((x) => x.t === 'star' || x.t === 'opt') ? N.star(altOf(xs.map((x) => x.x))) : null;
      }],
      ['r*r* = r*', (r) => {
        if (r.t !== 'cat') return null;
        const xs = catItems(r);
        for (let i = 0; i + 1 < xs.length; i++) {
          const a = xs[i], b = xs[i + 1];
          if (a.t === 'star' && (b.t === 'star' || b.t === 'opt') && sub(b.x, a)) return catOf([...xs.slice(0, i + 1), ...xs.slice(i + 2)]);
          if (b.t === 'star' && a.t === 'opt' && sub(a.x, b)) return catOf([...xs.slice(0, i), ...xs.slice(i + 1)]);
        }
        return null;
      }],
      ['rs|rt = r(s|t)', (r) => factor(r, false)],
      ['sr|tr = (s|t)r', (r) => factor(r, true)],
    ];
    if (post) {
      R.push(['rr* = r*r = r+', (r) => {
        if (r.t !== 'cat') return null;
        const xs = catItems(r);
        for (let i = 0; i + 1 < xs.length; i++) {
          const a = xs[i], b = xs[i + 1];
          if (b.t === 'star' && key(a) === key(b.x)) return catOf([...xs.slice(0, i), N.plus(a), ...xs.slice(i + 2)]);
          if (a.t === 'star' && key(b) === key(a.x)) return catOf([...xs.slice(0, i), N.plus(b), ...xs.slice(i + 2)]);
        }
        return null;
      }]);
      R.push(['ε|r = r?', (r) => {
        if (r.t !== 'alt') return null;
        const xs = altItems(r);
        if (!xs.some((x) => x.t === 'eps')) return null;
        const ys = xs.filter((x) => x.t !== 'eps');
        if (ys.some(nullable)) return altOf(ys);
        return N.opt(altOf(ys));
      }]);
    } else {
      R.push(['ε|r = r when r matches ε', (r) => {
        if (r.t !== 'alt') return null;
        const xs = altItems(r);
        if (!xs.some((x) => x.t === 'eps')) return null;
        const ys = xs.filter((x) => x.t !== 'eps');
        return ys.some(nullable) ? altOf(ys) : null;
      }]);
    }
    return R;
  }
  // Pull a common first (or last) factor out of two members of a union.
  function factor(r, fromEnd) {
    if (r.t !== 'alt') return null;
    const xs = altItems(r);
    for (let i = 0; i < xs.length; i++) for (let j = i + 1; j < xs.length; j++) {
      let a = catItems(xs[i]), b = catItems(xs[j]);
      if (fromEnd) { a = a.slice().reverse(); b = b.slice().reverse(); }
      let k = 0;
      while (k < a.length && k < b.length && key(a[k]) === key(b[k])) k++;
      if (!k || (k === a.length && k === b.length)) continue;
      const restA = a.slice(k), restB = b.slice(k);
      const order = (l) => (fromEnd ? l.slice().reverse() : l);
      const common = catOf(order(a.slice(0, k)));
      const inner = N.alt(catOf(order(restA)), catOf(order(restB)));
      const merged = fromEnd ? N.cat(inner, common) : N.cat(common, inner);
      // only worth it when it makes the expression smaller
      if (RE.size(merged) >= RE.size(xs[i]) + RE.size(xs[j]) + 1) continue;
      const out = xs.slice();
      out.splice(j, 1);
      out[i] = merged;
      return altOf(out);
    }
    return null;
  }

  // Simplify bottom-up, applying the first rule that fits at each node until none does. Every rule
  // application is traced with the subexpression before and after. Language is always preserved.
  RE.simplify = function (r, opts = {}) {
    r = ast(r, opts);
    const R = rules(opts.plus !== 'union'), trace = opts.quiet ? null : [];
    let budget = opts.budget || 5000;
    const go = (r) => {
      if (r.t === 'alt' || r.t === 'cat') r = { t: r.t, a: go(r.a), b: go(r.b) };
      else if (unary(r)) r = { t: r.t, x: go(r.x) };
      for (const [name, f] of R) {
        if (budget <= 0) return r;
        const s = f(r);
        if (s && key(s) !== key(r)) {
          budget--;
          if (trace) trace.push({ kind: 'rule', rule: name, before: key(r), after: key(s), say: `${name}: ${key(r)} becomes ${key(s)}.` });
          return go(s);
        }
      }
      return r;
    };
    const out = go(r);
    return { ast: out, regex: RE.show(out, opts), trace: trace || [] };
  };
  const quiet = (r) => RE.simplify(r, { quiet: true }).ast;

  // ---------------------------------------------------------------- automaton → regex

  // State elimination on a generalised NFA whose moves carry regexes: add a new start and a new final
  // state, then remove the old states one at a time, rerouting p → q → r as R(p,q) R(q,q)* R(q,r).
  RE.fromFA = function (m, opts = {}) {
    if (opts.method === 'kleene') return RE.kleene(m, opts);
    const v = FA.validate(m);
    if (!v.ok) throw new Error(v.errors[0]);
    const taken = new Set(m.states), S = FA.freshName(taken, 'S'), F = FA.freshName(taken, 'F');
    const lab = new Map(), k = (p, r) => p + '\u0000' + r;
    const addLab = (p, r, x) => { const kk = k(p, r); lab.set(kk, lab.has(kk) ? quiet(N.alt(lab.get(kk), x)) : x); };
    addLab(S, m.start, EPSN);
    for (const f of m.accept) addLab(f, F, EPSN);
    for (const e of m.trans) addLab(e.from, e.to, e.sym === '' ? EPSN : N.sym(e.sym));
    const edges = () => [...lab].map(([kk, x]) => { const [from, to] = kk.split('\u0000'); return { from, to, regex: key(x) }; });
    const trace = [{ kind: 'gnfa', start: S, final: F, edges: edges(), say: `Add a new start ${S} (ε to ${m.start}) and a new final ${F} (ε from ${m.accept.join(', ') || 'no state: the language is empty'}); parallel moves become one union.` }];
    let left = m.states.slice();
    const degree = (q) => { let i = 0, o = 0; for (const kk of lab.keys()) { const [p, r] = kk.split('\u0000'); if (p !== q && r === q) i++; if (p === q && r !== q) o++; } return i * o; };
    while (left.length) {
      let q;
      if (opts.order) q = opts.order.find((x) => left.includes(x)) || left[0];
      else if (opts.heuristic === false) q = left[0];
      else q = left.reduce((best, x) => (degree(x) < degree(best) ? x : best), left[0]);
      left = left.filter((x) => x !== q);
      const loop = lab.get(k(q, q));
      const ins = [], outs = [];
      for (const [kk, x] of lab) { const [p, r] = kk.split('\u0000'); if (p !== q && r === q) ins.push([p, x]); if (p === q && r !== q) outs.push([r, x]); }
      const updates = [];
      for (const [p, a] of ins) for (const [r, b] of outs) {
        const through = quiet(catOf([a, ...(loop ? [N.star(loop)] : []), b]));
        const old = lab.get(k(p, r));
        const nu = old ? quiet(N.alt(old, through)) : through;
        updates.push({ from: p, to: r, old: old ? key(old) : null, through: key(through), regex: key(nu), ast: nu });
      }
      for (const kk of [...lab.keys()]) { const [p, r] = kk.split('\u0000'); if (p === q || r === q) lab.delete(kk); }
      for (const u of updates) { lab.set(k(u.from, u.to), u.ast); delete u.ast; }
      trace.push({ kind: 'eliminate', state: q, loop: loop ? key(loop) : null, updates, edges: edges(),
        say: `Remove ${q}${loop ? ` (its loop ${key(loop)} becomes (${key(loop)})*)` : ''}: ${updates.length ? updates.map((u) => `${u.from} → ${u.to} gets ${u.regex}`).join('; ') : 'no path passes through it'}.` });
    }
    const fin = lab.get(k(S, F)) || EMPTY;
    const res = RE.simplify(fin, opts);
    trace.push({ kind: 'done', regex: res.regex, say: `Only ${S} → ${F} is left: the expression is ${res.regex}.` });
    return { regex: res.regex, ast: res.ast, trace };
  };

  // Kleene's construction: R[i][j]^k is the set of words leading from state i to state j through
  // intermediate states numbered < k. R^k_ij = R^{k-1}_ij | R^{k-1}_ik (R^{k-1}_kk)* R^{k-1}_kj.
  // The trace shows the whole table after each k (expressions simplified as they go).
  RE.kleene = function (m, opts = {}) {
    const v = FA.validate(m);
    if (!v.ok) throw new Error(v.errors[0]);
    const Q = m.states, n = Q.length;
    if (n > 9) throw new Error('Kleene\'s table is shown for at most 9 states; use state elimination instead.');
    let R = Q.map((p) => Q.map((q) => {
      const syms = m.trans.filter((e) => e.from === p && e.to === q).map((e) => (e.sym === '' ? EPSN : N.sym(e.sym)));
      if (p === q) syms.unshift(EPSN);
      return quiet(altOf(syms));
    }));
    const snap = () => R.map((row) => row.map(key));
    const trace = [{ kind: 'table', k: 0, cells: snap(), states: Q, say: 'k = 0: R_ij is the union of the symbols on moves from i to j (plus ε when i = j).' }];
    for (let kk = 0; kk < n; kk++) {
      const P = R;
      R = Q.map((_, i) => Q.map((_, j) => quiet(N.alt(P[i][j], catOf([P[i][kk], N.star(P[kk][kk]), P[kk][j]])))));
      trace.push({ kind: 'table', k: kk + 1, via: Q[kk], cells: snap(), states: Q, say: `k = ${kk + 1}: paths may now pass through ${Q[kk]}.` });
    }
    const s = Q.indexOf(m.start);
    const fin = quiet(altOf(m.accept.map((f) => R[s][Q.indexOf(f)])));
    const res = RE.simplify(fin, opts);
    trace.push({ kind: 'done', regex: res.regex, say: `The expression is the union of R_{${m.start},f} over accepting f: ${res.regex}.` });
    return { regex: res.regex, ast: res.ast, table: snap(), trace };
  };

  // ---------------------------------------------------------------- conversions and comparisons

  RE.toNFA = (r, opts = {}) => (opts.method === 'glushkov' ? RE.glushkov(r, opts) : RE.thompson(r, opts));
  RE.toDFA = (r, opts = {}) => (opts.method === 'subset' ? FA.subset(RE.thompson(r, opts).fa) : RE.derivativeDFA(r, opts));
  RE.minimalDFA = (r, opts = {}) => FA.minimizeHopcroft(RE.toDFA(r, opts).fa);

  // Equivalence of two regexes through their automata, with the shortest counterexample.
  RE.equivalent = function (r, s, opts = {}) {
    const a = ast(r, opts), b = ast(s, opts);
    const sigma = [...new Set([...RE.alphabet(a), ...RE.alphabet(b), ...(opts.alphabet || [])])].sort();
    const res = FA.equivalent(RE.thompson(a, { alphabet: sigma }).fa, RE.thompson(b, { alphabet: sigma }).fa);
    return { equal: res.equal, counterexample: res.counterexample, matchedBy: res.equal ? null : res.acceptedBy === 'A' ? 'first' : 'second' };
  };

  // Strings matched, in shortlex order (through the derivative DFA).
  RE.enumerate = (r, opts = {}) => FA.enumerate(RE.thompson(r, opts).fa, opts);

  // ---------------------------------------------------------------- random expressions (tests, presets)

  RE.random = function (rnd, { alphabet = ['a', 'b'], size = 6, eps = 0.05, empty = 0.02 } = {}) {
    const go = (n) => {
      if (n <= 1) { const u = rnd(); return u < empty ? EMPTY : u < empty + eps ? EPSN : N.sym(alphabet[Math.floor(rnd() * alphabet.length)]); }
      const u = rnd();
      if (u < 0.3) { const k = 1 + Math.floor(rnd() * (n - 1)); return N.alt(go(k), go(n - k)); }
      if (u < 0.65) { const k = 1 + Math.floor(rnd() * (n - 1)); return N.cat(go(k), go(n - k)); }
      if (u < 0.85) return N.star(go(n - 1));
      if (u < 0.93) return N.plus(go(n - 1));
      return N.opt(go(n - 1));
    };
    return go(size);
  };
})();
