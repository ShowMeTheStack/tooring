// Regular expressions and the regular-language tools (pumping game, transducers, two-way DFAs, KMP,
// lexers), checked against brute-force oracles on seeded random inputs.
import { load, rng, harness } from './load.mjs';

const T = load();
const { FA, RE, Found: F, Pump, KMP, Lexer, Transducer: Tr, TwoWay: TW } = T;
const t = harness('regex');
const R = rng(1017);

// ---------------------------------------------------------------- oracle: the language up to length n

// The set of strings of length ≤ n matched by an AST, computed by set operations alone.
function langUpTo(r, n) {
  const cat = (A, B) => { const out = new Set(); for (const x of A) for (const y of B) if (x.length + y.length <= n) out.add(x + y); return out; };
  // A* as a fixed point: keep appending members of A until nothing new of length ≤ n appears
  const star = (A) => {
    const out = new Set(['']);
    for (let grew = true; grew;) { grew = false; for (const w of cat(out, A)) if (!out.has(w)) { out.add(w); grew = true; } }
    return out;
  };
  const go = (r) => {
    switch (r.t) {
      case 'empty': return new Set();
      case 'eps': return new Set(['']);
      case 'sym': return new Set(n >= 1 ? [r.c] : []);
      case 'alt': return new Set([...go(r.a), ...go(r.b)]);
      case 'cat': return cat(go(r.a), go(r.b));
      case 'star': return star(go(r.x));
      case 'plus': { const A = go(r.x); return cat(A, star(A)); }
      case 'opt': return new Set(['', ...go(r.x)]);
    }
  };
  return go(r);
}
const SIG = ['a', 'b'];
const W7 = F.sigmaStar(SIG, 7);
const agrees = (acc, L, ws = W7) => ws.every((w) => acc(w) === L.has(w));
// the same language up to length 7 (as sets)
const sameSet = (A, B) => A.size === B.size && [...A].every((w) => B.has(w));

// ---------------------------------------------------------------- parser and printer

{
  const ok = ['a', 'ab|c', '(a|b)*abb', 'a+b?', '[a-c]x', '()', 'ε', '∅', 'a**', '\\(\\)', '(a|ε)(b|∅)*', 'a b  c'];
  for (const s of ok) {
    const c = RE.check(s);
    t.ok(c.ok, 'parses ' + s);
    if (c.ok) t.eq(RE.show(RE.parse(RE.show(c.ast))), RE.show(c.ast), 'show is stable ' + s);
  }
  const bad = [['', 'empty'], ['a|', 'missing'], ['(ab', 'never closed'], ['ab)', 'no matching'], ['*a', 'nothing to repeat'], ['a||b', 'Nothing before'], ['[ab', 'never closed'], ['.', 'alphabet'], ['[b-a]', 'backwards'], ['a\\', 'backslash']];
  for (const [s, msg] of bad) { const c = RE.check(s); t.ok(!c.ok && c.error.includes(msg), `rejects ${JSON.stringify(s)} with "${msg}" (got ${c.error})`); }
  t.eq(RE.show(RE.parse('a+b', { plus: 'union' })), 'a|b', 'plus as union');
  t.eq(RE.show(RE.parse('a+b')), 'a+b', 'plus as one-or-more');
  t.eq(RE.show(RE.parse('.b', { alphabet: ['a', 'b', 'c'] })), '(a|b|c)b', 'dot uses the alphabet');
  t.eq(RE.show(RE.parse('[^a]', { alphabet: ['a', 'b', 'c'] })), 'b|c', 'negated class');
  t.eq(RE.show(RE.parse('(a)(b)((c))')), 'abc', 'minimal parentheses');
  t.eq(RE.show(RE.parse('(a|b)(c|d)*')), '(a|b)(c|d)*', 'needed parentheses kept');
  t.eq(RE.show(RE.parse('(ab)*|c')), '(ab)*|c', 'star of a group');
  t.eq(RE.show(RE.parse('a+?'), { plus: 'union' }), 'ε+aa*', 'union mode prints r+ and r?');
  t.eq(RE.show(RE.parse('(a+?)b'), { plus: 'union' }), '(ε+aa*)b', 'union mode brackets r? inside a concatenation');
}

// ---------------------------------------------------------------- random expressions: every construction

for (let k = 0; k < +(process.env.N || 500); k++) {
  const r = RE.random(R, { alphabet: SIG, size: 2 + R.int(9) });
  const L = langUpTo(r, 7), src = RE.show(r);
  // printing and parsing round trip, in both syntaxes
  const back = RE.parse(src);
  t.eq(RE.show(back), src, 'round trip ' + src);
  const u = RE.show(r, { plus: 'union' });
  t.ok(sameSet(langUpTo(RE.parse(u, { plus: 'union' }), 7), L), 'union syntax round trip ' + u);
  t.eq(RE.nullable(r), L.has(''), 'nullable ' + src);
  t.eq(RE.isEmptyLang(r), langUpTo(r, 12).size === 0, 'isEmptyLang ' + src);
  // Thompson, Glushkov, derivatives, subset: all agree with the oracle on strings up to length 7
  const th = RE.thompson(r, { alphabet: SIG }), gl = RE.glushkov(r, { alphabet: SIG }), dv = RE.derivativeDFA(r, { alphabet: SIG });
  t.ok(agrees(FA.acceptor(th.fa), L), 'Thompson ' + src);
  t.ok(agrees(FA.acceptor(gl.fa), L), 'Glushkov ' + src);
  t.ok(FA.kind(gl.fa) !== 'enfa' && gl.fa.states.length === 1 + src.replace(/[^ab]/g, '').length, 'Glushkov has one state per position');
  t.ok(agrees(FA.acceptor(dv.fa), L), 'derivative DFA ' + src);
  t.ok(FA.isDFA(dv.fa) && FA.isComplete(dv.fa), 'derivative DFA is a complete DFA');
  t.ok(FA.equivalent(dv.fa, th.fa).equal, 'derivatives ≡ Thompson ' + src);
  const sub = FA.subset(th.fa).fa;
  t.ok(agrees(FA.acceptor(sub), L), 'Thompson + subset ' + src);
  t.ok(th.trace.length === RE.size(r), 'one fragment per node');
  // canonical form and simplification keep the language; simplification never grows the expression
  t.ok(sameSet(langUpTo(RE.canon(r), 7), L), 'canon ' + src);
  const s = RE.simplify(r);
  t.ok(sameSet(langUpTo(s.ast, 7), L), `simplify ${src} → ${s.regex}`);
  t.ok(RE.size(s.ast) <= RE.size(r), `simplify does not grow ${src} → ${s.regex}`);
  t.ok(FA.equivalent(RE.thompson(s.ast, { alphabet: SIG }).fa, th.fa).equal, 'simplify exact ' + src);
  // regex → NFA → DFA → regex round trips (state elimination with and without the heuristic, Kleene)
  const dfa = FA.minimize(sub).fa;
  for (const [how, res] of [['elim', RE.fromFA(dfa)], ['elim-order', RE.fromFA(dfa, { heuristic: false })], ['elim-nfa', RE.fromFA(th.fa)], ...(dfa.states.length <= 5 ? [['kleene', RE.kleene(dfa)]] : [])]) {
    t.ok(sameSet(langUpTo(res.ast, 7), L), `${how} round trip ${src} → ${res.regex}`);
    t.ok(FA.equivalent(RE.thompson(res.ast, { alphabet: SIG }).fa, dfa).equal, `${how} exact ${src}`);
  }
  // matching with a trace, by derivatives and by the NFA
  for (const w of W7.slice(0, 31)) {
    t.eq(RE.match(r, w).matched, L.has(w), `match ${src} on ${w}`);
    if (w.length <= 3) t.eq(RE.match(r, w, { method: 'nfa' }).matched, L.has(w), 'nfa match');
  }
  t.ok(agrees(RE.matcher(r, { alphabet: SIG }), L), 'matcher');
}

// regex equivalence: counterexamples are real and shortest
for (let k = 0; k < 300; k++) {
  const a = RE.random(R, { alphabet: SIG, size: 2 + R.int(6) }), b = R() < 0.3 ? RE.simplify(a).ast : RE.random(R, { alphabet: SIG, size: 2 + R.int(6) });
  const La = langUpTo(a, 7), Lb = langUpTo(b, 7);
  const e = RE.equivalent(a, b);
  const first = W7.find((w) => La.has(w) !== Lb.has(w));
  if (e.equal) t.ok(first === undefined, 'equal regexes agree');
  else if (first !== undefined) t.eq(e.counterexample, first, 'regex counterexample is the shortlex-least');
  else t.ok(e.counterexample.length > 7 && langUpTo(a, e.counterexample.length).has(e.counterexample) !== langUpTo(b, e.counterexample.length).has(e.counterexample), 'long counterexample is real');
}

// known identities hold, known non-identities fail with the expected witness
{
  const same = [['(a|b)*', '(a*b*)*'], ['(ab)*a', 'a(ba)*'], ['a*a*', 'a*'], ['(a*b)*a*', '(a|b)*'], ['ε|aa*', 'a*'], ['∅*', 'ε'], ['a∅|b', 'b'], ['(a+)?', 'a*']];
  for (const [x, y] of same) t.ok(RE.equivalent(x, y).equal, `${x} ≡ ${y}`);
  t.eq(RE.equivalent('(ab)*', '(ba)*').counterexample, 'ab', '(ab)* vs (ba)*');
  t.eq(RE.equivalent('a*b*', '(a|b)*').counterexample, 'ba', 'a*b* vs (a|b)*');
  t.eq(RE.equivalent('a', 'ε').counterexample, '', 'ε is the shortest counterexample');
  const s = RE.simplify('(a|ε)*|∅b|(b*)*');
  t.ok(s.trace.length > 0 && s.trace.every((x) => x.rule && x.before && x.after), 'simplify traces each rule');
  t.eq(RE.simplify('ab|ac').regex, 'a(b|c)', 'left factoring');
  t.eq(RE.simplify('ba|ca').regex, '(b|c)a', 'right factoring');
  t.eq(RE.simplify('(a*)*').regex, 'a*', '(r*)* = r*');
  t.eq(RE.simplify('ε|a*').regex, 'a*', 'ε|r* = r*');
  t.eq(RE.simplify('aa*').regex, 'a+', 'rr* = r+');
  t.eq(RE.simplify('aa*', { plus: 'union' }).regex, 'aa*', 'no r+ in union syntax');
  t.eq(RE.simplify('a|(a|b)*').regex, '(a|b)*', 'absorbed by a star');
  const d = RE.derivativeDFA('(a|b)*abb');
  t.eq(d.fa.states.length, 4, 'derivatives of (a|b)*abb: 4 states');
  t.ok(d.trace.filter((x) => x.kind === 'derivative').every((x) => x.raw && x.regex), 'derivative trace shows raw and simplified');
  const el = RE.fromFA(d.fa);
  t.ok(el.trace.filter((x) => x.kind === 'eliminate').length === 4, 'one elimination step per state');
  const kl = RE.kleene(FA.minimize(d.fa).fa);
  t.eq(kl.trace.filter((x) => x.kind === 'table').length, 5, 'Kleene table for k = 0..4');
  const emptyFA = FA.parse('start p\np -a-> p').fa;
  t.eq(RE.fromFA(emptyFA).regex, '∅', 'no accepting state gives ∅');
  t.eq(RE.kleene(emptyFA).regex, '∅', 'Kleene: no accepting state gives ∅');
}

// ---------------------------------------------------------------- pumping game

{
  for (const lang of Pump.catalogue) {
    const ws = F.sigmaStar(lang.alphabet, lang.alphabet.length === 1 ? 16 : lang.alphabet.length === 2 ? 9 : 6);
    if (lang.regular) {
      // the regex or DFA of the entry agrees with its membership test
      const d = Pump.dfa(lang), acc = FA.acceptor(d);
      t.ok(ws.every((w) => acc(w) === lang.member(w)), 'catalogue DFA matches predicate: ' + lang.id);
      const p = Pump.lengthFor(lang);
      // the adversary survives every long-enough string (up to a bound)
      const longs = ws.filter((w) => w.length >= p && w.length <= p + 4 && lang.member(w)).slice(0, 25);
      for (const s of longs) {
        const g = Pump.game(lang); g.pickP();
        t.ok(g.pickString(s).ok, 'string accepted by the game');
        const sp = g.pickSplit();
        t.ok(sp.survives, `adversary survives on ${lang.id} with ${s}`);
        for (const i of [0, 2, 3]) t.eq(g.pickI(i).winner, 'adversary', 'regular: pumping stays in L');
      }
      if (lang.id === 'anbn-small') t.eq(longs.length, 0, 'finite language: no string reaches the pumping length');
      // the Myhill–Nerode explorer sees exactly the minimal DFA's classes (catalogue consistency)
      const ex = FA.nerodeExplore(lang.member, lang.alphabet, F.sigmaStar(lang.alphabet, lang.alphabet.length === 1 ? 8 : 5), lang.alphabet.length === 1 ? 8 : 6);
      t.eq(ex.classes.length, d.states.length, 'Nerode explorer = minimal DFA size: ' + lang.id);
    } else {
      for (let p = 1; p <= Math.min(6, lang.maxP || 6); p++) {
        const s = lang.witness(p);
        t.ok(lang.member(s) && Array.from(s).length >= p, `witness is a long string of L: ${lang.id} p=${p}`);
        t.ok(Pump.wins(lang, p, s).wins, `witness defeats every split: ${lang.id} p=${p}`);
        const g = Pump.game(lang, { p });
        g.pickP();
        t.ok(g.pickString(s).ok, 'game takes the witness');
        const sp = g.pickSplit();
        t.ok(!sp.survives && sp.considered === (p * (p + 1)) / 2, 'adversary cannot survive: ' + lang.id);
        t.eq(g.pickI(g.winningI()).winner, 'student', 'student wins with the suggested i: ' + lang.id);
      }
      // a short string or one outside L is refused
      const g = Pump.game(lang, { p: 3 }); g.pickP();
      const outside = F.sigmaStar(lang.alphabet, 4).find((w) => !lang.member(w) && w.length >= 3);
      if (outside) t.ok(!g.pickString(outside).ok, 'string outside L refused');
      // members agree with themselves on simple sanity: some strings in, some out
      const inL = ws.filter(lang.member).length;
      t.ok(inL > 0 && inL < ws.length, 'predicate is non-trivial: ' + lang.id);
    }
  }
  // a losing string choice: for aⁿbⁿ with p = 3, the string ab... is too short; and (ab)… is not in L
  const g = Pump.game('anbn', { p: 3 }); g.pickP();
  t.ok(!g.pickString('ab').ok, 'too short');
  t.ok(g.pickString('aaabbb').ok, 'aaabbb ok');
  const sp = g.pickSplit();
  t.ok(!sp.survives, 'aⁿbⁿ: adversary loses');
  const fw = Pump.findWinningString('anbn', 3);
  t.ok(fw !== null && Pump.wins('anbn', 3, fw).wins, 'brute-force winning string for aⁿbⁿ, p = 3: ' + fw);
  t.ok(Pump.findWinningString('even-a', 2) === null, 'no winning string for a regular language');
}

// ---------------------------------------------------------------- Moore and Mealy

for (let k = 0; k < 150; k++) {
  const n = 1 + R.int(4), states = Array.from({ length: n }, (_, i) => 'q' + i), inputs = ['a', 'b'], outs = ['0', '1', 'x'];
  const moore = { states, inputs, start: 'q0', trans: [], out: {} };
  for (const q of states) { moore.out[q] = R.pick(outs); for (const a of inputs) moore.trans.push({ from: q, sym: a, to: R.pick(states) }); }
  const mealy = { states, inputs, start: 'q0', trans: [] };
  for (const q of states) for (const a of inputs) mealy.trans.push({ from: q, sym: a, to: R.pick(states), out: R.pick(outs) });
  const toMealy = Tr.mooreToMealy(moore).mealy, toMoore = Tr.mealyToMoore(mealy).moore, init = toMoore.out[toMoore.start];
  for (const w of F.sigmaStar(inputs, 6)) {
    const mo = Tr.runMoore(moore, w).output, me = Tr.runMealy(toMealy, w).output;
    t.eq(me, mo.slice(1), 'Moore → Mealy');
    t.eq(Tr.runMoore(toMoore, w).output, init + Tr.runMealy(mealy, w).output, 'Mealy → Moore');
    t.eq(mo.length, w.length + 1, 'Moore output length');
  }
}

// ---------------------------------------------------------------- two-way DFAs

for (const [name, m] of Object.entries(TW.examples)) {
  for (const w of F.sigmaStar(m.alphabet, 8)) {
    const r = TW.run(m, w);
    t.eq(r.accepted, m.member(w), `two-way ${name} on ${w}`);
    t.ok(r.trace.every((s) => s.say), 'two-way trace');
  }
}
for (let k = 0; k < 200; k++) {
  // random two-way machines: every run halts (accept, reject, fall off, or a detected loop)
  const states = ['p', 'q', 'r', 'acc', 'rej'], syms = ['⊢', '⊣', 'a', 'b'], delta = [];
  for (const q of ['p', 'q', 'r']) for (const c of syms) if (R() < 0.9) delta.push({ from: q, sym: c, to: R.pick(states), move: c === '⊢' ? 'R' : c === '⊣' ? 'L' : R.pick(['L', 'R']) });
  const m = { states, alphabet: ['a', 'b'], start: 'p', accept: 'acc', reject: 'rej', delta };
  for (const w of F.sigmaStar(['a', 'b'], 4)) {
    const r = TW.run(m, w);
    t.ok(r.trace[r.trace.length - 1].kind === 'halt' && !r.trace[r.trace.length - 1].limit, 'two-way run always ends');
    // the head never leaves the tape between moves
    t.ok(r.trace.filter((s) => s.kind === 'move').every((s) => s.head >= 0 && s.head < w.length + 2), 'head stays on the tape');
  }
}

// ---------------------------------------------------------------- KMP

for (let k = 0; k < 200; k++) {
  const alpha = R() < 0.5 ? ['a', 'b'] : ['a', 'b', 'c'];
  const pat = Array.from({ length: 1 + R.int(6) }, () => R.pick(alpha)).join('');
  const { fail } = KMP.failure(pat);
  // brute-force borders
  const border = (s) => { for (let l = s.length - 1; l > 0; l--) if (s.slice(0, l) === s.slice(s.length - l)) return l; return 0; };
  t.eq(fail, Array.from(pat).map((_, j) => border(pat.slice(0, j + 1))), 'failure function ' + pat);
  const d = KMP.dfa(pat, alpha).fa;
  t.ok(FA.isComplete(d) && d.states.length === pat.length + 1, 'KMP DFA is complete with |p|+1 states');
  t.ok(FA.equivalent(d, RE.thompson('(' + alpha.join('|') + ')*' + pat).fa).equal, 'KMP DFA ≡ Σ*p');
  t.eq(FA.minimize(d).fa.states.length, pat.length + 1, 'KMP DFA is minimal');
  for (let j = 0; j < 5; j++) {
    const text = Array.from({ length: R.int(20) }, () => R.pick(alpha)).join('');
    const naive = [];
    for (let i = 0; i + pat.length <= text.length; i++) if (text.slice(i, i + pat.length) === pat) naive.push(i);
    t.eq(KMP.search(pat, text).matches, naive, `KMP search ${pat} in ${text}`);
  }
}

// ---------------------------------------------------------------- lexer generator

{
  const rules = [
    { name: 'IF', regex: 'if' }, { name: 'IN', regex: 'in' }, { name: 'ID', regex: '[a-z][a-z0-9]*' }, { name: 'NUM', regex: '[0-9]+' },
    { name: 'OP', regex: '<|<=|=|==|!=' }, { name: 'WS', regex: '\\ +', skip: true },
  ];
  const lx = Lexer.build(rules);
  t.ok(lx.trace.some((s) => s.kind === 'tag' && s.rules.length > 1), 'priority conflicts are traced');
  const r = lx.tokenize('if x1<=42 in ifs == !');
  t.eq(r.tokens.map((x) => x.name + ':' + x.text), ['IF:if', 'ID:x1', 'OP:<=', 'NUM:42', 'IN:in', 'ID:ifs', 'OP:=='], 'tokenise');
  t.eq(r.errors.map((e) => e.ch), ['!'], 'lexical error reported');
  // brute force: at each position the longest prefix matching any rule, ties to the first rule
  const ms = rules.map((x) => RE.matcher(x.regex));
  const alphabet = ['i', 'f', 'n', 'x', '1', '0', '<', '=', '!', ' '];
  for (let k = 0; k < 400; k++) {
    const s = Array.from({ length: R.int(14) }, () => R.pick(alphabet)).join('');
    const want = [], errs = [];
    for (let pos = 0; pos < s.length;) {
      let best = null;
      for (let end = s.length; end > pos && !best; end--) { const i = ms.findIndex((m) => m(s.slice(pos, end))); if (i >= 0) best = { i, end }; }
      if (!best) { errs.push(pos); pos++; continue; }
      if (!rules[best.i].skip) want.push(rules[best.i].name + ':' + s.slice(pos, best.end));
      pos = best.end;
    }
    const got = lx.tokenize(s);
    t.eq(got.tokens.map((x) => x.name + ':' + x.text), want, 'lexer = brute force on ' + JSON.stringify(s));
    t.eq(got.errors.map((e) => e.pos), errs, 'lexer errors = brute force');
  }
  let threw = false;
  try { Lexer.build([{ name: 'E', regex: 'a*' }]); } catch (e) { threw = /empty string/.test(e.message); }
  t.ok(threw, 'a rule matching ε is refused');
}

t.done();
