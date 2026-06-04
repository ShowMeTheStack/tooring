// Finite automata and foundations, checked against brute-force oracles on seeded random machines.
import { load, rng, harness } from './load.mjs';

const T = load();
const { FA, Found: F } = T;
const t = harness('fa');
const R = rng(20261017);

// ---------------------------------------------------------------- oracles (independent of fa.js)

// Simulate any machine directly on sets of states, with ε-closures by repeated scanning.
function oracle(m) {
  const close = (S) => {
    S = new Set(S);
    for (let changed = true; changed;) { changed = false; for (const e of m.trans) if (e.sym === '' && S.has(e.from) && !S.has(e.to)) { S.add(e.to); changed = true; } }
    return S;
  };
  return (w) => {
    let S = close([m.start]);
    for (const c of Array.from(w)) { const N = new Set(); for (const e of m.trans) if (e.sym === c && S.has(e.from)) N.add(e.to); S = close(N); }
    return m.accept.some((q) => S.has(q));
  };
}
const strings = (alpha, n) => F.sigmaStar(alpha, n);
const sameOn = (f, g, ws) => ws.every((w) => f(w) === g(w));
const firstDiff = (f, g, ws) => ws.find((w) => f(w) !== g(w));
const randM = (r, kind) => {
  const n = 1 + r.int(5), alphabet = r() < 0.8 ? ['a', 'b'] : ['a', 'b', 'c'];
  if (kind === 'dfa') return FA.randomDFA(r, { n, alphabet, accept: 0.4, partial: r() < 0.3 ? 0.2 : 0 });
  return FA.randomNFA(r, { n, alphabet, density: 0.15 + r() * 0.2, eps: kind === 'enfa' ? 0.15 : 0 });
};

// ---------------------------------------------------------------- foundations

{
  const S = F.sigmaStar(['a', 'b'], 4);
  t.eq(S.length, 31, 'sigmaStar size');
  t.ok(S.every((w, i) => i === 0 || F.shortlexCmp(S[i - 1], w) < 0), 'sigmaStar is in shortlex order');
  S.forEach((w, i) => { t.eq(F.nthString(['a', 'b'], i), w, 'nthString ' + i); t.eq(F.indexOfString(['a', 'b'], w), i, 'indexOfString ' + w); });
  const viaEach = [];
  F.eachString(['x', 'y', 'z'], 3, (w) => { viaEach.push(w); });
  t.eq(viaEach, F.sigmaStar(['x', 'y', 'z'], 3), 'eachString = sigmaStar');
  t.ok(F.countUpTo(2, 4) === 31n, 'countUpTo');
  t.eq(F.sigmaStar([], 3), [''], 'Σ* over ∅ alphabet');
  t.eq(F.str.substrings('aba'), ['', 'a', 'b', 'ab', 'ba', 'aba'], 'substrings');
  t.ok(F.str.isSubsequence('ab', 'xaxb') && !F.str.isSubsequence('ba', 'ab'), 'subsequence');
  t.eq(F.str.prefixes('ab'), ['', 'a', 'ab'], 'prefixes');
  t.eq(F.str.suffixes('ab'), ['ab', 'b', ''], 'suffixes');

  // concat / power / star against brute force
  for (let k = 0; k < 60; k++) {
    const A = F.lang(Array.from({ length: R.int(4) }, () => F.nthString(['a', 'b'], R.int(7))));
    const B = F.lang(Array.from({ length: R.int(4) }, () => F.nthString(['a', 'b'], R.int(7))));
    const AB = new Set(); A.forEach((x) => B.forEach((y) => AB.add(x + y)));
    t.eq(F.concat(A, B).result, F.sortShortlex([...AB]), 'concat');
    const p2 = new Set(); A.forEach((x) => A.forEach((y) => p2.add(x + y)));
    t.eq(F.power(A, 2).result, F.sortShortlex([...p2]), 'power 2');
    t.eq(F.power(A, 0).result, [''], 'power 0');
    // w ∈ A* iff w splits into pieces of A (dynamic programme)
    const star = F.star(A, 6).result, inStar = (w) => { const ok = [true]; for (let i = 1; i <= w.length; i++) ok[i] = A.some((x) => x && x.length <= i && ok[i - x.length] && w.slice(i - x.length, i) === x); return ok[w.length]; };
    t.eq(star, F.sigmaStar(['a', 'b'], 6).filter(inStar), 'star up to 6');
    t.eq(F.union(A, B), F.sortShortlex([...new Set([...A, ...B])]), 'union');
    t.ok(F.intersect(A, B).every((w) => A.includes(w) && B.includes(w)), 'intersect');
  }

  // relations: closures against reachability
  for (let k = 0; k < 80; k++) {
    const n = 1 + R.int(5), D = Array.from({ length: n }, (_, i) => 'x' + i);
    const Rel = [];
    for (const x of D) for (const y of D) if (R() < 0.25) Rel.push([x, y]);
    const tc = F.transitiveClosure(D, Rel).result;
    // (x, y) in R+ iff a path of length ≥ 1 exists
    const reach = (x) => { const seen = new Set(), st = Rel.filter((p) => p[0] === x).map((p) => p[1]); while (st.length) { const y = st.pop(); if (!seen.has(y)) { seen.add(y); Rel.filter((p) => p[0] === y).forEach((p) => st.push(p[1])); } } return seen; };
    const brute = []; D.forEach((x) => { const s = reach(x); D.forEach((y) => { if (s.has(y)) brute.push([x, y]); }); });
    t.eq(tc, brute, 'transitive closure');
    t.ok(F.rel.isTransitive(D, tc), 'closure is transitive');
    const eq = F.equivalenceClosure(D, Rel).result;
    t.ok(F.rel.isEquivalence(D, eq), 'equivalence closure is an equivalence');
    const cls = F.classes(D, eq).result;
    t.ok(F.isPartition(D, cls), 'classes form a partition');
    t.eq(F.partitionToRelation(cls).length, eq.length, 'partition ↔ relation');
    t.ok(F.refines(cls.flatMap((b) => b.map((x) => [x])), cls), 'singletons refine');
    if (!F.rel.isEquivalence(D, Rel)) t.ok(F.rel.why(D, Rel).length > 0, 'why names a failing property');
    t.ok(F.rel.isReflexive(D, F.reflexiveClosure(D, Rel).result), 'reflexive closure');
    t.ok(F.rel.isSymmetric(D, F.symmetricClosure(D, Rel).result), 'symmetric closure');
  }
  t.eq([0, 1, 2, 3, 4, 5, 6].map((n) => Number(F.bell(n))), [1, 1, 2, 5, 15, 52, 203], 'Bell numbers');
  t.eq(F.powerset(['a', 'b', 'c']).length, 8, 'powerset size');

  // diagonal: differs from every row
  for (let k = 0; k < 30; k++) {
    const rows = Array.from({ length: 8 }, () => Array.from({ length: 8 }, () => R.int(2)));
    const d = F.diagonal(rows);
    t.ok(rows.every((r, i) => r[i] !== d.diag[i]), 'diagonal differs on the diagonal');
    const f = (x) => ['p', 'q', 'r', 's'].filter(() => R() < 0.5);
    const memo = {}; const ff = (x) => (memo[x] = memo[x] || f(x));
    const c = F.cantorSet(['p', 'q', 'r', 's'], ff);
    t.ok(['p', 'q', 'r', 's'].every((x) => ff(x).includes(x) !== c.D.includes(x)), 'Cantor set differs from each f(x) at x');
  }
  const ph = F.pigeonhole(['aa', 'ab', 'ba', 'bb', 'aab'], (w) => w.length % 2);
  t.ok(ph.found && ph.pair.length === 2, 'pigeonhole finds a collision');
  t.ok(F.induction({ P: (n) => (n * (n + 1)) / 2 === Array.from({ length: n + 1 }, (_, i) => i).reduce((a, b) => a + b, 0), upto: 30 }).ok, 'induction: sum formula');
  t.eq(F.induction({ P: (n) => n * n < 50, upto: 30 }).failAt, 8, 'induction: failing claim found');
}

// ---------------------------------------------------------------- text format and validation

{
  const r = FA.parse('# a machine\nalphabet a b\nstart q0\naccept q1\nq0 -a,b-> q1\nq1 -eps-> q0\nq1 -ε-> q2\n');
  t.ok(r.ok, 'parse ok');
  t.eq(FA.kind(r.fa), 'enfa', 'kind enfa');
  t.ok(!FA.parse('q0 -a-> q1').ok, 'missing start is an error');
  t.ok(!FA.parse('start q0\nq0 -ab-> q1').ok, 'multi-char symbol is an error');
  t.ok(!FA.parse('start q0\nfoo bar').ok, 'unknown line is an error');
  t.ok(!FA.parse('start q0\nstart q1').ok, 'two starts is an error');
  const bad = { states: ['p'], alphabet: ['a'], start: 'z', accept: ['w'], trans: [{ from: 'p', sym: 'c', to: 'p' }] };
  const v = FA.validate(bad);
  t.ok(!v.ok && v.errors.length >= 2, 'validate reports unknown start/accept/symbol');
  const nd = FA.parse('start p\np -a-> p\np -a-> q').fa;
  t.ok(FA.validate(nd).ok && !FA.validate(nd, { expect: 'dfa' }).ok, 'expect dfa rejects nondeterminism');
  t.ok(FA.validate(FA.parse('start p\naccept p\np -a-> p\nq -a-> q').fa).warnings.some((w) => /Unreachable/.test(w)), 'unreachable warning');
  const ws = FA.make({ states: ['s'], alphabet: [' ', 'a'], start: 's', accept: ['s'], trans: [{ from: 's', sym: ' ', to: 's' }] });
  t.ok(FA.accepts(FA.parse(FA.format(ws)).fa, '  '), 'whitespace symbols survive the text format');
}

// ---------------------------------------------------------------- random machines

const W8 = { 2: strings(['a', 'b'], 8), 3: strings(['a', 'b', 'c'], 5) };
const W = (m) => W8[m.alphabet.length];
const W6 = { 2: strings(['a', 'b'], 6), 3: strings(['a', 'b', 'c'], 4) };
const Ws = (m) => W6[m.alphabet.length];

for (let k = 0; k < +(process.env.N || 250); k++) {
  const kind = ['dfa', 'nfa', 'enfa'][k % 3];
  const m = randM(R, kind), o = oracle(m), acc = FA.acceptor(m);
  const ws = W(m);
  t.ok(FA.validate(m).ok, 'random machine valid');
  // text round trip
  const back = FA.parse(FA.format(m));
  t.ok(back.ok && back.fa.trans.length === m.trans.length && back.fa.states.join() === m.states.join(), 'format/parse round trip ' + k);
  t.ok(sameOn(acc, o, ws), 'acceptor = oracle ' + kind);
  for (const w of Ws(m).slice(0, 40)) {
    const r = FA.run(m, w);
    t.ok(r.accepted === o(w), 'run = oracle');
    t.ok(r.trace.length >= 2 && r.trace.every((s) => s.kind && typeof s.say === 'string'), 'run trace has steps');
    const p = FA.paths(m, w, 5);
    t.ok((p.total > 0) === o(w), 'accepting paths exist iff accepted');
    for (const path of p.paths) {
      let q = m.start, i = 0, ok = true;
      for (const e of path) { if (e.from !== q) ok = false; if (e.sym) { if (w[i] !== e.sym) ok = false; i++; } q = e.to; }
      t.ok(ok && i === w.length && m.accept.includes(q), 'path is a valid accepting computation');
    }
  }
  // subset construction ≡ NFA on all strings up to length 8
  const sub = FA.subset(m);
  t.ok(FA.isComplete(sub.fa), 'subset DFA is complete');
  t.ok(sameOn(FA.acceptor(sub.fa), o, ws), 'subset ≡ NFA (≤8)');
  t.ok(sub.trace.filter((s) => s.kind === 'subset-new').length === sub.fa.states.length, 'one subset-new per DFA state');
  const sub2 = FA.subset(m, { dropEmpty: true });
  t.ok(sameOn(FA.acceptor(sub2.fa), o, ws), 'subset without ∅ ≡ NFA');
  // ε-removal
  const ne = FA.removeEps(m).fa;
  t.ok(FA.kind(ne) !== 'enfa' && sameOn(FA.acceptor(ne), o, ws), 'removeEps ≡');
  // completion and complement
  const c = FA.complete(sub2.fa).fa;
  t.ok(FA.isComplete(c) && sameOn(FA.acceptor(c), o, ws), 'complete ≡');
  const comp = FA.acceptor(FA.complement(m).fa);
  t.ok(ws.every((w) => comp(w) === !o(w)), 'complement');
  // reversal
  const rev = FA.acceptor(FA.reverse(m).fa);
  t.ok(ws.every((w) => rev(w) === o(F.str.reverse(w))), 'reverse');
  // reachability / trim
  t.ok(sameOn(FA.acceptor(FA.removeUnreachable(m).fa), o, ws), 'removeUnreachable ≡');
  t.ok(sameOn(FA.acceptor(FA.trim(m).fa), o, ws), 'trim ≡');

  // minimisation four ways
  const mins = ['table', 'moore', 'hopcroft', 'brzozowski'].map((how) => FA.minimize(m, how).fa);
  const nMin = mins[0].states.length;
  mins.forEach((d, i) => {
    t.ok(FA.isDFA(d) && FA.isComplete(d), 'minimised is a complete DFA ' + i);
    t.ok(sameOn(FA.acceptor(d), o, ws), 'minimised ≡ original ' + ['table', 'moore', 'hopcroft', 'brzozowski'][i]);
    t.eq(d.states.length, nMin, 'all methods agree on size ' + i + ' ' + FA.format(m));
    t.ok(FA.isomorphic(d, mins[0]).iso, 'minimal DFAs are isomorphic');
  });
  // minimal: no two states of the minimal DFA are equivalent (signatures over strings ≤ n differ),
  // and the size equals the number of Myhill–Nerode classes found by brute force
  {
    const d = mins[2];
    if (d.alphabet.length ** nMin < 3000) {
      const probe = strings(d.alphabet, Math.max(0, nMin - 1));
      const sigs = d.states.map((q) => { const a = FA.acceptor({ ...d, start: q }); return probe.map((w) => (a(w) ? 1 : 0)).join(''); });
      t.eq(new Set(sigs).size, d.states.length, 'minimal: every pair of states is distinguishable');
    } else for (let i = 0; i < d.states.length; i++) for (let j = i + 1; j < d.states.length; j++) t.ok(!FA.equivalent({ ...d, start: d.states[i] }, { ...d, start: d.states[j] }).equal, 'minimal: states pairwise inequivalent');
    const mn = FA.nerode(m);
    t.eq(mn.classes.length, nMin, 'Nerode classes = minimal states');
    const repsAcc = mn.classes.map((c) => o(c.rep));
    t.ok(mn.classes.every((c, i) => repsAcc[i] === c.accepting), 'class representative acceptance');
    for (const [k2, z] of Object.entries(mn.distinguish)) {
      const [p, q] = k2.split('|');
      const cp = mn.classes.find((c) => c.state === p), cq = mn.classes.find((c) => c.state === q);
      t.ok(z !== null && o(cp.rep + z) !== o(cq.rep + z), 'distinguishing suffix separates representatives');
    }
  }
  // table filling trace: every marked pair has a reason, and symbol reasons point at marked pairs
  {
    const tb = FA.minimizeTable(m);
    const marks = tb.trace.filter((s) => s.kind === 'mark');
    const set = new Set(marks.map((s) => s.pair.slice().sort().join('|')));
    t.ok(marks.every((s) => s.reason === 'accept' || set.has(s.via.slice().sort().join('|'))), 'table marks cite marked pairs');
  }

  // isomorphism with a renamed copy
  {
    const d = mins[1], perm = d.states.slice().sort(() => R() - 0.5), ren = new Map(d.states.map((q, i) => [q, 'z' + perm.indexOf(q) + '_' + i]));
    const f = (q) => ren.get(q);
    const copy = FA.make({ states: d.states.map(f).reverse(), alphabet: d.alphabet, start: f(d.start), accept: d.accept.map(f), trans: d.trans.map((e) => ({ from: f(e.from), sym: e.sym, to: f(e.to) })) });
    t.ok(FA.isomorphic(d, copy).iso, 'renamed copy is isomorphic');
    if (d.states.length > 1) {
      const flip = FA.make({ ...copy, accept: copy.states.filter((q) => !copy.accept.includes(q)) });
      t.ok(!FA.isomorphic(d, flip).iso, 'complemented copy is not isomorphic');
    }
  }

  // emptiness, finiteness, counting, enumeration
  {
    const e = FA.isEmpty(m), acc8 = ws.filter(o);
    t.eq(e.empty, acc8.length === 0 && FA.enumerate(m, { max: 1, maxLen: 14 }).length === 0, 'emptiness');
    if (!e.empty) t.ok(o(e.witness) && (acc8.length === 0 || F.shortlexCmp(e.witness, acc8[0]) <= 0), 'empty witness is the shortlex-least accepted string');
    const fin = FA.isFinite(m), n = nMin;
    // infinite iff some accepted string has length in [n, 2n)
    if (m.alphabet.length ** (2 * n) < 5000) {
      const long = strings(m.alphabet, 2 * n - 1).some((w) => w.length >= n && o(w));
      t.eq(fin.finite, !long, 'finiteness');
    }
    if (!fin.finite) for (let i = 0; i < 4; i++) t.ok(o(fin.x + fin.y.repeat(i) + fin.z), 'infinite witness pumps');
    else t.ok(fin.words.every(o) && fin.count === fin.words.length, 'finite language listed');
    const cnt = FA.countByLength(m, m.alphabet.length === 2 ? 8 : 5).numbers;
    t.eq(cnt, cnt.map((_, len) => ws.filter((w) => w.length === len && o(w)).length), 'counts by length');
    const en = FA.enumerate(m, { max: 25, maxLen: m.alphabet.length === 2 ? 8 : 5 });
    t.eq(en, acc8.slice(0, 25).sort(F.shortlexCmp), 'enumerate in shortlex order');
  }

  // pumping split on the minimal DFA
  {
    const d = mins[0];
    for (const w of ws.filter((w) => w.length >= d.states.length && o(w)).slice(0, 4)) {
      const r = FA.pumpSplit(d, w);
      t.ok(r.ok && r.y.length >= 1 && (r.x + r.y).length <= d.states.length && r.x + r.y + r.z === w, 'pump split shape');
      for (let i = 0; i < 4; i++) t.ok(o(r.x + r.y.repeat(i) + r.z), 'pumped string accepted');
    }
  }
}

// ---------------------------------------------------------------- binary constructions

for (let k = 0; k < 300; k++) {
  const a = randM(R, ['dfa', 'nfa', 'enfa'][k % 3]), b = randM(R, ['dfa', 'nfa', 'enfa'][(k + 1) % 3]);
  const oa = oracle(a), ob = oracle(b);
  const sigma = [...new Set([...a.alphabet, ...b.alphabet])].sort();
  const ws = strings(sigma, sigma.length === 2 ? 7 : 4);
  const inA = (w) => Array.from(w).every((c) => a.alphabet.includes(c)) && oa(w);
  const inB = (w) => Array.from(w).every((c) => b.alphabet.includes(c)) && ob(w);
  const ops = { union: (x, y) => x || y, intersection: (x, y) => x && y, difference: (x, y) => x && !y, xor: (x, y) => x !== y };
  for (const [op, f] of Object.entries(ops)) {
    const p = FA.product(a, b, op);
    const acc = FA.acceptor(p.fa);
    t.ok(ws.every((w) => acc(w) === f(inA(w), inB(w))), 'product ' + op);
    t.ok(p.trace.some((s) => s.kind === 'pair-edge'), 'product traces pair edges');
  }
  // NFA union / concatenation / star
  const u = FA.acceptor(FA.unionNFA(a, b).fa);
  t.ok(ws.every((w) => u(w) === (inA(w) || inB(w))), 'unionNFA');
  const cc = FA.acceptor(FA.concatNFA(a, b).fa);
  t.ok(ws.every((w) => cc(w) === [...Array(w.length + 1).keys()].some((i) => inA(w.slice(0, i)) && inB(w.slice(i)))), 'concatNFA');
  const st = FA.acceptor(FA.starNFA(a).fa);
  const inStar = (w) => { const ok = [true]; for (let i = 1; i <= w.length; i++) { ok[i] = false; for (let j = 0; j < i; j++) if (ok[j] && inA(w.slice(j, i))) { ok[i] = true; break; } } return ok[w.length]; };
  t.ok(ws.every((w) => st(w) === inStar(w)), 'starNFA');

  // equivalence and inclusion with shortest counterexamples
  const eq = FA.equivalent(a, b);
  const diff = ws.find((w) => inA(w) !== inB(w));
  if (eq.equal) t.ok(diff === undefined, 'equal machines agree');
  else {
    const ce = eq.counterexample;
    t.ok(inA(ce) !== inB(ce), 'counterexample is a counterexample');
    t.ok(eq.acceptedBy === (inA(ce) ? 'A' : 'B'), 'acceptedBy');
    t.ok(diff === undefined ? ce.length > (sigma.length === 2 ? 7 : 4) : diff === ce, 'counterexample is the shortlex-least');
  }
  const self = FA.equivalent(a, FA.minimize(a, 'moore').fa);
  t.ok(self.equal, 'machine ≡ its minimisation');
  const inc = FA.includes(a, b), bad = ws.find((w) => inA(w) && !inB(w));
  if (inc.included) t.ok(bad === undefined, 'inclusion holds on samples');
  else t.ok(inA(inc.counterexample) && !inB(inc.counterexample) && (bad === undefined || bad === inc.counterexample), 'inclusion counterexample');
  t.ok(FA.includes(FA.product(a, b, 'intersection').fa, a).included, 'A ∩ B ⊆ A');
}

// ---------------------------------------------------------------- homomorphisms and quotients

for (let k = 0; k < 150; k++) {
  const m = randM(R, ['dfa', 'nfa', 'enfa'][k % 3]), o = oracle(m);
  if (m.alphabet.length !== 2) continue;
  const words = ['', 'x', 'y', 'xy', 'yx', 'xx', 'xyy'];
  const h = { a: R.pick(words.slice(1)), b: R.pick(words) };
  const hm = FA.homomorphism(m, h).fa, ah = FA.acceptor(hm);
  const hw = (w) => Array.from(w).map((c) => h[c]).join('');
  // forward: h of every accepted string is accepted
  for (const w of strings(['a', 'b'], 5)) if (o(w)) t.ok(ah(hw(w)), 'h(L) contains h(w)');
  // backward (h(a) non-empty, so preimages are no longer than the image): accepted ⇒ some preimage
  if (h.b) for (const v of strings(['x', 'y'], 5).filter((v) => Array.from(v).every((c) => hm.alphabet.includes(c)))) {
    const pre = strings(['a', 'b'], v.length).some((w) => hw(w) === v && o(w));
    t.eq(ah(v), pre, 'h(L) membership by preimages');
  }
  const ih = FA.acceptor(FA.inverseHomomorphism(m, { a: R.pick(['a', 'ab', 'ba', '', 'bb']), b: R.pick(['b', 'a', 'aab']) }, ['a', 'b']).fa);
  void ih;
  const g = { a: R.pick(['a', 'ab', 'ba', '', 'bb']), b: R.pick(['b', 'a', 'aab']) };
  const ig = FA.acceptor(FA.inverseHomomorphism(m, g, ['a', 'b']).fa);
  for (const w of strings(['a', 'b'], 6)) t.eq(ig(w), o(Array.from(w).map((c) => g[c]).join('')), 'inverse homomorphism');
}
for (let k = 0; k < 120; k++) {
  const a = FA.randomNFA(R, { n: 1 + R.int(3), density: 0.3 }), b = FA.randomNFA(R, { n: 1 + R.int(3), density: 0.3 });
  // the quotient searches need many membership tests: use the (separately checked) fast acceptors
  const oa = FA.acceptor(a), ob = FA.acceptor(b), ys = strings(['a', 'b'], 9).filter(ob);
  const q = FA.acceptor(FA.quotient(a, b).fa);
  for (const x of strings(['a', 'b'], 5)) t.eq(q(x), ys.some((y) => oa(x + y)), 'right quotient');
  const lq = FA.acceptor(FA.leftQuotient(a, b).fa);
  for (const y of strings(['a', 'b'], 5)) t.eq(lq(y), ys.some((x) => oa(x + y)), 'left quotient');
}

// ---------------------------------------------------------------- the exponential blow-up family

for (let n = 1; n <= 6; n++) {
  // "the n-th symbol from the end is a": n + 1 NFA states, 2^n DFA states after minimisation
  const states = Array.from({ length: n + 1 }, (_, i) => 'q' + i);
  const trans = [{ from: 'q0', sym: 'a', to: 'q0' }, { from: 'q0', sym: 'b', to: 'q0' }, { from: 'q0', sym: 'a', to: 'q1' }];
  for (let i = 1; i < n; i++) trans.push({ from: 'q' + i, sym: 'a', to: 'q' + (i + 1) }, { from: 'q' + i, sym: 'b', to: 'q' + (i + 1) });
  const m = FA.make({ states, alphabet: ['a', 'b'], start: 'q0', accept: ['q' + n], trans });
  t.eq(FA.subset(m).fa.states.length, 2 ** n, 'blow-up subset size n=' + n);
  t.eq(FA.minimize(m).fa.states.length, 2 ** n, 'blow-up minimal size n=' + n);
}

// ---------------------------------------------------------------- every trace step has a kind and a sentence

{
  const shaped = (tr, what) => t.ok(Array.isArray(tr) && tr.length > 0 && tr.every((s) => typeof s.kind === 'string' && typeof s.say === 'string' && s.say.length > 3 && !/undefined|NaN|\[object/.test(s.say)), 'trace shape: ' + what);
  for (let k = 0; k < 40; k++) {
    const a = randM(R, ['dfa', 'nfa', 'enfa'][k % 3]), b = randM(R, 'nfa');
    shaped(FA.run(a, 'abba').trace, 'run');
    shaped(FA.closure(a, [a.start]).trace, 'closure');
    shaped(FA.subset(a).trace, 'subset');
    shaped(FA.removeEps(a).trace, 'removeEps');
    shaped(FA.complete(FA.subset(a, { dropEmpty: true }).fa).trace, 'complete');
    shaped(FA.complement(a).trace, 'complement');
    shaped(FA.product(a, b, 'xor').trace, 'product');
    shaped(FA.reverse(a).trace, 'reverse');
    shaped(FA.unionNFA(a, b).trace, 'unionNFA');
    shaped(FA.concatNFA(a, b).trace, 'concatNFA');
    shaped(FA.starNFA(a).trace, 'starNFA');
    if (a.trans.some((e) => e.sym)) shaped(FA.homomorphism(a, { a: 'xy', b: '', c: 'z' }).trace, 'homomorphism');
    shaped(FA.inverseHomomorphism(a, { a: 'ab', b: '' }, ['a', 'b']).trace, 'inverse homomorphism');
    shaped(FA.quotient(a, b).trace, 'quotient');
    shaped(FA.removeUnreachable(a).trace, 'removeUnreachable');
    for (const how of ['table', 'moore', 'hopcroft', 'brzozowski']) shaped(FA.minimize(a, how).trace, how);
    shaped(FA.equivalent(a, b).trace, 'equivalent');
    shaped(FA.isEmpty(a).trace, 'isEmpty');
    shaped(FA.isFinite(a).trace, 'isFinite');
    shaped(FA.countByLength(a, 4).trace, 'count');
    shaped(FA.nerode(a).trace, 'nerode');
  }
}

// ---------------------------------------------------------------- distinguisher helpers

{
  const anbn = (w) => /^a*b*$/.test(w) && w.split('a').length - 1 === w.split('b').length - 1;
  for (let i = 0; i < 5; i++) for (let j = i + 1; j < 5; j++) {
    const z = FA.distinguishing(anbn, ['a', 'b'], 'a'.repeat(i), 'a'.repeat(j), 8);
    t.ok(z !== null && anbn('a'.repeat(i) + z) !== anbn('a'.repeat(j) + z), 'aⁱ and aʲ are distinguished');
  }
  const ex = FA.nerodeExplore(anbn, ['a', 'b'], F.sigmaStar(['a', 'b'], 4), 5);
  t.ok(ex.classes.length >= 6, 'aⁿbⁿ shows many classes');
  const even = (w) => w.split('a').length % 2 === 1;
  t.eq(FA.nerodeExplore(even, ['a', 'b'], F.sigmaStar(['a', 'b'], 5), 4).classes.length, 2, 'even a\'s has two classes');
}

t.done();
