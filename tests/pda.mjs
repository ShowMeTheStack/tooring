// Pushdown automata, the CFG ↔ PDA constructions, the product with a DFA, the CF pumping game and the
// closure constructions, checked against the bounded-language oracle and membership predicates.
import { load, rng, harness } from './load.mjs';

const T = load(), g = T.grammar, P = T.pda, C = T.cfpump;
const t = harness('pda');
const words = (alpha, n) => g.allWords(alpha, n).map((w) => w.join(''));
const langSet = (G, n) => new Set(g.language(G, n).map((w) => w.join('')));

// ---------- a hand-made PDA for aⁿbⁿ, text round trip, simulation ----------
const anbn = P.parse(`# a^n b^n by final state
start q0
stack-start Z
accept q2
q0, a, Z -> q0, AZ
q0, a, A -> q0, AA
q0, ε, Z -> q1, Z
q0, ε, A -> q1, A
q1, b, A -> q1, ε
q1, ε, Z -> q2, Z`);
t.eq(anbn.transitions[0].push, ['A', 'Z'], 'push is cut into stack symbols');
const again = P.parse(P.toString(anbn));
t.eq(again.transitions, anbn.transitions, 'text round trip keeps the transitions');
t.eq([again.start, again.startStack, again.accept, again.acceptBy], [anbn.start, anbn.startStack, anbn.accept, anbn.acceptBy], 'text round trip keeps the settings');
const isAnBn = (w) => /^a*b*$/.test(w) && w.split('a').length - 1 === w.split('b').length - 1;
for (const w of words(['a', 'b'], 9)) {
  const r = P.simulate(anbn, w);
  t.ok(r.accepted === isAnBn(w) && r.complete, 'aⁿbⁿ PDA on ' + w);
  if (r.accepted) {
    const path = r.paths[0];
    t.ok(path[0].id === 0 && path[path.length - 1].pos === w.length && anbn.accept.includes(path[path.length - 1].state), 'accepting path ends right on ' + w);
    t.ok(path.every((c, i) => i === 0 || c.parent === path[i - 1].id), 'parent links chain on ' + w);
  }
}
t.ok(P.tryParse('q0, a -> q1, A').error !== null, 'a malformed transition is reported');
t.ok(P.tryParse('accept-by sometimes\nq0, a, Z -> q0, Z').error !== null, 'a bad accept-by is reported');
// stepper: layers advance one move at a time and the frontier empties
{
  const s = P.stepper(anbn, 'aabb');
  let layers = 0;
  while (!s.done && layers < 50) { s.step(); layers++; }
  t.ok(s.accepted && layers >= 6 && layers < 50, 'stepper reaches acceptance layer by layer');
  t.ok(s.trace.some((x) => x.kind === 'move') && s.trace.some((x) => x.kind === 'accept') && s.trace.some((x) => x.kind === 'dead'), 'stepper trace has moves, an accept and dead branches');
}
// ε-loop that grows the stack must stop
{
  const loop = P.parse('start q\nstack-start Z\naccept-by empty\nq, ε, Z -> q, Z Z\nq, a, Z -> q, ε');
  const r = P.simulate(loop, 'aab');
  t.ok(!r.accepted && !r.complete, 'a growing ε-loop is cut off and reported incomplete');
  const r2 = P.simulate(loop, 'aaa');
  t.ok(r2.accepted, 'the looping PDA still accepts aaa');
}

// ---------- determinism ----------
{
  t.ok(!P.deterministic(anbn).deterministic, 'the guessing aⁿbⁿ PDA is nondeterministic');
  t.eq(P.deterministic(anbn).conflicts.length, 2, 'it has two competing pairs');
  const det = P.parse(`start q0\nstack-start Z\naccept q2\nq0, a, Z -> q0, A Z\nq0, a, A -> q0, A A\nq0, b, A -> q1, ε\nq1, b, A -> q1, ε\nq1, ε, Z -> q2, Z`);
  t.ok(P.deterministic(det).deterministic, 'the counting aⁿbⁿ (n ≥ 1) PDA is deterministic');
  for (const w of words(['a', 'b'], 8)) t.ok(P.accepts(det, w).accepted === (isAnBn(w) && w.length > 0), 'deterministic aⁿbⁿ on ' + w);
  const ign = P.parse('start p\nstack-start Z\np, a, ε -> p, A\np, a, Z -> p, Z');
  const d = P.deterministic(ign);
  t.ok(!d.deterministic && /ignores the stack/.test(d.conflicts[0].why), 'a move that ignores the stack competes with one that pops');
  const ok2 = P.parse('start p\nstack-start Z\np, a, Z -> p, Z\np, b, Z -> p, Z\np, a, A -> p, A');
  t.ok(P.deterministic(ok2).deterministic, 'different reads or different pops do not compete');
}

// ---------- random grammars: CFG → PDA (both ways) and back ----------
const R = rng(20261017);
let tdChecked = 0, buChecked = 0, rtChecked = 0;
for (let k = 0; k < 70; k++) {
  const eps = k % 2 ? 0 : 0.15;
  const G = g.random(R, { nonterminals: 2 + R.int(2), terminals: ['a', 'b'], maxRules: 3, maxLen: 3, eps });
  const n = 6, L = langSet(G, n);
  const td = P.fromCFGTopDown(G);
  t.ok(td.trace.filter((s) => s.kind === 'expand').length === G.productions.length, 'one expand move per rule');
  const bu = P.fromCFGBottomUp(G);
  for (const w of words(['a', 'b'], n)) {
    const r = P.accepts(td.pda, w);
    if (L.has(w)) t.ok(r.accepted, 'top-down PDA accepts ' + w + ' for ' + g.toString(G));
    else t.ok(!r.accepted && r.complete, 'top-down PDA rejects ' + w + ' for ' + g.toString(G));
    tdChecked++;
    // with ε-rules the shift-reduce PDA can push nullable symbols without end, so only short words
    // are tried there, for soundness
    if (eps === 0 || w.length <= 3) {
      const b = P.accepts(bu.pda, w, { maxConfigs: eps === 0 ? 40000 : 3000 });
      if (b.accepted) t.ok(L.has(w), 'bottom-up PDA accepts only words of L: ' + w + ' for ' + g.toString(G));
      else t.ok(!L.has(w) || !b.complete, 'bottom-up PDA rejects ' + w);
      if (eps === 0) t.ok(b.accepted === L.has(w) && b.complete, 'ε-free bottom-up PDA is exact on ' + w + ' for ' + g.toString(G));
      buChecked++;
    }
  }
  // round trip through the triple construction
  const back = P.toCFG(td.pda);
  const L2 = langSet(back.grammar, n);
  t.eq([...L2].sort(), [...L].sort(), 'CFG → PDA → CFG keeps the language of ' + g.toString(G));
  t.ok(back.trace.some((s) => s.kind === 'transition') && back.trace.some((s) => s.kind === 'cleanup'), 'triple construction is traced');
  rtChecked++;
  if (k < 6 && eps === 0) {
    const back2 = P.toCFG(bu.pda);
    t.eq([...langSet(back2.grammar, 5)].sort(), [...langSet(G, 5)].sort(), 'bottom-up PDA → CFG keeps the language of ' + g.toString(G));
  }
}
t.ok(tdChecked > 5000, 'top-down checks ran: ' + tdChecked);

// ---------- random PDAs: final ↔ empty and PDA → CFG against simulation ----------
let pdaChecked = 0;
for (let k = 0; k < 120; k++) {
  const by = k % 2 ? 'final' : 'empty';
  const A = P.random(R, { states: 2 + R.int(2), transitions: 5 + R.int(4), acceptBy: by });
  const conv = by === 'final' ? P.toEmpty(A).pda : P.toFinal(A).pda;
  t.ok(conv.acceptBy !== by, 'conversion switches the acceptance mode');
  let G = null;
  try { G = P.toCFG(A).grammar; } catch (e) { t.ok(false, 'toCFG threw ' + e.message); }
  const Lg = G ? langSet(G, 5) : null;
  for (const w of words(['a', 'b'], 5)) {
    const r1 = P.accepts(A, w, { maxStack: 14 }), r2 = P.accepts(conv, w, { maxStack: 15 });
    if (r1.complete && r2.complete) t.ok(r1.accepted === r2.accepted, 'final/empty conversion agrees on ' + w + '\n' + P.toString(A));
    // pop-ε moves on an empty stack cannot be expressed by triples; random PDAs by empty stack with
    // such moves are compared only one way
    const ignoresStack = A.transitions.some((x) => x.pop === '');
    if (G && r1.complete) {
      if (by === 'final' || !ignoresStack) t.ok(r1.accepted === Lg.has(w), 'PDA → CFG agrees with the PDA on ' + w + '\n' + P.toString(A));
      else if (Lg.has(w)) t.ok(r1.accepted, 'PDA → CFG word is accepted: ' + w);
    }
    pdaChecked++;
  }
}

// ---------- product with a DFA ----------
function randomDFA(r) {
  const qs = ['d0', 'd1', 'd2'].slice(0, 2 + r.int(2)), delta = {};
  for (const q of qs) { delta[q] = {}; for (const a of ['a', 'b']) if (r() < 0.9) delta[q][a] = r.pick(qs); }
  return { states: qs, alphabet: ['a', 'b'], start: 'd0', accept: qs.filter(() => r() < 0.5), delta };
}
const dfaAccepts = (D, w) => { let q = D.start; for (const c of w) { q = D.delta[q][c]; if (q == null) return false; } return D.accept.includes(q); };
for (let k = 0; k < 30; k++) {
  const G = g.random(R, { nonterminals: 2 + R.int(2), terminals: ['a', 'b'], eps: 0.1 });
  const D = randomDFA(R), L = langSet(G, 6), n = k < 10 ? 6 : 5;
  // half the time pass the DFA as a transition list, the shape the finite-automata engine uses
  const Dlist = { states: D.states, alphabet: D.alphabet, start: D.start, accept: D.accept,
    trans: D.states.flatMap((q) => Object.entries(D.delta[q]).map(([sym, to]) => ({ from: q, sym, to }))) };
  const X = C.intersectRegular(G, k % 2 ? Dlist : D);
  for (const w of words(['a', 'b'], n)) {
    const r = P.accepts(X.pda, w);
    t.ok(r.accepted === (L.has(w) && dfaAccepts(D, w)), 'PDA × DFA accepts the intersection on ' + w);
  }
  if (k < 8) {
    const Y = C.intersectRegular(G, D, { grammar: true });
    const want = [...L].filter((w) => dfaAccepts(D, w)).sort();
    t.eq([...langSet(Y.grammar, 6)].sort(), want, 'intersection grammar has the intersection language');
  }
}

// ---------- the catalogue ----------
t.ok(C.catalogue.length >= 20, 'catalogue has ' + C.catalogue.length + ' languages');
t.ok(new Set(C.catalogue.map((L) => L.id)).size === C.catalogue.length, 'catalogue ids are unique');
for (const L of C.catalogue) {
  for (let p = 1; p <= 6; p++) { const s = L.sample(p); t.ok(L.member(s) && s.length >= p, L.id + ' sample for p = ' + p); }
  if (L.cf) {
    const G = g.parse(L.grammar);
    const n = L.alphabet.length > 2 ? 7 : 9;
    const got = langSet(G, n);
    for (const w of words(L.alphabet, n)) t.ok(got.has(w) === L.member(w), L.id + ': grammar and predicate agree on ' + w);
    // a long word of a context-free language has a split that survives
    for (const p of [Math.max(4, L.pMin || 0), Math.max(5, L.pMin || 0)]) {
      const r = C.adversarySplit(L, L.sample(p), p);
      t.ok(r.survives, L.id + ': adversary finds a surviving split for p = ' + p);
    }
  } else {
    for (const p of [2, 3, 4]) {
      const s = L.sample(p);
      if (s.length > 40) continue;
      const r = C.adversarySplit(L, s, p);
      t.ok(!r.survives && r.trace[r.trace.length - 1].kind === 'none', L.id + ': no split of ' + s + ' survives for p = ' + p);
    }
  }
}
// splits enumerate exactly the legal decompositions
for (const [s, p] of [['abcab', 2], ['aaaa', 3], ['abc', 1]]) {
  const all = [...C.splits(s, p)];
  t.ok(all.every((d) => C.validSplit(s, p, d).ok), 'every enumerated split of ' + s + ' is legal');
  let brute = 0;
  for (let a = 0; a <= s.length; a++) for (let b = a; b <= s.length; b++) for (let c = b; c <= s.length; c++) for (let d = c; d <= s.length; d++)
    if (d - a <= p && (b - a) + (d - c) >= 1) brute++;
  t.eq(all.length, brute, 'split count for ' + s + ', p = ' + p);
}

// ---------- the game ----------
{
  const G = C.game('anbncn', { p: 3 });
  t.ok(G.chooseWord('aabbcc').ok, 'a member of length ≥ p is accepted');
  const G2 = C.game('anbncn', { p: 4 });
  t.ok(!G2.chooseWord('abc').ok, 'too-short word refused');
  t.ok(!G2.chooseWord('aabbc').ok, 'non-member refused');
  t.ok(G2.chooseWord('aaaabbbbcccc').ok, 'good word accepted');
  const sp = G2.adversaryMove();
  t.ok(sp && G2.trace.some((x) => x.kind === 'cornered'), 'adversary is cornered on aⁿbⁿcⁿ');
  const r = G2.chooseI(C.refute(C.byId('anbncn'), sp, [0, 2, 3]));
  t.ok(r.studentWins && G2.over, 'student wins by pumping the offered split');
  const G3 = C.game('anbn', { p: 4, word: 'aaaabbbb' });
  G3.adversaryMove();
  for (const i of [0, 2, 3, 5]) t.ok(C.byId('anbn').member(C.pump(G3.split, i)), 'aⁿbⁿ survivor pumps with i = ' + i);
  t.ok(!G3.chooseI(2).studentWins, 'student cannot win on aⁿbⁿ');
  const ch = C.challengerI('anbn', 'aaaabbbb', { u: 'aaa', v: 'a', x: '', y: 'b', z: 'bbb' }, 4);
  t.ok(ch.legal && ch.survives, 'challenger cannot break a good split');
  const ch2 = C.challengerI('anbn', 'aaaabbbb', { u: 'aa', v: 'a', x: 'a', y: '', z: 'bbbb' }, 4);
  t.ok(ch2.legal && !ch2.survives && ch2.i !== null, 'challenger breaks a bad split');
  const ch3 = C.challengerI('anbn', 'aaaabbbb', { u: '', v: 'aaaa', x: 'b', y: 'b', z: 'bb' }, 4);
  t.ok(!ch3.legal, 'challenger refuses a split with |vxy| > p');
}

// ---------- closure ----------
for (let k = 0; k < 30; k++) {
  const G1 = g.random(R, { nonterminals: 2, terminals: ['a', 'b'] }), G2 = g.random(R, { nonterminals: 2, terminals: ['a', 'b'] });
  const n = 5, A = langSet(G1, n), B = langSet(G2, n);
  const U = langSet(C.union(G1, G2).grammar, n);
  t.eq([...U].sort(), [...new Set([...A, ...B])].sort(), 'union language');
  const cat = new Set(); for (const x of A) for (const y of B) if ((x + y).length <= n) cat.add(x + y);
  t.eq([...langSet(C.concat(G1, G2).grammar, n)].sort(), [...cat].sort(), 'concatenation language');
  const st = new Set(['']); let grew = true;
  while (grew) { grew = false; for (const x of [...st]) for (const y of A) if ((x + y).length <= n && !st.has(x + y)) { st.add(x + y); grew = true; } }
  t.eq([...langSet(C.star(G1).grammar, n)].sort(), [...st].sort(), 'star language');
}
{
  const d = C.intersectionDemo(12, 3);
  t.eq(d.both, ['', 'abc', 'aabbcc', 'aaabbbccc', 'aaaabbbbcccc'], 'the two languages meet in aⁿbⁿcⁿ');
  t.ok(!d.game.survives, 'the game shows the meeting is not context-free');
  t.ok(d.trace.length === 4, 'intersection demo is traced');
}
console.log('checked words: top-down ' + tdChecked + ', bottom-up ' + buChecked + ', round trips ' + rtChecked + ', random PDAs ' + pdaChecked);
t.done();
