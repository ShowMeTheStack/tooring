// Other models and computability: register and counter machines, LBAs, unrestricted grammars, lambda
// calculus, recursive functions, the diagonal, decidable problems, reductions, Rice, PCP, tiling, Kolmogorov.
import { load, rng, harness } from './load.mjs';

const MINE = /core\/(tm|tm-multi|tm-lib|tm-macro|models|recursive|lambda|encode|computability|pcp|sat|complexity|reductions|cooklevin)\.js$/;
const T = load(['core'], (f) => MINE.test(f));
const t = harness('models');
const R = rng(77);
const TM = T.tm, L = T.tmLib, C = T.comp;

// ---------- register machines ----------
for (const p of T.ram.lib) {
  const P = T.ram.parse(p.text);
  t.eq(P.errors, [], `${p.id} parses`);
  t.eq(P.core, p.inputs !== 'array', `${p.id} ${p.inputs === 'array' ? 'uses' : 'avoids'} the random-access extras`);
  if (p.inputs === 2) for (let x = 0; x <= 12; x++) for (let y = 0; y <= 12; y++) t.eq(T.ram.run(P, [0, x, y], { trace: false }).output, p.oracle(x, y), `${p.id}(${x}, ${y})`);
  else if (p.inputs === 1) for (let x = 0; x <= 12; x++) t.eq(T.ram.run(P, [0, x], { trace: false }).output, p.oracle(x), `${p.id}(${x})`);
  else for (let i = 0; i < 60; i++) {
    const arr = [...Array(R.int(7))].map(() => R.int(20)), regs = { 1: arr.length };
    arr.forEach((v, j) => { regs[10 + j] = v; });
    t.eq(T.ram.run(P, regs, { trace: false }).output, p.oracle(arr), `${p.id} on [${arr}]`);
  }
}
{
  const r = T.ram.run(T.ram.lib[0].text, [0, 2, 1]);
  t.ok(r.trace.filter((s) => s.kind === 'exec').every((s) => s.say && s.ins && s.regs), 'register trace has instruction, registers and a sentence');
  t.ok(r.trace.some((s) => s.changed && s.changed[0]), 'trace records changed registers');
  t.ok(T.ram.parse('jmp nowhere\nfoo r1').errors.length === 2, 'register machine errors are reported');
  t.eq(T.ram.run('l: jmp l', [], { maxSteps: 100, trace: false }).verdict, 'limit', 'an endless program hits the limit');
}

// ---------- counter machines ----------
for (const p of T.counter.lib) {
  const P = T.counter.parse(p.text);
  t.eq(P.errors, [], `${p.id} parses`);
  t.ok(P.counters.length <= 2, `${p.id} uses at most two counters`);
  const inputs = p.id === 'prime-powers' ? [] : Array.from({ length: 31 }, (_, a) => a);
  if (p.id === 'prime-powers') for (let x = 0; x <= 5; x++) for (let y = 0; x + y <= 6; y++) inputs.push(2 ** x * 3 ** y);
  for (const a of inputs) {
    const r = T.counter.run(P, { A: a }, { trace: false });
    if (p.state) t.eq(r.state, p.oracle({ A: a }), `${p.id} on ${a}`);
    else t.eq({ A: r.counters.A, B: r.counters.B }, p.oracle({ A: a }), `${p.id} on ${a}`);
  }
}

// ---------- linear-bounded automata ----------
{
  const M = L.get('anbncn-lba'), e = L.entry('anbncn-lba');
  for (const w of TM.strings(['a', 'b', 'c'], 7)) { const r = T.lba.run(M, w, { trace: false }); t.eq(r.decided === 'accept', e.oracle(w), `LBA decides ${w}`); }
  const spin = TM.compile('mode: lba\ninput: a\nq0, a -> q1, a, R\nq1, a|> -> q0, *, L\nq0, < -> q0, <, R');
  const r = T.lba.run(spin, 'aa');
  t.eq([r.verdict, r.decided], ['loop', 'reject'], 'a cycling LBA is caught and rejected');
  t.ok(r.bound === spin.states.length * 4 * spin.gamma.length ** 2, 'configuration bound |Q|(n+2)|Γ|^n');
}

// ---------- unrestricted grammars ----------
for (const g of T.ugrammar.lib) {
  const G = T.ugrammar.parse(g.text);
  t.eq(G.errors, [], `${g.id} parses`);
  const n = g.id === 'double-a' ? 16 : g.id === 'equal-abc' ? 6 : 7;
  for (const w of TM.strings(g.alphabet, n)) {
    if (g.alphabet.length === 1 && w.length > 16) continue;
    const r = T.ugrammar.derive(G, w, { slack: g.id === 'double-a' ? 3 : undefined, trace: false });
    t.eq(r.found, g.oracle(w), `${g.id} derives ${w || 'ε'} exactly when it is in the language`);
    if (r.found) {
      const d = r.derivation;
      t.eq(d[0].form, G.start, `${g.id} derivation starts at the start symbol`);
      t.eq(d[d.length - 1].form, w, `${g.id} derivation ends at ${w}`);
      for (let i = 1; i < d.length; i++) {
        const [lhs, rhs] = d[i].via.rule.split(' → ').map((s) => (s === 'ε' ? '' : s));
        const prev = d[i - 1].form, at = d[i].via.at;
        t.ok(prev.slice(at, at + lhs.length) === lhs && prev.slice(0, at) + rhs + prev.slice(at + lhs.length) === d[i].form, `${g.id} derivation step ${i} for ${w} applies its rule`);
      }
    }
  }
}
t.ok(T.ugrammar.parse(T.ugrammar.lib[0].text).noncontracting, 'the aⁿbⁿcⁿ grammar is noncontracting');
t.ok(!T.ugrammar.parse(T.ugrammar.lib[2].text).noncontracting, 'the doubling grammar contracts');
t.eq(T.ugrammar.derive(T.ugrammar.lib[0].text, 'aabc').exact, true, 'a non-member of a noncontracting grammar is decided');

// ---------- lambda calculus ----------
{
  const λ = T.lambda;
  const num = (s) => λ.unchurch(λ.normalize(s, { trace: false }).term);
  for (let m = 0; m <= 4; m++) for (let n = 0; n <= 4; n++) {
    t.eq(num(`PLUS ${m} ${n}`), m + n, `PLUS ${m} ${n}`);
    t.eq(num(`MULT ${m} ${n}`), m * n, `MULT ${m} ${n}`);
    t.eq(num(`SUB ${m} ${n}`), Math.max(0, m - n), `SUB ${m} ${n}`);
    t.eq(λ.unbool(λ.normalize(`LEQ ${m} ${n}`, { trace: false }).term), m <= n, `LEQ ${m} ${n}`);
    t.eq(λ.unbool(λ.normalize(`EQ ${m} ${n}`, { trace: false }).term), m === n, `EQ ${m} ${n}`);
  }
  for (const [b, e] of [[2, 0], [2, 1], [2, 3], [3, 2], [1, 4]]) t.eq(num(`POW ${b} ${e}`), b ** e, `POW ${b} ${e}`);
  for (let n = 0; n <= 5; n++) { t.eq(num(`SUCC ${n}`), n + 1, `SUCC ${n}`); t.eq(num(`PRED ${n}`), Math.max(0, n - 1), `PRED ${n}`); t.eq(λ.unbool(λ.normalize(`ISZERO ${n}`).term), n === 0, `ISZERO ${n}`); }
  for (const a of [true, false]) for (const b of [true, false]) {
    const B = (x) => (x ? 'TRUE' : 'FALSE');
    t.eq(λ.unbool(λ.normalize(`AND ${B(a)} ${B(b)}`).term), a && b, 'AND');
    t.eq(λ.unbool(λ.normalize(`OR ${B(a)} ${B(b)}`).term), a || b, 'OR');
    t.eq(λ.unbool(λ.normalize(`NOT ${B(a)}`).term), !a, 'NOT');
  }
  t.eq(num('FACT 3'), 6, 'factorial through the fixed-point combinator');
  t.eq(num('FST (PAIR 3 5)'), 3, 'pairs');
  t.eq(λ.normalize('OMEGA', { maxSteps: 50 }).verdict, 'limit', 'Ω has no normal form');
  const ki = λ.normalize('K I OMEGA');
  t.ok(ki.verdict === 'normal' && λ.alphaEq(ki.term, λ.parse('λz. z')), 'normal order discards the looping argument');
  const cap = λ.normalize('(λx. λy. x) y');
  t.ok(λ.alphaEq(cap.term, λ.parse('λw. y', {})) && !λ.alphaEq(cap.term, λ.parse('λy. y', {})), 'substitution avoids capture');
  t.eq(ki.trace.filter((s) => s.kind === 'beta').length, ki.steps, 'one trace step per β-reduction');
  t.ok(ki.trace.every((s) => typeof s.say === 'string'), 'lambda trace speaks');
  for (let i = 0; i < 200; i++) { const n = R.int(12); t.eq(λ.unchurch(λ.church(n)), n, 'Church numeral round trip'); }
  t.ok(λ.alphaEq(λ.parse('λa b. a b'), λ.parse('λx y. x y')), 'alpha-equivalence');
}

// ---------- recursive functions ----------
{
  const env = T.rec.library(), O = T.rec.ORACLES;
  for (const name of Object.keys(O)) {
    const ar = env[name].arity, max = name === 'exp' ? 4 : ['fact', 'mult', 'tri', 'isqrt', 'log2', 'div'].includes(name) ? 5 : 7;
    const tuples = ar === 1 ? Array.from({ length: max + 1 }, (_, x) => [x]) : [];
    if (ar === 2) for (let x = 0; x <= max; x++) for (let y = 0; y <= max; y++) tuples.push([x, y]);
    for (const a of tuples) {
      const want = O[name](...a);
      const r = T.rec.evaluate(name, a, env, { trace: false, maxSearch: 200, maxCalls: 2e6 });
      if (want === undefined) t.eq(r.verdict, 'limit', `${name}(${a}) is undefined and the search gives up`);
      else t.eq(r.value, want, `${name}(${a})`);
    }
  }
  const r = T.rec.evaluate('add', [2, 1], env);
  t.ok(r.trace[0].kind === 'call' && r.trace[r.trace.length - 1].kind === 'return' && r.trace.every((s) => typeof s.depth === 'number'), 'call trace with depths');
  t.ok(T.rec.evaluate('isqrt', [10], env).trace.some((s) => s.kind === 'search'), 'μ search is traced');
  t.eq(T.rec.parseDefs('bad = C(add; P(1,1))', env).errors.length, 1, 'arity mismatch is reported');
  t.eq(T.rec.parseDefs('bad = P(3,2)').errors.length, 1, 'bad projection is reported');
  t.eq(T.rec.parseDefs('bad = R(P(1,1), P(1,2))').errors.length, 1, 'bad recursion arity is reported');
  t.eq(T.rec.arity(T.rec.parseExpr('M(C(nsg; P(1,2)))'), env), 1, 'μ lowers the arity by one');
  t.eq(T.rec.toText(T.rec.parseExpr('R(Z, C(S; P(2,2)))')), 'R(Z, C(S; P(2,2)))', 'expressions print back');
  // Ackermann against a plain recursive count
  const ack = (m, n, c) => { c.n++; return m === 0 ? n + 1 : n === 0 ? ack(m - 1, 1, c) : ack(m - 1, ack(m, n - 1, c), c); };
  for (let m = 0; m <= 3; m++) for (let n = 0; n <= 4; n++) {
    const c = { n: 0 }, v = ack(m, n, c), a = T.rec.ackermann(m, n, { trace: false });
    t.eq([a.value, a.calls], [v, c.n], `A(${m}, ${n})`);
    t.eq(T.rec.ackFormula(m, n).value, v, `closed form for A(${m}, ${n})`);
  }
  const tab = T.rec.ackTable(4, 3);
  t.ok(tab[4][0].computed && tab[4][0].value === 13 && !tab[4][1].computed && tab[4][1].value === 65533, 'growth table computes what it can and uses the closed form beyond');
  t.ok(T.rec.ackermann(2, 2).trace.length > 10, 'Ackermann call trace');
}

// ---------- the halting problem ----------
{
  const yes = C.diagonal(Object.assign(() => true, { label: 'always "halts"' }));
  t.ok(yes.answer === true && yes.actual === 'loop' && yes.wrong, 'H says D halts, D loops');
  const no = C.diagonal(() => false);
  t.ok(no.answer === false && no.actual === 'accept' && no.wrong, 'H says D loops, D halts');
  for (const N of [1, 5, 20, 60]) {
    const d = C.diagonal(N);
    t.ok(d.answer === false && d.halted && d.wrong, `the ${N}-step simulator is fooled`);
    t.ok(['build', 'ask', 'answer', 'act', 'run', 'contradiction'].every((k) => d.trace.some((s) => s.kind === k)), 'diagonal trace has every act');
  }
  const ms = T.enc.enumerateMachines(12);
  const tab = C.diagonalTable(ms, { maxSteps: 50 });
  t.eq(tab.rows.length, 12, 'diagonal table rows');
  tab.diag.forEach((v, i) => t.ok((v === 'accept') !== (tab.flipped[i] === 'accept'), `D differs from machine ${i + 1} on the diagonal`));
  // a TM program inside the program world
  const P = C.tmProgram(L.get('anbn'));
  t.eq(C.runProgram(P, 'aabb').verdict, 'accept', 'a TM runs as a program');
  t.eq(C.runProgram(C.tmProgram(TM.compile('q0, a -> q0, a, S')), 'a').verdict, 'loop', 'a TM loop is seen as a loop');
}

// ---------- decidable problems ----------
const randomDFA = (n, alpha, partial = false) => {
  const states = Array.from({ length: n }, (_, i) => 'p' + i), delta = {};
  for (const q of states) { delta[q] = {}; for (const a of alpha) if (!partial || R() < 0.8) delta[q][a] = R.pick(states); }
  return { states, alphabet: alpha, start: 'p0', accept: states.filter(() => R() < 0.35), delta };
};
const runDFA = (D, w) => { let q = D.start; for (const a of w) { q = q != null && D.delta[q] ? D.delta[q][a] : null; if (q == null) return false; } return D.accept.includes(q); };
// every string over al of length 0..n, lazily, in shortlex order
function* allStrings(al, n) { for (let len = 0; len <= n; len++) for (let x = 0; x < al.length ** len; x++) { let w = '', y = x; for (let i = 0; i < len; i++) { w = al[y % al.length] + w; y = Math.floor(y / al.length); } yield w; } }
const findStr = (al, n, p) => { for (const w of allStrings(al, n)) if (p(w)) return w; return undefined; };
for (let i = 0; i < 200; i++) {
  const al = ['a', 'b'], D1 = randomDFA(1 + R.int(3), al, true), D2 = randomDFA(1 + R.int(3), al, true);
  for (const w of TM.strings(al, 4)) t.eq(C.A_DFA(D1, w).accepted, runDFA(D1, w), 'A_DFA');
  const bruteEmpty = !TM.strings(al, D1.states.length).some((w) => runDFA(D1, w));
  t.eq(C.E_DFA(D1).empty, bruteEmpty, 'E_DFA against all short strings');
  const n = (D1.states.length + 1) * (D2.states.length + 1) - 1; // pairs, counting the implicit dead states
  const diff = findStr(al, n, (w) => runDFA(D1, w) !== runDFA(D2, w));
  const eq = C.EQ_DFA(D1, D2);
  t.eq(eq.equal, diff === undefined, 'EQ_DFA against all strings up to |Q1||Q2|');
  if (!eq.equal) { t.ok(runDFA(D1, eq.witness) !== runDFA(D2, eq.witness), 'EQ_DFA witness separates'); t.eq(eq.witness.length, diff.length, 'EQ_DFA witness is a shortest one'); }
  t.eq(C.EQ_DFA(D1, D1).equal, true, 'a DFA equals itself');
}
const randomCFG = () => {
  const vars = ['S', 'A', 'B'].slice(0, 1 + R.int(3)), sy = vars.concat(['a', 'b']), rules = [];
  for (const v of vars) for (let k = 0; k < 1 + R.int(3); k++) rules.push({ lhs: v, rhs: [...Array(R.int(4))].map(() => R.pick(sy)) });
  return { start: 'S', variables: vars, terminals: ['a', 'b'], rules };
};
for (let i = 0; i < 250; i++) {
  const G = randomCFG();
  const lang = C.cfgLanguage(G, 5);
  const { cnf } = C.toCNF(G);
  t.ok(cnf.rules.every((r) => (r.rhs.length === 2 && r.rhs.every((s) => cnf.variables.includes(s) && s !== cnf.start)) || (r.rhs.length === 1 && !cnf.variables.includes(r.rhs[0])) || (r.rhs.length === 0 && r.lhs === cnf.start)), 'the CNF grammar is in Chomsky normal form');
  const cl = C.cfgLanguage(cnf, 5);
  t.eq([...cl].sort(), [...lang].sort(), 'CNF generates the same strings up to length 5');
  for (const w of TM.strings(['a', 'b'], 5)) t.eq(C.A_CFG(G, w).accepted, lang.has(w), `A_CFG by CYK on ${w}`);
  const e = C.E_CFG(G);
  if (lang.size) t.eq(e.empty, false, 'E_CFG sees a generated string');
  if (!e.empty) t.ok(C.A_CFG(G, e.witness).accepted, 'E_CFG witness is generated');
  else t.eq(lang.size, 0, 'an empty grammar generates nothing short');
}
{
  const G = C.parseCFG('S -> a S b | ε');
  t.ok(C.A_CFG(G, 'aabb').accepted && !C.A_CFG(G, 'aab').accepted && C.A_CFG(G, '').accepted, 'aⁿbⁿ by CYK');
  const tr = C.A_CFG(G, 'ab').trace;
  t.ok(['start', 'epsilon', 'unit', 'terminals', 'binary', 'cell', 'accept'].every((k) => tr.some((s) => s.kind === k)), 'CNF and CYK are traced');
  t.ok(C.E_CFG(C.parseCFG('S -> A\nA -> a A')).empty, 'a grammar that never stops is empty');
}

// ---------- reductions as machine transformers ----------
{
  const loopy = TM.compile('name: L\ninput: a b\nq0, a -> q0, a, R\nq0, _ -> qa, _, S\nq0, b -> q0, b, S');
  const machines = [L.get('anbn'), L.get('palindrome'), loopy];
  const words = ['', 'ab', 'aab', 'aa', 'b'];
  const samples = TM.strings(['0', '1', 'a', 'b'], 3).concat(['0011', '000111']);
  const verdictOf = (M, w) => TM.run(M, w, { trace: false }).verdict;
  for (const M of machines) for (const w of words) {
    const v = verdictOf(M, w);
    const acc = v === 'accept', halts = v === 'accept' || v === 'reject';
    let r = C.reduce('ATM-coETM', M, w);
    t.ok(r.trace.some((s) => s.kind === 'build') && r.machines[0].lines.length === 4, 'reduction trace and description');
    for (const x of samples.concat([w])) t.eq(r.machines[0].run(x).verdict === 'accept', acc && x === w, `M₁ for ⟨${M.name}, ${w}⟩ on ${x}`);
    r = C.reduce('ATM-REGULAR', M, w);
    for (const x of samples) { const n = x.length / 2; t.eq(r.machines[0].run(x).verdict === 'accept', acc || x === '0'.repeat(n) + '1'.repeat(n), `M₂ for ⟨${M.name}, ${w}⟩ on ${x}`); }
    r = C.reduce('HALT-EQTM', M, w);
    for (const x of samples) t.eq(r.machines[1].run(x).verdict === 'accept', halts, `HALT ≤ EQ for ⟨${M.name}, ${w}⟩ on ${x}`);
    r = C.reduce('ATM-HALT', M, w);
    const h = r.machines[0].run(w).verdict;
    t.eq(h === 'accept', acc, `A ≤ HALT: M′ halts on ${w} iff ${M.name} accepts`);
    if (!acc) t.ok(h === 'loop', 'M′ loops instead of rejecting');
    r = C.reduce('HALT-ATM', M, w);
    t.eq(r.machines[0].run(w).verdict === 'accept', halts, `HALT ≤ A: M′ accepts ${w} iff ${M.name} halts`);
  }
}

// ---------- Rice ----------
{
  const entry = (id, lang) => ({ name: id, machine: L.get(id), lang, member: L.entry(id).oracle });
  const empty = { name: 'reject-all', machine: TM.compile('input: a b\nq0, a|b|_ -> qr, *, S'), lang: 'empty', member: () => false };
  const full = { name: 'accept-all', machine: TM.compile('input: a b\nq0, a|b|_ -> qa, *, S'), lang: 'all', member: () => true };
  const cat = [entry('anbn', 'anbn'), entry('anbn-oneway', 'anbn'), entry('palindrome', 'pal'), entry('pal-2tape', 'pal'), entry('pal-2head', 'pal'), entry('even-length', 'even'), entry('equal-ab', 'eqab'), empty, full];
  const eps = C.riceCheck({ test: (e) => e.member('') }, cat);
  t.ok(eps.semantic && !eps.trivial, '"contains ε" is semantic and non-trivial');
  const ab = C.riceCheck({ test: (e) => e.member('ab') }, cat);
  t.ok(ab.semantic && !ab.trivial && ab.emptyHas === false, '"contains ab" is non-trivial and ∅ lacks it');
  const states = C.riceCheck({ test: (e) => e.machine.states.length > 5 }, cat);
  t.ok(!states.semantic, '"more than 5 states" is about machines, not languages');
  const trivial = C.riceCheck({ test: () => true }, cat);
  t.ok(trivial.trivial, 'an always-true property is trivial');
  const nonEmptyComp = C.riceCheck({ test: (e) => !e.member('abab') }, cat);
  t.ok(nonEmptyComp.emptyHas === true, 'when ∅ has the property the template uses the complement');
  // the template machine behaves as the target when M accepts w, and accepts nothing otherwise
  for (const [M, w] of [[L.get('anbn'), 'ab'], [L.get('anbn'), 'ba']]) {
    const acc = TM.run(M, w, { trace: false }).verdict === 'accept';
    const Mw = ab.template(M, w);
    for (const x of TM.strings(['a', 'b'], 4)) {
      const target = cat.find((e) => e.name === ab.target);
      t.eq(Mw.run(x).verdict === 'accept', acc && target.member(x), `Rice template on ${x}`);
    }
  }
}

// ---------- PCP ----------
const P = T.pcp;
{
  const inst = [{ top: 'a', bottom: 'ab' }, { top: 'bb', bottom: 'b' }];
  const s = P.solve(inst);
  t.ok(s.verdict === 'match' && P.verify(inst, s.seq).ok, 'a small instance is solved');
  t.ok(s.trace.some((x) => x.kind === 'match' && x.rows.length === s.seq.length), 'the match is laid out domino by domino');
  t.eq(P.solve([{ top: 'ab', bottom: 'a' }, { top: 'b', bottom: 'bb' }]).verdict, 'match', 'another instance');
  t.eq(P.solve([{ top: 'a', bottom: 'b' }]).verdict, 'none', 'a hopeless instance is proved hopeless');
}
// against brute force over all sequences up to length 5
const randomDominoes = (k) => Array.from({ length: k }, () => ({ top: [...Array(1 + R.int(3))].map(() => R.pick(['a', 'b'])).join(''), bottom: [...Array(1 + R.int(3))].map(() => R.pick(['a', 'b'])).join('') }));
const bruteShortest = (d, maxLen, mpcp = false) => {
  let layer = [[]];
  for (let len = 1; len <= maxLen; len++) {
    const next = [];
    for (const s of layer) for (let i = 0; i < d.length; i++) { if (mpcp && !s.length && i) continue; const q = s.concat(i); if (P.verify(d, q, mpcp).ok) return q.length; const tp = q.map((j) => d[j].top).join(''), bt = q.map((j) => d[j].bottom).join(''); if (tp.startsWith(bt) || bt.startsWith(tp)) next.push(q); }
    layer = next;
  }
  return null;
};
for (let i = 0; i < 400; i++) {
  const d = randomDominoes(2 + R.int(2)), mp = R() < 0.3;
  const b = P.solve(d, { mpcp: mp, maxNodes: 20000, trace: false }), brute = bruteShortest(d, 5, mp);
  if (b.verdict === 'match') { t.ok(P.verify(d, b.seq, mp).ok, 'PCP solution verifies'); if (brute != null) t.eq(b.seq.length, brute, 'BFS finds a shortest match'); }
  if (b.verdict === 'none') t.eq(brute, null, 'no match means brute force finds none either');
  if (brute != null) t.eq(b.verdict, 'match', 'BFS finds what brute force finds');
  const id = P.solveIDDFS(d, { mpcp: mp, maxDepth: 6, maxNodes: 50000 });
  if (id.verdict === 'match') { t.ok(P.verify(d, id.seq, mp).ok, 'IDDFS solution verifies'); if (b.verdict === 'match') t.eq(id.seq.length, b.seq.length, 'IDDFS and BFS agree on the shortest length'); }
  if (mp) {
    const conv = P.mpcpToPcp(d);
    const c = P.solve(conv.dominoes, { maxNodes: 40000, trace: false });
    if (b.verdict === 'match') { t.ok(P.verify(conv.dominoes, conv.mapSeq(b.seq)).ok, 'MPCP solution maps to a PCP solution'); t.ok(c.verdict === 'match' || c.verdict === 'limit', 'converted instance is solvable'); }
    if (c.verdict === 'match') { t.eq(c.seq[0], 0, 'the converted instance must start with the starred first domino'); t.ok(b.verdict !== 'none', 'PCP match means an MPCP match'); }
    if (b.verdict === 'none') t.ok(c.verdict !== 'match', 'no MPCP match means no PCP match');
  }
}
{
  // TM -> MPCP: a tiny machine's accepting history is the match
  const M = TM.compile('input: a b\nq0, a -> q1, b, R\nq1, b -> q1, a, R\nq1, _ -> qa, _, S');
  for (const w of ['a', 'ab', 'abb', 'b', 'ba', 'aa']) {
    const run = TM.run(M, w);
    const red = P.tmToMpcp(M, w);
    t.ok(red.trace.length === 4 && red.dominoes[0].role === 'start', 'TM to MPCP is traced');
    const s = P.solve(red.dominoes, { mpcp: true, maxNodes: 300000, maxOver: 40, trace: false });
    t.eq(s.verdict === 'match', run.verdict === 'accept', `the MPCP instance for ${w} has a match iff the machine accepts`);
    if (s.verdict === 'match') {
      t.ok(P.verify(red.dominoes, s.seq, true).ok, 'the match verifies');
      const sym = red.symbols, configs = run.history.map((h) => h.replace(/(\S+)? ?(q\w+|qa) (\S+)/, (m0, u, q, v) => (u || '') + sym[q] + v));
      for (const c of configs.slice(0, -1)) t.ok(s.top.includes('#' + c), `the match contains configuration ${c}`);
    }
  }
}

// ---------- Wang tiles ----------
for (let i = 0; i < 300; i++) {
  const cols = ['r', 'g'], k = 2 + R.int(3);
  const tiles = Array.from({ length: k }, () => ({ n: R.pick(cols), e: R.pick(cols), s: R.pick(cols), w: R.pick(cols) }));
  const W = 1 + R.int(3), H = 1 + R.int(2), opts = { torus: R() < 0.3, border: R() < 0.2 ? 'r' : null, first: R() < 0.2 ? 0 : null, trace: false };
  const r = T.wang.tile(tiles, W, H, opts);
  let exists = false;
  const total = k ** (W * H);
  for (let m = 0; m < total && !exists; m++) {
    const board = [];
    let x = m;
    for (let y = 0; y < H; y++) { const row = []; for (let c = 0; c < W; c++) { row.push(x % k); x = Math.floor(x / k); } board.push(row); }
    exists = T.wang.check(tiles, board, opts);
  }
  t.eq(r.verdict === 'tiled', exists, 'backtracking agrees with brute force');
  if (r.board) t.ok(T.wang.check(tiles, r.board, opts), 'the tiling found is valid');
}
t.ok(T.wang.tile([{ n: 'a', e: 'b', s: 'a', w: 'b' }], 3, 3).trace.some((s) => s.kind === 'place'), 'tiling is traced');

// ---------- Kolmogorov ----------
for (let i = 0; i < 400; i++) {
  const s = [...Array(R.int(40))].map(() => R.pick(['a', 'b', 'c'])).join('');
  t.eq(T.kolmo.unlz78(T.kolmo.lz78(s).pairs), s, 'LZ78 round trip');
  const k = T.kolmo.kolmogorov(s);
  t.ok(k.best <= k.literal, 'the bound never exceeds the literal length');
}
{
  const k = T.kolmo.kolmogorov('ab'.repeat(32));
  t.ok(k.repeat != null && k.best < k.literal / 4, 'a repetitive string compresses well');
  t.eq(T.kolmo.repeatDescription('abcabcabc').text, 'repeat "abc" 3 times', 'repeat description');
  const c = T.kolmo.incompressible(10, 3);
  t.eq([c.total, c.short, c.atLeast], [1024, 127, 897], 'counting incompressible strings');
}

t.done();
