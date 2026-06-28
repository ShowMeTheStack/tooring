// Turing machines: the library against JS oracles, the engine's verdicts, the macro compiler, the k-tape
// simulation, nondeterminism, enumerators, encodings and the universal machine.
import { load, rng, harness } from './load.mjs';

const MINE = /core\/(tm|tm-multi|tm-lib|tm-macro|models|recursive|lambda|encode|computability|pcp|sat|complexity|reductions|cooklevin)\.js$/;
const T = load(['core'], (f) => MINE.test(f));
const t = harness('tm');
const R = rng(20261017);
const TM = T.tm, L = T.tmLib;
const all = (alpha, n) => TM.strings(alpha, n);

// ---------- the library, exhaustively ----------
for (const e of L.list) {
  const M = L.get(e.id);
  t.ok(M.rules.length > 0, `${e.id} compiles to a table`);
  if (e.kind === 'decider' || e.kind === 'transducer') {
    const inputs = all(e.alphabet, 8).filter((w) => !e.domain || e.domain(w));
    let bad = 0;
    for (const w of inputs) {
      const r = TM.run(M, w, { maxSteps: e.maxSteps || 100000, trace: false, loops: false });
      const want = e.oracle(w), got = e.kind === 'decider' ? r.verdict === 'accept' : r.output;
      if (!r.halted || got !== want) { bad++; if (bad < 4) t.ok(false, `${e.id} on "${w}": got ${got} (${r.verdict}), want ${want}`); }
      else t.ok(true);
    }
    t.ok(inputs.length > 5, `${e.id} was tested on ${inputs.length} inputs`);
  }
  if (e.kind === 'recogniser') for (const w of all(e.alphabet, 8)) {
    const r = TM.run(M, w, { trace: false });
    t.eq(r.verdict, e.oracle(w) ? 'accept' : 'loop', `recogniser ${e.id} on ${w}: accepts members, loops on the rest`);
  }
  if (e.kind === 'beaver') {
    const r = TM.run(M, '', { maxSteps: 1000 });
    t.eq([r.verdict, r.steps, r.ones], ['accept', e.steps, e.ones], `${e.id} steps and ones`);
  }
}
// the 3-state champions are the extremes among all 3-state machines (a fact checked in the library notes); 2-state by exhaustive search here
{
  let bestS = 0, bestO = 0;
  const moves = ['L', 'R'], states = ['A', 'B', 'H'];
  const opts = [];
  for (const wr of ['0', '1']) for (const mv of moves) for (const to of states) opts.push([wr, mv, to]);
  for (const a0 of opts) for (const a1 of opts) for (const b0 of opts) for (const b1 of opts) {
    const rows = [['A', '0', a0], ['A', '1', a1], ['B', '0', b0], ['B', '1', b1]].map(([q, s, [wr, mv, to]]) => `${q}, ${s} -> ${to}, ${wr}, ${mv}`);
    const M = TM.compile('blank: 0\ninput: 1\nstart: A\nhalt: H\n' + rows.join('\n'));
    const r = TM.run(M, '', { maxSteps: 50, trace: false });
    if (r.verdict === 'accept') { bestS = Math.max(bestS, r.steps); bestO = Math.max(bestO, r.ones); }
  }
  t.eq([bestS, bestO], [6, 4], 'exhaustive search over 2-state machines: at most 6 steps and 4 ones');
}

// ---------- engine verdicts and traces ----------
{
  const M = L.get('anbn');
  const r = TM.run(M, 'aabb');
  t.eq(r.trace[0].kind, 'start', 'trace starts with start');
  t.eq(r.trace[r.trace.length - 1].kind, 'accept', 'trace ends with the verdict');
  t.ok(r.trace.every((s) => typeof s.say === 'string' && s.say.length > 5), 'every step says something');
  t.ok(r.trace.filter((s) => s.kind === 'move').every((s) => s.tapes && s.tapes[0].cells.length >= 1), 'move steps carry tape windows');
  t.eq(r.history.length, r.steps + 1, 'one history entry per configuration');
  t.eq(r.history[0], 'q0 aabb', 'u q v notation');
  const loop = TM.compile('q0, a -> q1, a, R\nq1, _ -> q0, _, L');
  t.eq(TM.run(loop, 'a').verdict, 'loop', 'a repeated configuration is a provable loop');
  t.eq(TM.run(loop, 'a').loopAt, { first: 0, again: 2 }, 'loop found where it repeats');
  const runaway = TM.compile('q0, _ -> q0, 1, R');
  const rr = TM.run(runaway, '', { maxSteps: 300 });
  t.eq(rr.verdict, 'limit', 'a machine writing forever runs out of steps');
  t.eq(TM.run(L.get('anbn'), 'ba').reason.startsWith('no rule'), true, 'missing rule rejects with a reason');
  const bad = TM.parse('q0, a -> q1, b\nq0 a -> q1, b, R\nq0, a -> q1, b, Q');
  t.eq(bad.errors.length, 3, 'parse errors are reported per line');
  const ow = TM.parse('mode: oneway\ninput: a\nq0, > -> q0, >, L');
  t.ok(ow.errors.some((e) => /left-end/.test(e.msg)), 'one-way machines may not move left off the marker');
  const lba = TM.parse('mode: lba\ninput: a\nq0, > -> q0, x, S');
  t.ok(lba.errors.some((e) => /right-end/.test(e.msg)), 'an LBA may not overwrite its right marker');
  // printing and re-reading a machine gives the same behaviour
  for (const id of ['palindrome', 'copy', 'bin-less', 'pal-2tape', 'bin-add-3tape']) {
    const M0 = L.get(id), M1 = TM.compile(TM.toText(M0));
    const e = L.entry(id);
    for (const w of all(e.alphabet, 5).filter((w) => !e.domain || e.domain(w))) {
      const a = TM.run(M0, w, { trace: false }), b = TM.run(M1, w, { trace: false });
      t.eq([b.verdict, b.output, b.steps], [a.verdict, a.output, a.steps], `${id} survives printing, on ${w}`);
    }
  }
  t.ok(TM.decides(L.get('anbncn'), all(['a', 'b', 'c'], 5)).ok, 'decides() confirms a decider');
}

// ---------- k tapes on one tape ----------
for (const id of ['pal-2tape', 'anbncn-2tape', 'copy-2tape', 'bin-add-3tape']) {
  const M = L.get(id), e = L.entry(id);
  for (const w of all(e.alphabet, 6).filter((w) => !e.domain || e.domain(w))) {
    const d = TM.run(M, w, { trace: false }), s = TM.simulateKTape(M, w, { trace: false });
    t.eq(s.verdict, d.verdict, `${id} one-tape simulation verdict on ${w}`);
    t.eq(s.simulated, d.steps, `${id} simulated step count on ${w}`);
    t.eq(s.tapes, d.config.tapes.map((tp) => tp.trimmed().join('')), `${id} tracks decode to the tapes on ${w}`);
    t.eq(s.heads, d.config.heads.map((h) => h.p), `${id} head marks on ${w}`);
    t.ok(s.steps >= s.simulated, `${id} one-tape steps cover the simulated steps on ${w}`);
  }
}
{
  const s = TM.simulateKTape(L.get('pal-2tape'), 'abba');
  t.ok(['sim-start', 'gather', 'decide', 'update', 'sim-step', 'accept'].every((k) => s.trace.some((x) => x.kind === k)), 'k-tape simulation traces every phase');
  // quadratic slowdown: one-tape steps grow faster than the simulated steps
  const a = TM.simulateKTape(L.get('pal-2tape'), 'ab'.repeat(4), { trace: false }), b = TM.simulateKTape(L.get('pal-2tape'), 'ab'.repeat(8), { trace: false });
  t.ok(b.steps / b.simulated > a.steps / a.simulated, 'the one-tape overhead per step grows with the input');
}

// ---------- 2-D tapes ----------
for (const w of all(['a', 'b'], 6)) {
  const r = TM.run2d(L.get('copy-down-2d'), w, { trace: false });
  t.ok(r.verdict === 'accept' && [...w].every((c, i) => r.get(i, 0) === c && r.get(i, 1) === c), `2-D copy-down on ${w}`);
}
{
  const r = TM.run2d(L.get('ant-2d'), '', { maxSteps: 500, loops: false, traceLimit: 50 });
  t.eq(r.verdict, 'limit', 'the ant never halts');
  t.ok(r.trace.length === 50 && r.trace[1].rows.length >= 1, '2-D trace carries the grid');
  // the ant is reversible: count of black cells after 4 steps is 4 (it walks a square)
  const r4 = TM.run2d(L.get('ant-2d'), '', { maxSteps: 4, loops: false });
  t.eq(r4.grid.rows.flat().filter((c) => c === '#').length, 4, 'after four steps the ant has blackened four cells');
}

// ---------- nondeterminism ----------
for (const [id, n, depth] of [['ntm-repeat', 6, 20], ['ntm-ww', 6, 120], ['ntm-substring', 5, 40]]) {
  const N = L.get(id), e = L.entry(id);
  t.ok(!N.deterministic, `${id} is nondeterministic`);
  for (const w of all(e.alphabet, n)) {
    const bfs = TM.ntmTree(N, w, { maxDepth: depth, maxNodes: 200000, trace: false });
    const ex = TM.ntmExhaustive(N, w, depth);
    t.eq(bfs.verdict, ex, `${id} BFS agrees with exhaustive search on ${w}`);
    t.eq(bfs.verdict === 'accept', e.oracle(w), `${id} on ${w} matches the oracle`);
    if (bfs.verdict === 'accept') t.ok(TM.isAccept(N, bfs.nodes[bfs.path[bfs.path.length - 1]].state) && bfs.path[0] === 0, `${id} accepting path on ${w}`);
  }
}
for (const w of all(['a', 'b', 'c'], 5)) {
  const N = L.get('ntm-repeat');
  const ad = TM.ntmAddress(N, w, { maxLen: 8, trace: false });
  t.eq(ad.verdict, TM.ntmExhaustive(N, w, 8), `address-tape simulation agrees on ${w}`);
  t.eq(TM.ntmTree(N, w, { dedupe: true, trace: false, maxDepth: 20 }).verdict, TM.ntmExhaustive(N, w, 20), `deduplicated BFS agrees on ${w}`);
}
for (const w of ['#', 'a#a', 'ab#bab', 'b#aa', 'aa#a']) {
  const N = L.get('ntm-substring');
  t.eq(TM.ntmAddress(N, w, { maxLen: 14, trace: false }).verdict, TM.ntmExhaustive(N, w, 14), `two-tape address simulation on ${w}`);
}
{
  const tr = TM.ntmTree(L.get('ntm-repeat'), 'abca');
  t.ok(tr.trace.some((s) => s.kind === 'expand') && tr.trace.some((s) => s.kind === 'level'), 'tree trace has expansions and levels');
  t.ok(tr.nodes.every((n) => n.parent < n.id), 'parents come before children');
}

// ---------- enumerators and dovetailing ----------
{
  const e1 = TM.enumerate(L.get('enum-binary'), { maxPrints: 31 });
  t.eq(e1.prints, TM.strings(['0', '1'], 4), 'the binary enumerator prints shortlex order');
  const e2 = TM.enumerate(L.get('enum-even-a'), { maxPrints: 6 });
  t.eq(e2.prints, [0, 1, 2, 3, 4, 5].map((i) => 'a'.repeat(2 * i)), 'even a enumerator');
  const d = TM.dovetail(L.get('anbn'), ['a', 'b'], { rounds: 40 });
  t.ok(d.printed.every((w) => L.entry('anbn').oracle(w)), 'dovetailing prints only members');
  t.ok(['', 'ab', 'aabb'].every((w) => d.printed.includes(w)), 'dovetailing finds the short members');
  const loopy = TM.compile('input: a b\nq0, a -> q0, a, R\nq0, _ -> qa, _, S\nq0, b -> q0, b, S');
  const d2 = TM.dovetail(loopy, ['a', 'b'], { rounds: 20 });
  t.ok(d2.printed.includes('aa') && !d2.printed.includes('b'), 'a looping input does not block the others');
  t.eq(TM.recogniseByEnumerator(L.get('enum-binary'), '101').verdict, 'accept', 'recogniser from an enumerator');
}

// ---------- macros ----------
{
  const c = T.tmMacro.compile('alphabet: a b\ncall copy', { output: 'tape' });
  t.eq(c.errors, [], 'copy macro compiles');
  for (const w of all(['a', 'b'], 7)) t.eq(TM.run(c.machine, w, { trace: false }).output, w + '#' + w, `macro copy on ${w}`);
  t.ok(c.trace.some((s) => s.kind === 'inline') && c.trace.some((s) => s.kind === 'stmt') && c.trace[c.trace.length - 1].kind === 'done', 'expansion is traced');
  const d = T.tmMacro.compile('alphabet: 0 1\ncall tm:bin-inc\ncall tm:bin-inc', { output: 'tape' });
  for (const w of all(['0', '1'], 7)) {
    const want = L.entry('bin-inc').oracle(L.entry('bin-inc').oracle(w));
    t.eq(TM.run(d.machine, w, { trace: false }).output, want, `two inlined increments on ${w}`);
  }
  const even = T.tmMacro.compile(`alphabet: a b
even:
  if _ accept
  if a goto odd1
  right
  goto even
odd1:
  right
odd:
  if _ reject
  if a goto even1
  right
  goto odd
even1:
  right
  goto even`);
  for (const w of all(['a', 'b'], 8)) t.eq(TM.run(even.machine, w, { trace: false }).verdict, [...w].filter((c) => c === 'a').length % 2 ? 'reject' : 'accept', `macro parity of a's on ${w}`);
  const add = T.tmMacro.compile('alphabet: 1 +\nseek R +\nwrite 1\nseek R _\nleft\nwrite _', { output: 'tape' });
  for (const w of all(['1', '+'], 8).filter((w) => /^1*\+1*$/.test(w))) t.eq(TM.run(add.machine, w, { trace: false }).output, '1'.repeat(w.length - 1), `macro unary add on ${w}`);
  const sub = T.tmMacro.compile('alphabet: a b\nsub twice\n  right\n  right\nsub main\n  call twice\n  call twice\n  if a accept\n  reject');
  for (const w of all(['a', 'b'], 6)) t.eq(TM.run(sub.machine, w, { trace: false }).verdict, w[4] === 'a' ? 'accept' : 'reject', `macro subroutine called twice on ${w}`);
  t.ok(T.tmMacro.compile('goto nowhere').errors.length > 0, 'unknown label is an error');
  t.ok(T.tmMacro.compile('sub r\n  call r\nsub main\n  call r').errors.some((e) => /itself/.test(e.msg)), 'recursion is an error');
  t.ok(T.tmMacro.compile('x:\n  goto x').errors.some((e) => /never moves/.test(e.msg)), 'an empty goto loop is an error');
  t.ok(T.tmMacro.compile('frobnicate').errors.length === 1, 'unknown statement is an error');
}

// ---------- encodings ----------
const E = T.enc;
for (const e of L.list) {
  const M = L.get(e.id);
  if (M.k !== 1 || M.mode !== 'standard' || !M.deterministic || e.kind === 'grid' || e.kind === 'enumerator') continue;
  const enc = E.encodeTM(M);
  t.ok(E.checkTM(enc.code).ok, `${e.id} encodes to a valid code`);
  const dec = E.decodeTM(enc.code, { symbols: enc.symbolNames, input: M.input });
  t.ok(dec.ok, `${e.id} decodes`);
  t.eq(E.encodeTM(dec.machine).code, enc.code, `${e.id} encode ∘ decode ∘ encode is stable`);
  const inputs = e.kind === 'beaver' ? [''] : all(e.alphabet, 4).filter((w) => !e.domain || e.domain(w));
  for (const w of inputs) {
    const a = TM.run(M, w, { trace: false, maxSteps: 20000 }), b = TM.run(dec.machine, w, { trace: false, maxSteps: 20000 });
    t.eq([b.verdict, b.steps], [a.verdict, a.steps], `${e.id} decoded machine behaves the same on ${w}`);
    t.eq(b.config.tapes[0].trimmed().join(''), a.config.tapes[0].trimmed().join(''), `${e.id} decoded machine leaves the same tape on ${w}`);
    // the universal machine
    if (w.length <= 3) {
      const { code } = E.encodeTMInput(M, w);
      const u = T.utm.run(code, { maxSteps: 20000, trace: false });
      if (a.verdict === 'loop') { t.eq(u.verdict, 'limit', `UTM keeps running where ${e.id} loops on ${w}`); continue; }
      t.eq([u.verdict, u.steps], [a.verdict, a.steps], `UTM agrees with ${e.id} on ${w}`);
      const tape = a.config.tapes[0], lo = Math.min(tape.bounds().lo, 0);
      const strip = (arr) => { let s = 0, f = arr.length; while (s < f && arr[s] === 1) s++; while (f > s && arr[f - 1] === 1) f--; return arr.slice(s, f).join(','); };
      t.eq(strip(u.work), strip(tape.slice(lo, Math.max(tape.bounds().hi, 0)).map((s) => enc.symbols[s])), `UTM work tape matches ${e.id} on ${w}`);
    }
  }
}
{
  const { code } = E.encodeTMInput(L.get('anbn'), 'ab');
  const u = T.utm.run(code);
  t.ok(u.trace.some((s) => s.kind === 'utm-find') && u.trace.every((s) => typeof s.tape1 === 'string' && typeof s.tape2 === 'string' && /^0*$/.test(s.tape3)), 'UTM trace shows three tapes');
  t.eq(u.verdict, 'accept', 'UTM accepts ⟨anbn, ab⟩');
  t.ok(u.cost > u.steps, 'UTM cost exceeds the simulated steps');
  t.eq(T.utm.run('0101').verdict, 'invalid', 'UTM rejects a code with no 111');
}
// random binary strings: valid codes decode and re-encode to themselves (rules sorted), invalid ones are explained
{
  let valid = 0;
  for (let i = 0; i < 3000; i++) {
    const len = 9 + R.int(20);
    let s = '';
    for (let j = 0; j < len; j++) s += R() < 0.7 ? '0' : '1';
    const c = E.checkTM(s);
    if (c.ok) {
      valid++;
      const d = E.decodeTM(s);
      const back = E.checkTM(E.encodeTM(d.machine).code);
      t.eq(back.rules.map((r) => r.join()).sort(), c.rules.map((r) => r.join()).sort(), `re-encoding a decoded code keeps its rules (${s})`);
    } else t.ok(c.errors.length > 0, 'an invalid code says why');
  }
  t.ok(valid > 20, `some random strings are valid codes (${valid})`);
  t.ok(E.checkTM('010101010110101010100').errors.some((x) => /deterministic/.test(x)), 'duplicate rule is caught');
  t.ok(E.checkTM('0010101010').errors.some((x) => /halting/.test(x)), 'rules out of halting states are caught');
  t.ok(E.checkTM('0101010100000').errors.some((x) => /move/.test(x)), 'bad move is caught');
}
for (let i = 0; i < 500; i++) {
  const x = [...Array(R.int(8))].map(() => (R() < 0.5 ? '0' : '1')).join(''), y = [...Array(R.int(8))].map(() => (R() < 0.5 ? '0' : '1')).join('');
  t.eq(E.unpair(E.pair(x, y)), [x, y], 'pair round trip');
}
// random DFAs and grammars round trip
for (let i = 0; i < 300; i++) {
  const n = 1 + R.int(4), alpha = ['a', 'b', 'c'].slice(0, 1 + R.int(3));
  const states = Array.from({ length: n }, (_, j) => 'q' + (j + 1));
  const delta = {};
  for (const q of states) { delta[q] = {}; for (const a of alpha) delta[q][a] = R.pick(states); }
  const D = { states, alphabet: alpha, start: 'q1', accept: states.filter(() => R() < 0.5), delta };
  const d = E.decodeDFA(E.encodeDFA(D).code, { alphabet: alpha });
  t.ok(d.ok, 'DFA code decodes');
  t.eq(d.dfa.delta, delta, 'DFA round trip keeps the moves');
  t.eq(d.dfa.accept.slice().sort(), D.accept.slice().sort(), 'DFA round trip keeps the accepting states');
}
t.ok(!E.decodeDFA('0101110101011101').ok, 'an incomplete DFA code is invalid');
for (let i = 0; i < 200; i++) {
  const vars = ['S', 'A', 'B'].slice(0, 1 + R.int(3)), terms = ['a', 'b'];
  const rules = [];
  for (let k = 0; k < 1 + R.int(5); k++) rules.push({ lhs: R.pick(vars), rhs: [...Array(R.int(4))].map(() => R.pick(vars.concat(terms))) });
  const G = { start: 'S', variables: vars, terminals: terms, rules };
  const d = E.decodeCFG(E.encodeCFG(G).code, { variables: vars, terminals: terms });
  t.ok(d.ok, 'grammar code decodes');
  t.eq(d.cfg.rules, rules, 'grammar round trip');
}
// machines in the order of their encodings
{
  const ms = E.enumerateMachines(40);
  t.eq(ms.length, 40, 'forty machines enumerated');
  t.eq(ms[0].code, '', 'the empty code comes first (no rules: rejects everything)');
  for (let i = 1; i < ms.length; i++) t.ok(ms[i - 1].code.length < ms[i].code.length || (ms[i - 1].code.length === ms[i].code.length && ms[i - 1].code < ms[i].code), `enumeration is in shortlex order at ${i}`);
  for (const m of ms) t.ok(E.checkTM(m.code).ok && m.machine, `enumerated code ${m.code} is valid`);
}

t.done();
