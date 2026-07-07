// Complexity: SAT solvers against brute force, 2-SAT, the 3-SAT conversion, NP verifiers, every reduction
// on random instances (answers and certificates both ways), Cook–Levin, TQBF, Savitch and growth rates.
import { load, rng, harness } from './load.mjs';

const MINE = /core\/(tm|tm-multi|tm-lib|tm-macro|models|recursive|lambda|encode|computability|pcp|sat|complexity|reductions|cooklevin)\.js$/;
const T = load(['core'], (f) => MINE.test(f));
const t = harness('complexity');
const S = T.sat, X = T.cx, RD = T.red;
const R = S.rng(4242);

// ---------- parsing and printing ----------
{
  const f = S.parse('(x ∨ ¬y) ∧ (y ∨ z ∨ ~x) & (!z)');
  t.eq([f.n, f.clauses], [3, [[1, -2], [2, 3, -1], [-3]]], 'text CNF parses');
  t.eq(S.toText(f), '(x ∨ ¬y) ∧ (y ∨ z ∨ ¬x) ∧ (¬z)', 'CNF prints');
  const g = S.parse(S.toDimacs(f));
  t.eq([g.n, g.clauses], [f.n, f.clauses], 'DIMACS round trip');
  t.eq(S.parse('c comment\np cnf 2 2\n1 -2 0\n2 0').clauses, [[1, -2], [2]], 'DIMACS with comments');
  t.eq(S.parse('a or b\n-a').clauses, [[1, 2], [-1]], 'words and lines');
}

// ---------- DPLL and the fast solver against brute force ----------
for (let i = 0; i < 1500; i++) {
  const n = 1 + R.int(7), f = S.randomCNF(R, n, R.int(14), 4);
  const b = S.brute(f), d = S.dpll(f, { pure: R() < 0.7 }), s = S.solve(f);
  t.eq(d.sat, b.sat, 'traced DPLL agrees with brute force');
  t.eq(s.sat, b.sat, 'fast DPLL agrees with brute force');
  if (d.sat) t.ok(S.evaluate(f, d.assignment), 'traced DPLL assignment satisfies');
  if (s.sat) t.ok(S.evaluate(f, s.assignment), 'fast DPLL assignment satisfies');
  t.ok(d.tree.every((nd) => nd.parent < nd.id), 'decision tree parents precede children');
}
for (let i = 0; i < 40; i++) {
  const f = S.randomKCNF(R, 60, 230 + R.int(40), 3);
  const s = S.solve(f);
  if (s.sat) t.ok(S.evaluate(f, s.assignment), 'a 60-variable instance: the assignment satisfies');
  else t.ok(s.sat === false, 'a 60-variable instance is refuted');
}
{
  const f = S.parse('(a ∨ b) ∧ (¬a ∨ b) ∧ (a ∨ ¬b) ∧ (¬a ∨ ¬b ∨ c) ∧ (¬c ∨ d)');
  const d = S.dpll(f);
  t.ok(d.trace.some((s) => s.kind === 'decide') && d.trace.some((s) => s.kind === 'unit') && d.trace.some((s) => s.kind === 'satisfiable'), 'DPLL trace has decisions and unit steps');
  t.ok(S.dpll(S.parse('(a ∨ b) ∧ (a ∨ c)')).trace.some((s) => s.kind === 'pure'), 'pure literals are traced');
  const u = S.dpll(S.parse('(a) ∧ (¬a ∨ b) ∧ (¬b)'));
  t.ok(!u.sat && u.trace.some((s) => s.kind === 'conflict'), 'a conflict is traced');
}

// ---------- 2-SAT ----------
for (let i = 0; i < 800; i++) {
  const n = 1 + R.int(6), f = S.randomCNF(R, n, R.int(12), 2);
  const b = S.brute(f), r = S.twoSat(f);
  t.eq(r.sat, b.sat, '2-SAT agrees with brute force');
  if (r.sat) t.ok(S.evaluate(f, r.assignment), '2-SAT assignment satisfies');
  else t.ok(r.trace.some((s) => s.kind === 'conflict'), 'unsatisfiable 2-SAT names the clashing variable');
}

// ---------- SAT to 3-SAT ----------
for (let i = 0; i < 600; i++) {
  const n = 1 + R.int(5), f = S.randomCNF(R, n, 1 + R.int(6), 6);
  const r = RD.satTo3Sat(f), g = r.formula;
  t.ok(g.clauses.every((c) => c.length === 3), 'every clause has three literals');
  const bf = S.brute(f), bg = S.solve(g);
  t.eq(bg.sat, bf.sat, 'the 3-CNF is satisfiable exactly when the CNF is');
  if (bf.sat) t.ok(S.evaluate(g, r.forward(bf.assignment)), 'forward map gives a satisfying assignment');
  if (bg.sat) t.ok(S.evaluate(f, r.backward(bg.assignment)), 'backward map gives a satisfying assignment');
}

// ---------- verifiers and brute force ----------
const randomGraph = (n, p, directed = false) => { const edges = []; for (let u = 0; u < n; u++) for (let v = directed ? 0 : u + 1; v < n; v++) if (u !== v && R() < p) edges.push([u, v]); return { n, edges, directed }; };
for (let i = 0; i < 300; i++) {
  const G = randomGraph(2 + R.int(6), 0.5), k = 1 + R.int(4), adj = X.adjacency(G);
  const c = X.findClique(G, k), is = X.findIndependentSet(G, k), vc = X.findVertexCover(G, k), col = X.findColouring(G, 3);
  if (c) t.ok(X.verifyClique(G, k, c).ok, 'clique certificate verifies');
  if (is) t.ok(X.verifyIndependentSet(G, k, is).ok, 'independent set certificate verifies');
  if (vc) t.ok(X.verifyVertexCover(G, k, vc).ok, 'vertex cover certificate verifies');
  if (col) t.ok(X.verifyColouring(G, 3, col).ok, 'colouring certificate verifies');
  // random certificates: the verifier agrees with a direct check
  const S0 = [...new Set([...Array(k)].map(() => R.int(G.n)))];
  let clique = S0.length >= k;
  for (let a = 0; a < S0.length; a++) for (let b = a + 1; b < S0.length; b++) if (!adj[S0[a]].has(S0[b])) clique = false;
  t.eq(X.verifyClique(G, k, S0).ok, clique, 'clique verifier on a random set');
  const cols = [...Array(G.n)].map(() => R.int(3));
  t.eq(X.verifyColouring(G, 3, cols).ok, G.edges.every(([u, v]) => cols[u] !== cols[v]), 'colouring verifier on a random colouring');
  const D = randomGraph(2 + R.int(5), 0.45, true), hp = X.findHamPath(D);
  if (hp) t.ok(X.verifyHamPath(D, hp).ok, 'Hamiltonian path verifies');
  const perm = R.shuffle([...Array(D.n).keys()]);
  t.eq(!!hp || !X.verifyHamPath(D, perm).ok, true, 'no path found means a random order fails');
  const U = randomGraph(3 + R.int(4), 0.6), hc = X.findHamPath(U, null, null, { cycle: true });
  if (hc) t.ok(X.verifyHamCycle(U, hc).ok, 'Hamiltonian cycle verifies');
  const nums = [...Array(1 + R.int(6))].map(() => 1 + R.int(12)), target = R.int(30);
  const ss = X.findSubsetSum(nums, target);
  let exists = false;
  for (let m = 0; m < 2 ** nums.length; m++) if (nums.reduce((a, x, j) => a + (m & (1 << j) ? x : 0), 0) === target) exists = true;
  t.eq(!!ss, exists, 'subset sum search agrees with all subsets');
  if (ss) t.ok(X.verifySubsetSum(nums, target, ss).ok, 'subset sum certificate verifies');
}
t.ok(!X.verifyClique({ n: 3, edges: [[0, 1]] }, 2, [0, 2]).ok, 'a non-clique fails');
t.ok(X.verifySat(S.parse('(a ∨ b)'), [null, false, true]).ok, 'SAT verifier');

// ---------- the reductions ----------
// random 3-CNFs; some clauses shorter, some literals repeated
const random3 = () => {
  const n = 2 + R.int(3), m = 1 + R.int(6), clauses = [];
  for (let j = 0; j < m; j++) { const len = R() < 0.5 ? 3 : 1 + R.int(2), c = []; for (let p = 0; p < len; p++) { const v = 1 + R.int(n); c.push(R() < 0.5 ? -v : v); } clauses.push(c); }
  return { n, clauses, names: [null, ...Array.from({ length: n }, (_, i) => 'x' + (i + 1))] };
};
let sats = 0, unsats = 0;
for (let i = 0; i < 260; i++) {
  const f = random3(), b = S.brute(f);
  if (b.sat) sats++; else unsats++;
  // CLIQUE
  const c = RD.sat3ToClique(f), cq = X.findClique(c.graph, c.k);
  t.eq(!!cq, b.sat, '3SAT → CLIQUE keeps the answer');
  if (b.sat) t.ok(X.verifyClique(c.graph, c.k, c.forward(b.assignment)).ok, 'CLIQUE forward certificate');
  if (cq) t.ok(S.evaluate(f, c.backward(cq)), 'CLIQUE backward certificate');
  // INDEPENDENT SET
  const s = RD.sat3ToIS(f), is = X.findIndependentSet(s.graph, s.k);
  t.eq(!!is, b.sat, '3SAT → IS keeps the answer');
  if (b.sat) t.ok(X.verifyIndependentSet(s.graph, s.k, s.forward(b.assignment)).ok, 'IS forward certificate');
  if (is) t.ok(S.evaluate(f, s.backward(is)), 'IS backward certificate');
  // VERTEX COVER
  const v = RD.sat3ToVC(f), vc = X.findVertexCover(v.graph, v.k);
  t.eq(!!vc, b.sat, '3SAT → VC keeps the answer');
  if (b.sat) t.ok(X.verifyVertexCover(v.graph, v.k, v.forward(b.assignment)).ok, 'VC forward certificate');
  if (vc) t.ok(S.evaluate(f, v.backward(vc)), 'VC backward certificate');
  // SUBSET SUM
  const u = RD.sat3ToSubsetSum(f), ss = X.findSubsetSum(u.nums, u.target);
  t.eq(!!ss, b.sat, '3SAT → SUBSET SUM keeps the answer');
  if (b.sat) t.ok(X.verifySubsetSum(u.nums, u.target, u.forward(b.assignment)).ok, 'SUBSET SUM forward certificate');
  if (ss) t.ok(S.evaluate(f, u.backward(ss)), 'SUBSET SUM backward certificate');
  // 3-COLOUR
  const k3 = RD.sat3To3Colour(f), col = X.findColouring(k3.graph, 3);
  t.eq(!!col, b.sat, '3SAT → 3-COLOUR keeps the answer');
  if (b.sat) { const fc = k3.forward(b.assignment); t.ok(fc && X.verifyColouring(k3.graph, 3, fc).ok, '3-COLOUR forward certificate'); }
  if (col) t.ok(S.evaluate(f, k3.backward(col)), '3-COLOUR backward certificate');
  // HAM-PATH (smaller instances: the graph grows quickly)
  if (f.n <= 3 && f.clauses.length <= 3) {
    const h = RD.sat3ToHamPath(f), hp = X.findHamPath(h.graph, h.s, h.t);
    t.eq(!!hp, b.sat, '3SAT → HAM-PATH keeps the answer');
    if (b.sat) t.ok(X.verifyHamPath(h.graph, h.forward(b.assignment), h.s, h.t).ok, 'HAM-PATH forward certificate');
    if (hp) t.ok(S.evaluate(f, h.backward(hp)), 'HAM-PATH backward certificate');
  }
}
t.ok(sats > 30 && unsats > 30, `random formulas include both answers (${sats} satisfiable, ${unsats} not)`);
{
  const f = S.parse('(a ∨ b ∨ ¬c) ∧ (¬a ∨ c ∨ b)');
  for (const r of [RD.sat3ToClique(f), RD.sat3ToIS(f), RD.sat3ToVC(f), RD.sat3ToHamPath(f), RD.sat3To3Colour(f)]) {
    t.ok(r.draw.nodes.every((n) => n.label != null && n.role) && r.draw.edges.every((e) => e.role && e.a != null && e.b != null), `${r.name} is drawable with roles and labels`);
    t.ok(r.trace.length >= 3 && r.trace.every((s) => s.say), `${r.name} explains itself`);
  }
  const ham = RD.sat3ToHamPath(f);
  t.ok(['top', 'bottom', 'separator', 'left', 'right', 'clause'].every((role) => ham.draw.nodes.some((n) => n.role === role)), 'HAM-PATH gadget roles');
  const u = RD.sat3ToSubsetSum(f);
  t.eq(u.table.targetDigits, [1, 1, 1, 3, 3], 'subset sum target digits');
  t.eq(u.table.rows.length, 2 * 3 + 2 * 2, 'subset sum digit table rows');
}
for (let i = 0; i < 300; i++) {
  const G = randomGraph(1 + R.int(7), 0.45), k = R.int(G.n + 1);
  const is = X.findIndependentSet(G, k);
  const a = RD.isToVC(G, k), b = RD.isToClique(G, k);
  const vc = X.findVertexCover(a.graph, a.k), cl = X.findClique(b.graph, b.k);
  t.eq(!!vc, !!is, 'IS ↔ VC keeps the answer');
  t.eq(!!cl || k === 0, !!is || k === 0, 'IS ↔ CLIQUE keeps the answer');
  if (is) { t.ok(X.verifyVertexCover(a.graph, a.k, a.forward(is)).ok, 'IS → VC certificate'); t.ok(X.verifyClique(b.graph, b.k, b.forward(is)).ok, 'IS → CLIQUE certificate'); }
  if (vc) t.ok(X.verifyIndependentSet(G, k, a.backward(vc)).ok, 'VC → IS certificate');
  const c = RD.vcToIS(G, k), vc2 = X.findVertexCover(G, k);
  if (vc2) t.ok(X.verifyIndependentSet(c.graph, c.k, c.forward(vc2)).ok, 'VC → IS forward');
  const d = RD.cliqueToIS(G, k), cq = X.findClique(G, k);
  if (cq) t.ok(X.verifyIndependentSet(d.graph, d.k, d.forward(cq)).ok, 'CLIQUE → IS forward');
}

// ---------- Cook–Levin ----------
{
  const machines = [
    T.tm.compile('name: some-a\nnondet: yes\ninput: a b\nq0, a|b -> q0, *, R\nq0, a -> qa, a, S'),
    T.tm.compile('name: ends-b\nnondet: yes\ninput: a b\nq0, a|b -> q0, *, R\nq0, b -> q1, b, R\nq1, _ -> qa, _, S'),
    T.tm.compile('name: flip-guess\nnondet: yes\ninput: a b\nq0, a -> q1, b, R\nq0, a -> q0, a, R\nq0, b -> q0, b, R\nq1, b -> qa, b, S'),
    T.tm.compile('name: det-ab\ninput: a b\nq0, a -> q1, a, R\nq1, b -> qa, b, S'),
  ];
  for (const N of machines) for (const w of T.tm.strings(['a', 'b'], 3)) {
    const tb = 3;
    const ex = T.tm.ntmExhaustive(N, w, tb) === 'accept';
    const d = T.cook.demonstrate(N, w, tb, { solve: true });
    t.eq(d.accepts, ex, `${N.name} on ${w || 'ε'}: the tableau run agrees with exhaustive search`);
    t.eq(d.sat, ex, `${N.name} on ${w || 'ε'}: the formula is satisfiable exactly when the machine accepts`);
    if (ex) t.ok(d.runSatisfies, `${N.name} on ${w || 'ε'}: the accepting run satisfies the formula`);
    if (d.sat) {
      t.eq(d.solvedRows[0], d.build.start, 'the solved tableau starts with the start row');
      t.ok(d.solvedRows.some((row) => row.some((s) => s === 'q:qa')), 'the solved tableau reaches the accepting state');
    }
    const c = d.build.counts;
    t.eq(c.cell + c.start + c.accept + c.move, d.build.formula.clauses.length, 'clause counts add up');
  }
  const b = T.cook.build(machines[0], 'ab', 3);
  t.ok(['tableau', 'cell', 'start', 'accept', 'move', 'total'].every((k) => b.trace.some((s) => s.kind === k)), 'Cook–Levin construction is traced');
  t.eq(b.rows, 4, 'tableau has t + 1 rows');
  t.eq(b.cols, 7, 'tableau has max(|w|, t+1) + 3 columns');
  // a wrong tableau fails: break one cell of an accepting run
  const run = T.cook.acceptingRun(machines[0], 'ba', 3);
  const bad = run.rows.map((r) => r.slice());
  bad[1][3] = bad[1][3] === 'a' ? 'b' : 'a';
  const a = b.fromRun(run.rows), b2 = T.cook.build(machines[0], 'ba', 3);
  t.ok(S.evaluate(b2.formula, b2.fromRun(run.rows)), 'the true run satisfies');
  const ab = b2.fromRun(bad);
  t.ok(!ab || !S.evaluate(b2.formula, ab), 'a corrupted run does not');
  t.ok(a === null || Array.isArray(a), 'fromRun returns an assignment or null');
}

// ---------- TQBF ----------
const qbfBrute = (prefix, f) => {
  const a = new Array(f.n + 1).fill(false);
  const go = (i) => { if (i === prefix.length) return S.evaluate(f, a); const { q, v } = prefix[i]; a[v] = false; const x = go(i + 1); a[v] = true; const y = go(i + 1); a[v] = false; return q === 'E' ? x || y : x && y; };
  return go(0);
};
for (let i = 0; i < 400; i++) {
  const n = 1 + R.int(5), f = S.randomCNF(R, n, 1 + R.int(6), 3);
  const prefix = R.shuffle([...Array(n).keys()].map((x) => x + 1)).map((v) => ({ q: R() < 0.5 ? 'E' : 'A', v }));
  const r = X.tqbf(prefix, f);
  t.eq(r.value, qbfBrute(prefix, f), 'TQBF game tree agrees with full evaluation');
  t.ok(r.nodes.length >= 1 && r.trace[r.trace.length - 1].kind === 'value', 'TQBF tree and trace');
}

// ---------- reachability and Savitch ----------
for (let i = 0; i < 200; i++) {
  const G = randomGraph(2 + R.int(6), 0.25, true), s = R.int(G.n), d = R.int(G.n);
  const b = X.reach(G, s, d), sv = X.savitch(G, s, d);
  t.eq(sv.reachable, b.reachable, 'Savitch agrees with breadth-first search');
  t.ok(sv.depth <= sv.k, 'Savitch recursion depth is at most log n');
  const short = X.savitch(G, s, d, { k: 1 });
  t.eq(short.reachable, b.reachable && b.dist[d] <= 2, 'Savitch with 2 steps matches distance ≤ 2');
}

// ---------- time and growth ----------
{
  t.eq(X.stepCounts(T.tmLib.get('palindrome'), ['a', 'b'], 6).length, 7, 'one row per length');
  // worst cases on longer inputs: a run of a's is a palindrome, so every machine does its full work
  const runs = (n) => ['a'.repeat(n)];
  const pal = X.stepCounts(T.tmLib.get('palindrome'), ['a', 'b'], 48, { inputs: runs });
  t.eq(X.fitGrowth(pal.map((r) => ({ n: r.n, value: r.worst }))).id, 'n2', 'the palindrome machine takes quadratic time');
  const ev = X.stepCounts(T.tmLib.get('even-length'), ['a', 'b'], 48, { inputs: runs });
  t.eq(X.fitGrowth(ev.map((r) => ({ n: r.n, value: r.worst }))).id, 'n', 'the parity machine takes linear time');
  const two = X.stepCounts(T.tmLib.get('pal-2tape'), ['a', 'b'], 48, { inputs: runs });
  t.eq(X.fitGrowth(two.map((r) => ({ n: r.n, value: r.worst }))).id, 'n', 'two tapes make palindromes linear');
  t.eq(X.compareGrowth((n) => n, (n) => n * n).relation, 'o', 'n = o(n²)');
  t.eq(X.compareGrowth((n) => 3 * n * n + n, (n) => n * n).relation, 'Θ', '3n² + n = Θ(n²)');
  t.eq(X.compareGrowth((n) => 2 ** n, (n) => n ** 3).relation, 'ω', '2ⁿ = ω(n³)');
  t.eq(X.compareGrowth((n) => n * Math.log2(n), (n) => n).relation, 'ω', 'n log n = ω(n)');
  t.eq(X.crossover((n) => n * n, (n) => 2 ** n), 4, 'n² ≤ 2ⁿ from n = 4 on');
  t.eq(X.crossover((n) => 100 * n, (n) => n * n), 100, '100n ≤ n² from n = 100 on');
  t.eq(X.compareGrowth((n) => n, (n) => n * Math.log2(n)).relation, 'o', 'n = o(n log n)');
  t.eq(X.compareGrowth((n) => Math.log2(n), (n) => n).relation, 'o', 'log n = o(n)');
}

t.done();
