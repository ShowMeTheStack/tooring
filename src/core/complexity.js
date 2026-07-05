// Complexity helpers: step counts of Turing machines, growth-rate comparison, NP verifiers that check
// certificates, brute-force solvers, TQBF as a game tree, and reachability with Savitch's recursion.
//
// Graphs are {n, edges: [[u, v], …], directed?: bool, labels?: [..]} with vertices 0 … n-1.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  // ---------- time ----------
  // For each length, the worst and average number of steps over all inputs (or the inputs given).
  function stepCounts(M, alphabet, maxLen, opts = {}) {
    const rows = [];
    for (let n = 0; n <= maxLen; n++) {
      const ws = opts.inputs ? opts.inputs(n) : T.tm.strings(alphabet, n).filter((w) => w.length === n);
      let worst = -1, worstInput = null, total = 0, count = 0;
      for (const w of ws) {
        const r = T.tm.run(M, w, { maxSteps: opts.maxSteps || 100000, trace: false, loops: false });
        if (r.steps > worst) { worst = r.steps; worstInput = w; }
        total += r.steps; count++;
      }
      if (count) rows.push({ n, worst, average: total / count, worstInput, inputs: count });
    }
    return rows;
  }

  const GROWTH = [
    { id: '1', name: '1', f: () => 1 },
    { id: 'log', name: 'log n', f: (n) => Math.log2(Math.max(n, 2)) },
    { id: 'n', name: 'n', f: (n) => n },
    { id: 'nlog', name: 'n log n', f: (n) => n * Math.log2(Math.max(n, 2)) },
    { id: 'n2', name: 'n²', f: (n) => n * n },
    { id: 'n3', name: 'n³', f: (n) => n ** 3 },
    { id: '2n', name: '2ⁿ', f: (n) => 2 ** n },
    { id: 'fact', name: 'n!', f: (n) => { let r = 1; for (let i = 2; i <= n; i++) r *= i; return r; } },
  ];
  // Compare f and g by the trend of f(n)/g(n) along n = 2^k: if the ratio still grows by more than 15% over
  // the second half of the range, f = ω(g); if it still shrinks that much, f = o(g); otherwise Θ. A finite
  // range can only suggest the answer (n^1.01 against n looks like Θ here).
  function compareGrowth(f, g, opts = {}) {
    const ks = opts.ks || [4, 8, 12, 16, 20, 24, 28, 32, 36, 40];
    const ratios = ks.map((k) => { const n = 2 ** k; return f(n) / g(n); });
    const mid = ratios[Math.floor(ratios.length / 2)], last = ratios[ratios.length - 1];
    let rel;
    if (!isFinite(last) || (mid > 0 && last / mid > 1.15) || (mid === 0 && last > 0)) rel = 'ω';
    else if (last === 0 || last / mid < 1 / 1.15) rel = 'o';
    else rel = 'Θ';
    return { relation: rel, ratios: ratios.map((r, i) => ({ n: 2 ** ks[i], ratio: r })), say: rel === 'o' ? 'f grows strictly slower than g: f = o(g).' : rel === 'ω' ? 'f grows strictly faster than g: f = ω(g).' : 'f and g grow at the same rate up to constants: f = Θ(g).' };
  }
  // The smallest n ≥ 1 from which f(n) ≤ g(n) holds up to `upTo` (null if never).
  function crossover(f, g, upTo = 200) {
    let from = null;
    for (let n = 1; n <= upTo; n++) { if (f(n) <= g(n)) { if (from == null) from = n; } else from = null; }
    return from;
  }
  // Which growth class fits measured (n, steps) pairs best: the one whose ratio steps/f(n) varies least on the larger half.
  function fitGrowth(points) {
    const pts = points.filter((p) => p.n >= 2 && p.value > 0);
    const half = pts.slice(Math.floor(pts.length / 2));
    let best = null;
    for (const G of GROWTH) {
      const rs = half.map((p) => p.value / G.f(p.n));
      const mean = rs.reduce((a, b) => a + b, 0) / rs.length;
      const spread = Math.max(...rs.map((r) => Math.abs(Math.log(r / mean))));
      if (!best || spread < best.spread) best = { id: G.id, name: G.name, spread, constant: mean };
    }
    return best;
  }

  // ---------- graphs ----------
  const adjacency = (G) => {
    const adj = Array.from({ length: G.n }, () => new Set());
    for (const [u, v] of G.edges) { adj[u].add(v); if (!G.directed) adj[v].add(u); }
    return adj;
  };
  const hasEdge = (G, adj, u, v) => adj[u].has(v);
  function complement(G) {
    const adj = adjacency(G), edges = [];
    for (let u = 0; u < G.n; u++) for (let v = u + 1; v < G.n; v++) if (!adj[u].has(v)) edges.push([u, v]);
    return { n: G.n, edges, labels: G.labels };
  }
  function* combinations(n, k, start = 0, acc = []) {
    if (acc.length === k) { yield acc.slice(); return; }
    for (let i = start; i <= n - (k - acc.length); i++) { acc.push(i); yield* combinations(n, k, i + 1, acc); acc.pop(); }
  }

  // ---------- verifiers: each checks a certificate and explains every check ----------
  const verdict = (checks) => { const bad = checks.find((c) => !c.ok); return { ok: !bad, reason: bad ? bad.say : '', trace: checks.map((c) => Object.assign({ kind: c.ok ? 'check' : 'fail' }, c)) }; };
  const distinct = (S, n) => new Set(S).size === S.length && S.every((v) => Number.isInteger(v) && v >= 0 && v < n);

  function verifyClique(G, k, S) {
    const adj = adjacency(G), checks = [{ ok: distinct(S, G.n), say: `The certificate lists ${S.length} distinct vertices.` }, { ok: S.length >= k, say: `It has at least k = ${k} vertices.` }];
    for (let i = 0; i < S.length; i++) for (let j = i + 1; j < S.length; j++) checks.push({ ok: hasEdge(G, adj, S[i], S[j]), say: `${S[i]} and ${S[j]} are ${hasEdge(G, adj, S[i], S[j]) ? '' : 'not '}joined.`, pair: [S[i], S[j]] });
    return verdict(checks);
  }
  function verifyIndependentSet(G, k, S) {
    const adj = adjacency(G), checks = [{ ok: distinct(S, G.n), say: `The certificate lists ${S.length} distinct vertices.` }, { ok: S.length >= k, say: `It has at least k = ${k} vertices.` }];
    for (let i = 0; i < S.length; i++) for (let j = i + 1; j < S.length; j++) checks.push({ ok: !hasEdge(G, adj, S[i], S[j]), say: `${S[i]} and ${S[j]} are ${hasEdge(G, adj, S[i], S[j]) ? '' : 'not '}joined.`, pair: [S[i], S[j]] });
    return verdict(checks);
  }
  function verifyVertexCover(G, k, S) {
    const inS = new Set(S), checks = [{ ok: distinct(S, G.n), say: `The certificate lists ${S.length} distinct vertices.` }, { ok: S.length <= k, say: `It has at most k = ${k} vertices.` }];
    for (const [u, v] of G.edges) checks.push({ ok: inS.has(u) || inS.has(v), say: `Edge ${u}–${v} is ${inS.has(u) || inS.has(v) ? '' : 'not '}covered.`, edge: [u, v] });
    return verdict(checks);
  }
  function verifyHamPath(G, path, s = null, t = null) {
    const adj = adjacency(G), checks = [{ ok: path.length === G.n && distinct(path, G.n), say: `The path visits all ${G.n} vertices exactly once.` }];
    if (s != null) checks.push({ ok: path[0] === s, say: `It starts at ${s}.` });
    if (t != null) checks.push({ ok: path[path.length - 1] === t, say: `It ends at ${t}.` });
    for (let i = 0; i + 1 < path.length; i++) checks.push({ ok: hasEdge(G, adj, path[i], path[i + 1]), say: `${path[i]} → ${path[i + 1]} is ${hasEdge(G, adj, path[i], path[i + 1]) ? 'an' : 'not an'} edge.`, edge: [path[i], path[i + 1]] });
    return verdict(checks);
  }
  function verifyHamCycle(G, cyc) {
    const r = verifyHamPath(G, cyc);
    const adj = adjacency(G), close = cyc.length > 1 && hasEdge(G, adj, cyc[cyc.length - 1], cyc[0]);
    return verdict(r.trace.map((c) => ({ ok: c.kind === 'check', say: c.say })).concat([{ ok: close, say: `The last vertex ${cyc[cyc.length - 1]} ${close ? 'connects' : 'does not connect'} back to ${cyc[0]}.` }]));
  }
  function verifySubsetSum(nums, target, idxs) {
    const sum = idxs.reduce((a, i) => a + nums[i], 0);
    return verdict([{ ok: distinct(idxs, nums.length), say: 'The certificate picks distinct positions.' }, { ok: sum === target, say: `The chosen numbers add up to ${sum}${sum === target ? ', the target' : `, not ${target}`}.`, sum }]);
  }
  function verifyColouring(G, k, colour) {
    const checks = [{ ok: colour.length === G.n && colour.every((c) => Number.isInteger(c) && c >= 0 && c < k), say: `Every vertex gets one of ${k} colours.` }];
    for (const [u, v] of G.edges) checks.push({ ok: colour[u] !== colour[v], say: `Edge ${u}–${v}: colours ${colour[u]} and ${colour[v]}${colour[u] === colour[v] ? ' clash' : ' differ'}.`, edge: [u, v] });
    return verdict(checks);
  }
  function verifySat(f, a) {
    return verdict(f.clauses.map((c, i) => { const ok = T.sat.evalClause(c, a); return { ok, say: `Clause ${i + 1} ${T.sat.toText({ clauses: [c], names: f.names })} is ${ok ? 'true' : 'false'}.`, clause: i }; }));
  }

  // ---------- brute force ----------
  // Clique and independent set by backtracking over vertices in order, keeping only candidates that fit
  // with everything chosen so far, and giving up on a branch when too few candidates are left.
  function growSet(G, k, compatible) {
    const adj = adjacency(G), chosen = [];
    const go = (cands) => {
      if (chosen.length >= k) return true;
      for (let i = 0; i < cands.length; i++) {
        if (chosen.length + cands.length - i < k) return false;
        const v = cands[i];
        chosen.push(v);
        if (go(cands.slice(i + 1).filter((u) => compatible(adj, u, v)))) return true;
        chosen.pop();
      }
      return false;
    };
    return go([...Array(G.n).keys()]) ? chosen.slice(0, k) : null;
  }
  const findClique = (G, k) => growSet(G, k, (adj, u, v) => adj[u].has(v));
  const findIndependentSet = (G, k) => growSet(G, k, (adj, u, v) => !adj[u].has(v));
  // Vertex cover by the bounded search tree: some end of an uncovered edge must be in the cover.
  function findVertexCover(G, k) {
    const cover = new Set();
    const go = (budget) => {
      const e = G.edges.find(([u, v]) => !cover.has(u) && !cover.has(v));
      if (!e) return true;
      if (!budget) return false;
      for (const x of e) { cover.add(x); if (go(budget - 1)) return true; cover.delete(x); }
      return false;
    };
    return go(k) ? [...cover].sort((a, b) => a - b) : null;
  }
  // depth-first search with backtracking; s / t optional ends; cycle = true asks for a Hamiltonian cycle
  function findHamPath(G, s = null, t = null, opts = {}) {
    const adj = adjacency(G).map((x) => [...x]), n = G.n, used = new Array(n).fill(false), path = [];
    let budget = opts.maxNodes || 5e6;
    const go = (u) => {
      if (--budget < 0) throw new Error('search budget exhausted');
      path.push(u); used[u] = true;
      if (path.length === n) {
        if ((t == null || u === t) && (!opts.cycle || adj[u].includes(path[0]))) return true;
      } else for (const v of adj[u]) if (!used[v] && (t == null || v !== t || path.length === n - 1) && go(v)) return true;
      path.pop(); used[u] = false;
      return false;
    };
    for (const start of s != null ? [s] : opts.cycle ? [0] : Array.from({ length: n }, (_, i) => i)) if (n && go(start)) return path.slice();
    return null;
  }
  function findSubsetSum(nums, target) {
    const reach = new Map([[0, null]]);
    nums.forEach((x, i) => { for (const [s] of [...reach]) { const t = s + x; if (!reach.has(t) && t <= target) reach.set(t, { prev: s, i }); } });
    if (!reach.has(target)) return null;
    const idx = [];
    for (let s = target; reach.get(s); s = reach.get(s).prev) idx.push(reach.get(s).i);
    return idx.reverse();
  }
  function findColouring(G, k) {
    const adj = adjacency(G).map((x) => [...x]), col = new Array(G.n).fill(-1);
    const go = (v) => {
      if (v === G.n) return true;
      for (let c = 0; c < k; c++) { if (adj[v].some((u) => col[u] === c)) continue; col[v] = c; if (go(v + 1)) return true; }
      col[v] = -1; return false;
    };
    return go(0) ? col.slice() : null;
  }

  // ---------- space: TQBF and reachability ----------
  // A quantified formula: prefix [{q: 'E' | 'A', v}] over variables, matrix a CNF on the same numbering.
  // Evaluated as a game: the ∃-player picks values to make it true, the ∀-player to make it false.
  function tqbf(prefix, matrix, opts = {}) {
    const nodes = [], trace = [], traceLimit = opts.traceLimit || 2000;
    const a = new Array((matrix.n || 0) + 1).fill(false);
    const go = (i, parent, choice) => {
      const node = { id: nodes.length, parent, depth: i, choice, value: null, best: null };
      nodes.push(node);
      if (i === prefix.length) {
        node.value = T.sat.evaluate(matrix, a);
        if (trace.length < traceLimit) trace.push({ kind: 'leaf', say: `With ${prefix.map((p) => `${T.sat.litText(matrix, p.v)} = ${a[p.v] ? 1 : 0}`).join(', ')} the formula is ${node.value ? 'true' : 'false'}.`, node: node.id, value: node.value });
        return node.value;
      }
      const { q, v } = prefix[i];
      let val = q === 'A';
      for (const b of [false, true]) {
        a[v] = b;
        const r = go(i + 1, node.id, { v, value: b });
        if (q === 'E' && r) { val = true; node.best = b; break; }
        if (q === 'A' && !r) { val = false; node.best = b; break; }
      }
      a[v] = false;
      node.value = val;
      if (trace.length < traceLimit) trace.push({ kind: q === 'E' ? 'exists' : 'forall', say: q === 'E' ? (val ? `∃ ${T.sat.litText(matrix, v)}: the choice ${node.best ? 1 : 0} wins.` : `∃ ${T.sat.litText(matrix, v)}: neither value wins.`) : (val ? `∀ ${T.sat.litText(matrix, v)}: both values lead to true.` : `∀ ${T.sat.litText(matrix, v)}: the value ${node.best ? 1 : 0} refutes it.`), node: node.id, value: val });
      return val;
    };
    const value = go(0, -1, null);
    trace.push({ kind: 'value', say: `The quantified formula is ${value ? 'true: the ∃-player has a winning strategy' : 'false: the ∀-player has a winning strategy'}.`, value });
    // space used: one bit per variable on the recursion path
    return { value, nodes, trace, depth: prefix.length };
  }

  // Breadth-first reachability (linear space).
  function reach(G, s, t) {
    const adj = adjacency(G), dist = new Array(G.n).fill(-1), q = [s], trace = [];
    dist[s] = 0;
    while (q.length) { const u = q.shift(); for (const v of adj[u]) if (dist[v] < 0) { dist[v] = dist[u] + 1; q.push(v); trace.push({ kind: 'visit', say: `Visit ${v} from ${u} (distance ${dist[v]}).`, from: u, to: v }); } }
    trace.push({ kind: dist[t] >= 0 ? 'reached' : 'unreached', say: dist[t] >= 0 ? `${t} is reachable from ${s} in ${dist[t]} steps.` : `${t} cannot be reached from ${s}.` });
    return { reachable: dist[t] >= 0, dist, trace };
  }
  // Savitch: can u reach v in at most 2^i steps? Try every midpoint m with two half-size questions.
  // Only the current chain of questions is remembered: depth log t, each a few vertex names.
  function savitch(G, s, t, opts = {}) {
    const adj = adjacency(G), trace = [], traceLimit = opts.traceLimit || 3000;
    const k = opts.k != null ? opts.k : Math.max(0, Math.ceil(Math.log2(Math.max(1, G.n))));
    let calls = 0, maxDepth = 0;
    const can = (u, v, i, d) => {
      calls++; maxDepth = Math.max(maxDepth, d);
      if (i === 0) {
        const r = u === v || adj[u].has(v);
        if (trace.length < traceLimit) trace.push({ kind: 'base', say: `Can ${u} reach ${v} in at most 1 step? ${r ? 'Yes' : 'No'}.`, u, v, steps: 1, depth: d, result: r });
        return r;
      }
      if (trace.length < traceLimit) trace.push({ kind: 'ask', say: `Can ${u} reach ${v} in at most ${2 ** i} steps? Try each midpoint.`, u, v, steps: 2 ** i, depth: d });
      for (let m = 0; m < G.n; m++) {
        if (can(u, m, i - 1, d + 1) && can(m, v, i - 1, d + 1)) {
          if (trace.length < traceLimit) trace.push({ kind: 'yes', say: `Yes: through ${m}, each half within ${2 ** (i - 1)} steps.`, u, v, mid: m, steps: 2 ** i, depth: d, result: true });
          return true;
        }
      }
      if (trace.length < traceLimit) trace.push({ kind: 'no', say: `No midpoint works: ${u} cannot reach ${v} in ${2 ** i} steps.`, u, v, steps: 2 ** i, depth: d, result: false });
      return false;
    };
    const r = can(s, t, k, 0);
    const bits = Math.ceil(Math.log2(Math.max(2, G.n)));
    return { reachable: r, calls, depth: maxDepth, k, spaceBits: (maxDepth + 1) * (3 * bits + Math.ceil(Math.log2(k + 2))), trace };
  }

  T.cx = {
    stepCounts, GROWTH, compareGrowth, crossover, fitGrowth,
    adjacency, complement, combinations,
    verifyClique, verifyIndependentSet, verifyVertexCover, verifyHamPath, verifyHamCycle, verifySubsetSum, verifyColouring, verifySat,
    findClique, findIndependentSet, findVertexCover, findHamPath, findSubsetSum, findColouring,
    tqbf, reach, savitch,
  };
})();
