// A SAT toolkit: CNF parsing and printing, a DPLL solver traced as a decision tree (unit propagation and
// pure literals), a fast watched-literal DPLL for big formulas, 2-SAT by strongly connected components,
// the conversion to 3-SAT with certificate maps, random generators and brute force.
//
// A formula is {n, clauses: [[lit, …], …], names: [, name1, name2, …]} with literals as in DIMACS:
// variable v is v, its negation is -v.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  // ---------- seeded randomness ----------
  function rng(seed = 1) {
    let s = (seed >>> 0) || 0x9e3779b9;
    const r = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
    r.int = (n) => Math.floor(r() * n);
    r.pick = (a) => a[Math.floor(r() * a.length)];
    r.shuffle = (a) => { for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; };
    return r;
  }

  // ---------- parsing and printing ----------
  // DIMACS (p cnf n m, clauses ending in 0) or text like (x ∨ ¬y) ∧ (y ∨ z); also | & ~ ! - and "or"/"and".
  function parse(text) {
    const src = String(text).trim();
    if (/^(c|p)\s/m.test(src) && /(^|\n)\s*p\s+cnf/.test(src)) {
      let n = 0;
      const clauses = [];
      let cur = [];
      for (const line of src.split('\n')) {
        const l = line.trim();
        if (!l || l[0] === 'c') continue;
        if (l[0] === 'p') { n = +l.split(/\s+/)[2]; continue; }
        for (const tok of l.split(/\s+/)) { const v = +tok; if (v === 0) { clauses.push(cur); cur = []; } else { cur.push(v); n = Math.max(n, Math.abs(v)); } }
      }
      if (cur.length) clauses.push(cur);
      return { n, clauses, names: [null, ...Array.from({ length: n }, (_, i) => 'x' + (i + 1))] };
    }
    const names = [null], index = new Map(), clauses = [];
    const parts = src.split(/∧|&|\band\b|\)\s*\(|\n/).map((p) => p.replace(/[()]/g, '').trim()).filter(Boolean);
    for (const p of parts) {
      const clause = [];
      for (let lit of p.split(/∨|\||\bor\b|,/)) {
        lit = lit.trim();
        if (!lit) continue;
        let neg = false;
        while (/^[¬~!-]/.test(lit)) { neg = !neg; lit = lit.slice(1).trim(); }
        if (!/^[A-Za-z_][\w']*$/.test(lit)) throw new Error(`cannot read the literal "${lit}"`);
        if (!index.has(lit)) { index.set(lit, names.length); names.push(lit); }
        clause.push(neg ? -index.get(lit) : index.get(lit));
      }
      clauses.push(clause);
    }
    return { n: names.length - 1, clauses, names };
  }
  const litText = (f, l) => (l < 0 ? '¬' : '') + ((f.names && f.names[Math.abs(l)]) || 'x' + Math.abs(l));
  const toText = (f) => (f.clauses.length ? f.clauses.map((c) => '(' + (c.length ? c.map((l) => litText(f, l)).join(' ∨ ') : '□') + ')').join(' ∧ ') : '⊤');
  const toDimacs = (f) => [`p cnf ${f.n} ${f.clauses.length}`, ...f.clauses.map((c) => c.join(' ') + ' 0')].join('\n');

  // assignment: array a[1..n] of booleans
  const evalClause = (c, a) => c.some((l) => (l > 0 ? a[l] : !a[-l]));
  const evaluate = (f, a) => f.clauses.every((c) => evalClause(c, a));

  // ---------- brute force ----------
  function brute(f, opts = {}) {
    const a = new Array(f.n + 1).fill(false);
    let count = 0, first = null;
    for (let m = 0; m < 2 ** f.n; m++) {
      for (let v = 1; v <= f.n; v++) a[v] = !!(m & (1 << (v - 1)));
      if (evaluate(f, a)) { count++; if (!first) first = a.slice(); if (!opts.count) break; }
    }
    return { sat: !!first, assignment: first, count: opts.count ? count : null };
  }

  // ---------- DPLL, traced as a decision tree ----------
  // Each node of the tree is a decision (var := value) together with the assignments it forces by unit
  // propagation and pure literals; a node ends in a conflict, in success, or with two children.
  function dpll(f, opts = {}) {
    const usePure = opts.pure !== false, maxNodes = opts.maxNodes || 20000, traceLimit = opts.traceLimit || 3000;
    const trace = [], nodes = [];
    let stats = { decisions: 0, units: 0, pures: 0, conflicts: 0 };
    const name = (l) => litText(f, l);
    const note = (s) => { if (trace.length < traceLimit) trace.push(s); };
    // simplify a clause list under literal l being true
    const assign = (cls, l) => cls.filter((c) => !c.includes(l)).map((c) => c.filter((x) => x !== -l));
    let result = null;
    const go = (cls, asg, parent, decision) => {
      const node = { id: nodes.length, parent, decision, implied: [], result: 'open' };
      nodes.push(node);
      if (nodes.length > maxNodes) { node.result = 'cut'; return 'cut'; }
      if (decision) { stats.decisions++; note({ kind: 'decide', say: `Try ${name(decision)} = true.`, node: node.id, parent, lit: decision, clauses: cls.length }); }
      // unit propagation and pure literals until nothing changes
      for (let changed = true; changed;) {
        changed = false;
        if (cls.some((c) => !c.length)) break;
        const unit = cls.find((c) => c.length === 1);
        if (unit) {
          const l = unit[0];
          cls = assign(cls, l); asg[Math.abs(l)] = l > 0; node.implied.push({ lit: l, why: 'unit' }); stats.units++;
          note({ kind: 'unit', say: `The clause (${name(l)}) is a unit: ${name(l)} must be true.`, node: node.id, lit: l, clauses: cls.length });
          changed = true; continue;
        }
        if (usePure) {
          const seen = new Map();
          for (const c of cls) for (const l of c) seen.set(l, true);
          const pure = [...seen.keys()].find((l) => !seen.has(-l));
          if (pure != null) {
            cls = assign(cls, pure); asg[Math.abs(pure)] = pure > 0; node.implied.push({ lit: pure, why: 'pure' }); stats.pures++;
            note({ kind: 'pure', say: `${name(pure)} appears only with this sign: make it true.`, node: node.id, lit: pure, clauses: cls.length });
            changed = true;
          }
        }
      }
      if (cls.some((c) => !c.length)) {
        node.result = 'conflict'; stats.conflicts++;
        note({ kind: 'conflict', say: 'A clause has every literal false: back up.', node: node.id });
        return 'conflict';
      }
      if (!cls.length) {
        node.result = 'sat';
        const a = asg.slice();
        for (let v = 1; v <= f.n; v++) if (a[v] == null) a[v] = false;
        result = a;
        note({ kind: 'sat', say: 'Every clause is satisfied.', node: node.id, assignment: a.slice(1) });
        return 'sat';
      }
      // branch on a variable from a shortest clause (lowest number on ties)
      let best = null;
      for (const c of cls) if (!best || c.length < best.length) best = c;
      const v = Math.min(...best.map(Math.abs));
      node.result = 'split';
      for (const l of [v, -v]) {
        const r = go(assign(cls, l), Object.assign([], asg, { [v]: l > 0 }), node.id, l);
        if (r === 'sat' || r === 'cut') return r;
      }
      note({ kind: 'backtrack', say: `Both values of ${name(v)} fail here.`, node: node.id, var: v });
      return 'conflict';
    };
    const r = go(f.clauses.map((c) => [...new Set(c)]).filter((c) => !c.some((l) => c.includes(-l))), new Array(f.n + 1).fill(null), -1, null);
    note({ kind: r === 'sat' ? 'satisfiable' : r === 'cut' ? 'limit' : 'unsatisfiable', say: r === 'sat' ? 'The formula is satisfiable.' : r === 'cut' ? 'Stopped: the search tree grew too large.' : 'Every branch ended in a conflict: the formula is unsatisfiable.' });
    return { sat: r === 'sat', verdict: r === 'cut' ? 'limit' : r === 'sat' ? 'sat' : 'unsat', assignment: result, tree: nodes, stats, trace };
  }

  // ---------- a fast DPLL (watched literals, chronological backtracking), for big formulas ----------
  function solve(f, opts = {}) {
    const n = f.n, maxDecisions = opts.maxDecisions || 5e6;
    const val = new Int8Array(n + 1); // 0 unknown, 1 true, -1 false
    const lv = (l) => (l > 0 ? val[l] : -val[-l]);
    const clauses = [];
    for (const c0 of f.clauses) {
      const c = [...new Set(c0)];
      if (c.some((l) => c.includes(-l))) continue; // always true
      clauses.push(c);
    }
    const watch = new Map();
    const W = (l) => { let a = watch.get(l); if (!a) { a = []; watch.set(l, a); } return a; };
    const trail = [], units = [];
    for (let i = 0; i < clauses.length; i++) {
      const c = clauses[i];
      if (!c.length) return { sat: false, assignment: null, decisions: 0 };
      if (c.length === 1) units.push(c[0]); else { W(c[0]).push(i); W(c[1]).push(i); }
    }
    const set = (l) => { val[Math.abs(l)] = l > 0 ? 1 : -1; trail.push(l); };
    let qhead = 0;
    const propagate = () => {
      while (qhead < trail.length) {
        const p = trail[qhead++], fl = -p, ws = watch.get(fl);
        if (!ws) continue;
        for (let i = 0; i < ws.length;) {
          const ci = ws[i], c = clauses[ci];
          if (c[0] === fl) { c[0] = c[1]; c[1] = fl; }
          if (lv(c[0]) === 1) { i++; continue; }
          let moved = false;
          for (let k = 2; k < c.length; k++) if (lv(c[k]) !== -1) { c[1] = c[k]; c[k] = fl; W(c[1]).push(ci); ws[i] = ws[ws.length - 1]; ws.pop(); moved = true; break; }
          if (moved) continue;
          if (lv(c[0]) === -1) return false;
          if (lv(c[0]) === 0) set(c[0]);
          i++;
        }
      }
      return true;
    };
    // level-0 units
    for (const u of units) { if (lv(u) === -1) return { sat: false, assignment: null, decisions: 0 }; if (lv(u) === 0) set(u); }
    // order variables by how often they occur
    const occ = new Int32Array(n + 1);
    for (const c of clauses) for (const l of c) occ[Math.abs(l)]++;
    const order = Array.from({ length: n }, (_, i) => i + 1).sort((a, b) => occ[b] - occ[a] || a - b);
    const stack = []; // {trailLen, lit, flipped}
    let decisions = 0, ok = propagate();
    while (true) {
      if (!ok) {
        // back up to the last decision not yet flipped
        let d;
        while ((d = stack.pop()) && d.flipped) { while (trail.length > d.trailLen) val[Math.abs(trail.pop())] = 0; }
        if (!d) return { sat: false, assignment: null, decisions };
        while (trail.length > d.trailLen) val[Math.abs(trail.pop())] = 0;
        qhead = trail.length;
        stack.push({ trailLen: trail.length, lit: -d.lit, flipped: true });
        set(-d.lit);
        ok = propagate();
        continue;
      }
      const v = order.find((x) => val[x] === 0);
      if (v == null) { const a = [null]; for (let i = 1; i <= n; i++) a.push(val[i] === 1); return { sat: true, assignment: a, decisions }; }
      if (++decisions > maxDecisions) return { sat: null, assignment: null, decisions, verdict: 'limit' };
      qhead = trail.length;
      stack.push({ trailLen: trail.length, lit: -v, flipped: false }); // try false first: tableau formulas are mostly false
      set(-v);
      ok = propagate();
    }
  }

  // ---------- 2-SAT ----------
  // (a ∨ b) gives the implications ¬a → b and ¬b → a. The formula is unsatisfiable exactly when some x
  // and ¬x share a strongly connected component; otherwise components in reverse topological order give values.
  function twoSat(f) {
    if (f.clauses.some((c) => c.length > 2 || !c.length)) throw new Error('2-SAT needs clauses of one or two literals');
    const N = 2 * f.n, node = (l) => (l > 0 ? 2 * (l - 1) : 2 * (-l - 1) + 1), lit = (i) => (i % 2 ? -(i >> 1) - 1 : (i >> 1) + 1);
    const adj = Array.from({ length: N }, () => []), edges = [];
    for (const c of f.clauses) {
      const [a, b] = c.length === 1 ? [c[0], c[0]] : c;
      adj[node(-a)].push(node(b)); edges.push([-a, b]);
      if (a !== b) { adj[node(-b)].push(node(a)); edges.push([-b, a]); }
    }
    const trace = [{ kind: 'graph', say: `Each clause (a ∨ b) gives two implications, ¬a → b and ¬b → a: ${edges.length} edges on ${N} literal nodes.`, edges: edges.map(([a, b]) => [litText(f, a), litText(f, b)]) }];
    // Tarjan, iteratively
    let idx = 0, compCount = 0;
    const index = new Array(N).fill(-1), low = new Array(N).fill(0), onStack = new Array(N).fill(false), comp = new Array(N).fill(-1), st = [], comps = [];
    for (let s = 0; s < N; s++) {
      if (index[s] >= 0) continue;
      const work = [[s, 0]];
      index[s] = low[s] = idx++; st.push(s); onStack[s] = true;
      while (work.length) {
        const top = work[work.length - 1], v = top[0];
        if (top[1] < adj[v].length) {
          const w = adj[v][top[1]++];
          if (index[w] < 0) { index[w] = low[w] = idx++; st.push(w); onStack[w] = true; work.push([w, 0]); }
          else if (onStack[w]) low[v] = Math.min(low[v], index[w]);
        } else {
          work.pop();
          if (work.length) low[work[work.length - 1][0]] = Math.min(low[work[work.length - 1][0]], low[v]);
          if (low[v] === index[v]) {
            const members = [];
            let w;
            do { w = st.pop(); onStack[w] = false; comp[w] = compCount; members.push(w); } while (w !== v);
            comps.push(members.map((m) => litText(f, lit(m))));
            compCount++;
          }
        }
      }
    }
    trace.push({ kind: 'scc', say: `The strongly connected components: ${comps.map((c) => '{' + c.join(', ') + '}').join(' ')}.`, components: comps });
    for (let v = 1; v <= f.n; v++) if (comp[node(v)] === comp[node(-v)]) {
      trace.push({ kind: 'conflict', say: `${litText(f, v)} and ${litText(f, -v)} are in the same component: each implies the other, so no value works.`, var: v });
      return { sat: false, assignment: null, components: comps, trace };
    }
    // Tarjan numbers components sinks first, so a smaller number is later in topological order
    const a = [null];
    for (let v = 1; v <= f.n; v++) a.push(comp[node(v)] < comp[node(-v)]);
    trace.push({ kind: 'assign', say: 'Give each variable the value whose literal comes later in topological order: ' + a.slice(1).map((x, i) => `${litText(f, i + 1)} = ${x ? 'true' : 'false'}`).join(', ') + '.', assignment: a.slice(1) });
    return { sat: true, assignment: a, components: comps, trace };
  }

  // ---------- SAT to 3-SAT ----------
  // Short clauses are padded with fresh variables in every sign combination; long clauses become a chain
  // linked by fresh variables. forward extends a satisfying assignment, backward restricts one.
  function to3Sat(f) {
    let n = f.n;
    const names = (f.names || [null]).slice();
    for (let v = names.length; v <= f.n; v++) names[v] = 'x' + v;
    const fresh = (base) => { n++; names[n] = base + n; return n; };
    const clauses = [], roles = [], chains = [], trace = [];
    f.clauses.forEach((c, ci) => {
      if (c.length === 3) { clauses.push(c.slice()); roles.push({ from: ci, role: 'kept' }); return; }
      if (c.length === 0) { const y = fresh('y'), z = fresh('y'); for (const s of [[y, z], [y, -z], [-y, z], [-y, -z]]) { clauses.push([s[0], s[1], s[0]]); roles.push({ from: ci, role: 'empty' }); } return; }
      if (c.length === 1) {
        const y = fresh('y'), z = fresh('y');
        for (const [a, b] of [[y, z], [y, -z], [-y, z], [-y, -z]]) { clauses.push([c[0], a, b]); roles.push({ from: ci, role: 'padded' }); }
        trace.push({ kind: 'pad', say: `(${litText(f, c[0])}) becomes four clauses with fresh ${names[y]}, ${names[z]} in every sign: together they force ${litText(f, c[0])}.`, clause: ci });
        return;
      }
      if (c.length === 2) {
        const y = fresh('y');
        clauses.push([c[0], c[1], y], [c[0], c[1], -y]); roles.push({ from: ci, role: 'padded' }, { from: ci, role: 'padded' });
        trace.push({ kind: 'pad', say: `(${c.map((l) => litText(f, l)).join(' ∨ ')}) becomes two clauses with ${names[y]} and ¬${names[y]} added.`, clause: ci });
        return;
      }
      const zs = [];
      for (let i = 0; i < c.length - 3; i++) zs.push(fresh('z'));
      clauses.push([c[0], c[1], zs[0]]); roles.push({ from: ci, role: 'chain' });
      for (let i = 1; i < zs.length; i++) { clauses.push([-zs[i - 1], c[i + 1], zs[i]]); roles.push({ from: ci, role: 'chain' }); }
      clauses.push([-zs[zs.length - 1], c[c.length - 2], c[c.length - 1]]); roles.push({ from: ci, role: 'chain' });
      chains.push({ clause: ci, zs });
      trace.push({ kind: 'chain', say: `A clause of ${c.length} literals becomes a chain of ${c.length - 2} clauses linked by ${zs.map((z) => names[z]).join(', ')}.`, clause: ci });
    });
    const g = { n, clauses, names };
    const forward = (a) => {
      const b = a.slice(0, f.n + 1);
      for (let v = f.n + 1; v <= n; v++) b[v] = false;
      // z_i (after literals c[0], c[1], …, c[i+1]) is true when none of those literals is true yet
      for (const { clause, zs } of chains) {
        const c = f.clauses[clause], isTrue = (l) => (l > 0 ? a[l] : !a[-l]);
        let firstTrue = c.findIndex(isTrue);
        if (firstTrue < 0) firstTrue = c.length;
        zs.forEach((z, i) => { b[z] = firstTrue > i + 1; });
      }
      return b;
    };
    const backward = (b) => b.slice(0, f.n + 1);
    trace.push({ kind: 'done', say: `${f.clauses.length} clauses became ${clauses.length} clauses of exactly three literals, with ${n - f.n} fresh variables.`, from: f.clauses.length, to: clauses.length });
    return { formula: g, roles, forward, backward, trace };
  }

  // ---------- random formulas ----------
  function randomKCNF(r, n, m, k = 3) {
    const clauses = [];
    for (let i = 0; i < m; i++) {
      const vs = r.shuffle(Array.from({ length: n }, (_, j) => j + 1)).slice(0, Math.min(k, n));
      clauses.push(vs.map((v) => (r() < 0.5 ? -v : v)));
    }
    return { n, clauses, names: [null, ...Array.from({ length: n }, (_, i) => 'x' + (i + 1))] };
  }
  function randomCNF(r, n, m, maxLen = 4) {
    const clauses = [];
    for (let i = 0; i < m; i++) {
      const len = 1 + r.int(maxLen), c = [];
      for (let j = 0; j < len; j++) { const v = 1 + r.int(n); c.push(r() < 0.5 ? -v : v); }
      clauses.push(c);
    }
    return { n, clauses, names: [null, ...Array.from({ length: n }, (_, i) => 'x' + (i + 1))] };
  }

  T.sat = { rng, parse, toText, toDimacs, litText, evaluate, evalClause, brute, dpll, solve, twoSat, to3Sat, randomKCNF, randomCNF };
})();
