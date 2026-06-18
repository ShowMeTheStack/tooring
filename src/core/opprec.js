// Operator-precedence parsing: the relations <· ≐ ·> between terminals, computed from an operator
// grammar through LEADING and TRAILING or typed in as a table, the shift-reduce parse they drive, and
// precedence functions f and g found by the graph method when they exist.
//
// PUBLIC API (T.opp). Relations are kept as rel[a][b] ∈ '<' | '=' | '>' (missing means error); '$' is
// the end marker on both sides.
//   operatorCheck(G)               → { ok, problems: [{ prod, say }] }  (no ε right sides, no two
//                                    nonterminals side by side)
//   leadingTrailing(G)             → { leading: {A: [..]}, trailing: {A: [..]}, trace }
//                                    trace kinds: 'leading', 'trailing' (what was added and why)
//   relationsFromGrammar(G)        → R = { G, terminals, rel, conflicts, operator, leading, trailing, trace }
//                                    trace kinds: 'equal', 'less', 'greater', 'conflict'
//   fromTable(spec, G?)            → R from { terminals, rel } or text: a header line of terminals, then one
//                                    line per row terminal with entries < = > (also <· ≐ ·>) or . for blank
//   functions(R)                   → { ok, f, g, groups, cycle, trace }; trace kinds 'merge', 'edge',
//                                    'cycle', 'value'
//   parse(R, input, opts)          → { accepted, tree, trace, error }; opts.grammar (default R.G) checks each
//                                    handle against a right side, nonterminals matching anything;
//                                    opts.functions compares f and g instead of the table.
//                                    trace kinds: 'start', 'shift', 'reduce', 'accept', 'error'
// The tree is skeletal: unit rules leave no handle of their own, so a node is labelled with the left side
// of the rule its handle matched (or N without a grammar) and the tree has no unit-rule chains.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Gr = () => T.grammar;
  const END = '$';
  const NAMES = { '<': '<·', '=': '≐', '>': '·>' };

  function operatorCheck(G) {
    const problems = [];
    for (const p of G.productions) {
      if (p.A === null) problems.push({ prod: p.id, say: Gr().showProd(G, p) + ' is not context-free.' });
      else if (!p.rhs.length) problems.push({ prod: p.id, say: Gr().showProd(G, p) + ' has an empty right side.' });
      else for (let i = 0; i + 1 < p.rhs.length; i++) if (Gr().isN(G, p.rhs[i]) && Gr().isN(G, p.rhs[i + 1])) {
        problems.push({ prod: p.id, say: Gr().showProd(G, p) + ' puts ' + p.rhs[i] + ' and ' + p.rhs[i + 1] + ' side by side.' }); break;
      }
    }
    return { ok: !problems.length, problems };
  }

  // LEADING(A): terminals that can be the first terminal of something A derives (with at most one
  // nonterminal before it); TRAILING(A) the same from the right. Both are least fixpoints.
  function leadingTrailing(G) {
    const N = Gr().info(G).N, trace = [];
    const lead = new Map(G.nonterminals.map((A) => [A, new Set()])), trail = new Map(G.nonterminals.map((A) => [A, new Set()]));
    const sweep = (tbl, kind, pick) => {
      let changed = true;
      while (changed) {
        changed = false;
        for (const p of G.productions) {
          if (p.A === null) continue;
          const rhs = pick(p.rhs), tgt = tbl.get(p.A);
          // the first terminal, possibly after one nonterminal
          const t = !rhs.length ? null : !N.has(rhs[0]) ? rhs[0] : rhs.length > 1 && !N.has(rhs[1]) ? rhs[1] : null;
          if (t !== null && !tgt.has(t)) {
            tgt.add(t); changed = true;
            trace.push({ kind, A: p.A, add: [t], prod: p.id, say: t + ' joins ' + kind.toUpperCase() + '(' + p.A + ') because of ' + Gr().showProd(G, p) + '.' });
          }
          if (rhs.length && N.has(rhs[0])) {
            const add = [...tbl.get(rhs[0])].filter((x) => !tgt.has(x));
            if (add.length) {
              add.forEach((x) => tgt.add(x)); changed = true;
              trace.push({ kind, A: p.A, add, prod: p.id, from: rhs[0], say: kind.toUpperCase() + '(' + rhs[0] + ') flows into ' + kind.toUpperCase() + '(' + p.A + ') through ' + Gr().showProd(G, p) + ', adding ' + add.join(', ') + '.' });
            }
          }
        }
      }
    };
    sweep(lead, 'leading', (r) => r);
    sweep(trail, 'trailing', (r) => r.slice().reverse());
    const obj = (m) => Object.fromEntries([...m].map(([A, s]) => [A, [...s]]));
    return { leading: obj(lead), trailing: obj(trail), trace };
  }

  function newR(terminals) { return { terminals, rel: Object.fromEntries(terminals.map((a) => [a, {}])), conflicts: [], trace: [] }; }
  function setRel(R, a, b, r, why) {
    const old = R.rel[a][b];
    if (old === r) return;
    const kind = r === '<' ? 'less' : r === '=' ? 'equal' : 'greater';
    if (old) {
      const c = { a, b, relations: [old, r], say: a + ' ' + NAMES[old] + ' ' + b + ' and also ' + a + ' ' + NAMES[r] + ' ' + b + ' (' + why + '): the grammar is not operator-precedence.' };
      R.conflicts.push(c); R.trace.push(Object.assign({ kind: 'conflict' }, c));
      return;
    }
    R.rel[a][b] = r;
    R.trace.push({ kind, a, b, say: a + ' ' + NAMES[r] + ' ' + b + ' because ' + why + '.' });
  }
  function relationsFromGrammar(G) {
    const N = Gr().info(G).N, op = operatorCheck(G), lt = leadingTrailing(G);
    const R = newR(G.terminals.concat([END]));
    R.G = G; R.operator = op; R.leading = lt.leading; R.trailing = lt.trailing;
    R.trace.push(...lt.trace);
    const sp = (p) => Gr().showProd(G, p);
    for (const p of G.productions) {
      if (p.A === null) continue;
      const r = p.rhs;
      for (let i = 0; i + 1 < r.length; i++) {
        const x = r[i], y = r[i + 1];
        if (!N.has(x) && !N.has(y)) setRel(R, x, y, '=', x + ' and ' + y + ' sit side by side in ' + sp(p));
        if (i + 2 < r.length && !N.has(x) && N.has(y) && !N.has(r[i + 2])) setRel(R, x, r[i + 2], '=', x + ' and ' + r[i + 2] + ' enclose ' + y + ' in ' + sp(p));
        if (!N.has(x) && N.has(y)) for (const b of lt.leading[y]) setRel(R, x, b, '<', b + ' is in LEADING(' + y + ') and ' + y + ' follows ' + x + ' in ' + sp(p));
        if (N.has(x) && !N.has(y)) for (const a of lt.trailing[x]) setRel(R, a, y, '>', a + ' is in TRAILING(' + x + ') and ' + y + ' follows ' + x + ' in ' + sp(p));
      }
    }
    for (const b of lt.leading[G.start] || []) setRel(R, END, b, '<', b + ' can begin a sentence');
    for (const a of lt.trailing[G.start] || []) setRel(R, a, END, '>', a + ' can end a sentence');
    return R;
  }

  function fromTable(spec, G) {
    if (typeof spec === 'string') {
      const lines = spec.split(/\r?\n/).map((l) => l.trim()).filter(Boolean);
      const head = lines[0].split(/\s+/);
      const R = newR(head.slice());
      for (const l of lines.slice(1)) {
        const [a, ...cells] = l.split(/\s+/);
        if (!R.rel[a]) throw new Error('row ' + a + ' is not in the header');
        cells.forEach((c, k) => {
          const r = { '<': '<', '<·': '<', '=': '=', '≐': '=', '>': '>', '·>': '>' }[c];
          if (r) setRel(R, a, head[k], r, 'the table says so');
        });
      }
      R.G = G || null;
      return R;
    }
    const R = newR(spec.terminals.slice());
    for (const a of spec.terminals) for (const [b, r] of Object.entries(spec.rel[a] || {})) setRel(R, a, b, r, 'the table says so');
    R.G = G || null;
    return R;
  }

  // Precedence functions: ≐ glues f_a and g_b into one node; a ·> b gives an edge f_a → g_b and a <· b an
  // edge g_b → f_a; each value is the longest path out of its node, and a cycle means no functions exist.
  function functions(R) {
    const trace = [], ts = R.terminals, parent = new Map();
    const find = (x) => { while (parent.get(x) !== x) x = parent.get(x); return x; };
    for (const a of ts) { parent.set('f' + a, 'f' + a); parent.set('g' + a, 'g' + a); }
    for (const a of ts) for (const b of ts) if (R.rel[a][b] === '=') {
      const x = find('f' + a), y = find('g' + b);
      if (x !== y) { parent.set(y, x); trace.push({ kind: 'merge', a, b, say: a + ' ≐ ' + b + ', so f(' + a + ') and g(' + b + ') must be equal: one node.' }); }
    }
    const edges = new Map();
    const edge = (x, y, say) => { x = find(x); y = find(y); if (!edges.has(x)) edges.set(x, new Set()); if (!edges.get(x).has(y)) { edges.get(x).add(y); trace.push({ kind: 'edge', from: x, to: y, say }); } };
    for (const a of ts) for (const b of ts) {
      if (R.rel[a][b] === '>') edge('f' + a, 'g' + b, a + ' ·> ' + b + ': f(' + a + ') must exceed g(' + b + ').');
      if (R.rel[a][b] === '<') edge('g' + b, 'f' + a, a + ' <· ' + b + ': g(' + b + ') must exceed f(' + a + ').');
    }
    const memo = new Map(), state = new Map();
    let cycle = null;
    const longest = (x, path) => {
      if (memo.has(x)) return memo.get(x);
      if (state.get(x) === 1) { if (!cycle) cycle = path.slice(path.indexOf(x)).concat([x]); return 0; }
      state.set(x, 1); path.push(x);
      let best = 0;
      for (const y of edges.get(x) || []) best = Math.max(best, 1 + longest(y, path));
      path.pop(); state.set(x, 2); memo.set(x, best);
      return best;
    };
    for (const a of ts) { longest(find('f' + a), []); longest(find('g' + a), []); }
    if (cycle) {
      trace.push({ kind: 'cycle', cycle, say: 'The graph has a cycle ' + cycle.join(' → ') + ', so no precedence functions exist.' });
      return { ok: false, f: null, g: null, cycle, trace };
    }
    const f = {}, g = {};
    for (const a of ts) { f[a] = memo.get(find('f' + a)); g[a] = memo.get(find('g' + a)); }
    for (const a of ts) trace.push({ kind: 'value', a, f: f[a], g: g[a], say: 'f(' + a + ') = ' + f[a] + ' and g(' + a + ') = ' + g[a] + ', the longest paths out of their nodes.' });
    return { ok: true, f, g, cycle: null, trace };
  }

  function parse(R, input, opts) {
    opts = opts || {};
    const G = opts.grammar === undefined ? R.G : opts.grammar;
    const fn = opts.functions || null;
    const rel = (a, b) => {
      if (fn) { if (!(a in fn.f) || !(b in fn.g)) return undefined; return fn.f[a] < fn.g[b] ? '<' : fn.f[a] > fn.g[b] ? '>' : '='; }
      return R.rel[a] ? R.rel[a][b] : undefined;
    };
    const w = G ? Gr().input(G, input) : Array.isArray(input) ? input.slice() : [...String(input).replace(/\s+/g, '')];
    const inp = w.concat([END]), trace = [];
    const stack = [{ sym: END, term: true, node: null }];
    let i = 0;
    const view = () => stack.map((e) => (e.term ? e.sym : 'N'));
    const snap = (x) => Object.assign({ stack: view(), input: inp.slice(i) }, x);
    const topTerm = () => { for (let k = stack.length - 1; k >= 0; k--) if (stack[k].term) return k; return -1; };
    const fail = (msg) => { trace.push(snap({ kind: 'error', say: 'Error: ' + msg + '.' })); return { accepted: false, tree: null, trace, error: { position: i, message: msg } }; };
    trace.push(snap({ kind: 'start', say: 'Start with $ on the stack and ' + Gr().show(w) + '$ to read.' }));
    for (let guard = 0; guard < 4 * inp.length + 10; guard++) {
      const k = topTerm(), a = stack[k].sym, b = inp[i];
      if (a === END && b === END) {
        if (stack.length === 2 && !stack[1].term) { trace.push(snap({ kind: 'accept', say: 'Only $ and one phrase remain: accept.' })); return { accepted: true, tree: stack[1].node, trace, error: null }; }
        return fail('the input ended without forming one phrase');
      }
      const r = rel(a, b);
      if (r === '<' || r === '=') {
        trace.push(snap({ kind: 'shift', a, b, relation: r, say: a + ' ' + NAMES[r] + ' ' + b + ': shift ' + b + '.' }));
        stack.push({ sym: b, term: true, node: { sym: b, prod: null, children: null } }); i++;
        continue;
      }
      if (r !== '>') return fail('no relation between ' + a + ' and ' + b);
      // find the handle: walk down terminals linked by ≐ until one is <· the terminal above it
      let j = k, start = -1;
      for (;;) {
        let p = j - 1; while (p >= 0 && !stack[p].term) p--;
        if (p < 0) return fail('no <· below the handle');
        const r2 = rel(stack[p].sym, stack[j].sym);
        if (r2 === '<') { start = p + 1; break; }
        if (r2 !== '=') return fail('no relation between ' + stack[p].sym + ' and ' + stack[j].sym + ' inside the stack');
        j = p;
      }
      const handle = stack.slice(start), shape = handle.map((e) => (e.term ? e.sym : null));
      let prod = null;
      if (G) {
        prod = G.productions.find((p) => p.A !== null && p.rhs.length === shape.length && p.rhs.every((s, q) => (shape[q] === null ? Gr().isN(G, s) : s === shape[q])));
        if (!prod) return fail('the handle ' + view().slice(start).join(' ') + ' matches no right side');
      }
      const before = snap({});
      stack.splice(start);
      const node = { sym: prod ? prod.A : 'N', prod: prod ? prod.id : null, children: handle.map((e) => e.node) };
      stack.push({ sym: node.sym, term: false, node });
      trace.push(Object.assign(before, { kind: 'reduce', a, b, relation: '>', handle: { start, end: start + handle.length }, prod: prod ? prod.id : null,
        say: a + ' ·> ' + b + ': reduce the handle ' + before.stack.slice(start).join(' ') + (prod ? ' by ' + Gr().showProd(G, prod) : '') + '.' }));
    }
    return fail('step limit');
  }

  T.opp = { NAMES, operatorCheck, leadingTrailing, relationsFromGrammar, fromTable, functions, parse };
})();
