// Space: what a machine must remember rather than how long it runs. TQBF played as a game on a tree whose
// evaluation keeps only one path in memory; Savitch's midpoint recursion, whose stack stays short while the
// calls explode; reachability in logarithmic space by a walker that guesses; and the map of the classes,
// with the problems placed, the open questions marked and the separations the hierarchy theorems give.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'cx-space', part: 'complexity', order: 80, title: 'Space', blurb: 'Memory as the resource: quantified formulas as games, Savitch\'s midpoints, reachability in log space, and the map of the classes.' });

  const log2c = (n) => Math.max(1, Math.ceil(Math.log2(Math.max(2, n))));

  // ---------- quantified formulas ----------
  // "∃x ∀y ∃z : (x ∨ y) ∧ (¬y ∨ z)", also "E x A y : …", "exists x forall y : …"
  function parseQBF(text) {
    const src = String(text || '').trim();
    const at = src.indexOf(':');
    if (at < 0) throw new Error('Formula: write the quantifiers, a colon, then the clauses, like ∃x ∀y : (x ∨ y) ∧ (¬x ∨ ¬y)');
    const head = src.slice(0, at).replace(/∃/g, ' E ').replace(/∀/g, ' A ').replace(/\bexists\b/gi, ' E ').replace(/\bforall\b/gi, ' A ').trim();
    const toks = head.split(/[\s,]+/).filter(Boolean);
    const prefix = [];
    let q = null;
    for (const t of toks) {
      if (t === 'E' || t === 'A') { q = t; continue; }
      if (!q) throw new Error('Formula: "' + t + '" needs ∃ (or E) or ∀ (or A) in front of it');
      if (!/^[A-Za-z_][\w']*$/.test(t)) throw new Error('Formula: "' + t + '" is not a variable name');
      if (prefix.some((p) => p.name === t)) throw new Error('Formula: ' + t + ' is quantified twice');
      prefix.push({ q, name: t });
    }
    if (!prefix.length) throw new Error('Formula: no quantified variables before the colon');
    if (prefix.length > 4) throw new Error('Formula: at most 4 variables, so the game tree (2⁴ = 16 leaves) stays readable');
    const body = src.slice(at + 1).trim();
    if (!body) throw new Error('Formula: no clauses after the colon');
    let f;
    try { f = T.sat.parse(body); } catch (e) { throw new Error('Formula: ' + e.message); }
    if (f.clauses.some((c) => !c.length)) throw new Error('Formula: an empty clause ( )');
    for (let v = 1; v <= f.n; v++) if (!prefix.some((p) => p.name === f.names[v])) throw new Error('Formula: ' + f.names[v] + ' is not quantified; every variable needs ∃ or ∀');
    // quantified variables the clauses never mention still get a number
    for (const p of prefix) { let v = f.names.indexOf(p.name); if (v < 1) { f.names.push(p.name); f.n++; v = f.n; } p.v = v; }
    return { prefix, f };
  }
  const qSym = (q) => (q === 'E' ? '∃' : '∀');
  const qbfText = (Q) => Q.prefix.map((p) => qSym(p.q) + p.name).join(' ') + ' : ' + T.sat.toText(Q.f);

  // The evaluation, depth first, 0 before 1, stopping as soon as a node's value is settled (as T.cx.tqbf does).
  // Nodes are named by their path: 'r', 'r0', 'r01', …
  function playQBF(Q) {
    const { prefix, f } = Q;
    const ev = [], val = {}, best = {};
    const a = new Array(f.n + 1).fill(null);
    const go = (i, id) => {
      if (i === prefix.length) {
        const b = a.map((x) => !!x);
        const v = T.sat.evaluate(f, b);
        const bad = f.clauses.findIndex((c) => !T.sat.evalClause(c, b));
        val[id] = v;
        ev.push({ kind: 'leaf', id, a: a.slice(), value: v, bad });
        return v;
      }
      const { q, v } = prefix[i];
      let res = q === 'A';
      for (const bit of [false, true]) {
        a[v] = bit;
        ev.push({ kind: 'down', id: id + (bit ? '1' : '0'), from: id, q, name: prefix[i].name, bit, a: a.slice() });
        const r = go(i + 1, id + (bit ? '1' : '0'));
        if (q === 'E' && r) { res = true; best[id] = bit; break; }
        if (q === 'A' && !r) { res = false; best[id] = bit; break; }
      }
      a[v] = null;
      val[id] = res;
      ev.push({ kind: 'resolve', id, q, name: prefix[i].name, value: res, best: best[id], a: a.slice() });
      return res;
    };
    const value = go(0, 'r');
    return { ev, val, best, value };
  }

  T.topic({
    id: 'cx-tqbf', family: 'cx-space', order: 10, title: 'TQBF as a game',
    blurb: 'A fully quantified formula is a game: the ∃-player sets her variables to make it true, the ∀-player sets his to make it false. Evaluating the game tree takes exponential time but only one path of memory: TQBF is in PSPACE.',
    inputs: [{ id: 'q', kind: 'text', label: 'Quantified formula', def: '∃x ∀y ∃z : (x ∨ y) ∧ (¬y ∨ z) ∧ (y ∨ ¬z)', check: (v) => { try { parseQBF(v); return null; } catch (e) { return e.message; } } }],
    presets: [
      { label: 'True: ∃x ∀y ∃z', values: { q: '∃x ∀y ∃z : (x ∨ y) ∧ (¬y ∨ z) ∧ (y ∨ ¬z)' } },
      { label: 'False: ∀ wins', values: { q: '∀x ∃y ∀z : (x ∨ y) ∧ (¬y ∨ z)' } },
      { label: '∀y ∃x : x ≠ y (true)', values: { q: '∀y ∃x : (x ∨ y) ∧ (¬x ∨ ¬y)' } },
      { label: '∃x ∀y : x ≠ y (false)', values: { q: '∃x ∀y : (x ∨ y) ∧ (¬x ∨ ¬y)' } },
      { label: 'Only ∃: plain SAT', values: { q: '∃a ∃b ∃c : (a ∨ b) ∧ (¬a ∨ c) ∧ (¬b ∨ ¬c)' } },
      { label: 'Only ∀: a tautology', values: { q: '∀p ∀q : (p ∨ ¬p ∨ q) ∧ (q ∨ ¬q)' } },
    ],
    counters: [{ id: 'visited', label: 'nodes visited' }, { id: 'leaves', label: 'leaves evaluated' }, { id: 'memory', label: 'bits remembered now' }],
    run(inp) {
      const Q = parseQBF(inp.q);
      const { prefix, f } = Q;
      const k = prefix.length;
      const play = playQBF(Q);
      // the engine's own answer, as a check on this picture
      const eng = T.cx.tqbf(prefix.map((p) => ({ q: p.q, v: p.v })), f);
      if (eng.value !== play.value) throw new Error('the game tree and the TQBF engine disagree');
      const ids = [];
      const mk = (id, d) => { ids.push(id); if (d < k) { mk(id + '0', d + 1); mk(id + '1', d + 1); } };
      mk('r', 0);
      const depthOf = (id) => id.length - 1;
      const owner = (id) => prefix[depthOf(id)];
      const GX = k >= 4 ? 8 : k === 3 ? 22 : 40;
      const state = { seen: new Set(), val: {}, cur: 'r', pruned: false, strat: null };
      const treeOf = () => {
        const node = (id) => {
          const d = depthOf(id), leaf = d === k;
          const v = state.val[id];
          const cls = ['qnode', leaf ? 'qleaf' : owner(id).q === 'E' ? 'qe' : 'qa', v === true ? 'val-t' : v === false ? 'val-f' : '', !state.seen.has(id) ? (state.pruned ? 'pruned' : 'unseen') : '', id === state.cur ? 'hot' : '', state.cur.startsWith(id) && id !== state.cur ? 'onpath' : ''].filter(Boolean).join(' ');
          const label = leaf ? (v === true ? 'T' : v === false ? 'F' : '?') : qSym(owner(id).q) + owner(id).name;
          return { id, label, cls, children: leaf ? [] : [node(id + '0'), node(id + '1')] };
        };
        return node('r');
      };
      const F = new T.Frames(['visited', 'leaves', 'memory']);
      const scene = (a, opts) => {
        opts = opts || {};
        const path = state.strat ? [...state.strat] : [...state.cur].map((_, i) => state.cur.slice(0, i + 1)).filter((x) => x.length);
        const tr = K.tree.draw(treeOf(), { prefix: 'gt', gapX: GX, gapY: 86, path, grow: false });
        const items = tr.items.map((it) => (it.kind === 'state' && /accept-path/.test(it.cls) && !state.strat ? Object.assign({}, it, { cls: it.cls.replace('accept-path', '') }) : it));
        // the edges' choices: 0 to the left, 1 to the right
        let minX = Infinity, maxX = -Infinity;
        for (const [id, p] of tr.pos) { minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x); if (id.length > 1) { const pp = tr.pos.get(id.slice(0, -1)); const bit = id.slice(-1); items.push({ key: 'gt:b:' + id, kind: 'text', x: (p.x + pp.x) / 2 + (bit === '0' ? -13 : 13), y: (p.y + pp.y) / 2 + 5, text: bit, anchor: 'middle', size: 13, cls: 'strong' }); } }
        // who moves at each level
        for (let d = 0; d <= k; d++) items.push({ key: 'gt:lv:' + d, kind: 'text', x: minX - 50, y: d * 86 + 5, text: d < k ? (prefix[d].q === 'E' ? '∃ picks ' : '∀ picks ') + prefix[d].name : 'leaves', anchor: 'end', size: 14, cls: d < k ? (prefix[d].q === 'E' ? 'qe-text' : 'qa-text') : 'title' });
        // memory: the values on the current path, a stack
        const bits = prefix.map((p) => a[p.v] === null || a[p.v] === undefined ? null : p.name + ' = ' + (a[p.v] ? 1 : 0)).filter(Boolean);
        const sk = K.stack.draw({ items: bits.map((b) => ({ text: b })), x: maxX + 70, y: k * 86 + 20, label: 'memory', w: 84, h: 34, topLabel: '' });
        items.push(...sk.items);
        const fm = K.cx.formula({ f, a, x: minX - 20, y: k * 86 + 66, maxW: Math.max(420, maxX - minX + 40), prefix: 'fm', hot: opts.bad !== undefined && opts.bad >= 0 ? [opts.bad] : [] });
        return items.concat(fm.items);
      };
      const blank = new Array(f.n + 1).fill(null);
      state.seen.add('r');
      F.set('visited', 1);
      F.add({ items: scene(blank), say: 'The game ' + qbfText(Q) + '. Players move in order from the top: ' + prefix.map((p) => (p.q === 'E' ? '∃' : '∀') + ' sets ' + p.name).join(', ') + '. A leaf is won by ∃ when the formula is true there.', meta: { first: true } });
      for (const e of play.ev) {
        if (e.kind === 'down') {
          state.seen.add(e.id); state.cur = e.id;
          F.count('visited').set('memory', depthOf(e.id));
          if (depthOf(e.id) === k) continue; // the leaf frame says it
          F.add({ items: scene(e.a), say: (e.q === 'E' ? 'The ∃-player' : 'The ∀-player') + ' tries ' + e.name + ' = ' + (e.bit ? 1 : 0) + (e.bit ? ', the second choice' : '') + ', and the game goes on below.', meta: { down: e.id } });
        } else if (e.kind === 'leaf') {
          state.val[e.id] = e.value; state.cur = e.id;
          F.count('leaves');
          const asg = prefix.map((p) => p.name + ' = ' + (e.a[p.v] ? 1 : 0)).join(', ');
          F.add({ items: scene(e.a, { bad: e.bad }), say: 'Leaf ' + asg + ': ' + (e.value ? 'every clause is true, so ∃ wins here (T).' : 'clause C' + (e.bad + 1) + ' is false, so ∀ wins here (F).'), meta: { leaf: e.id } });
        } else {
          state.val[e.id] = e.value; state.cur = e.id;
          F.set('memory', depthOf(e.id));
          const who = e.q === 'E' ? '∃' : '∀';
          const say = e.q === 'E'
            ? (e.value ? '∃' + e.name + ': choosing ' + e.name + ' = ' + (e.best ? 1 : 0) + ' wins, so this node is T' + (e.best ? '' : ' and the other choice is never looked at') + '.' : '∃' + e.name + ': both choices lose, so this node is F.')
            : (e.value ? '∀' + e.name + ': both choices lead to T, so the ∀-player cannot escape: T.' : '∀' + e.name + ': ' + e.name + ' = ' + (e.best ? 1 : 0) + ' refutes it, so this node is F' + (e.best ? '' : ' and the other choice is never looked at') + '.');
          F.add({ items: scene(e.a), say: say + (e.id === 'r' ? ' That is the value of the whole formula.' : ''), meta: { resolve: e.id, root: e.id === 'r', who } });
        }
      }
      const unseen = ids.filter((id) => !state.seen.has(id));
      state.pruned = true; state.cur = '';
      F.set('memory', 0);
      F.add({ items: scene(blank), say: unseen.length ? unseen.length + ' of the ' + ids.length + ' nodes were never visited: once a player has a winning move, the other moves at that node do not matter.' : 'No shortcut was possible: all ' + ids.length + ' nodes had to be visited. The time is exponential in the number of variables.', meta: { pruneFrame: true } });
      // the winning strategy: the winner's chosen move at its own nodes, every move at the opponent's
      const win = play.value ? 'E' : 'A';
      const strat = new Set();
      const walk = (id) => { strat.add(id); if (depthOf(id) === k) return; if (owner(id).q === win) walk(id + (play.best[id] ? '1' : '0')); else { walk(id + '0'); walk(id + '1'); } };
      walk('r');
      state.strat = strat;
      F.add({ items: scene(blank), say: (play.value ? 'The formula is true. Lit: the ∃-player\'s winning strategy, one answer at each of her nodes that works against every move of ∀.' : 'The formula is false. Lit: the ∀-player\'s winning strategy, one refuting move at each of his nodes that works against every move of ∃.') + ' The memory never held more than ' + k + ' bits: one path.', mark: play.value ? 'accepted' : 'rejected', meta: { value: play.value } });
      const rootChild = owner('r').q === win ? 'gt:n:r' + (play.best.r ? '1' : '0') : null;
      return { frames: F.list, result: play.value, def: { sections: [
        { id: 'qbf', kind: 'math', title: 'The formula', text: qbfText(Q) },
        { id: 'rule', kind: 'math', title: 'Values in the tree', text: 'leaf: the formula under that assignment\n∃ node: T if some child is T (OR)\n∀ node: T if every child is T (AND)\nspace: one path, ' + k + ' bits, plus the formula' },
        { id: 'cls', kind: 'text', title: 'Why this matters', text: 'TQBF is PSPACE-complete: every problem solvable in polynomial space reduces to it. This depth-first evaluation uses space linear in the formula but time 2ⁿ.' },
      ] }, meta: { rootChild } };
    },
    predict: [
      { at: (f, i) => i === 0, pick: 'item', ask: 'The search is depth first, 0 before 1. Click the node it visits next.', answer: () => 'gt:n:r0', explain: 'From the root, the first player tries the value 0 first: the left child.' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.root, pick: 'option', options: ['True', 'False'], ask: 'The root is about to get its value. Is the whole formula true?', answer: (fr, i) => (fr[i + 1].say.includes('is T') || fr[i + 1].say.includes('lead to T') ? 'True' : 'False'), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => f.meta && f.meta.pruneFrame && fr[fr.length - 1].meta, pick: 'item', ask: (fr) => 'The winner owns the root here. Click the child the winner should move to first.', answer: (fr, i, inp) => { const Q = parseQBF(inp.q); const p = playQBF(Q); const win = p.value ? 'E' : 'A'; return Q.prefix[0].q === win ? 'gt:n:r' + (p.best.r ? '1' : '0') : null; }, explain: 'At its own node the winner needs just one good move; that child is T for ∃ (or F for ∀).' },
    ],
    quiz: [
      { q: 'Why is TQBF in PSPACE even though the tree has 2ⁿ leaves?', options: ['The tree is never built whole: depth-first evaluation remembers only the current path', 'Most leaves can be skipped', 'Formulas are short', 'It is in P'], answer: 0, why: 'Space can be reused: after a subtree is evaluated only its value is kept, so memory holds one path of n bits plus a little bookkeeping.' },
      { q: 'An ∃ node has children valued F and T. What is its value?', options: ['F', 'T', 'It depends on the ∀-player', 'Undefined'], answer: 1, why: 'The ∃-player picks the move she likes: one winning child is enough, so ∃ is an OR.' },
      { q: '∀y ∃x : x ≠ y is true but ∃x ∀y : x ≠ y is false. Why?', options: ['The clauses differ', 'The order of moves matters: picking x after seeing y is easier than before', 'One has more variables', 'TQBF is undecidable'], answer: 1, why: 'In the first, x is chosen knowing y and can be its opposite; in the second, x is fixed first and ∀ just picks y = x.' },
      { q: 'A formula with only ∃ quantifiers is the same problem as…', options: ['SAT', 'TAUTOLOGY', 'PATH', '2-SAT'], answer: 0, why: '∃x₁ … ∃xₙ φ asks whether some assignment makes φ true: satisfiability. Only ∀ asks whether φ is a tautology, a co-NP question.' },
      { q: 'What is the winning strategy of the ∃-player?', options: ['A single leaf', 'A choice at each of her nodes that wins whatever ∀ does', 'All paths of the tree', 'The first branch tried'], answer: 1, why: 'A strategy answers every possible move of the opponent: it is a subtree with one child at her nodes and all children at his.' },
    ],
  });

  // ---------- graphs for Savitch and for L / NL ----------
  // "a→b, b→c", "a>b b>c", "a-b" (both ways with -)
  function parseGraph(text, s, t) {
    const names = [], edges = [];
    const idx = (x) => { if (!names.includes(x)) names.push(x); return names.indexOf(x); };
    const parts = String(text || '').split(/[,;\n]+/).map((p) => p.trim()).filter(Boolean);
    for (const p of parts) {
      let m = /^(\w{1,3})\s*(?:→|->|>)\s*(\w{1,3})$/.exec(p), both = false;
      if (!m) { m = /^(\w{1,3})\s*(?:—|–|-)\s*(\w{1,3})$/.exec(p); both = !!m; }
      if (!m) { m = /^(\w{1,3})$/.exec(p); if (m) { idx(m[1]); continue; } }
      if (!m) throw new Error('Edges: cannot read "' + p + '"; write edges like a→b, b→c (a-b for both ways, a lone name for a vertex with no edges)');
      const a = idx(m[1]), b = idx(m[2]);
      if (a === b) continue;
      const add = (u, v) => { if (!edges.some((e) => e[0] === u && e[1] === v)) edges.push([u, v]); };
      add(a, b); if (both) add(b, a);
    }
    if (s !== undefined && !names.includes(s)) idx(s);
    if (t !== undefined && !names.includes(t)) idx(t);
    if (names.length > 7) throw new Error('Edges: at most 7 vertices, so the picture stays readable');
    if (names.length < 2) throw new Error('Edges: at least two vertices');
    return { n: names.length, edges, directed: true, names };
  }
  const graphCheck = (v, inp) => { try { const G = parseGraph(v); if (inp.s && !G.names.includes(inp.s)) return 'Start: ' + inp.s + ' is not a vertex of the graph'; if (inp.t && !G.names.includes(inp.t)) return 'Target: ' + inp.t + ' is not a vertex of the graph'; return null; } catch (e) { return e.message; } };

  // vertices on a ring, the start on the left
  function ringPos(G, cx, cy) {
    const R = Math.max(110, G.n * 24);
    const pos = {};
    for (let i = 0; i < G.n; i++) { const a = Math.PI + (2 * Math.PI * i) / G.n; pos[i] = { x: (cx || 0) + R + Math.cos(a) * R, y: (cy || 0) + R + Math.sin(a) * R }; }
    return { pos, R };
  }
  function drawGraph(G, pos, opts) {
    opts = opts || {};
    const cls = opts.cls || {};
    const nodes = G.names.map((nm, i) => ({ id: i, label: nm, x: pos[i].x, y: pos[i].y, cls: cls[i] || '' }));
    const ecls = opts.ecls || {};
    const edges = G.edges.map(([a, b]) => ({ a, b, cls: ecls[a + '>' + b] || '' }));
    return K.gadget.draw({ nodes, edges, directed: true, prefix: 'gr', r: 21 }).items;
  }

  // ---------- Savitch ----------
  T.topic({
    id: 'cx-savitch', family: 'cx-space', order: 20, title: 'Savitch: halving the question',
    blurb: 'Can u reach v in at most 2ⁱ steps? Try every midpoint m and ask the two half questions, one after the other, reusing the same memory. The stack is only log n questions deep, so nondeterministic space s becomes deterministic space s².',
    inputs: [
      { id: 'g', kind: 'text', label: 'Edges', def: 'a→b, b→c, c→d, b→e, e→a', check: graphCheck },
      { id: 's', kind: 'string', label: 'From', def: 'a', max: 3 },
      { id: 't', kind: 'string', label: 'To', def: 'd', max: 3 },
    ],
    presets: [
      { label: 'a reaches d', values: { g: 'a→b, b→c, c→d, b→e, e→a', s: 'a', t: 'd' } },
      { label: 'A chain of four steps', values: { g: 'a→b, b→c, c→d, d→e', s: 'a', t: 'e' } },
      { label: 'Unreachable: every midpoint fails', values: { g: 'a→b, b→a, c→d', s: 'a', t: 'd' } },
      { label: 'From a vertex to itself', values: { g: 'a→b, b→c', s: 'b', t: 'b' } },
    ],
    check: (inp) => graphCheck(inp.g, inp),
    counters: [{ id: 'calls', label: 'questions asked' }, { id: 'depth', label: 'stack depth' }, { id: 'maxd', label: 'deepest stack' }],
    run(inp) {
      const G = parseGraph(inp.g, inp.s, inp.t);
      const s = G.names.indexOf(inp.s), t = G.names.indexOf(inp.t);
      const n = G.n, k = log2c(n);
      const adj = T.cx.adjacency(G);
      const nm = (i) => G.names[i];
      // the same recursion as T.cx.savitch, with every move recorded
      const ev = [];
      let calls = 0;
      const stack = [];
      const can = (u, v, i, d) => {
        calls++;
        const fr = { u, v, i, m: null, half: null };
        stack.push(fr);
        if (i === 0) {
          const r = u === v || adj[u].has(v);
          ev.push({ kind: 'base', u, v, r, d, calls, stack: stack.map((x) => Object.assign({}, x)) });
          stack.pop();
          return r;
        }
        ev.push({ kind: 'ask', u, v, i, d, calls, stack: stack.map((x) => Object.assign({}, x)) });
        // real midpoints first, then u and v themselves (a shorter path: "at most" allows an empty half)
        const order = [...Array(n).keys()].filter((m) => m !== u && m !== v).concat(u === v ? [u] : [u, v]);
        for (const m of order) {
          fr.m = m; fr.half = 1;
          ev.push({ kind: 'try', u, v, i, m, d, calls, stack: stack.map((x) => Object.assign({}, x)) });
          if (!can(u, m, i - 1, d + 1)) continue;
          fr.half = 2;
          if (can(m, v, i - 1, d + 1)) {
            ev.push({ kind: 'yes', u, v, i, m, d, calls, stack: stack.map((x) => Object.assign({}, x)) });
            stack.pop();
            return true;
          }
        }
        ev.push({ kind: 'no', u, v, i, d, calls, stack: stack.map((x) => Object.assign({}, x)) });
        stack.pop();
        return false;
      };
      const ans = can(s, t, k, 0);
      const eng = T.cx.savitch(G, s, t, { k });
      if (eng.reachable !== ans) throw new Error('the picture and the Savitch engine disagree');
      const { pos } = ringPos(G, 0, 0);
      let gMaxX = -Infinity, gMinY = Infinity, gMaxY = -Infinity;
      for (const p of Object.values(pos)) { gMaxX = Math.max(gMaxX, p.x); gMinY = Math.min(gMinY, p.y); gMaxY = Math.max(gMaxY, p.y); }
      const SX = gMaxX + 90, SY = gMaxY + 60;
      const qText = (x) => nm(x.u) + ' ⇝ ' + nm(x.v) + ' in ≤ ' + (2 ** x.i) + (x.m !== null && x.i > 0 ? ' via ' + nm(x.m) : '');
      const F = new T.Frames(['calls', 'depth', 'maxd']);
      const scene = (e, opts) => {
        opts = opts || {};
        const top = e ? e.stack[e.stack.length - 1] : null;
        const cls = {}, ecls = {};
        if (top) {
          cls[top.u] = 'active'; cls[top.v] = cls[top.v] ? 'active' : 'active';
          if (top.m !== null && top.i > 0) cls[top.m] = 'hot';
          if (e.kind === 'base') { if (e.r && e.u !== e.v) ecls[e.u + '>' + e.v] = 'cert'; cls[e.u] = e.r ? 'good' : 'bad'; cls[e.v] = e.r ? 'good' : 'bad'; }
        }
        if (opts.final) { cls[s] = ans ? 'good' : 'bad'; cls[t] = ans ? 'good' : 'bad'; }
        const items = drawGraph(G, pos, { cls, ecls });
        const st = (e ? e.stack : []).map((x, j, all) => ({ text: qText(x) + (j === all.length - 1 && e.kind === 'base' ? (e.r ? '  ✓' : '  ✗') : j === all.length - 1 && e.kind === 'yes' ? '  ✓' : j === all.length - 1 && e.kind === 'no' ? '  ✗' : ''), cls: j === all.length - 1 ? (e.kind === 'base' || e.kind === 'yes' || e.kind === 'no' ? ((e.kind === 'base' ? e.r : e.kind === 'yes') ? 'good' : 'bad') : 'hot') : '' }));
        items.push(...K.stack.draw({ items: st, x: SX, y: SY, w: 196, h: 34, label: 'the recursion stack', topLabel: '', prefix: 'sv' }).items);
        items.push({ key: 'sv:cap', kind: 'text', x: SX + 98, y: SY + 46, text: 'at most ' + (k + 1) + ' questions deep', anchor: 'middle', size: 13, cls: 'tick' });
        return items;
      };
      const BUDGET = 46;
      F.add({ items: scene(null), say: 'Can ' + nm(s) + ' reach ' + nm(t) + '? A path never needs more than ' + (n - 1) + ' steps, so ask: in at most 2^' + k + ' = ' + (2 ** k) + ' steps? Each question of 2ⁱ steps splits into two of 2ⁱ⁻¹ at a midpoint.' });
      let shown = 0, skipped = 0, maxd = 0;
      ev.forEach((e, j) => {
        maxd = Math.max(maxd, e.stack.length);
        F.set('calls', e.calls).set('depth', e.stack.length).set('maxd', maxd);
        const last = j === ev.length - 1;
        if (shown >= BUDGET && e.d > 0 && !last) { skipped++; return; }
        if (shown === BUDGET && !F.list.some((f) => f.meta && f.meta.fast)) {
          F.add({ items: scene(e), say: 'The pattern repeats for every midpoint, so from here only the top question\'s moves are shown. The counters keep counting every question.', meta: { fast: true } });
        }
        shown++;
        const top = e.stack[e.stack.length - 1];
        let say;
        if (e.kind === 'ask') say = 'Ask: can ' + nm(e.u) + ' reach ' + nm(e.v) + ' in at most ' + (2 ** e.i) + ' steps? It goes on the stack, ' + e.stack.length + ' deep.';
        else if (e.kind === 'try' && (e.m === e.u || e.m === e.v)) say = 'Last, the midpoint ' + nm(e.m) + ' itself: one half is empty, which covers paths of at most ' + (2 ** (e.i - 1)) + ' steps. Ask ' + nm(e.u) + ' ⇝ ' + nm(e.m) + ', then ' + nm(e.m) + ' ⇝ ' + nm(e.v) + '.';
        else if (e.kind === 'try') say = 'Try the midpoint ' + nm(e.m) + ': first ' + nm(e.u) + ' ⇝ ' + nm(e.m) + ', then ' + nm(e.m) + ' ⇝ ' + nm(e.v) + ', each within ' + (2 ** (e.i - 1)) + ' steps.';
        else if (e.kind === 'base') say = 'Base question: ' + nm(e.u) + ' ⇝ ' + nm(e.v) + ' in at most 1 step? ' + (e.u === e.v ? 'Yes, it is the same vertex (0 steps).' : e.r ? 'Yes, there is an edge ' + nm(e.u) + '→' + nm(e.v) + '.' : 'No, there is no edge ' + nm(e.u) + '→' + nm(e.v) + '.');
        else if (e.kind === 'yes') say = 'Both halves hold through ' + nm(e.m) + ', so ' + nm(e.u) + ' reaches ' + nm(e.v) + ' within ' + (2 ** e.i) + ' steps. Pop the question; its memory is free again.';
        else say = 'No midpoint works: ' + nm(e.u) + ' cannot reach ' + nm(e.v) + ' within ' + (2 ** e.i) + ' steps. Pop it.';
        void top;
        F.add({ items: scene(e), say, meta: { kind: e.kind, d: e.d, m: e.m } });
      });
      const bits = log2c(n);
      F.add({ items: scene(null, { final: true }).concat(K.cx.bars({ rows: [{ id: 'calls', label: 'questions asked', value: calls, cls: 's4' }, { id: 'space', label: 'stack cells used', value: maxd, cls: 's1' }], x: SX + 130, y: SY + 84, w: 150, barH: 24, gap: 10, log: true, max: Math.max(calls, 10), prefix: 'cmp' }).items), say: (ans ? nm(s) + ' reaches ' + nm(t) + '.' : nm(s) + ' cannot reach ' + nm(t) + '.') + ' ' + calls + ' questions were asked (time grows like n^log n), yet the stack never held more than ' + maxd + ' of them, each ' + 3 + ' names of ' + bits + ' bits: O(log² n) space.' + (skipped ? ' (' + skipped + ' inner moves were not drawn.)' : ''), mark: ans ? 'accepted' : 'rejected', meta: { ans } });
      return { frames: F.list, result: ans, def: { sections: [
        { id: 'rec', kind: 'math', title: 'The recursion', text: 'reach(u, v, 1): u = v or u → v\nreach(u, v, 2t): for some m,\n  reach(u, m, t) and reach(m, v, t)\nstart: reach(' + nm(s) + ', ' + nm(t) + ', ' + (2 ** k) + '), ' + (2 ** k) + ' ≥ n − 1 = ' + (n - 1) },
        { id: 'cost', kind: 'math', title: 'Cost', text: 'depth: log₂ ' + (2 ** k) + ' = ' + k + ' (+1 for the base)\neach level: u, v, m: O(log n) bits\nspace O(log² n); time n^O(log n)\nNSPACE(s) ⊆ SPACE(s²), so NPSPACE = PSPACE' },
      ] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will the top question be answered yes?', answer: (fr) => (fr[fr.length - 1].meta.ans ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => f.meta && f.meta.kind === 'try' && f.meta.d === 0 && fr.slice(i + 1).find((x) => x.meta && x.meta.d === 0 && (x.meta.kind === 'yes' || x.meta.kind === 'try' || x.meta.kind === 'no')) && fr.slice(i + 1).find((x) => x.meta && x.meta.d === 0 && (x.meta.kind === 'yes' || x.meta.kind === 'try' || x.meta.kind === 'no')).meta.kind !== 'try', once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will this midpoint work for the top question?', answer: (fr, i) => (fr.slice(i + 1).find((x) => x.meta && x.meta.d === 0 && x.meta.kind !== 'try').meta.kind === 'yes' ? 'Yes' : 'No'), explain: 'It works exactly when both halves can be done in half the steps.' },
      { at: (f, i, fr) => f.meta && f.meta.kind === 'ask' && f.meta.d === 0 && fr[fr.length - 1].meta.ans, once: true, pick: 'item', ask: 'Other vertices are tried as midpoints in the order the edges name them, the two ends last. Click the vertex that will be the first midpoint to work for the top question.', answer: (fr) => { const y = fr.find((x) => x.meta && x.meta.kind === 'yes' && x.meta.d === 0); return y ? 'gr:v:' + y.meta.m : null; }, explain: 'A midpoint works when the start reaches it and it reaches the target, each in half the steps. If none in between works, an end itself serves: then the path is short enough for half the steps.' },
    ],
    quiz: [
      { q: 'Why does the recursion use so little space?', options: ['It remembers every answer', 'The two half questions run one after the other and reuse the same memory', 'It only asks log n questions in total', 'It uses a queue'], answer: 1, why: 'Only the current chain of questions is kept: log t levels, each with a few vertex names.' },
      { q: 'Savitch shows that NSPACE(s(n)) is inside…', options: ['SPACE(s(n))', 'SPACE(s(n)²)', 'TIME(s(n))', 'NTIME(s(n))'], answer: 1, why: 'Reachability among the 2^O(s) configurations is decided with depth O(s) and O(s) bits per level.' },
      { q: 'What does it cost in time?', options: ['Linear', 'Polynomial', 'About n^log n: each level tries n midpoints twice', 'Constant'], answer: 2, why: 'Each level multiplies the work by up to 2n, over log n levels: n^O(log n), more than any polynomial. Space is saved, time is not.' },
      { q: 'Why can the midpoint be the start vertex itself?', options: ['A mistake', 'A path of fewer steps is fine: "at most 2ⁱ" includes staying put for the first half', 'Because the graph is undirected', 'To end the recursion'], answer: 1, why: 'The question is "at most" 2ⁱ steps, and u reaches u in 0 steps, so shorter paths are covered.' },
      { q: 'Which famous equality follows from Savitch\'s theorem?', options: ['P = NP', 'L = NL', 'PSPACE = NPSPACE', 'P = PSPACE'], answer: 2, why: 'Squaring a polynomial gives a polynomial, so nondeterminism adds nothing to polynomial space.' },
    ],
  });

  // ---------- L and NL ----------
  T.topic({
    id: 'cx-lnl', family: 'cx-space', order: 30, title: 'Reachability in log space',
    blurb: 'A nondeterministic walker needs only the vertex it stands on and a step counter, about 2 log n bits, to decide PATH: it guesses each next vertex. Breadth-first search, deterministic, keeps a mark for every vertex.',
    inputs: [
      { id: 'g', kind: 'text', label: 'Edges', def: 'a→b, b→c, c→a, c→d, a→e, e→a', check: graphCheck },
      { id: 's', kind: 'string', label: 'From', def: 'a', max: 3 },
      { id: 't', kind: 'string', label: 'To', def: 'd', max: 3 },
    ],
    presets: [
      { label: 'A cycle: the counter stops a walk', values: { g: 'a→b, b→c, c→a, c→d, a→e, e→a', s: 'a', t: 'd' } },
      { label: 'A trap the target cannot be reached from', values: { g: 'a→b, b→c, a→d, d→e, e→d, c→f', s: 'a', t: 'f' } },
      { label: 'Unreachable: every guess fails', values: { g: 'a→b, b→c, c→a, d→e', s: 'a', t: 'e' } },
      { label: 'A dead end', values: { g: 'a→b, a→c, c→d, d→e', s: 'a', t: 'e' } },
    ],
    check: (inp) => graphCheck(inp.g, inp),
    counters: [{ id: 'steps', label: 'steps walked' }, { id: 'nl', label: 'NL bits' }, { id: 'bfs', label: 'BFS bits' }],
    run(inp) {
      const G = parseGraph(inp.g, inp.s, inp.t);
      const s = G.names.indexOf(inp.s), t = G.names.indexOf(inp.t);
      const n = G.n, adj = T.cx.adjacency(G).map((x) => [...x].sort((a, b) => a - b));
      const nm = (i) => G.names[i];
      const bits = log2c(n);
      const nlBits = 2 * bits;
      const R = T.cx.reach(G, s, t);
      // distance to t, along edges backwards
      const toT = new Array(n).fill(Infinity);
      toT[t] = 0;
      for (let ch = true; ch;) { ch = false; for (const [u, v] of G.edges) if (toT[v] + 1 < toT[u]) { toT[u] = toT[v] + 1; ch = true; } }
      const { pos } = ringPos(G, 0, 0);
      let gMaxX = -Infinity, gMaxY = -Infinity, gMinX = Infinity, gMinY = Infinity;
      for (const p of Object.values(pos)) { gMaxX = Math.max(gMaxX, p.x); gMaxY = Math.max(gMaxY, p.y); gMinX = Math.min(gMinX, p.x); gMinY = Math.min(gMinY, p.y); }
      const PX = gMaxX + 80;
      const F = new T.Frames(['steps', 'nl', 'bfs']);
      F.set('nl', nlBits).set('bfs', 0);
      const scene = (o) => {
        const cls = {}, ecls = {};
        cls[s] = 'active'; cls[t] = 'good';
        for (const v of o.dim || []) cls[v] = 'faded';
        for (const v of o.visited || []) if (v !== t && v !== s) cls[v] = 'cert';
        if (o.at !== undefined) cls[o.at] = o.atCls || 'hot';
        for (const [a, b] of o.walk || []) ecls[a + '>' + b] = o.walkCls || 'hot';
        const items = drawGraph(G, pos, { cls, ecls });
        // the guesses: a certificate read once, left to right
        const gs = o.guesses || [];
        if (o.guesses) {
          items.push({ key: 'lg:t', kind: 'text', x: gMinX - 20, y: gMaxY + 58, text: 'guesses, read once', cls: 'title' });
          items.push(...K.string.draw({ text: gs.length ? gs : [], x: gMinX - 20, y: gMaxY + 70, prefix: 'lg', head: false, cw: 42 }).items);
        }
        // the NL machine's whole memory
        const my = gMinY - 10;
        items.push({ key: 'nm:t', kind: 'text', x: PX, y: my, text: 'NL walker\'s memory', cls: 'title' });
        items.push({ key: 'nm:a', kind: 'cell', x: PX, y: my + 12, w: 116, h: 40, text: 'at: ' + (o.at === undefined ? '–' : nm(o.at)), cls: 'mono' + (o.at !== undefined ? ' act' : '') });
        items.push({ key: 'nm:c', kind: 'cell', x: PX + 124, y: my + 12, w: 136, h: 40, text: 'count: ' + (o.count === undefined ? '–' : o.count + ' / ' + (n - 1)), cls: 'mono' + (o.count === n - 1 && o.atCls === 'bad' ? ' bad' : '') });
        items.push({ key: 'nm:b', kind: 'text', x: PX, y: my + 72, text: '2 × ⌈log₂ ' + n + '⌉ = ' + nlBits + ' bits, whatever the path', size: 13, cls: 'tick' });
        // BFS's memory: a mark per vertex, and a queue
        const by = my + 112;
        items.push({ key: 'bm:t', kind: 'text', x: PX, y: by, text: 'BFS\'s memory: a mark per vertex', cls: 'title' });
        const vis = new Set(o.bfs || []);
        G.names.forEach((x, i) => items.push({ key: 'bm:c' + i, kind: 'cell', x: PX + i * 38, y: by + 12, w: 36, h: 38, text: x, sub: vis.has(i) ? '✓' : '·', cls: 'mono' + (vis.has(i) ? ' good' : '') + (o.bfsHot === i ? ' hot' : '') }));
        items.push({ key: 'bm:b', kind: 'text', x: PX, y: by + 86, text: n + ' bits, one per vertex, plus a queue', size: 13, cls: 'tick' });
        return items;
      };
      F.add({ items: scene({ guesses: [] }), say: 'Is there a path from ' + nm(s) + ' to ' + nm(t) + '? The NL walker keeps just two numbers: where it is and how many steps it has taken. Any path needs at most n − 1 = ' + (n - 1) + ' steps.' });
      // a walk: follow choices, at most n - 1 steps
      const walk = (choose, label) => {
        let at = s, count = 0;
        const guesses = [], path = [];
        F.set('steps', 0);
        F.add({ items: scene({ at, count, guesses: guesses.slice(), walk: [] }), say: label + ': the walker stands on ' + nm(s) + ' with its counter at 0.', meta: { walkStart: true, at } });
        while (true) {
          if (at === t) { F.add({ items: scene({ at, atCls: 'good', count, guesses: guesses.slice(), walk: path.slice(), walkCls: 'cert' }), say: 'The walker stands on ' + nm(t) + ': this branch accepts. One accepting branch is enough for a nondeterministic machine.', meta: { done: 'accept' } }); return 'accept'; }
          if (count === n - 1) { F.add({ items: scene({ at, atCls: 'bad', count, guesses: guesses.slice(), walk: path.slice(), walkCls: 'bad' }), say: 'The counter has reached n − 1 = ' + (n - 1) + ' without arriving: any real path would be shorter, so this branch rejects. The counter is what stops a walker going round a cycle for ever.', meta: { done: 'counter' } }); return 'counter'; }
          const nx = choose(at, count);
          if (nx === null) { F.add({ items: scene({ at, atCls: 'bad', count, guesses: guesses.slice(), walk: path.slice(), walkCls: 'bad' }), say: nm(at) + ' has no way out: the walker is stuck and this branch rejects.', meta: { done: 'stuck' } }); return 'stuck'; }
          const good = adj[at].filter((v) => toT[v] === toT[at] - 1);
          path.push([at, nx]); guesses.push(nm(nx));
          const from = at;
          at = nx; count++;
          F.count('steps');
          F.add({ items: scene({ at, count, guesses: guesses.slice(), walk: path.slice() }), say: 'Guess the next vertex: ' + nm(nx) + '. The edge ' + nm(from) + '→' + nm(nx) + ' exists, so step there; the counter becomes ' + count + '. The old vertex is forgotten.', meta: { from, good: good.map((v) => 'gr:v:' + v), lucky: label === 'A lucky branch' } });
        }
      };
      // an unlucky branch first: avoid getting closer to t while it can, preferring vertices not yet visited
      const unluckyStart = adj[s].some((v) => toT[v] !== toT[s] - 1);
      if (unluckyStart || !R.reachable) {
        const seen = new Set([s]);
        // worst first: a vertex with no way to t, then one that gets no closer, then anything; unvisited ones first
        walk((at) => { const out = adj[at]; if (!out.length) return null; const tiers = [out.filter((v) => toT[v] === Infinity), out.filter((v) => toT[v] !== Infinity && !(toT[v] < toT[at])), out]; for (const tier of tiers) { if (!tier.length) continue; const fresh = tier.filter((v) => !seen.has(v)); const v = (fresh.length ? fresh : tier)[0]; seen.add(v); return v; } return null; }, 'An unlucky branch');
      }
      if (R.reachable) walk((at) => adj[at].find((v) => toT[v] === toT[at] - 1), 'A lucky branch');
      else F.add({ items: scene({ guesses: [], dim: G.names.map((_, i) => i).filter((i) => i !== s && i !== t) }), say: 'Every branch fails like that one: no sequence of guesses reaches ' + nm(t) + ', so the nondeterministic machine rejects. NL needs no lucky branch to say no; it just has none.' });
      // breadth-first search, deterministically
      const order = [s], dist = new Array(n).fill(-1);
      dist[s] = 0;
      const vis = [s];
      F.set('bfs', n);
      F.add({ items: scene({ bfs: vis.slice(), visited: vis.slice(), bfsHot: s }), say: 'Now deterministically: breadth-first search marks ' + nm(s) + ' and works outward. It must remember every mark: ' + n + ' bits, one per vertex.' });
      for (let qi = 0; qi < order.length; qi++) {
        const u = order[qi];
        const fresh = adj[u].filter((v) => dist[v] < 0);
        if (!fresh.length) continue;
        for (const v of fresh) { dist[v] = dist[u] + 1; order.push(v); vis.push(v); }
        F.add({ items: scene({ bfs: vis.slice(), visited: vis.slice(), bfsHot: u, walk: fresh.map((v) => [u, v]), walkCls: 'cert' }), say: 'From ' + nm(u) + ', mark ' + fresh.map(nm).join(' and ') + '.' + (fresh.includes(t) ? ' ' + nm(t) + ' is marked: it is reachable.' : '') });
        if (fresh.includes(t)) break;
      }
      F.add({ items: scene({ bfs: vis.slice(), visited: vis.slice() }).concat(K.cx.bars({ rows: [8, 1024, 1e6].map((m) => ({ id: 'nl' + m, label: 'NL, n = ' + K.cx.num(m), value: 2 * log2c(m), cls: 's1' })).concat([8, 1024, 1e6].map((m) => ({ id: 'bf' + m, label: 'BFS, n = ' + K.cx.num(m), value: m, cls: 's4' }))), x: PX + 140, y: gMinY + 250, w: 170, barH: 18, gap: 6, log: true, max: 1e6, title: 'bits of memory, log scale', prefix: 'mem' }).items), say: (R.reachable ? nm(t) + ' is reachable.' : nm(t) + ' is not reachable.') + ' The walker\'s memory grows like log n; BFS grows like n. PATH is in NL; whether it is in L (deterministic log space) is the open question L = NL?', mark: R.reachable ? 'accepted' : 'rejected', meta: { reach: R.reachable } });
      return { frames: F.list, result: R.reachable, def: { sections: [
        { id: 'nl', kind: 'math', title: 'The NL walker', text: 'at := s, count := 0\nrepeat: if at = t accept\n  if count = n − 1 reject\n  guess v; if no edge at → v reject\n  at := v, count := count + 1\nmemory: 2⌈log₂ n⌉ bits' },
        { id: 'cls', kind: 'math', title: 'The classes', text: 'L = SPACE(log n)\nNL = NSPACE(log n)\nPATH is NL-complete\nL ⊆ NL ⊆ P; L = NL? is open\nNL = co-NL (proved)' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.lucky && fr[i + 1].meta.good && f.meta && f.meta.walkStart, pick: 'item', ask: 'This branch guesses well. Click a vertex it could step to next, on a shortest way to the target.', answer: (fr, i) => fr[i + 1].meta.good, explain: 'A lucky guess moves one step closer to the target along an edge.' },
      { at: (f, i, fr) => f.meta && f.meta.walkStart && !fr.slice(i + 1).some((x) => x.meta && x.meta.lucky), once: true, pick: 'option', options: ['It reaches the target', 'Its counter runs out', 'It gets stuck'], ask: 'How will this branch end?', answer: (fr, i) => { const d = fr.slice(i + 1).find((x) => x.meta && x.meta.done).meta.done; return d === 'accept' ? 'It reaches the target' : d === 'counter' ? 'Its counter runs out' : 'It gets stuck'; }, explain: 'A branch ends at the target, at a vertex with no way out, or when the counter shows it has walked n − 1 steps.' },
    ],
    quiz: [
      { q: 'What does the NL walker keep in memory?', options: ['The whole path so far', 'The current vertex and a step counter', 'A mark for every vertex', 'Nothing'], answer: 1, why: 'Two numbers below n: about 2 log n bits. The path itself is only in the guesses, which are never stored.' },
      { q: 'Why does the walker need a counter?', options: ['To count edges', 'Without it a branch could go round a cycle for ever; n − 1 steps suffice for any path', 'To make it deterministic', 'To store the answer'], answer: 1, why: 'Every branch must halt. A shortest path has at most n − 1 steps, so stopping there loses nothing.' },
      { q: 'How much memory does breadth-first search use?', options: ['log n bits', 'A mark per vertex: about n bits', 'n² bits', 'Constant'], answer: 1, why: 'It must remember which vertices are already reached, which takes a bit per vertex (and a queue).' },
      { q: 'In the unreachable case, how does the NL machine say no?', options: ['One branch rejects', 'Every branch rejects', 'It runs for ever', 'It cannot say no'], answer: 1, why: 'A nondeterministic machine accepts when some branch accepts; it rejects when none does. (That NL is closed under complement is a separate, surprising theorem.)' },
      { q: 'Which is known?', options: ['L = NL', 'L ≠ NL', 'NL ⊆ P', 'P ⊆ NL'], answer: 2, why: 'An NL machine has polynomially many configurations, so reachability among them is decided in polynomial time. L = NL is open.' },
    ],
  });

  // ---------- the class map ----------
  // Boxes (stage units), outermost first. NP and co-NP overlap; P lies in both.
  const BOX = {
    exp: { x: 0, y: 0, w: 900, h: 660, label: 'EXPTIME', cls: 'r4', def: 'TIME(2^poly n)' },
    pspace: { x: 24, y: 46, w: 852, h: 566, label: 'PSPACE = NPSPACE', cls: 'r3', def: 'SPACE(poly n)' },
    np: { x: 48, y: 92, w: 520, h: 460, label: 'NP', cls: 'r0', def: 'NTIME(poly n)' },
    conp: { x: 332, y: 92, w: 520, h: 460, label: 'co-NP', cls: 'r5', def: 'co-NTIME(poly n)' },
    p: { x: 346, y: 140, w: 208, h: 390, label: 'P', cls: 'r1', def: 'TIME(poly n)' },
    nl: { x: 360, y: 220, w: 180, h: 200, label: 'NL', cls: 'r2', def: 'NSPACE(log n)' },
    l: { x: 374, y: 300, w: 152, h: 104, label: 'L', cls: 'r1', def: 'SPACE(log n)' },
  };
  const ORDER = ['exp', 'pspace', 'np', 'conp', 'p', 'nl', 'l'];
  // problems: where they are known to lie (the smallest box on the map), and where they sit
  const PROBS = [
    { id: 'upath', label: 'UPATH', in: 'l', x: 456, y: 368, why: 'UPATH, reachability in an undirected graph can be done in deterministic log space.' },
    { id: 'path', label: 'PATH', in: 'nl', x: 410, y: 282, why: 'Directed reachability is NL-complete: the guessing walker.' },
    { id: '2sat', label: '2-SAT', in: 'nl', x: 496, y: 282, why: '2-SAT is NL-complete: unsatisfiable exactly when some x and ¬x reach each other in the implication graph.' },
    { id: 'cyk', label: 'CFG MEMBER', in: 'p', x: 410, y: 470, why: 'CYK decides membership in a context-free language in cubic time.' },
    { id: 'primes', label: 'PRIMES', in: 'p', x: 490, y: 500, why: 'Primality has a polynomial-time test; long before that it was known to be in NP ∩ co-NP.' },
    { id: 'sat', label: 'SAT', in: 'np', x: 120, y: 200, why: 'SAT is NP-complete: in P only if P = NP.' },
    { id: 'clique', label: 'CLIQUE', in: 'np', x: 120, y: 300, why: 'CLIQUE is NP-complete, by the reduction from 3SAT.' },
    { id: 'ham', label: 'HAM-PATH', in: 'np', x: 120, y: 400, why: 'HAM-PATH is NP-complete.' },
    { id: 'unsat', label: 'UNSAT', in: 'conp', x: 640, y: 220, why: 'UNSAT is co-NP-complete: a no-certificate (a satisfying assignment) is easy to check.' },
    { id: 'taut', label: 'TAUTOLOGY', in: 'conp', x: 640, y: 330, why: 'TAUTOLOGY is co-NP-complete.' },
    { id: 'tqbf', label: 'TQBF', in: 'pspace', x: 700, y: 584, why: 'TQBF is PSPACE-complete: the game tree needs only one path of memory.' },
    { id: 'game', label: 'n×n GAME', in: 'exp', x: 130, y: 638, why: 'Deciding who wins some generalised board games is EXPTIME-complete, so provably not in P.' },
  ];
  const QUESTIONS = [
    { id: 'lnl', text: 'L = NL ?', x: 450, y: 438 },
    { id: 'pnp', text: 'P = NP ?', x: 200, y: 130 },
    { id: 'npco', text: 'NP = co-NP ?', x: 590, y: 130 },
    { id: 'pps', text: 'P = PSPACE ?', x: 450, y: 78 },
  ];

  T.topic({
    id: 'cx-classmap', family: 'cx-space', order: 40, title: 'The map of the classes',
    blurb: 'L, NL, P, NP, co-NP, PSPACE and EXPTIME drawn as nested regions, problems placed where they are known to belong, the questions nobody can answer marked, and the two separations the hierarchy theorems prove.',
    inputs: [{ id: 'world', kind: 'choice', label: 'World', def: 'known', options: [{ value: 'known', label: 'As known today' }, { value: 'pnp', label: 'Suppose P = NP' }, { value: 'pps', label: 'Suppose P = PSPACE' }] }],
    presets: [
      { label: 'As known today', values: { world: 'known' } },
      { label: 'If P = NP: the middle collapses', values: { world: 'pnp' } },
      { label: 'If P = PSPACE: even games are easy', values: { world: 'pps' } },
    ],
    counters: [{ id: 'classes', label: 'classes drawn' }, { id: 'probs', label: 'problems placed' }, { id: 'open', label: 'open questions' }],
    run(inp) {
      const F = new T.Frames(['classes', 'probs', 'open']);
      const shown = new Set(), placed = new Set(), marks = new Set();
      let hot = null, seps = false;
      let box = Object.assign({}, BOX);
      let probIn = {};
      for (const p of PROBS) probIn[p.id] = { x: p.x, y: p.y };
      const scene = (opts) => {
        opts = opts || {};
        const items = [];
        for (const id of ORDER) {
          if (!shown.has(id) || box[id].gone) continue;
          const b = box[id];
          items.push({ key: 'cm:r:' + id, kind: 'region', x: b.x, y: b.y, w: b.w, h: b.h, text: '', rx: 18, cls: b.cls + (hot === id ? ' hot' : ''), pick: true });
          items.push({ key: 'cm:rl:' + id, kind: 'text', x: id === 'conp' ? b.x + b.w - 14 : b.x + 14, y: b.y + 24, text: b.label, anchor: id === 'conp' ? 'end' : 'start', size: 16, cls: 'region-label' });
        }
        for (const p of PROBS) {
          if (!placed.has(p.id)) continue;
          const at = probIn[p.id];
          items.push({ key: 'cm:p:' + p.id, kind: 'token', x: at.x - Geo.textWidth(p.label, 15, { bold: true }) / 2 - 10, y: at.y - 5, r: 5.5, cls: opts.newP === p.id ? 'act' : 'good' });
          items.push({ key: 'cm:pl:' + p.id, kind: 'text', x: at.x + 2, y: at.y + 1, text: p.label, anchor: 'middle', size: 15, cls: 'strong' });
        }
        for (const q of QUESTIONS) if (marks.has(q.id)) items.push({ key: 'cm:q:' + q.id, kind: 'text', x: q.x, y: q.y, text: q.text, anchor: 'middle', size: 15, cls: 'hot' });
        if (seps) {
          items.push({ key: 'cm:s1', kind: 'text', x: 450, y: 28, text: 'P ≠ EXPTIME (time hierarchy)', anchor: 'middle', size: 14, cls: 'bad' });
        }
        return items;
      };
      const hl = (id) => ({ cls: [String(ORDER.indexOf(id))] });
      const addClass = (id, say, extra) => { shown.add(id); hot = id; F.set('classes', shown.size); F.add(Object.assign({ items: scene(), say, hl: hl(id) }, extra || {})); };
      const place = (pid, say) => { placed.add(pid); F.set('probs', placed.size); F.add({ items: scene({ newP: pid }), say, meta: { placed: pid } }); };
      const ask = (pid) => ({ meta: { ask: pid } });
      addClass('p', 'Start with P: problems a deterministic machine decides in polynomial time. This is the usual picture of "efficiently solvable".');
      place('cyk', 'CFG MEMBER (is w generated by a fixed grammar?) is in P: CYK takes about n³ steps.');
      F.add(Object.assign({ items: scene(), say: 'Next, PRIMES: is a number given in binary prime? Where is it known to belong?' }, ask('primes')));
      place('primes', PROBS[4].why);
      addClass('np', 'NP: problems whose yes-answers have certificates a polynomial-time verifier can check. P ⊆ NP, since a P machine can ignore the certificate.');
      F.add(Object.assign({ items: scene(), say: 'SAT: is a formula satisfiable? Click the smallest region known to contain it.' }, ask('sat')));
      place('sat', PROBS[5].why); place('clique', PROBS[6].why); place('ham', PROBS[7].why);
      addClass('conp', 'co-NP: problems whose no-answers have checkable certificates. P lies inside both NP and co-NP.');
      place('unsat', PROBS[8].why); place('taut', PROBS[9].why);
      addClass('nl', 'Inside P: NL, nondeterministic log space. Its configurations are polynomially many, so NL ⊆ P.');
      place('path', PROBS[1].why); place('2sat', PROBS[2].why);
      addClass('l', 'And L, deterministic log space: a few counters and pointers into the input.');
      place('upath', PROBS[0].why);
      addClass('pspace', 'PSPACE: polynomial memory, any amount of time. NP ⊆ PSPACE: try every certificate, reusing the space. By Savitch, nondeterminism adds nothing here.');
      F.add(Object.assign({ items: scene(), say: 'TQBF: is a fully quantified formula true? Click the smallest region known to contain it.' }, ask('tqbf')));
      place('tqbf', PROBS[10].why);
      addClass('exp', 'EXPTIME: exponential time. A PSPACE machine has only exponentially many configurations, so PSPACE ⊆ EXPTIME.');
      place('game', PROBS[11].why);
      hot = null; seps = true;
      F.add({ items: scene(), say: 'What is proved: the time hierarchy theorem gives P ≠ EXPTIME, and the space hierarchy theorem gives NL ≠ PSPACE. So somewhere in each chain a containment is strict, but nobody knows where.', hl: { cls: ['4', '6'] } });
      for (const q of QUESTIONS) { marks.add(q.id); F.set('open', marks.size); }
      F.add({ items: scene(), say: 'And what is open: L = NL? P = NP? NP = co-NP? P = PSPACE? Every one of these containments might be an equality; none has been settled.', meta: { open: true } });
      if (inp.world === 'pnp') {
        box = Object.assign({}, box, { np: { x: 48, y: 92, w: 804, h: 460, label: 'P = NP = co-NP', cls: 'r1', def: BOX.np.def }, conp: Object.assign({}, BOX.conp, { gone: true }), p: Object.assign({}, BOX.p, { gone: true }) });
        hot = 'np'; marks.delete('pnp'); marks.delete('npco'); F.set('open', marks.size);
        F.add({ items: scene(), exits: { 'cm:r:conp': { exit: 'into', into: 'cm:r:np' }, 'cm:r:p': { exit: 'into', into: 'cm:r:np' } }, say: 'Suppose P = NP. Then P grows to fill NP, and co-NP joins them (P is closed under complement). SAT, CLIQUE, HAM-PATH, UNSAT and TAUTOLOGY all move into P: every checkable answer could also be found fast.', mark: 'accepted', meta: { world: 'pnp' } });
      } else if (inp.world === 'pps') {
        const P = BOX.p;
        box = Object.assign({}, box, { pspace: Object.assign({}, BOX.pspace, { label: 'P = NP = co-NP = PSPACE', cls: 'r1' }), np: Object.assign({}, P, { gone: true }), conp: Object.assign({}, P, { gone: true }), p: Object.assign({}, P, { gone: true }) });
        hot = 'pspace'; marks.delete('pnp'); marks.delete('npco'); marks.delete('pps'); F.set('open', marks.size);
        F.add({ items: scene(), exits: { 'cm:r:np': { exit: 'into', into: 'cm:r:pspace' }, 'cm:r:conp': { exit: 'into', into: 'cm:r:pspace' }, 'cm:r:p': { exit: 'into', into: 'cm:r:pspace' } }, say: 'Suppose P = PSPACE. Then everything between collapses too: P = NP = co-NP = PSPACE, and TQBF, the game tree with 2ⁿ leaves, would have a polynomial-time algorithm. EXPTIME stays bigger, by the hierarchy theorem.', mark: 'accepted', meta: { world: 'pps' } });
      } else {
        F.add({ items: scene(), say: 'The map as known today: every region is drawn as if strictly bigger than the one inside, which is what most people believe, but only the two separations are proved.', mark: 'accepted' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'cls', kind: 'table', title: 'The classes', colHead: ['class', 'resource'], rows: ORDER.map((id) => [BOX[id].label, BOX[id].def]) },
        { id: 'chain', kind: 'math', title: 'Known', text: 'L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME\nP ⊆ co-NP ⊆ PSPACE\nP ≠ EXPTIME, NL ≠ PSPACE' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask === 'primes', pick: 'item', ask: 'Click the smallest region on the map known to contain PRIMES.', answer: () => 'cm:r:p', explain: PROBS[4].why },
      { at: (f) => f.meta && f.meta.ask === 'sat', pick: 'item', ask: 'Click the smallest region known to contain SAT.', answer: () => 'cm:r:np', explain: 'SAT is in NP (an assignment is a certificate). It is not known to be in P, nor in co-NP.' },
      { at: (f) => f.meta && f.meta.ask === 'tqbf', pick: 'item', ask: 'Click the smallest region known to contain TQBF.', answer: () => 'cm:r:pspace', explain: PROBS[10].why },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.open, pick: 'option', options: ['P ≠ NP', 'P ≠ EXPTIME', 'NP ≠ co-NP', 'L ≠ P'], ask: 'Which of these separations is actually proved?', answer: () => 'P ≠ EXPTIME', explain: 'The time hierarchy theorem: more time decides strictly more. The others are open.' },
    ],
    quiz: [
      { q: 'Which containment is proved to be strict?', options: ['P ⊂ NP', 'NL ⊂ PSPACE', 'L ⊂ NL', 'NP ⊂ PSPACE'], answer: 1, why: 'The space hierarchy theorem: log space is strictly less than polynomial space. The others are open.' },
      { q: 'Why is NP inside PSPACE?', options: ['NP problems are easy', 'A machine can try every certificate one after another, reusing the same polynomial space', 'Because of Savitch', 'It is not known'], answer: 1, why: 'Time is spent freely but memory is reused: each certificate is checked and then erased.' },
      { q: 'If someone proved P = NP, what would happen to co-NP?', options: ['Nothing', 'It would equal P too', 'It would become larger', 'It would become empty'], answer: 1, why: 'P is closed under complement: if NP = P then co-NP = co-P = P.' },
      { q: 'Where is PRIMES known to be?', options: ['Only in NP', 'Only in co-NP', 'In P', 'In EXPTIME only'], answer: 2, why: 'There is a deterministic polynomial-time primality test.' },
      { q: 'P ≠ EXPTIME is proved. What does it tell us about P vs PSPACE?', options: ['P = PSPACE', 'P ≠ PSPACE', 'At least one of P ≠ PSPACE and PSPACE ≠ EXPTIME holds', 'Nothing at all'], answer: 2, why: 'If both were equalities then P = EXPTIME, which is false. Which one is strict is unknown.' },
    ],
  });
})();
