// Coping with NP-completeness: a search that backtracks and prunes (vertex cover with a budget, whose tree
// has at most 2^k leaves however big the graph), an approximation with a guarantee (take both ends of an
// uncovered edge: never more than twice the best), and a special case that is easy (the largest independent
// set of a tree, by two numbers per vertex computed from the leaves up).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'cx-cope', part: 'complexity', order: 70, title: 'Coping with NP-completeness', blurb: 'When a problem is NP-complete: search cleverly, settle for a provably good answer, or notice that your instances are a special case that is easy.' });

  /** "0-1 1-2 3" as a graph {n, edges}; a lone number is a vertex with no edges */
  function parseGraph(text, maxN) {
    const toks = String(text || '').split(/[\s,;]+/).filter(Boolean);
    const edges = [];
    let n = 0;
    for (const tk of toks) {
      const m = /^(\d+)(?:-(\d+))?$/.exec(tk);
      if (!m) throw new Error('Edges: write them like 0-1 1-2, with vertices numbered from 0 ("' + tk + '" is not an edge)');
      const a = +m[1], b = m[2] === undefined ? null : +m[2];
      n = Math.max(n, a + 1, b === null ? 0 : b + 1);
      if (b === null) continue;
      if (a === b) throw new Error('Edges: ' + tk + ' joins a vertex to itself');
      if (edges.some(([x, y]) => (x === a && y === b) || (x === b && y === a))) throw new Error('Edges: ' + tk + ' is listed twice');
      edges.push([a, b]);
    }
    if (!n) throw new Error('Edges: give at least one vertex, like 0-1');
    if (n > (maxN || 9)) throw new Error('Edges: at most ' + (maxN || 9) + ' vertices (0 to ' + ((maxN || 9) - 1) + '), so the picture stays readable');
    return { n, edges };
  }
  const graphCheck = (maxN, maxE) => (v) => { try { const G = parseGraph(v, maxN); if (G.edges.length > maxE) return 'Edges: at most ' + maxE + ' edges'; return null; } catch (e) { return e.message; } };
  const ekey = (a, b) => (a < b ? a + '|' + b : b + '|' + a);
  /** The graph drawn with the gadget kit; cover vertices lit, edges coloured by cls(u, v) */
  function drawGraph(G, o) {
    const nodes = Array.from({ length: G.n }, (_, i) => ({ id: i, label: String(i), cls: (o.vcls && o.vcls(i)) || '', x: o.pos ? o.pos[i].x + (o.dx || 0) : undefined, y: o.pos ? o.pos[i].y + (o.dy || 0) : undefined }));
    const edges = G.edges.map(([a, b]) => ({ a, b, cls: (o.ecls && o.ecls(a, b)) || '' }));
    return K.gadget.draw({ nodes, edges, cert: o.cert || [], prefix: o.prefix || 'gd', r: 21 });
  }
  const binom = (n, k) => { let r = 1; for (let i = 0; i < k; i++) r = (r * (n - i)) / (i + 1); return Math.round(r); };

  // ---------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cx-backtrack', family: 'cx-cope', order: 10, title: 'Backtracking with pruning',
    blurb: 'Is there a vertex cover of size k? Some end of every edge must be in it, so branch on the two ends of an uncovered edge and give up on a branch when the budget runs out. The tree has at most 2^k leaves, whatever the size of the graph.',
    inputs: [
      { id: 'g', kind: 'text', label: 'Edges', def: '0-1 1-2 2-3 3-4 4-5 5-0', check: graphCheck(9, 14) },
      { id: 'k', kind: 'number', label: 'Budget k', def: 3, min: 0, max: 3 },
    ],
    presets: [
      { label: 'A six-cycle, k = 3', values: { g: '0-1 1-2 2-3 3-4 4-5 5-0', k: 3 } },
      { label: 'A six-cycle, k = 2: no cover', values: { g: '0-1 1-2 2-3 3-4 4-5 5-0', k: 2 } },
      { label: 'A star, the wrong end first', values: { g: '1-0 2-0 3-0 4-0 5-0', k: 1 } },
      { label: 'A house, k = 3', values: { g: '0-1 1-2 2-3 3-0 2-4 3-4', k: 3 } },
      { label: 'Budget 0 with an edge', values: { g: '0-1', k: 0 } },
    ],
    counters: [{ id: 'nodes', label: 'search nodes' }, { id: 'pruned', label: 'pruned' }, { id: 'brute', label: 'subsets of size ≤ k' }],
    run(inp) {
      const G = parseGraph(inp.g), k = inp.k;
      const pos = drawGraph(G, {}).pos;
      // the search, recorded as a list of events on a tree
      const tree = [], events = [];
      let found = null;
      const go = (cover, budget, parent, label) => {
        const id = tree.length;
        tree.push({ id, parent, label, status: 'open', cover: cover.slice(), budget });
        const set = new Set(cover);
        const e = G.edges.find(([u, v]) => !set.has(u) && !set.has(v));
        if (!e) { tree[id].status = 'found'; found = cover.slice(); events.push({ kind: 'found', node: id, cover: cover.slice() }); return true; }
        if (!budget) { tree[id].status = 'pruned'; events.push({ kind: 'prune', node: id, edge: e, cover: cover.slice() }); return false; }
        tree[id].status = 'split';
        events.push({ kind: 'split', node: id, edge: e, cover: cover.slice(), budget });
        for (const x of e) if (go(cover.concat([x]), budget - 1, id, '+' + x)) return true;
        events.push({ kind: 'back', node: id, edge: e, cover: cover.slice() });
        return false;
      };
      go([], k, -1, 'k=' + k);
      let brute = 0; for (let i = 0; i <= k; i++) brute += binom(G.n, i);
      const F = new T.Frames(['nodes', 'pruned', 'brute']);
      F.set('brute', brute);
      const seen = new Set();
      const treeOf = (hot) => {
        const mk = (id) => {
          const nd = tree[id];
          return { id: 'n' + id, label: nd.label, cls: [nd.status === 'pruned' ? 'pruned reject' : nd.status === 'found' ? 'good' : '', id === hot ? 'hot' : ''].filter(Boolean).join(' '), children: tree.filter((c) => c.parent === id && seen.has(c.id)).map((c) => mk(c.id)) };
        };
        return mk(0);
      };
      // the tree sits to the right of the graph
      const gx = Math.max(...Object.values(pos).map((p) => p.x)) + 70;
      const gy = Math.min(...Object.values(pos).map((p) => p.y));
      const scene = (ev, extra) => {
        const set = new Set(ev ? ev.cover : []);
        const cur = ev && ev.edge ? ekey(ev.edge[0], ev.edge[1]) : null;
        const g = drawGraph(G, { pos, cert: ev ? ev.cover : [], ecls: (a, b) => (ekey(a, b) === cur ? (ev.kind === 'prune' ? 'bad thick' : 'hot thick') : set.has(a) || set.has(b) ? 'good' : '') }).items;
        const tr = K.tree.draw(treeOf(ev ? ev.node : -1), { x: gx + 150, y: gy, gapX: 12, gapY: 76, prefix: 'st' }).items;
        return g.concat(tr, [{ key: 'tt', kind: 'text', x: gx + 150, y: gy - 42, text: 'search tree', anchor: 'middle', cls: 'title' }], extra || []);
      };
      const name = (e) => e[0] + '–' + e[1];
      F.add({ items: scene(null), say: 'Is there a vertex cover of at most k = ' + k + ' vertices? Trying every set of ' + k + ' or fewer of the ' + G.n + ' vertices would mean ' + brute + ' subsets. Search instead.', meta: { yes: 'unknown' } });
      for (const ev of events) {
        if (ev.kind === 'back') { F.add({ items: scene(ev), say: 'Both ways of covering ' + name(ev.edge) + ' failed from here: back up.' }); continue; }
        seen.add(ev.node);
        F.count('nodes');
        const nd = tree[ev.node];
        const here = nd.parent < 0 ? 'At the start, with nothing chosen' : 'With {' + ev.cover.join(', ') + '} chosen';
        if (ev.kind === 'split') F.add({ items: scene(ev), say: here + ', edge ' + name(ev.edge) + ' is not covered. Any cover must contain ' + ev.edge[0] + ' or ' + ev.edge[1] + ', so branch on the two, ' + ev.budget + ' left in the budget.', meta: { next: ev.edge.map((x) => 'gd:v:' + x) } });
        else if (ev.kind === 'prune') { F.count('pruned'); F.add({ items: scene(ev), say: here + ' the budget is used up, but edge ' + name(ev.edge) + ' is still uncovered: prune this branch. Nothing below it can work.' }); }
        else F.add({ items: scene(ev), say: here + ' every edge is covered: {' + ev.cover.join(', ') + '} is a vertex cover of size ' + ev.cover.length + '.', mark: 'found' });
      }
      F.add({ items: scene(found ? events[events.length - 1] : null), say: (found ? 'Found a cover of size ' + found.length + ' after ' + F.counts.nodes + ' search nodes. ' : 'Every branch was pruned: no vertex cover of size ' + k + ' exists, proved with ' + F.counts.nodes + ' search nodes. ') + 'The tree has at most 2^k = ' + Math.pow(2, k) + ' leaves however many vertices there are: about 2^k · m work instead of ' + brute + ' subsets.', mark: found ? 'yes' : 'no' });
      F.list[0].meta.yes = found ? 'Yes' : 'No';
      return { frames: F.list, result: !!found, def: { sections: [
        { id: 'rule', kind: 'math', title: 'The search', text: 'cover(C, b):\n  if every edge touches C: success\n  if b = 0: prune\n  take an uncovered edge u–v\n  try cover(C + u, b − 1), then cover(C + v, b − 1)' },
        { id: 'cost', kind: 'math', title: 'Cost', text: 'leaves ≤ 2^k = ' + Math.pow(2, k) + '\nsubsets of size ≤ k: ' + brute + ' (grows like n^k)' },
      ] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Before the search: is there a vertex cover within the budget?', answer: (fr) => fr[0].meta.yes, explain: (fr) => fr[fr.length - 1].say },
      { at: (f) => f.meta && f.meta.next, once: true, pick: 'item', ask: 'The search branches on this uncovered edge. Click a vertex it will try to add.', answer: (fr, i) => fr[i].meta.next, explain: 'Either end of the edge: any cover must contain one of them, so these two branches miss nothing.' },
    ],
    quiz: [
      { q: 'Why may the search branch only on the two ends of one uncovered edge?', options: ['To save memory', 'Every cover contains an end of that edge, so the two branches between them miss no solution', 'Because the graph is a tree', 'It is a heuristic that may miss covers'], answer: 1, why: 'A vertex cover touches every edge, so it must contain u or v: trying both is exhaustive.' },
      { q: 'How many leaves can the tree have with budget k?', options: ['k', '2^k', 'n^k', '2^n'], answer: 1, why: 'Two branches per level and at most k levels before the budget runs out.' },
      { q: 'When is a branch pruned?', options: ['When it finds a cover', 'When the budget is used up and an edge is still uncovered', 'When a vertex has no edges', 'Never'], answer: 1, why: 'With nothing left to spend, the uncovered edge can never be covered on this branch.' },
      { q: 'Does this make vertex cover polynomial?', options: ['Yes, always', 'No: 2^k is exponential in k, but for small k the search is fast whatever n is', 'Only on trees', 'Only if k > n'], answer: 1, why: 'The running time is about 2^k times the graph size: exponential only in the parameter k. Such problems are called fixed-parameter tractable.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cx-approx-vc', family: 'cx-cope', order: 20, title: 'An approximation within twice the best',
    blurb: 'Take any edge not yet covered and put both of its ends in the cover. The edges taken share no vertex, and any cover needs one end of each, so the result is never more than twice the smallest cover.',
    inputs: [{ id: 'g', kind: 'text', label: 'Edges (in the order they are looked at)', def: '0-1 1-2 2-3', check: graphCheck(8, 12) }],
    presets: [
      { label: 'A path: exactly twice', values: { g: '0-1 1-2 2-3' } },
      { label: 'A triangle: optimal', values: { g: '0-1 1-2 2-0' } },
      { label: 'A star', values: { g: '0-1 0-2 0-3 0-4 0-5' } },
      { label: 'Separate edges', values: { g: '0-1 2-3 4-5' } },
      { label: 'Complete bipartite 3 by 3', values: { g: '0-3 0-4 0-5 1-3 1-4 1-5 2-3 2-4 2-5' } },
    ],
    counters: [{ id: 'looked', label: 'edges looked at' }, { id: 'taken', label: 'edges taken' }, { id: 'cover', label: 'cover size' }],
    run(inp) {
      const G = parseGraph(inp.g, 8);
      const pos = drawGraph(G, {}).pos;
      const F = new T.Frames(['looked', 'taken', 'cover']);
      const cover = new Set(), matched = new Set();
      const ecls = (a, b) => (matched.has(ekey(a, b)) ? 'hot thick' : cover.has(a) || cover.has(b) ? 'good' : '');
      const xs = Object.values(pos).map((p) => p.x), ys = Object.values(pos).map((p) => p.y);
      const W = Math.max(...xs) - Math.min(...xs);
      const top = Math.min(...ys) - 70;
      const head = (key, x, text) => ({ key, kind: 'text', x, y: top, text, cls: 'title' });
      const left = Math.min(...xs) - 30;
      const scene = (extra, cur) => drawGraph(G, { pos, cert: [...cover], ecls: (a, b) => (cur && ekey(a, b) === cur ? 'bad thick' : ecls(a, b)) }).items.concat([head('h1', left, 'take both ends')], extra || []);
      F.add({ items: scene(), say: 'Go through the edges in order. Whenever an edge has neither end in the cover yet, put both of its ends in.' });
      let asked = false;
      for (const [a, b] of G.edges) {
        F.count('looked');
        if (cover.has(a) || cover.has(b)) { F.add({ items: scene([], null), say: 'Edge ' + a + '–' + b + ' is already covered by ' + (cover.has(a) ? a : b) + ': skip it.' }); continue; }
        if (!asked) { asked = true; F.add({ items: scene([], ekey(a, b)), say: 'Edge ' + a + '–' + b + ' has neither end in the cover.', meta: { take: ['gd:v:' + a, 'gd:v:' + b] } }); }
        cover.add(a); cover.add(b); matched.add(ekey(a, b));
        F.count('taken').set('cover', cover.size);
        F.add({ items: scene(), say: 'Edge ' + a + '–' + b + ' is not covered: take both ' + a + ' and ' + b + '. The cover now has ' + cover.size + ' vertices.' });
      }
      // the best cover, for comparison, drawn beside
      let opt = null;
      for (let k = 0; k <= G.n && !opt; k++) opt = T.cx.findVertexCover(G, k);
      const dx = W + 150;
      const optG = drawGraph(G, { pos, dx, prefix: 'op', cert: opt, ecls: (a, b) => (matched.has(ekey(a, b)) ? 'hot thick' : '') }).items;
      const ratio = opt.length ? cover.size / opt.length : 1;
      const rtxt = opt.length ? (Math.round(ratio * 100) / 100) : 1;
      const bars = K.cx.bars({ rows: [{ id: 'ap', label: 'take both ends', value: cover.size, cls: 's3' }, { id: 'op', label: 'smallest cover', value: opt.length, cls: 's1' }], x: left + 140, y: Math.max(...ys) + 70, w: 200, barH: 26, max: Math.max(cover.size, 1), prefix: 'cmp' }).items;
      const verdict = ratio === 2 ? 'exactly 2' : ratio === 1 ? '1' : 'between 1 and 2';
      F.add({ items: scene([head('h2', left + dx, 'smallest cover')].concat(optG)), say: 'The approximation took ' + matched.size + ' edge' + (matched.size === 1 ? '' : 's') + ' and has ' + cover.size + ' vertices. Beside it, a smallest cover, found by exhaustive search: how do they compare?', meta: { ratio: verdict } });
      F.add({ items: scene([head('h2', left + dx, 'smallest cover')].concat(optG, bars)), say: 'The smallest cover has ' + opt.length + ' vertices, so the ratio is ' + cover.size + ' / ' + opt.length + ' = ' + rtxt + '. The taken edges (amber) share no vertex, and any cover, the best included, needs one end of each: best ≥ ' + matched.size + ', while ours = 2 · ' + matched.size + ' = ' + cover.size + '.' + (ratio === 2 ? ' Here the bound of 2 is reached exactly.' : ratio === 1 ? ' Here it happens to be optimal.' : ''), mark: 'ratio ' + rtxt });
      return { frames: F.list, def: { sections: [
        { id: 'alg', kind: 'math', title: 'The algorithm', text: 'C = ∅\nfor each edge u–v:\n  if neither u nor v is in C: add both\nreturn C' },
        { id: 'why', kind: 'math', title: 'Why at most twice the best', text: 'taken edges M share no vertex\nany cover has ≥ |M| vertices (one per edge of M)\n|C| = 2|M| ≤ 2 · best' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.take, once: true, pick: 'item', ask: 'This edge is not covered. Click a vertex the algorithm will add.', answer: (fr, i) => fr[i].meta.take, explain: 'Both ends go in, not just one: that is what keeps the taken edges disjoint and the bound provable.' },
      { at: (f) => f.meta && f.meta.ratio, once: true, pick: 'option', options: ['1', 'between 1 and 2', 'exactly 2'], ask: 'What will the ratio approximation / best be here?', answer: (fr, i) => fr[i].meta.ratio, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why must any vertex cover have at least as many vertices as the number of edges taken?', options: ['The taken edges share no vertex, and each needs its own covering end', 'Because the graph is connected', 'Because covers are minimal', 'It need not'], answer: 0, why: 'One vertex can cover at most one of a set of edges with no shared ends.' },
      { q: 'What is the worst ratio this algorithm can give?', options: ['1.5', '2', 'log n', 'n'], answer: 1, why: 'The cover is exactly twice the number of taken edges, and the best cover is at least that number.' },
      { q: 'On a path 0–1–2–3 with edges in order, what does it return?', options: ['{1, 2}', '{0, 1, 2, 3}', '{1, 3}', '{0, 2}'], answer: 1, why: 'It takes 0–1, skips 1–2, takes 2–3: four vertices, twice the best {1, 2}.' },
      { q: 'Why not take just one end of each uncovered edge?', options: ['It would be slower', 'Then there is no guarantee: on a star, always picking the leaf gives n − 1 against 1', 'It would not be a cover', 'It always gives the best'], answer: 1, why: 'Taking one end can be arbitrarily bad, and the edges taken no longer give a lower bound on the best.' },
      { q: 'What does a 2-approximation promise?', options: ['The best answer', 'An answer at most twice the best, always, in polynomial time', 'An answer within 2 of the best', 'A fast exact answer on most graphs'], answer: 1, why: 'A ratio guarantee holds on every input, without knowing the best.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cx-tree-dp', family: 'cx-cope', order: 30, title: 'A special case that is easy: trees',
    blurb: 'The largest independent set is NP-hard on graphs, but on a tree two numbers per vertex settle it: the best below with the vertex in, and the best with it out, computed from the leaves up.',
    inputs: [{ id: 'g', kind: 'text', label: 'Tree edges (root 0)', def: '0-1 0-2 1-3 1-4 2-5 2-6', check: (v) => { const e = graphCheck(11, 10)(v); if (e) return e; const G = parseGraph(v, 11); if (G.edges.length !== G.n - 1) return 'Edges: a tree on ' + G.n + ' vertices has ' + (G.n - 1) + ' edges, this has ' + G.edges.length + (G.edges.length >= G.n ? ': there is a cycle, and on graphs with cycles the problem is NP-hard' : ''); const adj = T.cx.adjacency(G); const seen = new Set([0]), st = [0]; while (st.length) { const u = st.pop(); for (const x of adj[u]) if (!seen.has(x)) { seen.add(x); st.push(x); } } return seen.size === G.n ? null : 'Edges: the graph falls into pieces, so it is not one tree'; } }],
    presets: [
      { label: 'A balanced tree of 7', values: { g: '0-1 0-2 1-3 1-4 2-5 2-6' } },
      { label: 'A path of 6', values: { g: '0-1 1-2 2-3 3-4 4-5' } },
      { label: 'A star: the root is left out', values: { g: '0-1 0-2 0-3 0-4' } },
      { label: 'A caterpillar', values: { g: '0-1 1-2 2-3 0-4 1-5 1-6 2-7 3-8' } },
      { label: 'A single vertex', values: { g: '0' } },
    ],
    counters: [{ id: 'done', label: 'vertices solved' }, { id: 'nums', label: 'numbers computed' }, { id: 'subsets', label: 'subsets brute force tries' }],
    run(inp) {
      const G = parseGraph(inp.g, 11);
      const adj = T.cx.adjacency(G);
      const kids = Array.from({ length: G.n }, () => []);
      const order = [], seen = new Set([0]);
      const dfs = (u) => { for (const v of [...adj[u]].sort((a, b) => a - b)) if (!seen.has(v)) { seen.add(v); kids[u].push(v); dfs(v); } order.push(u); };
      dfs(0);
      const IN = [], OUT = [], chosen = new Set(), done = new Set();
      let hot = -1;
      const F = new T.Frames(['done', 'nums', 'subsets']);
      F.set('subsets', Math.pow(2, G.n));
      const mk = (u) => ({ id: 'v' + u, label: done.has(u) ? u + ': ' + IN[u] + ' / ' + OUT[u] : String(u), cls: [chosen.has(u) ? 'good' : done.has(u) ? 'act' : '', u === hot ? 'hot' : ''].filter(Boolean).join(' '), children: kids[u].map(mk) });
      const scene = (extra) => K.tree.draw(mk(0), { gapX: 18, gapY: 80, prefix: 'tr' }).items.concat([{ key: 'legend', kind: 'text', x: 0, y: -44, text: 'a solved vertex shows  v: in / out', anchor: 'middle', size: 14, cls: 'strong' }], extra || []);
      F.add({ items: scene(), say: 'A tree on ' + G.n + ' vertices, hung from vertex 0. Brute force would try all ' + Math.pow(2, G.n) + ' subsets. Instead, give each vertex v two numbers: in(v), the largest independent set below v that uses v, and out(v), the largest that does not.' });
      for (const u of order) {
        hot = u;
        const c = kids[u];
        IN[u] = 1 + c.reduce((s, v) => s + OUT[v], 0);
        OUT[u] = c.reduce((s, v) => s + Math.max(IN[v], OUT[v]), 0);
        const pre = c.length >= 2 && !F.list.some((f) => f.meta && f.meta.out !== undefined);
        if (pre) F.add({ items: scene(), say: 'Vertex ' + u + ' has children ' + c.join(', ') + ', all solved.', meta: { out: String(OUT[u]), outOpts: [OUT[u] - 1, OUT[u], OUT[u] + 1].filter((x) => x >= 0).map(String) } });
        done.add(u);
        F.count('done').count('nums', 2);
        F.add({ items: scene(), say: c.length ? 'Vertex ' + u + ': in = 1 + ' + c.map((v) => 'out(' + v + ')').join(' + ') + ' = ' + IN[u] + ' (with ' + u + ' in, its children must stay out); out = ' + c.map((v) => 'max(in, out)(' + v + ')').join(' + ') + ' = ' + OUT[u] + ' (each child free to choose).' : 'Vertex ' + u + ' is a leaf: in = 1, out = 0.' });
      }
      hot = -1;
      F.add({ items: scene(), say: 'At the root: in(0) = ' + IN[0] + ' and out(0) = ' + OUT[0] + '. The largest independent set has ' + Math.max(IN[0], OUT[0]) + ' vertices. Now walk down to find it.', meta: { root: IN[0] >= OUT[0] ? 'Yes' : 'No' } });
      const pick = (u, parentIn) => {
        const take = !parentIn && IN[u] >= OUT[u];
        if (take) chosen.add(u);
        for (const v of kids[u]) pick(v, take);
      };
      pick(0, false);
      F.add({ items: scene(), say: (IN[0] >= OUT[0] ? 'Take 0, since in(0) ≥ out(0); its children must then stay out.' : 'Leave 0 out, since out(0) > in(0).') + ' Each child of a vertex left out takes whichever of its numbers is larger. The set {' + [...chosen].sort((a, b) => a - b).join(', ') + '} has ' + chosen.size + ' vertices, no two joined.', mark: 'size ' + chosen.size });
      F.add({ items: scene(), say: 'Two numbers per vertex, each from its children: ' + 2 * G.n + ' numbers instead of ' + Math.pow(2, G.n) + ' subsets. A tree splits cleanly at every vertex; a general graph does not, which is why the same problem there is NP-hard. Other easy special cases: 2-SAT (by its implication graph) and vertex cover on bipartite graphs (by matching).' });
      return { frames: F.list, def: { sections: [
        { id: 'rec', kind: 'math', title: 'The recurrence', text: 'in(v) = 1 + Σ out(c)\nout(v) = Σ max(in(c), out(c))\nover the children c of v; a leaf has in 1, out 0\nanswer: max(in(root), out(root))' },
        { id: 'vals', kind: 'table', title: 'Values', colHead: ['vertex', 'in', 'out'], rows: order.map((u) => [String(u), String(IN[u]), String(OUT[u])]) },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.out !== undefined, once: true, pick: 'option', options: (fr, i) => fr[i].meta.outOpts, ask: 'What will out(v) be for this vertex: the best set below it that leaves it out?', answer: (fr, i) => fr[i].meta.out, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.root, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Is the root in the largest independent set found?', answer: (fr, i) => fr[i].meta.root, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why must the children be out when v is in?', options: ['To keep the set small', 'v is joined to each child, and an independent set has no two joined vertices', 'Children are leaves', 'They need not be'], answer: 1, why: 'Every child shares an edge with v.' },
      { q: 'Why is this fast on trees but the problem NP-hard on graphs?', options: ['Trees have fewer vertices', 'Removing a vertex splits a tree into independent pieces that can be solved separately', 'Trees are bipartite', 'Graphs have no leaves'], answer: 1, why: 'The subtrees below a vertex share nothing, so their best answers combine; general graphs have no such clean splits.' },
      { q: 'How many numbers does the method compute for a tree of n vertices?', options: ['n', '2n', 'n²', '2ⁿ'], answer: 1, why: 'Two per vertex, each in time proportional to its number of children.' },
      { q: 'On a star with centre 0 and 4 leaves, what is the answer?', options: ['1, the centre', '4, the leaves', '5', '2'], answer: 1, why: 'in(0) = 1 but out(0) = 4: leaving the centre out frees all four leaves.' },
      { q: 'Which of these is another NP-hard problem that becomes easy in a special case?', options: ['SAT with clauses of two literals', 'Sorting', 'Shortest paths', 'Reachability'], answer: 0, why: 'SAT is NP-complete, but 2-SAT is solved in linear time through its implication graph.' },
    ],
  });
})();
