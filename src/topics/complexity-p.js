// The class P by example: three problems with polynomial-time algorithms, each run with its work counted.
// PATH by breadth-first search, relatively prime by Euclid's remainders, and context-free membership by
// CYK, set beside the exponential ways of doing the same jobs.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CX = K.cx;
  const Geo = T.geom;

  T.family({ id: 'cx-p', part: 'complexity', order: 20, title: 'The class P', blurb: 'Problems a deterministic machine solves in polynomial time: reachability, relative primality, context-free membership. Count the work and watch it stay polynomial.' });

  const keepLabels = (items, P, top, bottom) => {
    const ls = items.filter((it) => it.key.startsWith(P + ':sl:')).sort((a, b) => a.y - b.y);
    for (let i = ls.length - 1; i >= 0; i--) ls[i].y = Math.min(ls[i].y, i === ls.length - 1 ? bottom : ls[i + 1].y - 20);
    for (let i = 0; i < ls.length; i++) ls[i].y = Math.max(ls[i].y, i ? ls[i - 1].y + 20 : top);
    return items;
  };

  // =========================================================================================================
  // 1. PATH by breadth-first search
  // =========================================================================================================
  /** Edges written u>v (one way) or u-v (both ways), separated by spaces, commas or new lines */
  const parseGraph = (text) => {
    const vs = [], arcs = [];
    const add = (v) => { if (!vs.includes(v)) vs.push(v); };
    for (const tok of String(text).split(/[\s,;]+/).filter(Boolean)) {
      const m = /^([A-Za-z0-9]+)([->])([A-Za-z0-9]+)$/.exec(tok);
      if (!m) {
        if (/^[A-Za-z0-9]+$/.test(tok)) { add(tok); continue; }
        throw new Error('Graph: cannot read "' + tok + '"; write edges like a>b (one way) or a-b (both ways)');
      }
      add(m[1]); add(m[3]);
      if (m[1] === m[3]) continue;
      const push = (a, b) => { if (!arcs.some((e) => e[0] === a && e[1] === b)) arcs.push([a, b]); };
      push(m[1], m[3]);
      if (m[2] === '-') push(m[3], m[1]);
    }
    return { vs, arcs };
  };
  const G1 = 's-a s-b a-c b-c c-d d-t b-e e-f';
  const ISLANDS = 's-a a-b b-s c-t t-d d-c';
  const ONEWAY = 's>a a>b t>b b>c c>s';
  const LONG = 's-a a-b b-c c-d d-e e-t s-f f-g';

  T.topic({
    id: 'cx-path', family: 'cx-p', order: 10, title: 'PATH by breadth-first search',
    blurb: 'Is there a path from s to t? Mark s, then repeatedly take a vertex from a queue and mark every unmarked vertex it points to. Each vertex is taken once and each edge looked at once: polynomial time.',
    inputs: [
      { id: 'g', kind: 'text', label: 'Graph (a>b one way, a-b both ways)', def: G1, check: (v) => { const g = parseGraph(v); if (g.vs.length > 10) return 'Graph: at most 10 vertices, so the picture stays readable'; if (g.vs.length < 1) return 'Graph: at least one vertex'; return null; } },
      { id: 's', kind: 'string', label: 'From s', def: 's', max: 3 },
      { id: 't', kind: 'string', label: 'To t', def: 't', max: 3 },
    ],
    check: (inp) => { const g = parseGraph(inp.g); if (!g.vs.includes(inp.s)) return 'From s: ' + (inp.s || 'ε') + ' is not a vertex of the graph'; if (!g.vs.includes(inp.t)) return 'To t: ' + (inp.t || 'ε') + ' is not a vertex of the graph'; return null; },
    presets: [
      { label: 'A path to find', values: { g: G1, s: 's', t: 't' } },
      { label: 't on another island', values: { g: ISLANDS, s: 's', t: 't' } },
      { label: 'One-way streets', values: { g: ONEWAY, s: 's', t: 't' } },
      { label: 's = t', values: { g: G1, s: 'c', t: 'c' } },
      { label: 'A long way round', values: { g: LONG, s: 's', t: 't' } },
    ],
    counters: [{ id: 'marked', label: 'vertices marked' }, { id: 'edges', label: 'edges looked at' }],
    run(inp) {
      const g = parseGraph(inp.g);
      const both = (a, b) => g.arcs.some((e) => e[0] === b && e[1] === a);
      const nodes = g.vs.map((v) => ({ id: v, label: v }));
      const base = K.gadget.draw({ prefix: 'gd', nodes, edges: g.arcs.filter(([a, b]) => !(both(a, b) && a > b)).map(([a, b]) => ({ a, b })), directed: true, r: 28 });
      const pos = base.pos;
      const xs = g.vs.map((v) => pos[v].x), ys = g.vs.map((v) => pos[v].y);
      const minX = Math.min(...xs) - 40, maxX = Math.max(...xs) + 40, botY = Math.max(...ys) + 80;
      const st = { mark: new Set([inp.s]), dist: { [inp.s]: 0 }, parent: {}, queue: [inp.s], done: new Set() };
      const scene = (o) => {
        o = o || {};
        const items = [];
        for (const it of base.items) {
          const c = Object.assign({}, it);
          if (c.kind === 'state') {
            const v = c.key.slice(5);
            const cls = [c.cls, o.cur === v ? 'active' : st.done.has(v) ? 'good' : st.mark.has(v) ? 'hot' : '', o.path && o.path.includes(v) ? 'cert' : ''];
            c.cls = cls.filter(Boolean).join(' ');
            // the distance sits inside the vertex, under its name: a label below it would collide with edges
            if (st.dist[v] !== undefined) { c.lines = [v, 'd=' + st.dist[v]]; c.size = 15; delete c.text; }
            c.accept = v === inp.t;
          }
          if (c.kind === 'edge') {
            const [a, b] = c.key.slice(5).split('>');
            if (both(a, b)) { c.head = false; c.gapB = 0; }
            const on = (x, y) => (o.edge && ((o.edge[0] === x && o.edge[1] === y) || (both(x, y) && o.edge[0] === y && o.edge[1] === x)));
            const tree = (x, y) => st.parent[y] === x || (both(x, y) && st.parent[x] === y);
            const inPath = o.path && o.path.some((v, k) => k && ((o.path[k - 1] === a && v === b) || (o.path[k - 1] === b && v === a)));
            c.cls = [c.cls, on(a, b) ? 'hot thick' : inPath ? 'cert thick' : tree(a, b) ? 'alt' : ''].filter(Boolean).join(' ');
          }
          items.push(c);
        }
        // the queue, front on the left
        items.push({ key: 'ql', kind: 'text', x: minX, y: botY + 6, text: 'queue (front first)', cls: 'title' });
        st.queue.forEach((v, k) => items.push({ key: 'q:' + v, kind: 'cell', x: minX + k * 50, y: botY + 18, w: 44, h: 40, text: v, cls: 'mono' + (k === 0 ? ' act' : ''), enter: 'fly', from: { x: minX + (st.queue.length + 2) * 50, y: botY + 18 }, exit: 'rise' }));
        if (!st.queue.length) items.push({ key: 'q:empty', kind: 'text', x: minX + 4, y: botY + 44, text: 'empty', cls: 'strong' });
        void maxX;
        return items;
      };
      const F = new T.Frames(['marked', 'edges']);
      F.set('marked', 1);
      const L = { mark: '0', loop: '1', take: '2', each: '3', test: '4', end: '5' };
      F.add({ items: scene(), say: 'Is there a path from ' + inp.s + ' to ' + inp.t + '? Mark ' + inp.s + ' (distance 0) and put it in the queue.', hl: { alg: [L.mark] } });
      let found = st.mark.has(inp.t);
      if (found) F.add({ items: scene({ path: [inp.s] }), say: 's and t are the same vertex, ' + inp.s + ': the path of length 0 is a path. Accept without looking at a single edge.', hl: { alg: [L.end] }, mark: 'accept', meta: { found: true } });
      while (!found && st.queue.length) {
        const u = st.queue[0];
        F.add({ items: scene({ cur: u }), say: 'Take ' + u + ' from the front of the queue (distance ' + st.dist[u] + ') and look at its edges.', hl: { alg: [L.take] }, meta: { take: u } });
        st.queue.shift();
        const out = g.arcs.filter((e) => e[0] === u).map((e) => e[1]);
        if (!out.length) F.add({ items: scene({ cur: u }), say: u + ' has no edges going out: nothing to do.', hl: { alg: [L.each] } });
        for (const v of out) {
          F.count('edges');
          if (st.mark.has(v)) { F.add({ items: scene({ cur: u, edge: [u, v] }), say: 'Edge ' + u + ' → ' + v + ': ' + v + ' is already marked, so skip it. Each edge costs one look, never more.', hl: { alg: [L.test] } }); continue; }
          st.mark.add(v); st.dist[v] = st.dist[u] + 1; st.parent[v] = u; st.queue.push(v);
          F.count('marked');
          F.add({ items: scene({ cur: u, edge: [u, v] }), say: 'Edge ' + u + ' → ' + v + ': ' + v + ' is new. Mark it at distance ' + st.dist[v] + ' and put it at the back of the queue.' + (v === inp.t ? ' That is t!' : ''), hl: { alg: [L.test] } });
          if (v === inp.t) { found = true; break; }
        }
        st.done.add(u);
      }
      if (found && inp.s !== inp.t) {
        const path = [inp.t];
        while (path[0] !== inp.s) path.unshift(st.parent[path[0]]);
        F.add({ items: scene({ path }), say: 't is marked: accept. Following the parents back gives the path ' + path.join(' → ') + ', of length ' + (path.length - 1) + ', a shortest one. At most ' + g.vs.length + ' vertices taken and ' + g.arcs.length + ' edges looked at: O(|V| + |E|) steps.', hl: { alg: [L.end] }, mark: 'accept', meta: { found: true } });
      } else if (!found) {
        const oneWay = g.arcs.some((e) => e[0] === inp.t) && !g.arcs.some((e) => e[1] === inp.t && st.mark.has(e[0]));
        F.add({ items: scene(), say: 'The queue is empty and t was never marked: reject. ' + (oneWay ? 'Edges leave ' + inp.t + ', but none of the marked vertices has an edge into it: a one-way street counts only in its own direction.' : 'Every vertex reachable from ' + inp.s + ' is marked, and ' + inp.t + ' is not among them: it lies on another island.') + ' The search still stopped after ' + st.mark.size + ' vertices: no path, proved in polynomial time.', hl: { alg: [L.end] }, mark: 'reject', meta: { found: false } });
      }
      return { frames: F.list, def: { sections: [
        { id: 'alg', kind: 'math', title: 'Breadth-first search', text: 'mark s; queue ← [s]\nwhile the queue is not empty:\n  u ← take the front of the queue\n  for each edge u → v:\n    if v is unmarked: mark v, add v to the queue\naccept if t is marked, else reject' },
        { id: 'key', kind: 'text', title: 'In the picture', text: 's is where the search starts; t has the double ring. Amber: marked and waiting in the queue; green: finished; purple: the vertex being expanded. Purple edges are how each vertex was first reached; green, the path found.' },
        { id: 'cost', kind: 'text', title: 'Why polynomial', text: 'Each vertex enters the queue at most once and each edge is looked at at most once: O(|V| + |E|) steps, at most quadratic in the size of the graph. Trying every possible path instead could take exponentially many.' },
        { id: 'g', kind: 'math', title: 'The graph', text: 'V = {' + g.vs.join(', ') + '}\n' + g.vs.map((v) => v + ' → ' + (g.arcs.filter((e) => e[0] === v).map((e) => e[1]).join(', ') || '(none)')).join('\n') },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.take === undefined && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.take !== undefined && i > 2, pick: 'item', once: true,
        ask: 'Which vertex will be taken from the queue next? Click it in the graph.', answer: (fr, i) => 'gd:v:' + fr[i + 1].meta.take, explain: 'The queue is first in, first out: the vertex at its front, marked earliest, goes next.' },
      { at: (f, i, fr) => i === 0, pick: 'option', options: ['Yes', 'No'], once: true, ask: 'Look at the graph. Is there a path from s to t?', answer: (fr) => (fr[fr.length - 1].meta && fr[fr.length - 1].meta.found ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'How many times can breadth-first search put a vertex in the queue?', options: ['Once at most', 'Once per edge into it', 'As many times as it is reached', 'Twice'], answer: 0, why: 'A vertex is marked when it is first put in, and marked vertices are never added again.' },
      { q: 'Why is PATH in P although a graph can have exponentially many paths?', options: ['Search never lists paths: it only marks vertices, each once', 'Because graphs are small', 'Because there are only n paths', 'It is not in P'], answer: 0, why: 'The marks remember where we have been, so the work is bounded by the vertices and edges, not by the paths.' },
      { q: 'When the queue empties without t being marked, what has the search shown?', options: ['That t is not reachable from s', 'Nothing, it must try again', 'That the graph has a cycle', 'That s is not reachable from t'], answer: 0, why: 'Every vertex reachable from s gets marked; if t is not, no path exists.' },
      { q: 'With edges written a>b one way, can s reach t if the only edge at t is t>b?', options: ['Yes, edges work both ways', 'No, nothing leads into t', 'Only if b is marked', 'Only when s = t'], answer: 1, why: 'A path must follow edges in their direction; t has no incoming edge.' },
      { q: 'What distances does breadth-first search find?', options: ['Shortest numbers of edges from s', 'Longest paths', 'Random ones', 'Distances to t only'], answer: 0, why: 'Vertices are taken in order of distance, so each is first marked along a shortest path.' },
    ],
  });

  // =========================================================================================================
  // 2. Relatively prime by Euclid
  // =========================================================================================================
  const euclidSteps = (a, b) => { const st = []; while (b) { st.push({ a, b, q: Math.floor(a / b), r: a % b }); [a, b] = [b, a % b]; } return { steps: st, g: a }; };
  T.topic({
    id: 'cx-gcd', family: 'cx-p', order: 20, title: 'Relatively prime by Euclid',
    blurb: 'Are a and b relatively prime? Trying every possible common divisor takes time exponential in the number of digits. Euclid replaces the pair (a, b) by (b, a mod b) and is done after a few steps per digit.',
    inputs: [
      { id: 'a', kind: 'number', label: 'a', def: 391, min: 0, max: 999999999 },
      { id: 'b', kind: 'number', label: 'b', def: 299, min: 0, max: 999999999 },
    ],
    check: (inp) => (inp.a === 0 && inp.b === 0 ? 'a and b: at least one of them must not be 0 (every number divides 0)' : null),
    presets: [
      { label: '391 and 299', values: { a: 391, b: 299 } },
      { label: 'Neighbours: 1000 and 999', values: { a: 1000, b: 999 } },
      { label: 'Worst case: 144 and 89', values: { a: 144, b: 89 } },
      { label: 'One is 0: 35 and 0', values: { a: 35, b: 0 } },
      { label: 'Smaller first: 48 and 180', values: { a: 48, b: 180 } },
      { label: 'Big: 912 345 678 and 87 654 321', values: { a: 912345678, b: 87654321 } },
    ],
    counters: [{ id: 'steps', label: 'Euclid steps' }, { id: 'digits', label: 'digits' }, { id: 'trial', label: 'divisors to try instead' }],
    run(inp) {
      const E = euclidSteps(inp.a, inp.b);
      const digits = String(Math.max(inp.a, inp.b)).length;
      const trial = Math.max(0, Math.min(inp.a || Infinity, inp.b || Infinity) - 1);
      const F = new T.Frames(['steps', 'digits', 'trial']);
      F.set('digits', digits).set('trial', trial === Infinity ? 0 : trial);
      const W = 520, X0 = 60;
      const hist = [];
      const table = () => {
        if (!hist.length) return [];
        const tb = K.table.draw({ prefix: 'ht', x: X0, y: 230, rows: hist.slice(-5).map((s) => [CX.num(s.a), '= ' + s.q + ' ×', CX.num(s.b), '+', CX.num(s.r)]), colHead: ['a', '', 'b', '', 'a mod b'], mono: true, size: 14, ch: 34, hot: [[Math.min(hist.length, 5) - 1, 4]] });
        return tb.items;
      };
      const bar = (key, v, x, y, w, cls, label) => {
        const t = label !== undefined ? label : CX.num(v);
        const fits = Geo.textWidth(t, 15, { bold: true }) + 12 <= w;
        const items = [{ key, kind: 'cell', x, y, w: Math.max(3, w), h: 40, text: fits ? t : '', rx: 4, cls: cls || '', pick: true }];
        if (!fits) items.push({ key: key + ':t', kind: 'text', x: x + Math.max(3, w) + 6, y: y + 25, text: t, cls: 'strong', size: 14 });
        return items;
      };
      // a step: a on top, b below it with its q copies laid under a, and the remainder r left over
      const scene = (s, phase) => {
        const sc = W / Math.max(s.a, s.b || 0, 1);
        const items = [{ key: 'la', kind: 'text', x: X0 - 12, y: 45, text: 'a', anchor: 'end', cls: 'title' }, { key: 'lb', kind: 'text', x: X0 - 12, y: 115, text: 'b', anchor: 'end', cls: 'title' }];
        items.push(...bar('v:' + s.a, s.a, X0, 20, s.a * sc, 'mono'));
        if (!s.b) { items.push({ key: 'zero', kind: 'cell', x: X0, y: 90, w: 52, h: 40, text: '0', cls: 'mono empty', rx: 4 }); return items.concat(table()); }
        if (phase === 0 || s.q === 0) { items.push(...bar('v:' + s.b + (s.a === s.b ? 'b' : ''), s.b, X0, 90, s.b * sc, 'mono act')); if (phase && !s.q) items.push({ key: 'swap', kind: 'text', x: X0, y: 160, text: 'b does not fit into a even once: q = 0, r = a', cls: 'hot' }); return items.concat(table()); }
        // the copies of b under a, at most 6 drawn
        const shown = Math.min(s.q, 6);
        for (let j = 0; j < shown; j++) {
          const x = X0 + j * s.b * sc;
          if (j === 0) items.push(...bar('v:' + s.b + (s.a === s.b ? 'b' : ''), s.b, x, 90, s.b * sc, 'mono act', s.b * sc > 70 ? CX.num(s.b) : ''));
          else items.push({ key: 'cp:' + j, kind: 'cell', x, y: 90, w: Math.max(2, s.b * sc), h: 40, text: s.b * sc > 70 ? CX.num(s.b) : '', rx: 4, cls: 'mono read', enter: 'fly', from: { x: X0, y: 90 } });
        }
        if (s.q > shown) items.push({ key: 'cp:more', kind: 'text', x: X0 + shown * s.b * sc + (s.q * s.b * sc - shown * s.b * sc) / 2, y: 115, text: '… ' + s.q + ' copies', anchor: 'middle', cls: 'strong', size: 13 });
        items.push({ key: 'qb', kind: 'bracket', x1: X0, x2: X0 + s.q * s.b * sc, y: 136, side: 'below', text: s.q + ' × ' + CX.num(s.b) });
        if (s.r) items.push(...bar('v:' + s.r, s.r, X0 + s.q * s.b * sc, 90, s.r * sc, 'mono hot'));
        else items.push({ key: 'r0', kind: 'text', x: X0 + W + 8, y: 115, text: 'r = 0', cls: 'good' });
        return items.concat(table());
      };
      F.add({ items: scene({ a: inp.a, b: inp.b, q: 0, r: 0 }, 0), say: 'Are ' + inp.a + ' and ' + inp.b + ' relatively prime, that is, is their greatest common divisor 1? Trying every candidate divisor would mean up to ' + CX.num(trial) + ' tries. Euclid instead keeps replacing (a, b) by (b, a mod b).' });
      if (!E.steps.length) {
        F.add({ items: scene({ a: inp.a, b: 0 }, 0), say: 'b is 0, and every number divides 0, so gcd(' + inp.a + ', 0) = ' + inp.a + ' with no division at all. ' + (inp.a === 1 ? 'That is 1: relatively prime.' : inp.a + ' ≠ 1: not relatively prime (unless a is 1).'), mark: 'gcd ' + inp.a, meta: { g: inp.a } });
      }
      E.steps.forEach((s, k) => {
        F.count('steps');
        F.add({ items: scene(s, 0), say: 'Step ' + (k + 1) + ': the pair is (' + CX.num(s.a) + ', ' + CX.num(s.b) + '). How many times does ' + CX.num(s.b) + ' fit into ' + CX.num(s.a) + '?', meta: { pre: s } });
        hist.push(s);
        F.add({ items: scene(s, 1), say: CX.num(s.a) + ' = ' + s.q + ' × ' + CX.num(s.b) + ' + ' + CX.num(s.r) + '. ' + (s.q === 0 ? 'b is bigger, so q = 0: this first step just swaps the two.' : s.r ? 'The remainder ' + CX.num(s.r) + ' is all that matters: any common divisor of a and b also divides it.' : 'No remainder: ' + CX.num(s.b) + ' divides ' + CX.num(s.a) + ' exactly.') + (k > 0 && s.r && s.r <= hist[k - 1].r / 2 ? ' Every two steps the numbers at least halve.' : ''), meta: { step: s } });
      });
      if (E.steps.length) {
        const g = E.g;
        F.add({ items: scene({ a: g, b: 0 }, 0), mark: 'gcd ' + g, meta: { g }, say: 'The remainder reached 0, so gcd(' + inp.a + ', ' + inp.b + ') = ' + CX.num(g) + ' after ' + E.steps.length + ' step' + (E.steps.length === 1 ? '' : 's') + '. ' + (g === 1 ? 'They are relatively prime.' : 'Not relatively prime: ' + CX.num(g) + ' divides both.') + ' Trying divisors one by one would have taken up to ' + CX.num(trial) + ' tries.' });
      }
      // the chart: steps against digits, Euclid's worst case against trying every divisor
      const fib = [1, 1]; while (fib.length < 50) fib.push(fib[fib.length - 1] + fib[fib.length - 2]);
      const worst = (d) => { let i = 1; while (fib[i + 1] < Math.pow(10, d)) i++; return euclidSteps(fib[i + 1], fib[i]).steps.length; };
      const ds = [1, 2, 3, 4, 5, 6, 7, 8, 9];
      const plot = CX.plot({ prefix: 'pl', x: X0, y: 30, w: 420, h: 250, xs: [0, 9], ys: [1, 1e9], logY: true, yTicks: [1, 1e3, 1e6, 1e9], xTicks: [0, 3, 6, 9], xLabel: 'digits in the numbers', yLabel: 'steps (log scale)',
        series: [{ id: 'trial', label: 'every divisor', cls: 's4', pts: ds.map((d) => [d, Math.pow(10, d)]) }, { id: 'eu', label: 'Euclid, worst', cls: 's1', pts: ds.map((d) => [d, worst(d)]) }, { id: 'me', label: 'yours: ' + E.steps.length, cls: 's3', hot: true, pts: [[digits, Math.max(1, E.steps.length)]] }] });
      F.add({ items: keepLabels(plot.items, 'pl', 26, 290), mark: 'O(digits)', say: 'Euclid\'s worst cases are neighbouring Fibonacci numbers (like 144 and 89): even then, about 5 steps per decimal digit, ' + worst(9) + ' steps for 9 digits. Trying every divisor grows like 10ᵈ. Each Euclid step is one division, polynomial in the digits, so relative primality is in P.' });
      return { frames: F.list, def: { sections: [
        { id: 'alg', kind: 'math', title: 'Euclid', text: 'while b ≠ 0:\n  (a, b) ← (b, a mod b)\nanswer a = gcd\nrelatively prime ⇔ gcd = 1' },
        { id: 'why', kind: 'text', title: 'Why it is fast', text: 'After two steps the larger number has at least halved: if b ≤ a/2 then a mod b < b ≤ a/2, otherwise a mod b = a − b < a/2. So the number of steps is at most about 2·log₂ a, linear in the length of the input.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.pre && f.meta.pre.q > 0 && fr[i + 1], pick: 'option', once: true,
        options: (fr, i) => { const s = fr[i].meta.pre; return [...new Set([s.r, (s.r + s.b - 1) % s.b, s.b - s.r, (s.r + 1) % s.b])].slice(0, 3).sort((x, y) => x - y).map(String); },
        ask: (fr, i) => 'What is the remainder ' + fr[i].meta.pre.a + ' mod ' + fr[i].meta.pre.b + '?', answer: (fr, i) => String(fr[i].meta.pre.r), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => f.meta && f.meta.step && f.meta.step.r && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.pre, pick: 'item', once: true,
        ask: 'Click the bar that will be the next a.', answer: (fr, i) => 'v:' + fr[i].meta.step.b, explain: 'The new pair is (b, a mod b): the old b moves up to be the new a, and the remainder becomes the new b.' },
    ],
    quiz: [
      { q: 'Why is "try every d from 2 to min(a, b)" not polynomial time?', options: ['min(a, b) is exponential in the number of digits', 'Division is slow', 'It misses some divisors', 'It is polynomial'], answer: 0, why: 'A d-digit number is about 10ᵈ: the number of tries grows exponentially with the length of the input.' },
      { q: 'gcd(a, 0) is', options: ['0', '1', 'a', 'undefined'], answer: 2, why: 'Every number divides 0, so the greatest common divisor of a and 0 is a itself.' },
      { q: 'Which pairs make Euclid take the most steps for their size?', options: ['Neighbouring Fibonacci numbers', 'Equal numbers', 'Powers of two', 'Primes'], answer: 0, why: 'Their quotients are all 1, so the numbers shrink as slowly as possible.' },
      { q: 'After two Euclid steps, the larger number has', options: ['At least halved', 'Dropped by one', 'Stayed the same', 'Doubled'], answer: 0, why: 'This halving every two steps is why the number of steps is linear in the number of digits.' },
      { q: 'Euclid on 48 and 180 starts with 48 = 0 × 180 + 48. What happened?', options: ['The pair swapped, at the cost of one step', 'An error', 'gcd is 0', 'The algorithm stopped'], answer: 0, why: 'With a < b the quotient is 0 and the step simply exchanges them.' },
    ],
  });

  // =========================================================================================================
  // 3. CYK's work counted
  // =========================================================================================================
  const DYCK = 'S → A B | A C | S S\nC → S B\nA → a\nB → b';
  const AMB = 'S → S S | a';
  const cnfErr = (g) => {
    for (const r of g.rules) {
      const ok = (r.rhs.length === 1 && g.terminals.includes(r.rhs[0])) || (r.rhs.length === 2 && r.rhs.every((s) => g.nonterminals.includes(s)));
      if (!ok) return 'Grammar: this needs Chomsky normal form, A → B C or A → a, but ' + r.lhs + ' → ' + (r.rhs.join(' ') || 'ε') + ' is neither';
    }
    return null;
  };
  const setText = (xs) => (xs.length ? '{' + xs.join(',') + '}' : '∅');
  const catalan = (n) => { let c = 1; for (let k = 0; k < n; k++) c = (c * 2 * (2 * k + 1)) / (k + 2); return c; };
  T.topic({
    id: 'cx-cyk-work', family: 'cx-p', order: 30, title: 'Why CYK is polynomial',
    blurb: 'A string of length n can have exponentially many parse trees, yet CYK decides membership by filling n(n + 1)/2 cells, trying at most n − 1 splits in each: about n³ steps. Count them row by row.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar (Chomsky normal form)', def: DYCK, check: (v) => cnfErr(T.GrammarText.parse(v)) },
      { id: 'w', kind: 'string', label: 'String', def: 'aabbab', min: 1, max: 8 },
    ],
    check: (inp) => { const g = T.GrammarText.parse(inp.g); const bad = [...inp.w].find((c) => !g.terminals.includes(c)); return bad !== undefined ? 'String: "' + bad + '" is not a terminal of the grammar' : null; },
    presets: [
      { label: 'Nested pairs: aabbab', values: { g: DYCK, w: 'aabbab' } },
      { label: 'Rejected: abba', values: { g: DYCK, w: 'abba' } },
      { label: 'One symbol: no splits at all', values: { g: DYCK, w: 'a' } },
      { label: 'Very ambiguous: aaaaaaa', values: { g: AMB, w: 'aaaaaaa' } },
    ],
    counters: [{ id: 'cells', label: 'cells filled' }, { id: 'splits', label: 'splits tried' }, { id: 'checks', label: 'rule checks' }],
    run(inp) {
      const g = T.GrammarText.parse(inp.g);
      const w = [...inp.w], n = w.length;
      const bin = g.rules.filter((r) => r.rhs.length === 2);
      const table = Array.from({ length: n }, () => Array(n).fill(null));
      const trees = Array.from({ length: n }, () => Array.from({ length: n }, () => ({})));
      const F = new T.Frames(['cells', 'splits', 'checks']);
      const CW = n > 6 ? 84 : 96;
      const scene = (row, opts) => {
        opts = opts || {};
        const rows = table.map((r, l) => r.map((c, i) => (i + l < n ? (c === null ? { lines: ['', l + ' split' + (l === 1 ? '' : 's')] } : { lines: [setText(c), l + ' split' + (l === 1 ? '' : 's')] }) : null)));
        const tb = K.table.draw({ prefix: 'cy', rows, skip: (l, i) => i + l >= n, rowHead: table.map((_, l) => 'len ' + (l + 1)), cw: CW, mono: true, size: 13, x: 0, y: 64,
          hot: opts.hot || [], cls: (l, i) => (l === row ? 'act' : table[l][i] && l === n - 1 && table[l][i].includes(g.start) ? 'good' : l === n - 1 && table[l][i] && !table[l][i].includes(g.start) ? 'bad' : '') });
        const c0 = tb.cellBox(0, 0);
        const s = K.string.draw({ prefix: 'w', text: w, x: c0.x, y: 0, cw: CW, ch: 44, head: false, cls: (i) => (opts.span && i >= opts.span[0] && i < opts.span[1] ? 'hot' : '') });
        return tb.items.concat(s.items);
      };
      F.add({ items: scene(-1), say: 'The string ' + w.join('') + ' has n = ' + n + ' symbols, so the triangle has ' + n + ' + ' + (n - 1 > 0 ? (n - 1) + ' + … + 1 = ' : '') + (n * (n + 1)) / 2 + ' cells. Each cell is labelled with how many ways its substring can be split in two: a substring of length L has L − 1 splits.', meta: { start: true } });
      let total = 0;
      for (let l = 0; l < n; l++) {
        let rowSplits = 0, rowChecks = 0;
        for (let i = 0; i + l < n; i++) {
          if (l === 0) {
            table[0][i] = [...new Set(g.rules.filter((r) => r.rhs.length === 1 && r.rhs[0] === w[i]).map((r) => r.lhs))];
            for (const A of table[0][i]) trees[0][i][A] = 1;
            rowChecks += g.rules.length;
            continue;
          }
          const got = new Set();
          for (let k = 0; k < l; k++) {
            rowSplits++;
            const A = table[k][i], B = table[l - k - 1][i + k + 1];
            for (const r of bin) {
              rowChecks++;
              if (A.includes(r.rhs[0]) && B.includes(r.rhs[1])) { got.add(r.lhs); trees[l][i][r.lhs] = (trees[l][i][r.lhs] || 0) + trees[k][i][r.rhs[0]] * trees[l - k - 1][i + k + 1][r.rhs[1]]; }
            }
          }
          table[l][i] = [...got];
        }
        total += rowChecks;
        F.count('cells', n - l).count('splits', rowSplits).count('checks', rowChecks);
        F.add({ items: scene(l), meta: { row: l + 1, rowSplits }, say: l === 0
          ? 'Row len 1: ' + n + ' cells, no splits: each symbol is matched against the ' + g.rules.length + ' rules directly, ' + rowChecks + ' rule checks.' + (n === 1 ? ' With one symbol that is all CYK ever does.' : '')
          : 'Row len ' + (l + 1) + ': ' + (n - l) + ' cell' + (n - l === 1 ? '' : 's') + ' × ' + l + ' split' + (l === 1 ? '' : 's') + ' = ' + rowSplits + ' splits, each tried against the ' + bin.length + ' rules A → B C: ' + rowChecks + ' rule checks.' });
      }
      const yes = table[n - 1][0].includes(g.start);
      const nTrees = trees[n - 1][0][g.start] || 0;
      const sumSplits = ((n - 1) * n * (n + 1)) / 6;
      F.add({ items: scene(-1, { hot: [[n - 1, 0]] }), mark: yes ? 'accepted' : 'rejected', meta: { yes }, say: (yes ? g.start + ' is in the top cell: ' + w.join('') + ' is in the language' : g.start + ' is not in the top cell: ' + w.join('') + ' is not in the language') + '. In all ' + sumSplits + ' splits = (n − 1)n(n + 1)/6 and ' + total + ' rule checks.' + (yes ? ' The string has ' + nTrees + ' parse tree' + (nTrees === 1 ? '' : 's') + ', but CYK never builds them one by one.' : '') });
      // the chart: CYK's splits against the number of binary trees a string of length n could have
      const ns = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
      const plot = CX.plot({ prefix: 'pl', x: 60, y: 30, w: 420, h: 240, xs: [0, 16], ys: [1, 1e8], logY: true, yTicks: [1, 100, 1e4, 1e6, 1e8], xTicks: [0, 4, 8, 12, 16], xLabel: 'string length n', yLabel: 'work (log scale)',
        series: [{ id: 'tr', label: 'possible parse trees', cls: 's4', pts: ns.map((m) => [m, Math.max(1, catalan(m - 1))]) }, { id: 'cy', label: 'CYK splits', cls: 's1', pts: ns.map((m) => [m, Math.max(1, ((m - 1) * m * (m + 1)) / 6)]) }, { id: 'me', label: 'this string', cls: 's3', hot: true, pts: [[n, Math.max(1, sumSplits)]] }] });
      F.add({ items: keepLabels(plot.items, 'pl', 26, 280), mark: 'O(n³)', say: 'A string of length n can be split into a binary tree in C(n − 1) ways (the Catalan numbers: 1, 1, 2, 5, 14, 42, …), which grows like 4ⁿ. Trying trees one by one is exponential; CYK shares the work of every substring among all trees that use it, and its splits grow like n³/6. For a fixed grammar, membership is in P.' });
      return { frames: F.list, def: { sections: [
        { id: 'g', kind: 'grammar', title: 'Grammar', rules: g.rules.map((r) => r.lhs + ' → ' + r.rhs.join(' ')), nonterminals: g.nonterminals },
        { id: 'count', kind: 'math', title: 'Counting the work', text: 'cells: n(n+1)/2 = ' + (n * (n + 1)) / 2 + '\nsplits: Σ (n−L+1)(L−1) = (n−1)n(n+1)/6 = ' + sumSplits + '\nrule checks: splits × ' + bin.length + ' binary rules (+ row 1)\ntotal: O(n³ · |G|)' },
      ] } };
    },
    predict: [
      { at: (f, i) => f.meta && f.meta.start, pick: 'item', once: true, ask: 'Which cell will need the most splits? Click it.', answer: (fr, i, inp) => 'cy:' + ([...inp.w].length - 1) + ',0', explain: 'The top cell holds the whole string, of length n, so it has the most splits: n − 1.' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.row === 3, pick: 'option', once: true,
        options: (fr, i) => { const s = fr[i + 1].meta.rowSplits; return [...new Set([s, s + 2, Math.max(1, s - 2), 2 * s])].sort((a, b) => a - b).map(String); },
        ask: 'Row len 3 next. How many splits will its cells need in total?', answer: (fr, i) => String(fr[i + 1].meta.rowSplits), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'How many splits does the cell for a substring of length L have?', options: ['L − 1', 'L', '2ᴸ', 'L²'], answer: 0, why: 'The cut can go after any of the first L − 1 symbols.' },
      { q: 'Why is CYK polynomial although there may be exponentially many parse trees?', options: ['Each substring\'s cell is computed once and shared by every tree that uses it', 'It only finds one tree', 'Grammars in CNF are unambiguous', 'It guesses the tree'], answer: 0, why: 'This is dynamic programming: the work is per substring and split, not per tree.' },
      { q: 'For a fixed grammar, CYK runs in', options: ['O(n)', 'O(n³)', 'O(2ⁿ)', 'O(n!)'], answer: 1, why: 'About n³/6 splits, each a constant amount of work for a fixed grammar.' },
      { q: 'With S → S S | a, how many parse trees does aaaa have?', options: ['1', '4', '5', '16'], answer: 2, why: 'The binary trees with 4 leaves: the Catalan number C(3) = 5. CYK checks it with just 10 splits.' },
      { q: 'The string has one symbol. How many splits does CYK try?', options: ['0', '1', 'n', 'It cannot run'], answer: 0, why: 'Only row len 1 exists, matched against the rules A → a directly.' },
    ],
  });
})();
