// Graphs with roles, for reductions: vertices that belong to variable gadgets and clause gadgets, grouped
// in shaded regions, the edges a reduction adds between them, and a certificate (a clique, a cover, a path,
// a colouring) lit on top. Positions come from the gadgets (each group a small circle or a row, groups in
// rows) or from the state-diagram kit's stress layout when there are no groups.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const GD = (K.gadget = {});

  /**
   * opts: {nodes: [{id, label, role: 'var'|'clause'|'plain', group, cls, x, y, colour}], edges: [{a, b, cls,
   *   label}], groups: [{id, label, row, shape: 'ring'|'row'|'col'}], cert: [node ids], certEdges: [[a, b]],
   *   directed, prefix, r}
   * Returns {items, pos}.
   */
  GD.draw = function (opts) {
    const P = opts.prefix || 'gd';
    const nodes = opts.nodes || [], edges = opts.edges || [];
    const r = opts.r || 22;
    const pos = {};
    for (const n of nodes) if (n.x !== undefined) pos[n.id] = { x: n.x, y: n.y };
    const groups = opts.groups || [];
    if (groups.length && nodes.some((n) => !pos[n.id])) {
      // each group as a little shape, groups left to right in their rows
      const rows = new Map();
      for (const g of groups) { const k = g.row || 0; if (!rows.has(k)) rows.set(k, []); rows.get(k).push(g); }
      let y = 0;
      for (const k of [...rows.keys()].sort((a, b) => a - b)) {
        let x = 0, rowH = 0;
        for (const g of rows.get(k)) {
          const mem = nodes.filter((n) => n.group === g.id);
          const shape = g.shape || (mem.length <= 2 ? 'row' : 'ring');
          let w, h;
          if (shape === 'ring') {
            const R = Math.max(42, mem.length * 17);
            mem.forEach((n, i) => { const a = -Math.PI / 2 + 2 * Math.PI * i / mem.length; pos[n.id] = { x: x + R + r + 14 + Math.cos(a) * R, y: y + 40 + R + r + Math.sin(a) * R }; });
            w = 2 * (R + r + 14); h = 2 * (R + r) + 54;
          } else if (shape === 'col') {
            mem.forEach((n, i) => { pos[n.id] = { x: x + r + 18, y: y + 44 + r + i * (2 * r + 30) }; });
            w = 2 * r + 36; h = 44 + mem.length * (2 * r + 30);
          } else {
            mem.forEach((n, i) => { pos[n.id] = { x: x + r + 18 + i * (2 * r + 34), y: y + 44 + r }; });
            w = mem.length * (2 * r + 34) + 2; h = 2 * r + 60;
          }
          g._box = { x, y, w, h };
          x += w + 46;
          rowH = Math.max(rowH, h);
        }
        // centre each row under the widest
        y += rowH + 90;
      }
      const widest = Math.max(...groups.map((g) => g._box.x + g._box.w));
      for (const k of rows.keys()) {
        const gs = rows.get(k), rw = Math.max(...gs.map((g) => g._box.x + g._box.w));
        const dx = (widest - rw) / 2;
        for (const g of gs) { g._box.x += dx; for (const n of nodes) if (n.group === g.id) pos[n.id].x += dx; }
      }
    }
    if (nodes.some((n) => !pos[n.id])) {
      const m = { states: nodes.map((n) => n.id), start: nodes[0] && nodes[0].id, accept: [], trans: edges.map((e) => ({ from: e.a, to: e.b, label: '' })), kind: 'nfa' };
      const lay = K.graph.layout(m, { mode: 'stress', gapX: 120, fixed: pos }).pos;
      for (const n of nodes) if (!pos[n.id]) pos[n.id] = lay[n.id];
    }
    const items = [];
    const cert = new Set(opts.cert || []);
    const certE = new Set((opts.certEdges || []).map(([a, b]) => (a < b ? a + '|' + b : b + '|' + a)));
    const obstacles = [];
    for (const g of groups) {
      const mem = nodes.filter((n) => n.group === g.id);
      if (!mem.length) continue;
      const xs = mem.map((n) => pos[n.id].x), ys = mem.map((n) => pos[n.id].y);
      const b = { x: Math.min(...xs) - r - 14, y: Math.min(...ys) - r - 34, w: Math.max(...xs) - Math.min(...xs) + 2 * r + 28, h: Math.max(...ys) - Math.min(...ys) + 2 * r + 48 };
      obstacles.push({ x: b.x + 6, y: b.y + 4, w: Geo.textWidth(g.label || g.id, 13, { bold: true }) + 12, h: 22 });
      items.push({ key: P + ':g:' + g.id, kind: 'region', x: b.x, y: b.y, w: b.w, h: b.h, text: g.label || g.id, cls: g.cls || (mem[0].role === 'clause' ? 'r3' : 'r0'), rx: 16 });
    }
    // edges: bent round any vertex they would run through
    const m = { states: nodes.map((n) => n.id), accept: [], trans: edges.map((e) => ({ from: e.a, to: e.b, label: e.label || ' ' })), kind: 'pda' };
    const sizes = {};
    for (const n of nodes) sizes[n.id] = { w: 2 * r, h: 2 * r, rx: r };
    const routes = K.graph.route(m, pos, sizes, { obstacles });
    for (const e of edges) {
      const rt = routes.find((x) => x.from === e.a && x.to === e.b);
      const k = e.a < e.b ? e.a + '|' + e.b : e.b + '|' + e.a;
      const it = { key: P + ':e:' + e.a + '>' + e.b, kind: 'edge', from: P + ':v:' + e.a, to: P + ':v:' + e.b, bend: rt ? rt.bend || 0 : 0, head: !!opts.directed, gapB: opts.directed ? 1.5 : 0, cls: ['gedge', certE.has(k) ? 'cert' : '', e.cls || ''].filter(Boolean).join(' '), audit: 'edge-x' };
      if (e.label) { it.label = e.label; it.lx = rt.lx; it.ly = rt.ly; }
      items.push(it);
    }
    for (const n of nodes) {
      const label = String(n.label === undefined ? n.id : n.label);
      const w = Math.max(2 * r, Geo.textWidth(label, 15, { bold: true }) + 16);
      items.push({ key: P + ':v:' + n.id, kind: 'state', x: pos[n.id].x, y: pos[n.id].y, w, h: 2 * r, rx: r, text: label, cls: ['gnode', n.role === 'var' ? 'var' : n.role === 'clause' ? 'clause' : '', cert.has(n.id) ? 'cert' : '', n.cls || ''].filter(Boolean).join(' '), pick: true });
    }
    return { items, pos };
  };

  GD.demos = [
    { name: 'gadget: 3SAT to CLIQUE with a certificate', frames: () => {
      // two clauses (x ∨ y ∨ ¬z) and (¬x ∨ y ∨ z): a vertex per literal, edges between consistent literals of different clauses
      const C = [['x', 'y', '¬z'], ['¬x', 'y', 'z']];
      const nodes = [], edges = [];
      C.forEach((cl, i) => cl.forEach((l, j) => nodes.push({ id: i + ':' + j, label: l, group: 'c' + i, role: 'clause' })));
      const neg = (a, b) => a === '¬' + b || b === '¬' + a;
      for (let a = 0; a < nodes.length; a++) for (let b = a + 1; b < nodes.length; b++) if (nodes[a].group !== nodes[b].group && !neg(nodes[a].label, nodes[b].label)) edges.push({ a: nodes[a].id, b: nodes[b].id });
      const groups = [{ id: 'c0', label: 'clause 1', shape: 'col' }, { id: 'c1', label: 'clause 2', shape: 'col' }];
      return [
        { items: GD.draw({ nodes, edges, groups }).items, say: 'One vertex per literal; edges join literals of different clauses that can both be true.' },
        { items: GD.draw({ nodes, edges, groups, cert: ['0:1', '1:1'], certEdges: [['0:1', '1:1']] }).items, say: 'A clique of size 2: y in both clauses, so y = true satisfies the formula.' },
      ];
    } },
    { name: 'gadget: a graph laid out without groups', frames: () => {
      const nodes = 'abcdef'.split('').map((id) => ({ id }));
      const edges = [['a', 'b'], ['b', 'c'], ['c', 'd'], ['d', 'e'], ['e', 'f'], ['f', 'a'], ['a', 'd']].map(([a, b]) => ({ a, b }));
      return [{ items: GD.draw({ nodes, edges, cert: ['a', 'c', 'e'] }).items, say: 'A vertex cover lit: every edge touches a green vertex.' }];
    } },
  ];
})();
