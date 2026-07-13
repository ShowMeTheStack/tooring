// Sets of things: Venn diagrams of two or three languages with their members written in the right
// regions, and nested regions for hierarchies (the Chomsky hierarchy, the map of complexity classes), with
// labelled points placed inside the innermost region they belong to.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const SE = (K.set = {});

  /**
   * A Venn diagram. opts: {sets: [{id, label}] (one, two or three), members: {region: [strings]} where a
   *   region names the sets it is in ('A', 'AB', 'ABC', and '' for outside all of them), hot: [set ids],
   *   x, y (centre), r, prefix, universe: label of the box around (default none)}
   */
  SE.venn = function (opts) {
    const P = opts.prefix || 'vn';
    const sets = opts.sets || [];
    const r = opts.r || 120;
    const cx = opts.x || 0, cy = opts.y || 0;
    const n = sets.length;
    const d = r * 0.95;
    const centres = n === 1 ? [{ x: cx, y: cy }] : n === 2 ? [{ x: cx - d / 2 - 6, y: cy }, { x: cx + d / 2 + 6, y: cy }] : [{ x: cx - d / 2, y: cy - d * 0.3 }, { x: cx + d / 2, y: cy - d * 0.3 }, { x: cx, y: cy + d * 0.55 }];
    const items = [];
    const hot = new Set(opts.hot || []);
    const ids = sets.map((s) => s.id);
    if (opts.universe !== undefined) items.push({ key: P + ':U', kind: 'region', x: cx - r * 2.05, y: cy - r * 1.75, w: r * 4.1, h: r * (n === 3 ? 3.65 : 3.4), text: opts.universe, cls: 'frame', rx: 18 });
    sets.forEach((s, i) => {
      const c = centres[i];
      const away = n === 1 ? { x: 0, y: -1 } : { x: c.x - cx, y: c.y - cy };
      const l = Math.hypot(away.x, away.y) || 1;
      const lx = c.x + away.x / l * r * 0.62, ly = c.y + (n === 3 && i === 2 ? r * 0.72 : -r * 0.78);
      items.push({ key: P + ':' + s.id, kind: 'ellipse', x: c.x, y: c.y, rx: r, ry: r, text: s.label || s.id, tx: n === 1 ? c.x : lx, ty: ly, cls: 'e' + i + (hot.has(s.id) ? ' hot' : '') });
    });
    // where each region's members go: a point inside exactly those sets
    const anchor = (reg) => {
      const inside = ids.filter((id) => reg.includes(id));
      if (!inside.length) return { x: cx + r * (n === 1 ? 1.45 : 1.75), y: cy + r * (n === 3 ? 1.3 : 1.1) };
      const pts = inside.map((id) => centres[ids.indexOf(id)]);
      const m = { x: pts.reduce((a, p) => a + p.x, 0) / pts.length, y: pts.reduce((a, p) => a + p.y, 0) / pts.length };
      if (inside.length === n) return { x: cx, y: n === 3 ? cy + d * 0.0 : cy };
      // move away from the centres of the sets it is not in
      const out = ids.filter((id) => !reg.includes(id)).map((id) => centres[ids.indexOf(id)]);
      let vx = 0, vy = 0;
      for (const o of out) { vx += m.x - o.x; vy += m.y - o.y; }
      const l = Math.hypot(vx, vy) || 1;
      const push = inside.length === 1 ? r * (n === 3 ? 0.42 : 0.5) : r * 0.32;
      return { x: m.x + vx / l * push, y: m.y + vy / l * push };
    };
    for (const [reg, list] of Object.entries(opts.members || {})) {
      const a = anchor(reg);
      const shown = list.slice(0, 6);
      if (list.length > 6) shown.push('…');
      shown.forEach((m, k) => items.push({ key: P + ':m:' + reg + ':' + m, kind: 'text', x: a.x, y: a.y + (k - (shown.length - 1) / 2) * 19 + 5, text: m === '' ? 'ε' : m, anchor: 'middle', cls: 'mono' }));
    }
    return { items, box: { x: cx - r * 2.1, y: cy - r * 1.8, w: r * 4.2, h: r * 3.7 } };
  };

  /**
   * Nested regions. opts: {regions: [{id, label, children: [...], cls}] (the outermost first), points:
   *   [{id, label, in: region id, cls}], x, y, prefix, hot: [region ids]}. Children sit side by side inside
   *   their parent under its label; points are listed inside their region, below its children.
   */
  SE.nested = function (opts) {
    const P = opts.prefix || 'ns';
    const hot = new Set(opts.hot || []);
    const pts = opts.points || [];
    const PAD = 16, BAND = 30, PT = 24;
    const size = new Map();
    const measure = (r) => {
      const ch = r.children || [];
      ch.forEach(measure);
      const mine = pts.filter((p) => p.in === r.id);
      const ptW = mine.length ? Math.max(...mine.map((p) => Geo.textWidth(p.label, 14) + 34)) : 0;
      const cw = ch.reduce((a, c) => a + size.get(c.id).w, 0) + Math.max(0, ch.length - 1) * PAD;
      const chH = ch.length ? Math.max(...ch.map((c) => size.get(c.id).h)) : 0;
      const w = Math.max(Geo.textWidth(r.label, 13, { bold: true }) + 30, cw + 2 * PAD, ptW + 2 * PAD, 150);
      const h = BAND + chH + (ch.length ? PAD : 0) + mine.length * PT + (mine.length ? 8 : 18);
      size.set(r.id, { w, h, mine });
    };
    const items = [];
    let depth = 0;
    const place = (r, x, y, d) => {
      const s = size.get(r.id);
      items.push({ key: P + ':' + r.id, kind: 'region', x, y, w: s.w, h: s.h, text: r.label, cls: 'r' + (d % 6) + (hot.has(r.id) ? ' hot' : '') + (r.cls ? ' ' + r.cls : '') });
      depth = Math.max(depth, d);
      const ch = r.children || [];
      const cw = ch.reduce((a, c) => a + size.get(c.id).w, 0) + Math.max(0, ch.length - 1) * PAD;
      let cx = x + (s.w - cw) / 2;
      for (const c of ch) { place(c, cx, y + BAND, d + 1); cx += size.get(c.id).w + PAD; }
      const chH = ch.length ? Math.max(...ch.map((c) => size.get(c.id).h)) + PAD : 0;
      s.mine.forEach((p, k) => {
        const py = y + BAND + chH + k * PT + 8;
        items.push({ key: P + ':p:' + p.id, kind: 'token', x: x + PAD + 6, y: py, r: 5, cls: p.cls || 'act' });
        items.push({ key: P + ':pl:' + p.id, kind: 'text', x: x + PAD + 18, y: py + 5, text: p.label, cls: 'strong' });
      });
    };
    let x = opts.x || 0;
    for (const r of opts.regions || []) { measure(r); place(r, x, opts.y || 0, 0); x += size.get(r.id).w + PAD; }
    return { items };
  };

  SE.demos = [
    { name: 'set: two languages as a Venn diagram', frames: () => [
      { items: SE.venn({ sets: [{ id: 'A', label: 'L₁: even length' }, { id: 'B', label: 'L₂: starts with a' }], members: { A: ['bb', 'ε'], AB: ['ab', 'aaba'], B: ['a', 'abb'], '': ['b'] }, hot: ['B'], universe: 'Σ*' }).items, say: 'Strings sorted into the regions of two languages.' },
    ] },
    { name: 'set: three sets', frames: () => [
      { items: SE.venn({ sets: [{ id: 'A', label: 'A' }, { id: 'B', label: 'B' }, { id: 'C', label: 'C' }], members: { ABC: ['x'], AB: ['y'], C: ['z'], A: ['w'] } }).items, say: 'Three sets and their regions.' },
    ] },
    { name: 'set: the Chomsky hierarchy', frames: () => [
      { items: SE.nested({ regions: [{ id: 're', label: 'Recursively enumerable', children: [{ id: 'dec', label: 'Decidable', children: [{ id: 'cs', label: 'Context-sensitive', children: [{ id: 'cf', label: 'Context-free', children: [{ id: 'reg', label: 'Regular' }] }] }] }] }], points: [{ id: 'p1', label: 'a*b*', in: 'reg' }, { id: 'p2', label: 'aⁿbⁿ', in: 'cf' }, { id: 'p3', label: 'aⁿbⁿcⁿ', in: 'cs' }, { id: 'p4', label: 'HALT', in: 're' }], hot: ['cf'] }).items, say: 'Each class sits inside the next.' },
    ] },
  ];
})();
