// Relations on a small set: the elements on a circle with an arrow for every pair (a loop for (x, x), a
// pair of bowed arrows when both directions are there), and the same relation as a 0/1 matrix. Pairs can be
// lit (hot), new (good), missing but needed (drawn dashed in red), or faded, so a scene can show the edges
// that make or break a property. Also a two-column picture for functions: arrows from a domain to a codomain.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const RL = (K.rel = {});

  const pk = (x, y) => x + '\u0000' + y;
  const NR = 22;
  /** The radius of a node: a circle that fits its name */
  RL.nodeR = (x) => Math.max(NR, Geo.textWidth(String(x), 16, { bold: true }) / 2 + 9);

  /** Positions on a circle, the first element at the top, going clockwise. opts: {x, y (centre), radius} */
  RL.circle = function (D, opts) {
    opts = opts || {};
    const n = D.length, maxR = Math.max(NR, ...D.map(RL.nodeR));
    // neighbours far enough apart for two arrows and a label-free gap between them
    const R = opts.radius || (n <= 1 ? 0 : n === 2 ? 70 : Math.max(78, (maxR + 30) / Math.sin(Math.PI / n)));
    const cx = opts.x || 0, cy = opts.y || 0, pos = {};
    D.forEach((x, i) => { const a = -Math.PI / 2 + (2 * Math.PI * i) / Math.max(1, n); pos[x] = { x: cx + R * Math.cos(a), y: cy + R * Math.sin(a), a }; });
    // two elements sit side by side rather than one above the other
    if (n === 2) { pos[D[0]] = { x: cx - R, y: cy, a: Math.PI }; pos[D[1]] = { x: cx + R, y: cy, a: 0 }; }
    if (n === 1) pos[D[0]] = { x: cx, y: cy, a: -Math.PI / 2 };
    return { pos, R, cx, cy, box: { x: cx - R - maxR - 70, y: cy - R - maxR - 70, w: 2 * (R + maxR + 70), h: 2 * (R + maxR + 70) } };
  };

  /**
   * The relation as a graph. opts: {D, R: [[x, y]], pos (from circle), prefix, hot, good, bad, dim: [[x, y]]
   *   pair classes, ghost: [[x, y]] (missing pairs drawn dashed), ghostCls, nodeCls: {x: classes}, nodeSub: {x: text},
   *   enter: {pairKey: key to grow from}, edges: false (nodes only)}
   * Returns {items, box, nodeKey(x), edgeKey(x, y)}.
   */
  RL.graph = function (opts) {
    const P = opts.prefix || 'rl';
    const D = opts.D, R = opts.R || [], pos = opts.pos || RL.circle(D).pos;
    const nk = (x) => P + ':n:' + x, ek = (x, y) => P + ':e:' + x + '>' + y;
    const set = (a) => new Set((a || []).map(([x, y]) => pk(x, y)));
    const hot = set(opts.hot), good = set(opts.good), bad = set(opts.bad), dim = set(opts.dim);
    const has = set(R);
    const items = [];
    const centre = { x: 0, y: 0 };
    const ps = D.map((x) => pos[x]);
    if (ps.length) { centre.x = ps.reduce((a, p) => a + p.x, 0) / ps.length; centre.y = ps.reduce((a, p) => a + p.y, 0) / ps.length; }
    for (const x of D) {
      const p = pos[x], r = RL.nodeR(x);
      const it = { key: nk(x), kind: 'state', x: p.x, y: p.y, r, w: 2 * r, h: 2 * r, rx: r, text: String(x), cls: 'state ' + ((opts.nodeCls && opts.nodeCls[x]) || ''), pick: true };
      if (opts.nodeSub && opts.nodeSub[x] !== undefined) it.sub = opts.nodeSub[x];
      items.push(it);
    }
    const edge = (x, y, cls, extra) => {
      const it = { key: ek(x, y), kind: 'edge', from: nk(x), to: nk(y), cls: 'rel ' + cls, audit: 'edge-x' };
      if (x === y) {
        // a loop points away from the middle of the picture
        const p = pos[x];
        let a = Math.atan2(p.y - centre.y, p.x - centre.x);
        if (D.length === 1) a = -Math.PI / 2;
        it.loop = a; it.loopSize = 30;
      } else if (has.has(pk(y, x)) || (extra && extra.twin)) it.bend = 14;
      if (opts.enter && opts.enter[pk(x, y)]) { it.enter = 'from'; it.src = opts.enter[pk(x, y)]; }
      items.push(it);
    };
    if (opts.edges !== false) {
      for (const [x, y] of R) {
        const k = pk(x, y);
        const cls = [hot.has(k) ? 'hot' : '', good.has(k) ? 'good' : '', bad.has(k) ? 'bad' : ''].filter(Boolean).join(' ');
        edge(x, y, cls);
        if (dim.has(k)) items[items.length - 1].dim = true;
      }
      for (const [x, y] of opts.ghost || []) if (!has.has(pk(x, y))) edge(x, y, 'dead ' + (opts.ghostCls || 'bad'), { twin: true });
    }
    const boxes = D.map((x) => { const p = pos[x], r = RL.nodeR(x); return { x: p.x - r, y: p.y - r, w: 2 * r, h: 2 * r }; });
    return { items, box: Geo.union(boxes), nodeKey: nk, edgeKey: ek };
  };

  /**
   * The relation as a 0/1 matrix: row x, column y holds 1 when (x, y) is in R. opts: {D, R, x, y, prefix, hot,
   *   good, bad, act: [[x, y]] cell classes, lit: {rows: [x], cols: [y]} (a row and column lit, as Warshall's
   *   round k does), arrows: [{from: [x, y], to: [x, y], cls}], corner, cw, blank: 0s left empty}
   */
  RL.matrix = function (opts) {
    const D = opts.D, has = new Set((opts.R || []).map(([x, y]) => pk(x, y)));
    const ix = (x) => D.indexOf(x);
    const cellSet = (a) => new Set((a || []).map(([x, y]) => ix(x) + ',' + ix(y)));
    const good = cellSet(opts.good), bad = cellSet(opts.bad), act = cellSet(opts.act), hot = cellSet(opts.hot);
    const litR = new Set(((opts.lit && opts.lit.rows) || []).map(ix)), litC = new Set(((opts.lit && opts.lit.cols) || []).map(ix));
    const rows = D.map((x) => D.map((y) => (has.has(pk(x, y)) ? '1' : opts.blank ? '' : '0')));
    const t = K.table.draw({
      rows, rowHead: D.map(String), colHead: D.map(String), corner: opts.corner || 'R', x: opts.x || 0, y: opts.y || 0, prefix: opts.prefix || 'rm', cw: opts.cw || 40, ch: opts.ch || 38, mono: true, size: 16,
      cls: (r, c, v) => [v === '1' ? 'one' : 'empty', hot.has(r + ',' + c) ? 'hot' : good.has(r + ',' + c) ? 'good' : bad.has(r + ',' + c) ? 'bad' : act.has(r + ',' + c) ? 'act' : (litR.has(r) || litC.has(c)) ? 'mark' : ''].filter(Boolean).join(' '),
      arrows: (opts.arrows || []).map((a) => ({ from: [ix(a.from[0]), ix(a.from[1])], to: [ix(a.to[0]), ix(a.to[1])], cls: a.cls, bend: a.bend })),
    });
    t.cellKey = (x, y) => t.key(ix(x), ix(y));
    return t;
  };

  /**
   * A function or any relation from A to B drawn as two columns with arrows. opts: {A, B, pairs: [[a, b]],
   *   x, y, gap (between the columns), prefix, titles: [left, right], hot, good, bad: [[a, b]], nodeCls: {'A:a' | 'B:b': cls},
   *   ghost: [[a, b]] (dashed)}
   */
  RL.columns = function (opts) {
    const P = opts.prefix || 'fn';
    const A = opts.A, B = opts.B, x0 = opts.x || 0, y0 = opts.y || 0, gap = opts.gap || 240, step = opts.step || 58;
    const hA = (A.length - 1) * step, hB = (B.length - 1) * step, H = Math.max(hA, hB);
    const ak = (a) => P + ':a:' + a, bk = (b) => P + ':b:' + b;
    const items = [];
    const nodeCls = opts.nodeCls || {};
    const pill = (x) => { const w = Math.max(44, Geo.textWidth(String(x), 16, { bold: true }) + 24); return { w, h: 40, rx: 20 }; };
    const wA = Math.max(44, ...A.map((a) => pill(a).w)), wB = Math.max(44, ...B.map((b) => pill(b).w));
    if (opts.titles) {
      items.push({ key: P + ':tA', kind: 'text', x: x0, y: y0 - 38, text: opts.titles[0], anchor: 'middle', cls: 'title' });
      items.push({ key: P + ':tB', kind: 'text', x: x0 + gap, y: y0 - 38, text: opts.titles[1], anchor: 'middle', cls: 'title' });
    }
    items.push({ key: P + ':bgA', kind: 'region', x: x0 - wA / 2 - 14, y: y0 - 16 - 20, w: wA + 28, h: H + 72, cls: 'r0', rx: 22 });
    items.push({ key: P + ':bgB', kind: 'region', x: x0 + gap - wB / 2 - 14, y: y0 - 16 - 20, w: wB + 28, h: H + 72, cls: 'r1', rx: 22 });
    A.forEach((a, i) => { const s = pill(a); items.push({ key: ak(a), kind: 'state', x: x0, y: y0 + (H - hA) / 2 + i * step, w: s.w, h: s.h, rx: s.rx, text: String(a), cls: 'state ' + (nodeCls['A:' + a] || ''), pick: true }); });
    B.forEach((b, i) => { const s = pill(b); items.push({ key: bk(b), kind: 'state', x: x0 + gap, y: y0 + (H - hB) / 2 + i * step, w: s.w, h: s.h, rx: s.rx, text: String(b), cls: 'state ' + (nodeCls['B:' + b] || ''), pick: true }); });
    const set = (a) => new Set((a || []).map(([x, y]) => pk(x, y)));
    const hot = set(opts.hot), good = set(opts.good), bad = set(opts.bad);
    const arrow = (a, b, cls, rev) => items.push({ key: P + ':e:' + a + '>' + b, kind: 'edge', from: rev ? bk(b) : ak(a), to: rev ? ak(a) : bk(b), cls: 'rel ' + cls, audit: 'edge-x' });
    for (const [a, b] of opts.pairs || []) { const k = pk(a, b); arrow(a, b, [hot.has(k) ? 'hot' : '', good.has(k) ? 'good' : '', bad.has(k) ? 'bad' : ''].filter(Boolean).join(' '), opts.reverse); }
    for (const [a, b] of opts.ghost || []) arrow(a, b, 'dead bad');
    return { items, akey: ak, bkey: bk, box: { x: x0 - wA / 2 - 14, y: y0 - 56, w: gap + wA / 2 + wB / 2 + 28, h: H + 92 } };
  };

  // ---- reading relations typed by a student, and writing them back ----
  /** Is the screen narrow (a phone)? Scenes stack their parts instead of placing them side by side. */
  RL.narrow = () => typeof globalThis.innerWidth === 'number' && globalThis.innerWidth < 640;
  /** Read pairs written as "1-2, 2-3", "(a,b) (b,c)" or "x→y": [[x, y]] in the order given, without repeats */
  RL.parsePairs = function (text) {
    const s = String(text || '');
    const re = /\(?\s*([^\s,()\-→>]+)\s*(?:->|→|-|,|>)\s*([^\s,()\-→>]+)\s*\)?/g;
    const out = [], seen = new Set();
    let m, rest = s;
    while ((m = re.exec(s))) { const k = m[1] + '\u0000' + m[2]; if (!seen.has(k)) { seen.add(k); out.push([m[1], m[2]]); } }
    rest = s.replace(re, ' ');
    if (/[^\s,;]/.test(rest)) throw new Error('Could not read "' + rest.trim().slice(0, 12) + '": write pairs as x-y, separated by commas');
    return out;
  };
  RL.showPairs = (R) => (R.length ? '{' + R.map(([x, y]) => '(' + x + ', ' + y + ')').join(', ') + '}' : '∅');
  /** Pairs wrapped onto lines of a few, for the definition panel */
  RL.pairLines = (name, R, per) => {
    per = per || 4;
    if (!R.length) return [name + ' = ∅'];
    const parts = R.map(([x, y]) => '(' + x + ', ' + y + ')');
    const out = [];
    for (let i = 0; i < parts.length; i += per) out.push((i === 0 ? name + ' = {' : '      ') + parts.slice(i, i + per).join(', ') + (i + per >= parts.length ? '}' : ','));
    return out;
  };
  RL.checkDomain = (D, label) => {
    if (new Set(D).size !== D.length) return (label || 'Set') + ': an element is listed twice';
    if (D.some((x) => x === '')) return (label || 'Set') + ': ε is not an element here; use names like 1, 2, a, b';
    if (D.some((x) => [...x].length > 3)) return (label || 'Set') + ': keep names to at most 3 characters, so they fit in the circles';
    return null;
  };
  RL.checkPairs = (text, D, label) => {
    let R;
    try { R = RL.parsePairs(text); } catch (e) { return (label || 'Pairs') + ': ' + e.message; }
    for (const [x, y] of R) for (const v of [x, y]) if (!D.includes(v)) return (label || 'Pairs') + ': ' + v + ' is not in the set {' + D.join(', ') + '}';
    return null;
  };

  RL.demos = [
    { name: 'relation: a graph and its matrix', frames: () => {
      const D = ['1', '2', '3', '4'];
      const R = [['1', '2'], ['2', '3'], ['3', '3'], ['2', '1'], ['3', '4']];
      const c = RL.circle(D);
      const m = (o) => RL.matrix(Object.assign({ D, R, x: c.box.x + c.box.w + 30, y: -100 }, o)).items;
      return [
        { items: RL.graph({ D, R, pos: c.pos }).items.concat(m({})), say: 'A relation on four elements, drawn two ways.' },
        { items: RL.graph({ D, R, pos: c.pos, hot: [['1', '2'], ['2', '3']], ghost: [['1', '3']] }).items.concat(m({ hot: [['1', '2'], ['2', '3']], bad: [['1', '3']] })), say: '1 → 2 → 3 with no arrow 1 → 3: not transitive.' },
      ];
    } },
    { name: 'relation: a function between two sets', frames: () => {
      const A = ['1', '2', '3'], B = ['a', 'b', 'c', 'd'];
      const pairs = [['1', 'b'], ['2', 'a'], ['3', 'b']];
      return [
        { items: RL.columns({ A, B, pairs, titles: ['A', 'B'] }).items, say: 'A function: one arrow out of every element of A.' },
        { items: RL.columns({ A, B, pairs, titles: ['A', 'B'], bad: [['1', 'b'], ['3', 'b']], nodeCls: { 'B:b': 'bad', 'B:c': 'hot', 'B:d': 'hot' } }).items, say: 'Two arrows meet at b, and nothing reaches c or d.' },
      ];
    } },
  ];
})();
