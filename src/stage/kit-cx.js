// Pictures for complexity: bars that race (the growth of n, n², 2ⁿ…), a line chart with plain or
// logarithmic steps on the y axis (step counts against input length, with fitted curves), CNF formulas drawn
// clause by clause with each literal coloured by its value, a row of variable chips for an assignment, and
// big numbers written so they fit (3.6 million, 1.2 × 10¹⁸).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const CX = (K.cx = {});

  const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹', '-': '⁻' };
  CX.sup = (n) => String(n).split('').map((c) => SUP[c] || c).join('');
  /** A count written to be read at a glance: 1 234, 3.6 million, 4.1 × 10¹², ∞ */
  CX.num = function (v) {
    if (v === Infinity) return '∞';
    if (!Number.isFinite(v)) return '?';
    const a = Math.abs(v);
    if (a < 1000) return String(Math.round(v * 100) / 100);
    if (a < 1e6) return Math.round(v).toLocaleString('en-US').replace(/,/g, ' ');
    if (a < 1e9) return (Math.round(v / 1e5) / 10) + ' million';
    if (a < 1e12) return (Math.round(v / 1e8) / 10) + ' billion';
    const e = Math.floor(Math.log10(a)), m = Math.round((v / Math.pow(10, e)) * 10) / 10;
    return (m === 1 ? '' : m + ' × ') + '10' + CX.sup(e);
  };

  /**
   * Horizontal bars, one per row, that grow and shrink between frames (the key is the row's id).
   * opts: {rows: [{id, label, value, cls, text (written after the bar; default the value)}], x, y (top-left of
   *   the bars; labels go to the left), w (longest bar), barH, gap, max (the value of a full bar), log (bars by
   *   log₁₀(1 + value)), prefix, title, cap: a value past which a bar is drawn full with an arrow, labelW}
   * Returns {items, box}.
   */
  CX.bars = function (opts) {
    const P = opts.prefix || 'br';
    const rows = opts.rows || [];
    const W = opts.w || 420, BH = opts.barH || 30, GAP = opts.gap || 14;
    const x0 = opts.x || 0, y0 = opts.y || 0;
    const f = opts.log ? (v) => Math.log10(1 + Math.max(0, v)) : (v) => Math.max(0, v);
    const max = opts.max !== undefined ? opts.max : Math.max(1, ...rows.map((r) => (r.value === Infinity ? 0 : r.value)));
    const fm = f(max) || 1;
    const items = [];
    const labelW = opts.labelW || Math.max(30, ...rows.map((r) => Geo.textWidth(r.label, 15, { bold: true }) + 14));
    if (opts.title) items.push({ key: P + ':title', kind: 'text', x: x0 - labelW, y: y0 - 14, text: opts.title, cls: 'title' });
    let right = x0 + W;
    rows.forEach((r, i) => {
      const y = y0 + i * (BH + GAP);
      const over = r.value === Infinity || r.value > max;
      const w = over ? W : Math.max(3, (f(r.value) / fm) * W);
      items.push({ key: P + ':l:' + r.id, kind: 'text', x: x0 - 12, y: y + BH / 2 + 5, text: r.label, anchor: 'end', cls: 'strong', size: 15 });
      items.push({ key: P + ':b:' + r.id, kind: 'cell', x: x0, y, w, h: BH, text: '', rx: 5, cls: 'bar ' + (r.cls || 's' + (i % 8)) + (over ? ' over' : ''), enter: 'grow' });
      const t = r.text !== undefined ? r.text : (over ? (r.value === Infinity ? '∞' : CX.num(r.value)) + ' →' : CX.num(r.value));
      const tw = Geo.textWidth(t, 14, { bold: true });
      items.push({ key: P + ':v:' + r.id, kind: 'text', x: x0 + w + 9, y: y + BH / 2 + 5, text: t, anchor: 'start', cls: 'strong' + (over ? ' bad' : ''), size: 14 });
      right = Math.max(right, x0 + w + 9 + tw);
    });
    const h = rows.length * (BH + GAP) - GAP;
    return { items, box: { x: x0 - labelW, y: y0 - (opts.title ? 30 : 0), w: right - x0 + labelW, h: h + (opts.title ? 30 : 0) } };
  };

  /**
   * A line chart. opts: {x, y, w, h (the plotting area), xs: [min, max], ys: [min, max], logY (the y axis in
   *   powers of ten; ys then gives the range as values ≥ 1), xTicks: [values], yTicks: [values], xLabel, yLabel,
   *   series: [{id, label, pts: [[x, y], …], cls ('s0'…'s7'), dash, dots (default true), hot}], marks: [{id, x,
   *   text}] (a dashed upright line at x), prefix}
   * A series that leaves the top is cut where it crosses the edge and gets an arrow; series labels are written
   * in a column to the right of the area, at the height where each line ends, pushed apart so they never touch.
   * Returns {items, box, at(x, y) -> stage point}.
   */
  CX.plot = function (opts) {
    const P = opts.prefix || 'pl';
    const X0 = opts.x || 0, Y0 = opts.y || 0, W = opts.w || 520, H = opts.h || 300;
    const [xmin, xmax] = opts.xs || [0, 10];
    const log = !!opts.logY;
    const fy = (v) => (log ? Math.log10(Math.max(v, 1e-9)) : v);
    const [ymin, ymax] = (opts.ys || [0, 10]).map(fy);
    const sx = (v) => X0 + ((v - xmin) / (xmax - xmin || 1)) * W;
    const sy = (v) => Y0 + H - ((fy(v) - ymin) / (ymax - ymin || 1)) * H;
    const items = [];
    // grid and axes are scenery: the checker leaves them alone
    for (const t of opts.yTicks || []) {
      const y = sy(t);
      if (y < Y0 - 0.5 || y > Y0 + H + 0.5) continue;
      items.push({ key: P + ':gy:' + t, kind: 'line', x1: X0, y1: y, x2: X0 + W, y2: y, cls: 'grid', audit: 'ignore' });
      items.push({ key: P + ':ty:' + t, kind: 'text', x: X0 - 9, y: y + 4.5, text: opts.yTickText ? opts.yTickText(t) : CX.num(t), anchor: 'end', size: 12, cls: 'tick' });
    }
    for (const t of opts.xTicks || []) {
      const x = sx(t);
      items.push({ key: P + ':tk:' + t, kind: 'line', x1: x, y1: Y0 + H, x2: x, y2: Y0 + H + 6, cls: 'axis', audit: 'ignore' });
      items.push({ key: P + ':tx:' + t, kind: 'text', x, y: Y0 + H + 22, text: opts.xTickText ? opts.xTickText(t) : String(t), anchor: 'middle', size: 12, cls: 'tick' });
    }
    items.push({ key: P + ':ax', kind: 'line', x1: X0, y1: Y0 + H, x2: X0 + W, y2: Y0 + H, cls: 'axis', audit: 'ignore' });
    items.push({ key: P + ':ay', kind: 'line', x1: X0, y1: Y0 - 6, x2: X0, y2: Y0 + H, cls: 'axis', audit: 'ignore' });
    if (opts.xLabel) items.push({ key: P + ':xl', kind: 'text', x: X0 + W / 2, y: Y0 + H + 46, text: opts.xLabel, anchor: 'middle', cls: 'title' });
    if (opts.yLabel) items.push({ key: P + ':yl', kind: 'text', x: X0 - 4, y: Y0 - 18, text: opts.yLabel, anchor: 'start', cls: 'title' });
    for (const m of opts.marks || []) {
      const x = sx(m.x);
      items.push({ key: P + ':mk:' + m.id, kind: 'line', x1: x, y1: Y0, x2: x, y2: Y0 + H, cls: 'mark-line ' + (m.cls || ''), audit: 'ignore' });
    }
    const ends = [];
    (opts.series || []).forEach((s, si) => {
      const cls = 'ser ' + (s.cls || 's' + (si % 8)) + (s.dash ? ' dash' : '') + (s.hot ? ' hot-ser' : '');
      const pts = (s.pts || []).filter((p) => Number.isFinite(p[1]) || p[1] === Infinity).map((p) => ({ x: sx(p[0]), y: p[1] === Infinity ? -Infinity : sy(p[1]), v: p }));
      let last = null, cut = false;
      for (let k = 0; k < pts.length; k++) {
        const p = pts[k];
        if (p.y < Y0 - 0.5) {
          // leaves the top: run the segment up to the edge and stop
          if (last) { const t = (Y0 - last.y) / (p.y - last.y), cx = last.x + (p.x - last.x) * (Number.isFinite(t) ? t : 0); items.push({ key: P + ':s:' + s.id + ':' + k, kind: 'line', x1: last.x, y1: last.y, x2: cx, y2: Y0, cls, audit: 'edge-x' }); last = { x: cx, y: Y0 }; }
          else last = { x: p.x, y: Y0 };
          cut = true;
          break;
        }
        if (last) items.push({ key: P + ':s:' + s.id + ':' + k, kind: 'line', x1: last.x, y1: last.y, x2: p.x, y2: p.y, cls, audit: 'edge-x' });
        if (s.dots !== false) items.push({ key: P + ':d:' + s.id + ':' + k, kind: 'token', x: p.x, y: p.y, r: s.hot ? 5.5 : 4.5, cls, audit: 'overlap-ok', title: s.label + ': ' + p.v[0] + ' → ' + CX.num(p.v[1]) });
        last = p;
      }
      if (last && s.label) ends.push({ id: s.id, y: last.y, text: (cut ? '↑ ' : '') + s.label, cls });
    });
    // labels in a column to the right, in the order the lines end, at least 20 apart
    ends.sort((a, b) => a.y - b.y);
    for (let i = 0; i < ends.length; i++) ends[i].ly = Math.max(ends[i].y, i ? ends[i - 1].ly + 20 : Y0 - 4);
    // then, from the bottom, pull back up any that were pushed below the axis
    for (let i = ends.length - 1; i >= 0; i--) ends[i].ly = Math.min(ends[i].ly, i === ends.length - 1 ? Y0 + H + 4 : ends[i + 1].ly - 20);
    let lw = 0;
    for (const e of ends) {
      items.push({ key: P + ':sl:' + e.id, kind: 'text', x: X0 + W + 14, y: e.ly + 5, text: e.text, anchor: 'start', size: 14, cls: 'ser-label ' + e.cls });
      lw = Math.max(lw, Geo.textWidth(e.text, 14, { bold: true }) + 16);
    }
    // a marker's label sits over its line, lifted above the y axis title when the two would meet
    const ylEnd = opts.yLabel ? X0 - 4 + Geo.textWidth(opts.yLabel, 13, { bold: true }) * 1.15 + 8 : -Infinity;
    for (const m of opts.marks || []) if (m.text) { const x = sx(m.x), half = Geo.textWidth(m.text, 13) / 2; items.push({ key: P + ':mt:' + m.id, kind: 'text', x, y: x - half < ylEnd ? Y0 - 38 : Y0 - 12, text: m.text, anchor: 'middle', size: 13, cls: 'hot' }); }
    const left = Math.max(30, ...(opts.yTicks || []).map((t) => Geo.textWidth(opts.yTickText ? opts.yTickText(t) : CX.num(t), 12) + 14));
    return { items, at: (x, y) => ({ x: sx(x), y: sy(y) }), box: { x: X0 - left, y: Y0 - 30, w: W + left + lw + 14, h: H + 30 + (opts.xLabel ? 54 : 30) } };
  };

  /**
   * A CNF formula drawn clause by clause: each clause a rounded group of literal cells, ∧ between groups,
   * wrapping into rows no wider than maxW. f is a formula as in T.sat ({n, clauses, names}).
   * opts: {f, a (assignment a[1..n]: true, false or null for unset), x, y, maxW, prefix, labels (C1, C2… above
   *   each clause), clauseCls(i) -> classes, litCls(i, j, lit) -> classes, hot: [clause indexes], dimmed:
   *   [clause indexes] (satisfied and set aside), only: [clause indexes] to draw}
   * Clauses are coloured by status: satisfied (green), falsified (red), unit (amber: one literal left).
   * Returns {items, box, litKey(i, j), clauseKey(i), status(i)}.
   */
  CX.formula = function (opts) {
    const P = opts.prefix || 'cnf';
    const f = opts.f, a = opts.a || [];
    const name = (l) => T.sat.litText(f, l);
    const val = (l) => { const v = a[Math.abs(l)]; return v === null || v === undefined ? null : l > 0 ? !!v : !v; };
    const status = (i) => {
      const c = f.clauses[i];
      if (c.some((l) => val(l) === true)) return 'sat';
      const open = c.filter((l) => val(l) === null);
      if (!open.length) return 'false';
      return open.length === 1 ? 'unit' : 'open';
    };
    const maxW = opts.maxW || 760, CH = 40, PAD = 7, AND = 30, top = opts.labels ? 22 : 0;
    const x0 = opts.x || 0, y0 = opts.y || 0;
    const items = [];
    const hot = new Set(opts.hot || []), dim = new Set(opts.dimmed || []);
    const which = opts.only || f.clauses.map((_, i) => i);
    let x = x0, y = y0, right = x0, rowH = CH + 2 * PAD + top;
    which.forEach((i, k) => {
      const c = f.clauses[i];
      const ws = c.map((l) => Math.max(40, Geo.textWidth(name(l), 16, { mono: true }) + 18));
      const cw = (ws.length ? ws.reduce((s, w) => s + w, 0) + (ws.length - 1) * 3 : 40) + 2 * PAD;
      if (k && x + AND + cw > x0 + maxW) { x = x0; y += rowH + 14; }
      else if (k) {
        items.push({ key: P + ':and:' + i, kind: 'text', x: x + AND / 2, y: y + top + PAD + CH / 2 + 6, text: '∧', anchor: 'middle', size: 17, cls: 'strong' });
        x += AND;
      }
      const st = status(i);
      const ccls = ['clause-box', 'cl-' + st, hot.has(i) ? 'hot' : '', dim.has(i) ? 'cl-dim' : '', opts.clauseCls ? opts.clauseCls(i) || '' : ''].filter(Boolean).join(' ');
      items.push({ key: P + ':c:' + i, kind: 'region', x, y, w: cw, h: CH + 2 * PAD + top, rx: 12, text: opts.labels ? 'C' + (i + 1) : '', cls: ccls });
      let lx = x + PAD;
      if (!c.length) items.push({ key: P + ':l:' + i + ':e', kind: 'cell', x: lx, y: y + top + PAD, w: 40, h: CH, text: '□', cls: 'mono lit lit-f' });
      c.forEach((l, j) => {
        const v = val(l);
        items.push({ key: P + ':l:' + i + ':' + j, kind: 'cell', x: lx, y: y + top + PAD, w: ws[j], h: CH, rx: 6, text: name(l), cls: ['mono', 'lit', v === true ? 'lit-t' : v === false ? 'lit-f' : 'lit-u', opts.litCls ? opts.litCls(i, j, l) || '' : ''].filter(Boolean).join(' '), pick: true });
        lx += ws[j] + 3;
      });
      x += cw;
      right = Math.max(right, x);
    });
    return { items, box: { x: x0, y: y0, w: right - x0, h: y + rowH - y0 }, litKey: (i, j) => P + ':l:' + i + ':' + j, clauseKey: (i) => P + ':c:' + i, status };
  };

  /**
   * An assignment as a row of chips, one per variable: name above, value (1, 0 or ?) below.
   * opts: {f (for the names) or names: [, n1, n2…], n, a (a[1..n]), x, y, prefix, hot: [variables], why: {v:
   *   'unit'|'pure'|'decide'} (a small tag under the chip), label}
   */
  CX.assignment = function (opts) {
    const P = opts.prefix || 'asg';
    const n = opts.n !== undefined ? opts.n : opts.f.n;
    const nm = (v) => (opts.f ? T.sat.litText(opts.f, v) : (opts.names && opts.names[v]) || 'x' + v);
    const a = opts.a || [];
    const hot = new Set(opts.hot || []);
    const x0 = opts.x || 0, y0 = opts.y || 0;
    const items = [];
    if (opts.label) items.push({ key: P + ':label', kind: 'text', x: x0 - 12, y: y0 + 32, text: opts.label, anchor: 'end', cls: 'title' });
    let x = x0;
    for (let v = 1; v <= n; v++) {
      const w = Math.max(46, Geo.textWidth(nm(v), 15, { mono: true }) + 18);
      const val = a[v];
      const t = val === true ? '1' : val === false ? '0' : '?';
      items.push({ key: P + ':n:' + v, kind: 'text', x: x + w / 2, y: y0 + 13, text: nm(v), anchor: 'middle', size: 14, cls: 'mono' });
      const it = { key: P + ':v:' + v, kind: 'cell', x, y: y0 + 22, w, h: 36, text: t, rx: 8, cls: ['mono', 'chip', val === true ? 'lit-t' : val === false ? 'lit-f' : 'lit-u', hot.has(v) ? 'hot' : ''].filter(Boolean).join(' '), pick: true };
      if (opts.why && opts.why[v]) it.sub = opts.why[v];
      items.push(it);
      x += w + 8;
    }
    return { items, box: { x: x0 - (opts.label ? Geo.textWidth(opts.label, 13, { bold: true }) + 20 : 0), y: y0, w: x - x0, h: 58 + (opts.why ? 18 : 0) } };
  };

  /** A boxed note: a panel region with lines of text in it, for verdicts and side remarks. opts {x, y, w, lines, cls, prefix, size} */
  CX.note = function (opts) {
    const P = opts.prefix || 'note';
    const fs = opts.size || 15, lh = fs * 1.45;
    const lines = [].concat(opts.lines || []);
    const w = opts.w || Math.max(...lines.map((l) => Geo.textWidth(l, fs, { bold: true }) + 28));
    const h = lines.length * lh + 18;
    const items = [{ key: P + ':box', kind: 'region', x: opts.x || 0, y: opts.y || 0, w, h, rx: 10, text: '', cls: 'panel ' + (opts.cls || '') }];
    lines.forEach((l, i) => items.push({ key: P + ':t' + i, kind: 'text', x: (opts.x || 0) + 14, y: (opts.y || 0) + 9 + (i + 0.5) * lh + fs * 0.35, text: l, size: fs, cls: i === 0 && opts.head !== false ? 'strong' : '' }));
    return { items, box: { x: opts.x || 0, y: opts.y || 0, w, h } };
  };

  CX.demos = [
    { name: 'cx: growth rates racing as bars', frames: () => [4, 8, 16].map((n) => ({
      items: CX.bars({ rows: T.cx.GROWTH.filter((g) => ['n', 'nlog', 'n2', '2n'].includes(g.id)).map((g) => ({ id: g.id, label: g.name, value: g.f(n) })), w: 380, log: true, max: 2 ** 16, title: 'n = ' + n }).items,
      say: 'At n = ' + n + ' the exponential bar pulls away.' })) },
    { name: 'cx: a line chart with a log axis', frames: () => [{
      items: CX.plot({ w: 420, h: 240, xs: [0, 20], ys: [1, 1e6], logY: true, yTicks: [1, 100, 1e4, 1e6], xTicks: [0, 5, 10, 15, 20], xLabel: 'n', yLabel: 'steps',
        series: [{ id: 'n2', label: 'n²', pts: [0, 5, 10, 15, 20].map((n) => [n, Math.max(1, n * n)]) }, { id: 'e', label: '2ⁿ', pts: [0, 5, 10, 15, 20].map((n) => [n, 2 ** n]) }], marks: [{ id: 'm', x: 10, text: 'n = 10' }] }).items,
      say: 'On a log scale a polynomial bends over and an exponential is a straight line that leaves the chart.' }] },
    { name: 'cx: a formula with an assignment', frames: () => {
      const f = T.sat.parse('(x ∨ ¬y ∨ z) ∧ (¬x ∨ y) ∧ (¬z) ∧ (y ∨ z)');
      const a = [null, true, null, false];
      return [{ items: CX.formula({ f, a, labels: true, maxW: 560 }).items.concat(CX.assignment({ f, a, y: 150, label: 'values' }).items), say: 'Green literals are true, red ones false; the second clause is a unit.' }];
    } },
  ];
})();
