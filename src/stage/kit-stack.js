// Stacks for PDAs and parsers: a vertical column with the top up, where a push drops a cell in from above
// and a pop lifts it away; a row form (bottom on the left) for parser traces; and the two-column stack of
// an LR parser, symbols beside states.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const SK = (K.stack = {});

  const txt = (v) => (v && typeof v === 'object' ? v.text : v);
  const clsOf = (v) => (v && typeof v === 'object' ? v.cls || '' : '');

  /**
   * A stack. opts: {items: [bottom .. top] (strings or {text, cls}), x, y (the bottom-left corner),
   *   w, h (cell size), prefix, label, dir: 'up' (default) | 'row', max (cells shown; the bottom ones are
   *   elided), hot: [indexes lit], topLabel ('top' by default; '' for none), bottom: a marker drawn under it}
   * Cells are named by their depth and symbol, so a push slides in and a pop rises away.
   */
  SK.draw = function (opts) {
    const P = opts.prefix || 'k';
    const all = opts.items || [];
    const max = opts.max || 12;
    const skip = all.length > max ? all.length - max + 1 : 0;
    const shown = all.slice(skip);
    const longest = Math.max(1, ...all.map((v) => Geo.textWidth(txt(v), 16, { mono: true })));
    const W = opts.w || Math.max(52, longest + 24), H = opts.h || 40;
    const x0 = opts.x || 0, y0 = opts.y || 0;
    const hot = new Set(opts.hot || []);
    const items = [];
    const row = opts.dir === 'row';
    const at = (k) => (row ? { x: x0 + k * (W + 4), y: y0 - H } : { x: x0, y: y0 - (k + 1) * (H + 4) });
    if (skip) {
      const p = at(0);
      items.push({ key: P + ':more', kind: 'cell', x: p.x, y: p.y, w: W, h: H, text: '⋮ ' + skip, cls: 'elide' });
    }
    shown.forEach((v, j) => {
      const i = j + skip, k = j + (skip ? 1 : 0);
      const p = at(k);
      items.push({ key: P + ':' + i + ':' + txt(v), kind: 'cell', x: p.x, y: p.y, w: W, h: H, text: txt(v), cls: ['mono', 'stack', hot.has(i) ? 'hot' : '', clsOf(v)].filter(Boolean).join(' '), enter: row ? 'fly' : 'drop', from: row ? { x: p.x + 40, y: p.y } : undefined, exit: 'rise' });
    });
    const n = shown.length + (skip ? 1 : 0);
    // the base line, and the label under it
    if (row) {
      items.push({ key: P + ':base', kind: 'line', x1: x0 - 6, y1: y0 + 6, x2: x0 - 6, y2: y0 - H - 6, cls: '' });
      if (opts.label) items.push({ key: P + ':label', kind: 'text', x: x0 - 16, y: y0 - H / 2 + 5, text: opts.label, anchor: 'end', cls: 'title' });
    } else {
      items.push({ key: P + ':base', kind: 'line', x1: x0 - 8, y1: y0 + 2, x2: x0 + W + 8, y2: y0 + 2, cls: '' });
      if (opts.label) items.push({ key: P + ':label', kind: 'text', x: x0 + W / 2, y: y0 + 24, text: opts.label, anchor: 'middle', cls: 'title' });
    }
    if (!all.length) items.push({ key: P + ':empty', kind: 'text', x: row ? x0 + 4 : x0 + W / 2, y: row ? y0 - H / 2 + 5 : y0 - 18, text: 'empty', anchor: row ? 'start' : 'middle', cls: '' });
    else if (opts.topLabel !== '') {
      const p = at(n - 1);
      if (row) items.push({ key: P + ':top', kind: 'text', x: p.x + W / 2, y: p.y - 10, text: opts.topLabel || 'top', anchor: 'middle', cls: 'hot' });
      else items.push({ key: P + ':top', kind: 'text', x: p.x + W + 12, y: p.y + H / 2 + 5, text: opts.topLabel || '← top', anchor: 'start', cls: 'hot' });
    }
    const top = row ? y0 - H - 30 : y0 - n * (H + 4) - 10;
    return { items, box: { x: x0 - 10, y: top, w: row ? n * (W + 4) + 20 : W + 70, h: y0 + 30 - top }, cellW: W };
  };

  /** An LR parser's stack: [[symbol, state], ...] bottom first, drawn as two columns (or a row of pairs) */
  SK.lr = function (opts) {
    const P = opts.prefix || 'lr';
    const pairs = opts.pairs || [];
    const W = 54, H = 38, x0 = opts.x || 0, y0 = opts.y || 0;
    const items = [];
    items.push({ key: P + ':hs', kind: 'text', x: x0 + W / 2, y: y0 + 24, text: 'symbol', anchor: 'middle', cls: 'title' });
    items.push({ key: P + ':hq', kind: 'text', x: x0 + W + 6 + W / 2, y: y0 + 24, text: 'state', anchor: 'middle', cls: 'title' });
    pairs.forEach(([sym, st], i) => {
      const y = y0 - (i + 1) * (H + 4);
      const k = P + ':' + i + ':' + sym + ':' + st;
      const hot = (opts.hot || []).includes(i) ? ' hot' : '';
      items.push({ key: k + ':s', kind: 'cell', x: x0, y, w: W, h: H, text: sym === '' || sym === null || sym === undefined ? '' : sym, cls: 'mono stack' + hot, enter: 'drop', exit: 'rise' });
      items.push({ key: k + ':q', kind: 'cell', x: x0 + W + 6, y, w: W, h: H, text: st, cls: 'mono stack act' + hot, enter: 'drop', exit: 'rise' });
    });
    items.push({ key: P + ':base', kind: 'line', x1: x0 - 8, y1: y0 + 2, x2: x0 + 2 * W + 14, y2: y0 + 2 });
    return { items };
  };

  SK.demos = [
    { name: 'stack: push and pop', frames: () => {
      const st = [['$'], ['$', 'A'], ['$', 'A', 'A'], ['$', 'A']];
      const say = ['The stack starts with its bottom marker $.', 'Reading a pushes A.', 'Another a pushes another A.', 'Reading b pops an A.'];
      return st.map((s, i) => ({ items: SK.draw({ items: s, label: 'stack', x: 0, y: 0 }).items.concat(SK.draw({ items: s, label: 'as a row', dir: 'row', prefix: 'kr', x: 220, y: -40 }).items), say: say[i] }));
    } },
    { name: 'stack: an LR parser stack', frames: () => [
      { items: SK.lr({ pairs: [['', 0], ['E', 1], ['+', 6], ['T', 9]], hot: [3] }).items, say: 'An LR stack keeps a state above each symbol.' },
    ] },
  ];
})();
