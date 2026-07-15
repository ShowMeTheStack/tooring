// Puzzles from computability: Post correspondence dominoes (a set of tiles, and a sequence laid out with
// the top and bottom strings written out under it so a match or a mismatch shows) and Wang tiles placed
// on a grid, with clashing edges marked.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const DO = (K.dominoes = {});

  const domW = (t) => Math.max(58, Geo.textWidth(t.top, 16, { mono: true }) + 26, Geo.textWidth(t.bottom, 16, { mono: true }) + 26);
  const show = (s) => (s === '' ? 'ε' : s);

  /** The set of dominoes, numbered. opts: {tiles: [{top, bottom}], x, y, prefix, hot: [i], h} */
  DO.set = function (opts) {
    const P = opts.prefix || 'pcp';
    const H = opts.h || 78;
    let x = opts.x || 0;
    const y = opts.y || 0;
    const items = [];
    const hot = new Set(opts.hot || []);
    (opts.tiles || []).forEach((t, i) => {
      const w = domW({ top: show(t.top), bottom: show(t.bottom) });
      items.push({ key: P + ':d' + i, kind: 'domino', x, y, w, h: H, top: show(t.top), bottom: show(t.bottom), cls: hot.has(i) ? 'hot' : '', pick: true });
      items.push({ key: P + ':n' + i, kind: 'text', x: x + w / 2, y: y + H + 20, text: String(i + 1), anchor: 'middle', cls: 'strong' });
      x += w + 16;
    });
    return { items, box: { x: opts.x || 0, y, w: x - (opts.x || 0), h: H + 28 } };
  };

  /**
   * A sequence of dominoes laid side by side, then the top string and the bottom string written out under
   * it symbol by symbol, agreeing symbols green and the first disagreement red.
   * opts: {tiles, seq: [tile indexes], x, y, prefix}
   */
  DO.sequence = function (opts) {
    const P = opts.prefix || 'pq';
    const H = 78, x0 = opts.x || 0, y0 = opts.y || 0;
    const items = [];
    let x = x0;
    let top = '', bot = '';
    (opts.seq || []).forEach((ti, k) => {
      const t = opts.tiles[ti];
      const w = domW({ top: show(t.top), bottom: show(t.bottom) });
      items.push({ key: P + ':' + k + ':' + ti, kind: 'domino', x, y: y0, w, h: H, top: show(t.top), bottom: show(t.bottom), enter: 'drop' });
      items.push({ key: P + ':i:' + k + ':' + ti, kind: 'text', x: x + w / 2, y: y0 - 10, text: String(ti + 1), anchor: 'middle', cls: 'title' });
      x += w + 6;
      top += t.top; bot += t.bottom;
    });
    const n = Math.max(top.length, bot.length);
    const CW = 30, ry = y0 + H + 34;
    let bad = -1;
    for (let i = 0; i < Math.min(top.length, bot.length); i++) if (top[i] !== bot[i]) { bad = i; break; }
    items.push({ key: P + ':lt', kind: 'text', x: x0 - 12, y: ry + 22, text: 'top', anchor: 'end', cls: 'title' });
    items.push({ key: P + ':lb', kind: 'text', x: x0 - 12, y: ry + 22 + 40, text: 'bottom', anchor: 'end', cls: 'title' });
    for (let i = 0; i < n; i++) {
      const st = (row) => (i >= Math.min(top.length, bot.length) ? 'act' : bad >= 0 && i >= bad ? (i === bad ? 'bad' : 'gone') : 'good');
      if (i < top.length) items.push({ key: P + ':t:' + i, kind: 'cell', x: x0 + i * CW, y: ry, w: CW, h: 34, text: top[i], cls: 'mono ' + st('t'), rx: 3 });
      if (i < bot.length) items.push({ key: P + ':b:' + i, kind: 'cell', x: x0 + i * CW, y: ry + 40, w: CW, h: 34, text: bot[i], cls: 'mono ' + st('b'), rx: 3 });
    }
    const match = n > 0 && bad < 0 && top.length === bot.length;
    return { items, match, clash: bad >= 0, top, bottom: bot, box: { x: x0, y: y0 - 24, w: Math.max(x - x0, n * CW), h: H + 34 + 80 + 24 } };
  };

  /**
   * Wang tiles on a grid. opts: {tiles: [[n, e, s, w]] colour numbers, grid: [[tile index or null]],
   *   x, y, size, prefix, check: true (mark tiles whose edges clash with a neighbour)}
   */
  DO.wang = function (opts) {
    const P = opts.prefix || 'wg';
    const S = opts.size || 54, gap = 3;
    const items = [];
    const g = opts.grid || [];
    const at = (r, c) => (g[r] && g[r][c] !== null && g[r][c] !== undefined ? opts.tiles[g[r][c]] : null);
    g.forEach((row, r) => row.forEach((ti, c) => {
      const x = (opts.x || 0) + c * (S + gap), y = (opts.y || 0) + r * (S + gap);
      if (ti === null || ti === undefined) { items.push({ key: P + ':e:' + r + ',' + c, kind: 'cell', x, y, w: S, h: S, text: '', cls: 'gone', rx: 3 }); return; }
      const t = opts.tiles[ti];
      let clash = false;
      if (opts.check !== false) {
        const right = at(r, c + 1), below = at(r + 1, c), left = at(r, c - 1), above = at(r - 1, c);
        clash = (right && right[3] !== t[1]) || (below && below[0] !== t[2]) || (left && left[1] !== t[3]) || (above && above[2] !== t[0]);
      }
      items.push({ key: P + ':' + r + ',' + c, kind: 'tile', x, y, size: S, edges: t, cls: clash ? 'bad' : '', enter: 'drop' });
    }));
    return { items };
  };

  DO.demos = [
    { name: 'dominoes: a PCP instance and a partial match', frames: () => {
      const tiles = [{ top: 'b', bottom: 'ca' }, { top: 'a', bottom: 'ab' }, { top: 'ca', bottom: 'a' }, { top: 'abc', bottom: 'c' }];
      const set = DO.set({ tiles, y: -150 }).items;
      return [
        { items: set.concat(DO.sequence({ tiles, seq: [1], y: 0 }).items), say: 'Start with domino 2: top a, bottom ab.' },
        { items: set.concat(DO.sequence({ tiles, seq: [1, 0], y: 0 }).items), say: 'Then domino 1.' },
        { items: set.concat(DO.sequence({ tiles, seq: [1, 0, 2, 1, 3], y: 0 }).items), say: 'Five dominoes and the top and bottom read the same: a match.' },
      ];
    } },
    { name: 'dominoes: Wang tiles with a clash', frames: () => {
      const tiles = [[0, 1, 2, 3], [4, 3, 2, 1], [2, 1, 0, 3], [2, 3, 0, 1]];
      return [{ items: DO.wang({ tiles, grid: [[0, 1, 0], [2, 3, 2], [0, null, 1]] }).items, say: 'Neighbouring edges must have the same colour; the red tiles clash.' }];
    } },
  ];
})();
