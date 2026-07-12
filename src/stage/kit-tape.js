// Turing-machine tapes: a window of cells that scrolls smoothly as the head walks (cells are named by their
// place on the tape, so when the window moves they glide), the blank symbol, the head with the state's name
// on it, several tapes one above the other, a two-dimensional grid tape, and tracks (a cell holding one
// symbol per track) with marks for simulating many tapes on one.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = (T.Kit = T.Kit || {});
  const TP = (K.tape = {});
  TP.CELL = 46;
  TP.BLANK = '⊔';

  /**
   * Keeps the head inside a window of n cells, moving the window only when the head comes within margin
   * cells of an edge. Make one per tape for a whole run; at(head) gives the first cell shown.
   */
  TP.scroller = function (opts) {
    opts = opts || {};
    const n = opts.cells || 13, margin = opts.margin === undefined ? 2 : opts.margin;
    let origin = opts.origin === undefined ? -2 : opts.origin, prev = origin;
    return {
      n,
      at(head) {
        prev = origin;
        if (head < origin + margin) origin = head - margin;
        if (head > origin + n - 1 - margin) origin = head - (n - 1 - margin);
        return origin;
      },
      get prev() { return prev; },
      get origin() { return origin; },
    };
  };

  /** The symbol at an absolute place on a tape given as an array (or string) starting at `offset` */
  const symAt = (tape, offset, i, blank) => { const k = i - (offset || 0); const v = k >= 0 && k < tape.length ? tape[k] : undefined; return v === undefined || v === null || v === '' || v === '_' ? blank : v; };

  /**
   * One tape. opts: {tape: array or string, offset (the place of tape[0], default 0), head, state, blank,
   *   cells (window), origin (first place shown; from a scroller), prevOrigin, x, y, prefix, label,
   *   headCls, headSide: 'below'|'above', cls(i, sym) -> classes, tracks: k (cells hold arrays of k symbols),
   *   noHead, sub: true to number the cells}
   * Returns {items, box, cellX(i)}.
   */
  TP.draw = function (opts) {
    const P = opts.prefix || 't';
    const tape = typeof opts.tape === 'string' ? [...opts.tape] : (opts.tape || []);
    const blank = opts.blank || TP.BLANK;
    const n = opts.cells || 13;
    const head = opts.head || 0;
    const origin = opts.origin === undefined ? Math.min(head - 2, (opts.offset || 0) - 1) : opts.origin;
    const tracks = opts.tracks || 1;
    const CW = opts.cw || TP.CELL, CH = tracks > 1 ? 30 * tracks + 8 : (opts.ch || TP.CELL);
    const x0 = opts.x || 0, y0 = opts.y || 0;
    const items = [];
    const cellX = (i) => x0 + (i - origin) * CW;
    if (opts.label) items.push({ key: P + ':label', kind: 'text', x: x0 - 30, y: y0 + CH / 2 + 5, text: opts.label, anchor: 'end', cls: 'title' });
    for (let i = origin; i < origin + n; i++) {
      const v = symAt(tape, opts.offset, i, blank);
      const isBlank = v === blank;
      const lines = tracks > 1 ? [].concat(v === blank ? new Array(tracks).fill(blank) : v).map((s) => (s === undefined || s === null || s === '' ? ' ' : String(s))) : null;
      const cls = ['mono', isBlank ? 'blank' : '', i === head && !opts.noHead ? (opts.headCellCls || 'act') : '', opts.cls ? opts.cls(i, v) || '' : ''].filter(Boolean).join(' ');
      const it = { key: P + ':c:' + i, kind: 'cell', x: cellX(i), y: y0, w: CW, h: CH, cls, rx: 4 };
      if (lines) it.lines = lines; else it.text = v;
      if (opts.sub) it.sub = i;
      if (opts.prevOrigin !== undefined && opts.prevOrigin !== origin) { it.enter = 'fly'; it.from = { x: x0 + (i - opts.prevOrigin) * CW, y: y0 }; }
      items.push(it);
    }
    // the tape goes on for ever both ways
    items.push({ key: P + ':more-l', kind: 'text', x: x0 - 8, y: y0 + CH / 2 + 5, text: '⋯', anchor: 'end', cls: 'strong', layer: 'labels' });
    items.push({ key: P + ':more-r', kind: 'text', x: x0 + n * CW + 8, y: y0 + CH / 2 + 5, text: '⋯', anchor: 'start', cls: 'strong' });
    if (!opts.noHead) {
      const side = opts.headSide || 'below';
      items.push({ key: P + ':head', kind: 'head', x: cellX(head) + CW / 2, y: side === 'above' ? y0 - 2 : y0 + CH + 2, side, text: opts.state === undefined ? '' : String(opts.state), cls: opts.headCls || '' });
    }
    return { items, cellX: (i) => cellX(i) + CW / 2, box: { x: x0 - 30, y: y0 - 40, w: n * CW + 60, h: CH + 80 }, origin };
  };

  /**
   * Several tapes, one under the other, each with its own head. tapes: [{tape, head, offset, label}].
   * opts: {state (one state, shown on the first head), scrollers (one per tape), x, y, prefix, cells}
   */
  TP.multi = function (tapes, opts) {
    opts = opts || {};
    const items = [];
    const gap = (opts.ch || TP.CELL) + 64;
    tapes.forEach((t, k) => {
      const sc = opts.scrollers && opts.scrollers[k];
      const origin = sc ? sc.at(t.head) : t.origin;
      const r = TP.draw(Object.assign({}, opts, t, { prefix: (opts.prefix || 'mt') + k, y: (opts.y || 0) + k * gap, origin, prevOrigin: sc ? sc.prev : undefined, label: t.label || 'tape ' + (k + 1), state: k === 0 ? opts.state : t.state === undefined ? (k + 1) : t.state, headCls: k === 0 ? opts.headCls : 'read' }));
      items.push(...r.items);
    });
    return { items };
  };

  /**
   * A two-dimensional tape. opts: {cells: {'x,y': sym} or rows [[sym]], head: {x, y}, state, window:
   * {x0, y0, w, h} (the part shown), x, y, prefix, blank, cs (cell size)}. The head's cell is lit, and the
   * state is written above the grid with an arrow down to the column.
   */
  TP.grid = function (opts) {
    const P = opts.prefix || 'g2';
    const blank = opts.blank || TP.BLANK;
    const S = opts.cs || 44;
    const win = opts.window || { x0: 0, y0: 0, w: 7, h: 5 };
    const get = (x, y) => {
      if (Array.isArray(opts.cells)) { const r = opts.cells[y]; const v = r ? r[x] : undefined; return v === undefined || v === null || v === '' ? blank : v; }
      const v = opts.cells && opts.cells[x + ',' + y]; return v === undefined || v === null || v === '' ? blank : v;
    };
    const items = [];
    const X = opts.x || 0, Y = opts.y || 0;
    for (let j = 0; j < win.h; j++) for (let i = 0; i < win.w; i++) {
      const gx = win.x0 + i, gy = win.y0 + j;
      const v = get(gx, gy);
      const at = opts.head && opts.head.x === gx && opts.head.y === gy;
      items.push({ key: P + ':c:' + gx + ',' + gy, kind: 'cell', x: X + i * S, y: Y + j * S, w: S, h: S, rx: 3, text: v, cls: 'mono' + (v === blank ? ' blank' : '') + (at ? ' act' : '') });
    }
    if (opts.head) {
      const hx = X + (opts.head.x - win.x0) * S + S / 2;
      items.push({ key: P + ':head', kind: 'head', x: hx, y: Y - 2, side: 'above', text: opts.state === undefined ? '' : String(opts.state) });
    }
    return { items, box: { x: X, y: Y - 40, w: win.w * S, h: win.h * S + 40 } };
  };

  TP.demos = [
    { name: 'tape: a head walking right and scrolling', frames: () => {
      const tape = [...'0110'];
      const sc = TP.scroller({ cells: 9, origin: -2 });
      const fr = [];
      const states = ['scan', 'scan', 'scan', 'scan', 'scan', 'back'];
      for (let h = 0; h <= 5; h++) {
        const origin = sc.at(h);
        fr.push({ items: TP.draw({ tape, head: h, state: states[h], origin, prevOrigin: sc.prev, cells: 9, label: 'tape' }).items, say: 'The head is on cell ' + h + ', in state ' + states[h] + '.' });
      }
      return fr;
    } },
    { name: 'tape: two tapes and a track-marked tape', frames: () => {
      const m = TP.multi([{ tape: 'abba', head: 1 }, { tape: 'ab', head: 2 }], { state: 'copy', cells: 8 }).items;
      const tr = TP.draw({ tape: [['a', ' '], ['b', '▲'], ['b', ' '], ['a', ' ']], tracks: 2, head: 1, state: 'q', cells: 8, prefix: 'tk', y: 260, label: 'tracks', origin: -2 }).items;
      return [{ items: m.concat(tr), say: 'Two tapes with their own heads; below them one tape with two tracks, the second marking where a simulated head is.' }];
    } },
    { name: 'tape: a two-dimensional tape', frames: () => [
      { items: TP.grid({ cells: { '1,1': 'x', '2,1': 'x', '3,2': 'o' }, head: { x: 2, y: 1 }, state: 'q2', window: { x0: 0, y0: 0, w: 6, h: 4 } }).items, say: 'A grid tape: the head can also move up and down.' },
    ] },
  ];
})();
