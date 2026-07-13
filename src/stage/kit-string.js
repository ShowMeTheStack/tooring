// Input strings: a row of symbols with a read head under the next one, the consumed part greyed, brackets
// that split the string into parts (x y z for the pumping lemma, u v x y z for its context-free cousin)
// with their lengths, and pumping, where the middle part is repeated and each copy grows out of it.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const ST = (K.string = {});

  const syms = (s) => (Array.isArray(s) ? s.map(String) : [...String(s === undefined || s === null ? '' : s)]);
  const widthOf = (list, min) => Math.max(min || 40, ...list.map((t) => Geo.textWidth(t, 17, { mono: true }) + 18));

  /**
   * An input string. opts: {text (string or array of symbols), pos (the next symbol to read; null for no
   *   head), x, y, prefix, cw, consumed (grey what is read, default true), head: 'below' | 'above' | false,
   *   headText, headCls, label, cls(i, sym) -> classes, brackets: [{from, to (exclusive), text, cls, side,
   *   level}], sub: true (number the cells)}
   * Cells are named by their index, so a string that changes keeps the symbols that stay.
   * Returns {items, box, cellX(i)}.
   */
  ST.draw = function (opts) {
    const P = opts.prefix || 's';
    const s = syms(opts.text);
    const CW = opts.cw || widthOf(s), CH = opts.ch || 44;
    const x0 = opts.x || 0, y0 = opts.y || 0;
    const items = [];
    const pos = opts.pos;
    if (opts.label) items.push({ key: P + ':label', kind: 'text', x: x0 - 14, y: y0 + CH / 2 + 5, text: opts.label, anchor: 'end', cls: 'title' });
    if (!s.length) items.push({ key: P + ':eps', kind: 'cell', x: x0, y: y0, w: CW, h: CH, text: 'ε', cls: 'mono empty' });
    s.forEach((c, i) => {
      const cls = ['mono', opts.consumed !== false && pos !== null && pos !== undefined && i < pos ? 'read' : '', i === pos ? 'hot' : '', opts.cls ? opts.cls(i, c) || '' : ''].filter(Boolean).join(' ');
      const it = { key: P + ':c:' + i, kind: 'cell', x: x0 + i * CW, y: y0, w: CW, h: CH, text: c, cls, pick: true };
      if (opts.sub) it.sub = i + 1;
      items.push(it);
    });
    const subPad = opts.sub ? 18 : 0;
    let bottom = y0 + CH + subPad;
    if (pos !== null && pos !== undefined && opts.head !== false) {
      const side = opts.head || 'below';
      // at the end of the string the head points just past the last symbol
      const hx = x0 + Math.min(pos, Math.max(s.length, 1)) * CW + (pos >= s.length ? 4 : CW / 2);
      items.push({ key: P + ':head', kind: 'head', x: hx, y: side === 'above' ? y0 - 2 : y0 + CH + 2 + subPad, side, text: opts.headText === undefined ? (pos >= s.length ? 'end' : 'next') : String(opts.headText), cls: opts.headCls || 'read' });
      if (side !== 'above') bottom += 40;
    }
    let top = y0 - (opts.head === 'above' ? 40 : 0);
    for (const b of opts.brackets || []) {
      const side = b.side || 'below', lvl = b.level || 0;
      const y = side === 'above' ? top - 6 - lvl * 40 : bottom + 8 + lvl * 44;
      items.push({ key: P + ':br:' + (b.id || b.text), kind: 'bracket', x1: x0 + b.from * CW, x2: x0 + Math.max(b.from, b.to) * CW, y, side, text: b.text, cls: b.cls || '' });
    }
    const nb = (opts.brackets || []).filter((b) => (b.side || 'below') === 'below');
    if (nb.length) bottom += 8 + (Math.max(...nb.map((b) => b.level || 0)) + 1) * 44;
    return { items, box: { x: x0, y: top, w: Math.max(1, s.length) * CW, h: bottom - top }, cellX: (i) => x0 + i * CW + CW / 2, cw: CW };
  };

  /**
   * A string split as x y z and pumped: x, then y written i times, then z. opts: {x, y, z (strings), i,
   *   prefix, at: {x, y} (position), names: ['x', 'y', 'z'] (or the five of u v x y z with parts: [..])}
   * Copies of y are named by their copy number, so going from i to i + 1 adds a copy that grows out of y.
   */
  ST.pump = function (opts) {
    const P = opts.prefix || 'pm';
    const parts = opts.parts || [{ name: 'x', text: opts.x || '' }, { name: 'y', text: opts.y || '', pump: true }, { name: 'z', text: opts.z || '' }];
    const i = opts.i === undefined ? 1 : opts.i;
    const all = [].concat(...parts.map((p) => syms(p.text)));
    const CW = opts.cw || widthOf(all.length ? all : ['a']);
    const x0 = opts.at ? opts.at.x : 0, y0 = opts.at ? opts.at.y : 0;
    const items = [];
    let k = 0;
    const brackets = [];
    const cls = { x: 'part-x', y: 'part-y', z: 'part-z', u: 'part-z', v: 'part-y', w: 'part-x' };
    parts.forEach((p, pi) => {
      const s = syms(p.text);
      const copies = p.pump ? i : 1;
      for (let c = 0; c < copies; c++) {
        const start = k;
        s.forEach((ch, j) => {
          const it = { key: P + ':' + pi + ':' + c + ':' + j, kind: 'cell', x: x0 + k * CW, y: y0, w: CW, h: 44, text: ch, cls: 'mono ' + (p.cls || cls[p.name] || ''), enter: c > 0 ? 'from' : undefined, src: c > 0 ? P + ':' + pi + ':' + (c - 1) + ':' + j : undefined, exit: 'into', into: P + ':' + pi + ':0:' + j };
          items.push(it);
          k++;
        });
        if (p.pump && s.length) brackets.push({ id: pi + ':' + c, from: start, to: k, text: p.name + (copies > 1 ? ' (' + (c + 1) + ')' : ''), cls: p.name === 'y' || p.name === 'v' ? 'y' : 'x' });
      }
      if (!p.pump || !s.length) brackets.push({ id: String(pi), from: k - s.length, to: k, text: p.name + (s.length ? '' : ' = ε'), cls: p.name === 'x' || p.name === 'u' ? 'x' : 'z' });
      if (p.pump && !s.length) { /* nothing to draw */ }
    });
    if (!k) items.push({ key: P + ':eps', kind: 'cell', x: x0, y: y0, w: CW, h: 44, text: 'ε', cls: 'mono empty' });
    for (const b of brackets) if (b.to > b.from) items.push({ key: P + ':br:' + b.id, kind: 'bracket', x1: x0 + b.from * CW, x2: x0 + b.to * CW, y: y0 + 52, side: 'below', text: b.text, cls: b.cls });
    return { items, box: { x: x0, y: y0, w: Math.max(1, k) * CW, h: 96 }, length: k };
  };

  ST.demos = [
    { name: 'string: reading with a head', frames: () => {
      const s = 'abba';
      return [0, 1, 2, 4].map((p) => ({ items: ST.draw({ text: s, pos: p, label: 'input', sub: true }).items, say: p < s.length ? 'Next to read: ' + s[p] + '.' : 'The whole input is read.' }));
    } },
    { name: 'string: x y z with lengths, then pumped', frames: () => [
      { items: ST.draw({ text: 'aaabbb', brackets: [{ from: 0, to: 1, text: 'x, |x| = 1', cls: 'x' }, { from: 1, to: 3, text: 'y, |y| = 2', cls: 'y' }, { from: 3, to: 6, text: 'z', cls: 'z' }] }).items, say: 'The string split as x y z.' },
      { items: ST.pump({ x: 'a', y: 'aa', z: 'abbb', i: 2 }).items, say: 'Pumped with i = 2: x y y z.' },
      { items: ST.pump({ x: 'a', y: 'aa', z: 'abbb', i: 3 }).items, say: 'And with i = 3.' },
    ] },
  ];
})();
