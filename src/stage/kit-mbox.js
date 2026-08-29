// Machines as boxes: the block diagrams of computability. A machine is a rounded box with its name, its
// program written inside line by line (the line running now lit), boxes for the machines it runs inside it,
// an arrow carrying its input in from the left, and its possible answers (accept, reject, loops) as lamps
// on the right, the one it gives lit. Deciders, the diagonal machine D, the machines a reduction writes
// down and the oracle a Turing reduction asks are all drawn with it.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const K = (T.Kit = T.Kit || {});
  const MB = (K.mbox = {});

  const LH = 27, FS = 15, PAD = 18, BAND = 34;
  const lineW = (s, mono) => Geo.textWidth(s, FS, { mono });

  /** The size a box will take, without drawing it: {w, h} */
  MB.measure = function (opts) {
    const lines = opts.lines || [];
    const inner = (opts.inner || []).map(MB.measure);
    const w = Math.max(opts.w || 0, Geo.textWidth(opts.title || '', 13, { bold: true }) + 40 + (opts.tag ? Geo.textWidth(opts.tag, 12, { bold: true }) + 30 : 0),
      ...lines.map((l) => lineW(l, opts.mono) + 2 * PAD + 6), ...inner.map((b) => b.w + 2 * PAD), opts.room ? opts.room.w + 2 * PAD : 0);
    const h = BAND + lines.length * LH + inner.reduce((a, b) => a + b.h + 12, 0) + (opts.room ? opts.room.h + 12 : 0) + (lines.length || inner.length || opts.room ? 10 : 6);
    return { w: Math.ceil(w), h: Math.ceil(h) };
  };

  /**
   * One machine box. opts: {prefix, x, y, w (at least), title, tag (a small word on the right of the title
   *   band: 'decider', 'oracle'), lines: [text], hot: [line indexes lit], done: [indexes ticked], bad: [indexes
   *   marked wrong], cls (region colour r0..r5, 'hot' for a lit border), mono (lines in monospace),
   *   inner: [box options] (machines it runs, drawn inside below its lines), input: text on an arrow coming in
   *   from the left (inCls), outs: [{id, text, cls ('good' | 'bad' | 'hot'), lit, dim}] lamps on the right,
   *   outGap (length of the arrows out), inLen (length of the arrow in), room: {w, h} (space kept free
   *   under the lines and inner boxes, for a picture the topic draws there itself), enter}
   * Returns {items, box (the machine itself), all (with arrows and lamps), inPt, out: {id: key of its lamp},
   *   outBox: {id: box}, room: {x, y, w, h} (where the free space is), lineY(i)}.
   */
  MB.draw = function (opts) {
    const P = opts.prefix || 'mb';
    const x = opts.x || 0, y = opts.y || 0;
    const m = MB.measure(opts);
    const W = m.w, H = m.h;
    const items = [];
    const hot = new Set(opts.hot || []), done = new Set(opts.done || []), bad = new Set(opts.bad || []);
    items.push({ key: P + ':box', kind: 'region', x, y, w: W, h: H, text: opts.title || '', cls: 'mbox ' + (opts.cls || 'r0'), rx: 14, enter: opts.enter });
    if (opts.tag) {
      const tw = Geo.textWidth(opts.tag, 12, { bold: true }) + 18;
      items.push({ key: P + ':tag', kind: 'cell', x: x + W - tw - 10, y: y + 7, w: tw, h: 22, text: opts.tag, size: 12, cls: 'mtag ' + (opts.tagCls || ''), rx: 11 });
    }
    const lineY = (i) => y + BAND + i * LH + 18;
    (opts.lines || []).forEach((l, i) => {
      const cls = hot.has(i) ? 'hot' : bad.has(i) ? 'bad' : done.has(i) ? 'done' : '';
      if (cls) items.push({ key: P + ':lb' + i, kind: 'region', x: x + 8, y: lineY(i) - 18, w: W - 16, h: LH - 2, text: '', cls: 'mline ' + cls, rx: 6, audit: 'overlap-ok' });
      items.push({ key: P + ':l' + i, kind: 'text', x: x + PAD, y: lineY(i), text: l, cls: 'mcode' + (opts.mono ? ' mono' : '') + (cls ? ' ' + cls : '') });
    });
    let cy = y + BAND + (opts.lines || []).length * LH + 4;
    const innerOut = [];
    (opts.inner || []).forEach((o, k) => {
      const r = MB.draw(Object.assign({}, o, { prefix: o.prefix || P + ':in' + k, x: x + PAD, y: cy, w: Math.max(o.w || 0, W - 2 * PAD) }));
      items.push(...r.items);
      innerOut.push(r);
      cy += r.box.h + 12;
    });
    const room = opts.room ? { x: x + (W - opts.room.w) / 2, y: cy + 4, w: opts.room.w, h: opts.room.h } : null;
    const box = { x, y, w: W, h: H };
    const all = [box];
    const midY = y + Math.min(H / 2, BAND + 40);
    let inPt = { x, y: midY };
    if (opts.input !== undefined && opts.input !== null) {
      const len = Math.max(opts.inLen || 0, Geo.textWidth(opts.input, 15, { bold: true }) + 34, 70);
      items.push({ key: P + ':in', kind: 'edge', from: { x: x - len, y: midY }, to: { x: x - 2, y: midY }, label: opts.input, lx: x - len / 2 - 2, ly: midY - 15, cls: 'mflow ' + (opts.inCls || '') });
      all.push({ x: x - len, y: midY - 28, w: len, h: 30 });
      inPt = { x: x - len, y: midY };
    }
    const out = {}, outBox = {};
    const outs = opts.outs || [];
    if (outs.length) {
      const gap = opts.outGap || 64, OH = 34, SP = 14;
      const tot = outs.length * OH + (outs.length - 1) * SP;
      let oy = Math.max(y + 6, y + H / 2 - tot / 2);
      for (const o of outs) {
        const ow = Math.max(84, Geo.textWidth(o.text, 15, { bold: true }) + 28);
        const ox = x + W + gap;
        const k = P + ':o:' + o.id;
        const lit = !!o.lit;
        items.push({ key: k, kind: 'cell', x: ox, y: oy, w: ow, h: OH, text: o.text, rx: 17, cls: 'lamp ' + (o.cls || '') + (lit ? ' lit' : '') + (o.dim ? ' off' : ''), enter: opts.enter });
        items.push({ key: k + ':a', kind: 'edge', from: { x: x + W + 2, y: Math.max(y + 12, Math.min(y + H - 12, oy + OH / 2)) }, to: k, cls: 'mflow' + (lit ? ' ' + (o.cls || 'hot') : ' soft'), head: true });
        out[o.id] = k;
        outBox[o.id] = { x: ox, y: oy, w: ow, h: OH };
        all.push(outBox[o.id]);
        oy += OH + SP;
      }
    }
    return { items, box, all: Geo.union(all), inPt, out, outBox, inner: innerOut, room, lineY };
  };

  /** The usual answers of a machine: accept, reject and (optionally) loops, with the one given lit */
  MB.answers = function (given, opts) {
    opts = opts || {};
    const list = [{ id: 'accept', text: opts.acceptText || 'accept', cls: 'good' }, { id: 'reject', text: opts.rejectText || 'reject', cls: 'bad' }];
    if (opts.loop) list.push({ id: 'loop', text: opts.loopText || 'loops ∞', cls: 'hot' });
    return list.map((o) => Object.assign(o, { lit: given === o.id, dim: given !== undefined && given !== null && given !== o.id }));
  };

  /** A plain arrow between two points or keys, for wiring boxes together. opts: {label, lx, ly, cls, bend} */
  MB.wire = function (key, from, to, opts) {
    opts = opts || {};
    const it = { key, kind: 'edge', from, to, cls: 'mflow ' + (opts.cls || ''), bend: opts.bend || 0 };
    if (opts.label) { it.label = opts.label; it.lx = opts.lx; it.ly = opts.ly; }
    return it;
  };

  MB.demos = [
    { name: 'machine box: a decider with its program and answers', frames: () => {
      const base = { title: 'Decider for E_DFA', tag: 'decider', input: '⟨D⟩', lines: ['1. Mark the start state.', '2. Repeat: mark every state a marked state reaches.', '3. If an accepting state is marked, reject; else accept.'] };
      return [
        { items: MB.draw(Object.assign({}, base, { hot: [0], outs: MB.answers() })).items, say: 'The decider reads ⟨D⟩ and starts on line 1.' },
        { items: MB.draw(Object.assign({}, base, { done: [0, 1], hot: [2], outs: MB.answers('accept') })).items, say: 'No accepting state was marked: it accepts, so L(D) is empty.' },
      ];
    } },
    { name: 'machine box: a machine that runs another inside it', frames: () => [
      { items: MB.draw({ title: 'M′', input: 'x', lines: ['On input x:'], inner: [{ title: 'run M on x', cls: 'r2', lines: ['accepts → accept', 'rejects → loop forever'], hot: [1] }], outs: MB.answers('loop', { loop: true }) }).items, say: 'M′ runs M inside it and turns a rejection into an endless loop.' },
    ] },
  ];
})();
