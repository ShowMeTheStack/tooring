// Helpers shared by the topics of part 2 (finite automata and regular languages): machines between the
// text the student types, the engines' form and the diagram form; the definition panel (the tuple and the
// transition table, with an NFA's sets); the language pyramid (every string up to a length, accepted ones
// lit); small captions and notes on the stage; and checks with friendly messages.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const R = (T.Reg = T.Reg || {});

  R.w = (w) => (w === '' || w === undefined || w === null ? 'ε' : String(w));
  R.set = (xs) => (xs && xs.length ? '{' + xs.join(', ') + '}' : '∅');
  R.sym = (a) => (a === '' ? 'ε' : a);
  R.plural = (n, w, ws) => n + ' ' + (n === 1 ? w : ws || w + 's');

  /** Machine text (or the diagram form) to the engines' form {states, alphabet, start, accept, trans: [{from, sym, to}]} */
  R.fa = function (text, alphabet) {
    const m = typeof text === 'string' ? T.Machine.parse(text) : text;
    const spec = { states: m.states, start: m.start, accept: m.accept, trans: T.Machine.moves(m) };
    if (alphabet) spec.alphabet = [...new Set([...alphabet, ...spec.trans.map((e) => e.sym).filter(Boolean)])].sort();
    return T.FA.make(spec);
  };
  /** The engines' form to the diagram form the drawing kit reads (labels merged per edge, ε first) */
  R.dia = function (fa) {
    const by = new Map();
    const ord = (a) => (a === '' ? -1 : fa.alphabet.indexOf(a));
    for (const e of fa.trans) {
      const k = e.from + '>' + e.to;
      if (!by.has(k)) by.set(k, { from: e.from, to: e.to, syms: [] });
      if (!by.get(k).syms.includes(e.sym)) by.get(k).syms.push(e.sym);
    }
    const trans = [...by.values()].map((g) => ({ from: g.from, to: g.to, label: g.syms.sort((x, y) => ord(x) - ord(y)).map(R.sym).join(', ') }));
    return { kind: T.FA.kind(fa) === 'dfa' ? 'dfa' : 'nfa', states: fa.states.slice(), start: fa.start, accept: fa.accept.slice(), trans, pos: {} };
  };
  /** Machine text from the engines' form (for presets built by code) */
  R.text = (fa) => T.Machine.format(R.dia(fa));

  /**
   * A machine input. o: {id, label, def, kind: 'dfa' | 'nfa' | 'any', max (states), eps (ε-moves allowed,
   * default true for nfa), complete (a DFA must have every move)}
   */
  R.machineInput = function (o) {
    const max = o.max || 8;
    return {
      id: o.id || 'm', kind: 'machine', machine: o.kind === 'dfa' ? 'dfa' : 'nfa', label: o.label || 'Machine', def: o.def,
      check: (v) => {
        const m = T.Machine.parse(v);
        const L = o.label || 'Machine';
        if (m.kind !== 'dfa' && m.kind !== 'nfa') return L + ': a finite automaton, with rules like q0 -a-> q1';
        if (o.kind === 'dfa' && !T.Machine.isDeterministic(m)) return L + ': a DFA has one move per state and symbol and no ε moves';
        if (o.eps === false && T.Machine.moves(m).some((x) => x.sym === '')) return L + ': no ε-moves here (write them out as symbol moves)';
        if (m.states.length > max) return L + ': at most ' + max + ' states, so the picture stays readable';
        const bad = T.Machine.moves(m).find((x) => x.sym.length > 1 || x.sym === 'ε');
        if (bad) return L + ': each move reads one symbol, but ' + bad.from + ' → ' + bad.to + ' reads "' + bad.sym + '"';
        if (o.complete) { const f = R.fa(v); const miss = T.FA.missing(f); if (miss.length) return L + ': every state needs a move on every symbol (' + miss[0].state + ' has none on ' + miss[0].sym + ')'; }
        if (!T.Machine.alphabet(m).length) return L + ': the machine reads no symbols at all';
        return null;
      },
    };
  };
  /** A topic check: the string input w uses only the machine m's symbols */
  R.alphaCheck = (mId, wId, label) => (inp) => {
    const al = T.Machine.alphabet(T.Machine.parse(inp[mId || 'm']));
    const bad = [...(inp[wId || 'w'] || '')].find((c) => !al.includes(c));
    return bad !== undefined ? (label || 'Input') + ': "' + bad + '" is not in the machine\'s alphabet {' + al.join(', ') + '}' : null;
  };

  // ---- the definition panel --------------------------------------------------------------------------------
  /** The five-tuple as a math section */
  R.tuple = (fa, title, id) => ({ id: id || 'tuple', kind: 'math', title: title || 'The machine', text: 'Q  = ' + R.set(fa.states) + '\nΣ  = ' + R.set(fa.alphabet) + '\nq₀ = ' + fa.start + '\nF  = ' + R.set(fa.accept) });
  /**
   * The transition table: a DFA's cells hold one state, an NFA's a set (and there is an ε column when it
   * has ε-moves). Returns {section, rc(q, a)} where rc names the cell to light.
   */
  R.delta = function (fa, opts) {
    opts = opts || {};
    const eps = fa.trans.some((e) => e.sym === '');
    const cols = (eps ? [''] : []).concat(fa.alphabet);
    const dfa = T.FA.kind(fa) === 'dfa';
    const rows = fa.states.map((q) => cols.map((a) => {
      const to = fa.trans.filter((e) => e.from === q && e.sym === a).map((e) => e.to);
      return dfa ? (to[0] || '') : to.length ? R.set(to) : '∅';
    }));
    const section = { id: opts.id || 'delta', kind: 'table', title: opts.title || 'Transition function δ', corner: 'δ', colHead: cols.map(R.sym), rowHead: fa.states.map((q) => (q === fa.start ? '→ ' : '') + (fa.accept.includes(q) ? '* ' : '') + q), rows, emptyText: '–' };
    return { section, rc: (q, a) => fa.states.indexOf(q) + ',' + cols.indexOf(a), row: (q) => String(fa.states.indexOf(q)) };
  };

  // ---- strings ------------------------------------------------------------------------------------------------
  /** Every string over the alphabet of length 0..n, in shortlex order */
  R.upTo = function (alphabet, n) {
    const out = [''];
    let level = [''];
    for (let k = 1; k <= n; k++) { level = level.flatMap((w) => alphabet.map((a) => w + a)); out.push(...level); }
    return out;
  };
  /**
   * The language pyramid: a row per length with every string of that length, accepted ones lit.
   * o: {alphabet, maxLen, member(w) -> true | false | 'cls', x (centre), y (top), prefix, cls(w) -> extra
   *   classes, label, cw}. Strings are keyed by themselves so a recolouring glides.
   */
  R.pyramid = function (o) {
    const P = o.prefix || 'py';
    const rows = [];
    for (let k = 0; k <= o.maxLen; k++) rows.push(R.upTo(o.alphabet, k).filter((w) => [...w].length === k));
    const cw = o.cw || Math.max(40, Geo.textWidth('x'.repeat(o.maxLen), 15, { mono: true }) + 16), ch = 34, gap = 6;
    const widest = Math.max(...rows.map((r) => r.length)) * (cw + gap) - gap;
    const items = [];
    const x0 = (o.x || 0) - widest / 2, y0 = o.y || 0;
    if (o.label) items.push({ key: P + ':label', kind: 'text', x: o.x || 0, y: y0 - 12, text: o.label, anchor: 'middle', cls: 'title' });
    rows.forEach((r, k) => {
      const w = r.length * (cw + gap) - gap;
      r.forEach((s, i) => {
        const m = o.member ? o.member(s) : false;
        const cls = ['mono', m === true ? 'good' : typeof m === 'string' ? m : '', o.cls ? o.cls(s) || '' : ''].filter(Boolean).join(' ');
        items.push({ key: P + ':w:' + (s === '' ? 'ε' : s), kind: 'cell', x: x0 + (widest - w) / 2 + i * (cw + gap), y: y0 + k * (ch + gap), w: cw, h: ch, text: R.w(s), cls, size: 14, pick: true });
      });
    });
    return { items, box: { x: x0, y: y0 - (o.label ? 24 : 0), w: widest, h: rows.length * (ch + gap) - gap + (o.label ? 24 : 0) }, key: (s) => P + ':w:' + (s === '' ? 'ε' : s) };
  };

  // ---- small things on the stage ------------------------------------------------------------------------------
  /** A caption: one line of text, centred by default */
  R.caption = (key, x, y, text, cls, anchor) => ({ key, kind: 'text', x, y, text, anchor: anchor || 'middle', cls: cls || 'strong' });
  /**
   * A note: a panel with a title and lines of text. o: {x, y (top-left), title, lines, w, mono, cls}
   * Returns {items, box}.
   */
  R.note = function (key, o) {
    const lines = o.lines || [];
    const fs = o.size || 15;
    // titles are drawn in capitals with letter spacing
    const title = String(o.title || '').toUpperCase();
    const tw = Math.max(Geo.textWidth(title, 13, { bold: true }) + title.length * 0.8 + 4, ...lines.map((l) => Geo.textWidth(l, fs, { mono: o.mono, bold: true })));
    const w = o.w || tw + 28, lh = fs + 9;
    const h = (o.title ? 30 : 12) + lines.length * lh + 6;
    const items = [{ key: key, kind: 'region', x: o.x, y: o.y, w, h, cls: 'panel' + (o.cls ? ' ' + o.cls : ''), rx: 12 }];
    if (o.title) items.push({ key: key + ':t', kind: 'text', x: o.x + 14, y: o.y + 21, text: o.title, cls: 'title' });
    lines.forEach((l, i) => items.push({ key: key + ':l' + i, kind: 'text', x: o.x + 14, y: o.y + (o.title ? 30 : 12) + i * lh + fs * 0.95, text: l, cls: (o.mono ? 'mono' : 'strong') + (o.lineCls && o.lineCls[i] ? ' ' + o.lineCls[i] : ''), size: fs }));
    return { items, box: { x: o.x, y: o.y, w, h } };
  };
  /** A verdict line: accepted / rejected, in colour */
  R.verdict = (key, x, y, ok, text) => ({ key, kind: 'text', x, y, text, anchor: 'middle', cls: 'big ' + (ok ? 'good' : 'bad') });

  /** The box around a list of stage items (bent edges and loops included), with no margin */
  R.bounds = (items) => T.stageBounds(items, { margin: 0, minW: 1, minH: 1 });
  /** Move stage items by (dx, dy): positions of shapes, cells, texts, lines and edge labels */
  R.shift = function (items, dx, dy) {
    return items.map((it) => {
      const o = Object.assign({}, it);
      for (const k of ['x', 'lx', 'x1', 'x2', 'tx']) if (typeof o[k] === 'number') o[k] += dx;
      for (const k of ['y', 'ly', 'y1', 'y2', 'ty']) if (typeof o[k] === 'number') o[k] += dy;
      for (const k of ['from', 'to']) if (o[k] && typeof o[k] === 'object') o[k] = { x: o[k].x + dx, y: o[k].y + dy };
      return o;
    });
  };

  /** Positions on a circle, the first at the top (or at angle a0), clockwise */
  R.ring = function (names, cx, cy, rad, a0) {
    const pos = {};
    const n = names.length;
    names.forEach((q, i) => { const a = (a0 === undefined ? -Math.PI / 2 : a0) + (2 * Math.PI * i) / Math.max(1, n); pos[q] = { x: cx + Math.cos(a) * rad, y: cy + Math.sin(a) * rad }; });
    return pos;
  };
  /** Positions in a row */
  R.row = function (names, x0, y, gap) { const pos = {}; names.forEach((q, i) => { pos[q] = { x: x0 + i * gap, y }; }); return pos; };

  /** Run a DFA (partial allowed): the states visited and where it got stuck (-1 if never) */
  R.runDFA = function (fa, w) {
    const d = T.FA._deltaMap(fa);
    const path = [fa.start];
    let q = fa.start, stuck = -1;
    const s = [...w];
    for (let i = 0; i < s.length; i++) { const r = d.get(q) && d.get(q).get(s[i]); if (r === undefined) { stuck = i; break; } q = r; path.push(q); }
    return { path, stuck, accept: stuck < 0 && fa.accept.includes(q), end: q };
  };
  /** The states an NFA can be in after each prefix of w (with ε-closures): [set after 0 symbols, after 1, ...] */
  R.clouds = function (fa, w) {
    const r = T.FA.run(fa, w);
    return r.trace.filter((s) => s.kind === 'start' || s.kind === 'read' || s.kind === 'stuck').map((s) => s.states);
  };
  /** Options for a "how many" prediction: the answer and its neighbours, at least 0 */
  R.numberOptions = (n, extra) => { const s = new Set([n, n + 1, Math.max(0, n - 1), n + 2].concat(extra || [])); return [...s].sort((a, b) => a - b).map(String); };
})();
