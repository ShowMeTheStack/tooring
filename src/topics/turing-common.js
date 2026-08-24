// Shared pieces for the part 5 topics (Turing machines and other models): reading machine text into the
// core engine, a step-by-step run that keeps every configuration, the diagram form of a machine with its
// rules merged per edge, the transition table for the definition panel, tapes drawn from configurations,
// program listings with the line being run lit, and plain-English narration of a move.
// Topics call these only inside run(), so the order the files load in does not matter.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const TK = (T.TK = T.TK || {});
  const BL = '⊔';
  TK.BL = BL;

  /** A symbol as drawn: the blank _ becomes ⊔ (a machine with another blank, such as 0, keeps it) */
  TK.sym = (s) => (s === '_' || s === '' || s === undefined || s === null ? BL : s);
  TK.word = (list) => (list.length ? list.map(TK.sym).join('') : 'ε');
  const MOVE = { L: 'moves left', R: 'moves right', S: 'stays put', U: 'moves up', D: 'moves down' };
  TK.moveWord = (m) => MOVE[m] || m;

  // ---- machine text --------------------------------------------------------------------------------------
  /**
   * Text in either of the two forms (the diagram editor's, with "start q0" and "at q x y", or the engine's,
   * with "start: q0") read by the engine. Returns {M, errors: [messages]}.
   */
  TK.compile = function (text) {
    const lines = String(text || '').split('\n').map((l) => l.replace(/\/\/.*$/, '').trim()).filter((l) => l && !/^at\s/i.test(l) && !/^kind\s*:?\s*tm$/i.test(l))
      .map((l) => (l.includes('->') || l.includes('→') || /^[A-Za-z]+\s*:/.test(l) ? l : l.replace(/^([A-Za-z]+)\s+/, '$1: ')));
    const r = T.tm.parse(lines.join('\n'));
    return { M: r.machine, errors: r.errors.map((e) => (e.line ? 'line ' + e.line + ': ' : '') + e.msg) };
  };
  /** A friendly error for machine text, or null. want: {tapes, deterministic, maxStates, mode} */
  TK.checkMachine = function (text, want, label) {
    want = want || {};
    const L = (label || 'Machine') + ': ';
    const { M, errors } = TK.compile(text);
    if (errors.length) return L + errors[0];
    if (!M) return L + 'cannot be read';
    if (want.tapes && M.k !== want.tapes) return L + 'this picture needs ' + (want.tapes === 1 ? 'a one-tape machine' : 'a machine with ' + want.tapes + ' tapes') + ', not ' + M.k;
    if (want.deterministic && !M.deterministic) { const k = [...M.delta.entries()].find(([, a]) => a.length > 1); return L + 'two rules apply in ' + k[0].split(T.tm.SEP)[0] + ' on ' + TK.sym(k[0].split(T.tm.SEP)[1]) + ', so it is not deterministic'; }
    if (want.mode && M.mode !== want.mode) return L + 'this picture needs mode: ' + want.mode;
    if (want.maxStates && M.states.length > want.maxStates) return L + 'at most ' + want.maxStates + ' states, so the picture stays readable';
    if (!M.accept.length && !M.halt.length && !want.anyHalt) return L + 'name an accepting state (accept: qa)';
    return null;
  };

  // ---- running -------------------------------------------------------------------------------------------
  /**
   * Run a deterministic machine one step at a time, keeping every configuration. Returns {list: [{cfg, rule}],
   * verdict: 'accept'|'reject'|'loop'|'limit', how: 'state' | 'stuck' (no rule), loopAt (the step repeated)}.
   */
  TK.trace = function (M, w, opts) {
    opts = opts || {};
    const max = opts.max || 200;
    const c = T.tm.initial(M, w);
    const list = [{ cfg: T.tm.cloneCfg(c), rule: null }];
    const seen = new Map();
    let verdict = null, how = null, loopAt = null;
    for (;;) {
      if (T.tm.isAccept(M, c.state)) { verdict = 'accept'; how = 'state'; break; }
      if (T.tm.isReject(M, c.state)) { verdict = 'reject'; how = 'state'; break; }
      if (opts.loops !== false) { const k = T.tm.key(c); if (seen.has(k)) { verdict = 'loop'; loopAt = seen.get(k); break; } seen.set(k, c.step); }
      const rs = T.tm.rulesFor(M, c);
      if (!rs.length) { verdict = 'reject'; how = 'stuck'; break; }
      if (c.step >= max) { verdict = 'limit'; break; }
      T.tm.apply(c, rs[0]);
      list.push({ cfg: T.tm.cloneCfg(c), rule: rs[0] });
    }
    return { list, verdict, how, loopAt, last: list[list.length - 1].cfg };
  };
  /** The symbols under a configuration's heads */
  TK.reads = (cfg) => cfg.heads.map((h) => cfg.tapes[h.t].get(h.p));
  /** One tape of a configuration as {tape: [..], offset} for the tape kit */
  TK.tapeOf = (cfg, t) => { const tp = cfg.tapes[t || 0]; return { tape: tp.a.map((v) => (v === undefined ? tp.b : v)), offset: -tp.o }; };
  /** The trimmed contents of a tape (blanks at both ends dropped) */
  TK.contents = (cfg, t, M) => cfg.tapes[t || 0].trimmed().filter((s) => !(M && (M.mode === 'oneway' || M.mode === 'lba') && (s === M.leftEnd || s === M.rightEnd)));

  /** A move in plain words: "In q1 reading a: writes X, moves right and goes to q2." */
  TK.sayRule = function (r, M) {
    if (r.read.length === 1) {
      const rd = TK.sym(r.read[0]), wr = TK.sym(r.write[0]);
      return 'In ' + r.from + ' reading ' + rd + ': ' + (wr === rd ? 'it leaves ' + rd : 'it writes ' + wr) + ', ' + TK.moveWord(r.move[0]) + ' and goes to ' + r.to + '.';
    }
    const parts = r.read.map((x, i) => 'head ' + (i + 1) + ' reads ' + TK.sym(x) + (TK.sym(r.write[i]) === TK.sym(x) ? '' : ', writes ' + TK.sym(r.write[i])) + ', ' + ({ L: 'left', R: 'right', S: 'stays' })[r.move[i]]);
    return 'In ' + r.from + ': ' + parts.join('; ') + '. Next state ' + r.to + '.';
  };

  // ---- the machine drawn -----------------------------------------------------------------------------------
  /**
   * The diagram form of an engine machine for the graph kit, rules merged per edge: "a, b → R" leaves the
   * symbol, "a → X, R" writes one. opts.symbols(s) can rename symbols.
   */
  TK.diagram = function (M) {
    const by = new Map();
    for (const r of M.rules) {
      const e = r.from + '>' + r.to;
      if (!by.has(e)) by.set(e, { from: r.from, to: r.to, groups: new Map() });
      const keep = r.write.every((w, i) => w === r.read[i]);
      const g = r.write.length === 1 ? (keep ? '' : TK.sym(r.write[0])) + '|' + r.move[0] : r.write.map(TK.sym).join('') + '|' + r.move.join('');
      const gs = by.get(e).groups;
      if (!gs.has(g)) gs.set(g, { keep, write: r.write.map(TK.sym), move: r.move, reads: [] });
      gs.get(g).reads.push(r.read.map(TK.sym).join(''));
    }
    const trans = [];
    for (const e of by.values()) {
      const lines = [];
      for (const g of e.groups.values()) {
        let reads = g.reads;
        if (reads.length === M.gamma.length) reads = ['any'];
        const lhs = reads.join(',');
        lines.push(g.write.length === 1 ? (g.keep ? lhs + ' → ' + g.move[0] : lhs + ' → ' + g.write[0] + ', ' + g.move[0]) : lhs + ' → ' + g.write.join('') + ', ' + g.move.join(''));
      }
      trans.push({ from: e.from, to: e.to, label: lines.join('\n') });
    }
    return { kind: 'tm', states: M.states.slice(), start: M.start, accept: M.accept.concat(M.halt), trans, pos: {} };
  };
  /** States that halt: accepting, halting and rejecting ones */
  TK.halting = (M) => M.states.filter((q) => T.tm.isHalting(M, q));

  // ---- the definition panel -----------------------------------------------------------------------------------
  /** The columns of δ: input symbols, then the other tape symbols, the blank last */
  TK.columns = function (M) {
    const out = [];
    for (const s of M.input.concat(M.gamma)) if (!out.includes(s) && s !== M.blank) out.push(s);
    out.push(M.blank);
    return out;
  };
  /**
   * The machine as a tuple and as a table δ(state, read) = write, move, next for one-tape machines; returns
   * {sections, hl(rule) -> the cell to light}. Rows are the states that have moves, then the halting ones.
   */
  TK.defOf = function (M, opts) {
    opts = opts || {};
    const cols = TK.columns(M);
    const rows = M.states.filter((q) => !T.tm.isHalting(M, q)).concat(TK.halting(M));
    const cells = rows.map((q) => cols.map((a) => {
      const rs = M.delta.get(q + T.tm.SEP + a) || [];
      if (!rs.length) return T.tm.isHalting(M, q) ? '' : '';
      return rs.map((r) => TK.sym(r.write[0]) + ', ' + r.move[0] + ', ' + r.to).join(' | ');
    }));
    const tuple = [
      'Q = {' + M.states.join(', ') + '}',
      'Σ = {' + M.input.join(', ') + '}   Γ = {' + cols.map(TK.sym).join(', ') + '}',
      'start ' + M.start + (M.accept.length || M.halt.length ? ', accept {' + M.accept.concat(M.halt).join(', ') + '}' : '') + (M.reject.length ? ', reject {' + M.reject.join(', ') + '}' : ''),
      'no move in a state means: halt there' + (M.reject.length ? '' : ' and reject'),
    ];
    const sections = [
      { id: 'tuple', kind: 'math', title: opts.title || 'The machine', text: tuple.join('\n') },
      { id: 'delta', kind: 'table', title: 'δ(state, read) = write, move, next', corner: 'δ', colHead: cols.map(TK.sym), rowHead: rows, rows: cells, emptyText: '–' },
    ];
    return { sections, hl: (r) => (r ? { delta: [rows.indexOf(r.from) + ',' + cols.indexOf(r.read[0])] } : {}), rows, cols };
  };

  // ---- drawing -----------------------------------------------------------------------------------------------------
  /** A tape drawn from a configuration (one tape). opts as the tape kit's draw, plus cfg, t (which tape) */
  TK.tape = function (cfg, opts) {
    const t = opts.t || 0;
    const tp = TK.tapeOf(cfg, t);
    const hd = cfg.heads.find((h) => h.t === t);
    return T.Kit.tape.draw(Object.assign({ tape: tp.tape, offset: tp.offset, head: hd ? hd.p : 0 }, opts));
  };

  /**
   * A program listing: one line of code per row, numbered, with the running line lit. opts: {lines, x, y,
   * hot (index), done (index, lit green), bad (index), prefix, lh (row height), w (width), num (show numbers)}.
   * Returns {items, box, lineY(i)}.
   */
  TK.listing = function (opts) {
    const P = opts.prefix || 'ls';
    const lh = opts.lh || 26, x = opts.x || 0, y = opts.y || 0, size = opts.size || 14;
    const lines = opts.lines || [];
    const numW = opts.num === false ? 0 : 30;
    const w = opts.w || Math.max(160, ...lines.map((l) => T.geom.textWidth(l, size, { mono: true }) + numW + 24));
    const items = [];
    const mark = (i, cls, key) => { if (i === undefined || i === null || i < 0 || i >= lines.length) return; items.push({ key: P + ':' + key, kind: 'region', x: x, y: y + i * lh, w, h: lh, rx: 6, text: '', cls }); };
    items.push({ key: P + ':bg', kind: 'region', x: x - 6, y: y - 8, w: w + 12, h: lines.length * lh + 16, rx: 10, text: '', cls: 'tu-soft' });
    mark(opts.hot, 'tu-line', 'hot');
    mark(opts.done, 'tu-done', 'done');
    mark(opts.bad, 'tu-fail', 'bad');
    lines.forEach((l, i) => {
      if (numW) items.push({ key: P + ':n' + i, kind: 'text', x: x + numW - 8, y: y + i * lh + lh / 2 + 5, text: String(i + 1), anchor: 'end', cls: 'tu-num', size: 12, mono: true });
      items.push({ key: P + ':l' + i, kind: 'text', x: x + numW, y: y + i * lh + lh / 2 + 5, text: l, cls: 'tu-code', mono: true, size });
    });
    return { items, box: { x: x - 6, y: y - 8, w: w + 12, h: lines.length * lh + 16 }, lineY: (i) => y + i * lh + lh / 2, w };
  };

  /** A labelled value: a small title over a big number or word, e.g. the clocks of a simulation */
  TK.dial = function (key, x, y, title, value, cls) {
    return [
      { key: key + ':t', kind: 'text', x, y, text: title, anchor: 'middle', cls: 'title' },
      { key: key + ':v', kind: 'text', x, y: y + 32, text: String(value), anchor: 'middle', cls: 'strong' + (cls ? ' ' + cls : ''), size: 26, bold: true },
    ];
  };

  /** Verdict words */
  TK.verdictWord = { accept: 'accepts', reject: 'rejects', loop: 'loops for ever', limit: 'is still running' };
})();
