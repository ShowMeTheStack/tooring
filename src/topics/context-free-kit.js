// Drawing helpers shared by the context-free topics (part 3): sentential forms as rows of symbol cells that
// keep their identity from one step to the next, parse trees from the grammar engine's trees, grammars as
// rows of rule chips that glide, grow and fade as a cleanup or a normal form rewrites them, and the input
// checks every grammar and machine topic needs. Everything here is only called while a topic runs.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Geo = T.geom;
  const CF = (T.CF = T.CF || {});

  /** Tag every item of a run's frames with the class cf (the context-free styles are scoped to it) */
  CF.mark = function (out) {
    const frames = Array.isArray(out) ? out : out && out.frames ? out.frames : [];
    for (const f of frames) for (const it of f.items || []) if (it && !/(^| )cf( |$)/.test(it.cls || '')) it.cls = it.cls ? it.cls + ' cf' : 'cf';
    return out;
  };

  // ---- inputs ------------------------------------------------------------------------------------------------
  /** Grammar text to the engine's grammar object (throws with a line number on a mistake) */
  CF.grammar = (text) => T.grammar.parse(text);
  /**
   * A friendly error for grammar text, or null. o: {label, cf (default true), cnf, maxRules, maxN, rightOnly}
   */
  CF.checkGrammar = function (text, o) {
    o = o || {};
    const L = o.label || 'Grammar';
    const r = T.grammar.tryParse(text);
    if (r.error) return L + ': ' + r.error;
    const G = r.grammar;
    if (!G.productions.length) return L + ': there are no rules';
    if (o.cf !== false && !G.productions.every((p) => p.A !== null)) return L + ': each left side must be one nonterminal, as in a context-free grammar';
    if (o.maxRules && G.productions.length > o.maxRules) return L + ': at most ' + o.maxRules + ' rules (alternatives count one each), so the picture stays readable';
    if (o.maxN && G.nonterminals.length > o.maxN) return L + ': at most ' + o.maxN + ' nonterminals';
    // the shape of Chomsky normal form (the start may appear on right sides here: the trees are what matter)
    const bad = o.cnf && G.productions.find((p) => !((p.rhs.length === 2 && p.rhs.every((s) => T.grammar.isN(G, s))) || (p.rhs.length === 1 && !T.grammar.isN(G, p.rhs[0]))));
    if (bad) {
      return L + ': this needs Chomsky normal form (A → B C or A → a), but ' + T.grammar.showProd(G, bad) + ' is neither. The Chomsky normal form topic converts any grammar.';
    }
    return null;
  };
  /** A word typed by the student as terminals of G; an error message when a symbol is not a terminal */
  CF.word = (G, s) => T.grammar.input(G, s);
  CF.checkWord = function (G, s, label) {
    const w = CF.word(G, s);
    const bad = w.find((x) => !G.terminals.includes(x));
    return bad !== undefined ? (label || 'Word') + ': "' + bad + '" is not a terminal of the grammar (they are ' + G.terminals.join(' ') + ')' : null;
  };
  CF.show = (w) => (w.length ? T.grammar.show(w) : 'ε');
  CF.isN = (G, s) => T.grammar.isN(G, s);
  CF.prod = (G, p) => T.grammar.showProd(G, typeof p === 'number' ? G.productions[p] : p);
  CF.rhs = (G, rhs) => T.grammar.showRhs(G, rhs);
  /** The definition-panel section for a grammar: one line per rule, lit by production id */
  CF.gsec = (G, id, title) => ({ id, kind: 'grammar', title, rules: G.productions.map((p) => T.grammar.showProd(G, p)), nonterminals: G.nonterminals });

  // ---- sentential forms --------------------------------------------------------------------------------------
  const symW = (s, size) => Math.max(36, Math.ceil(Geo.textWidth(s, size || 17, { mono: true })) + 16);
  /**
   * A sentential form as a row of cells. form: [{s, id}] (ids stay with a symbol from step to step, so a
   * symbol that survives a rewrite glides and the new ones grow out of the one they replace).
   * o: {x, y, prefix, h, hot: [ids], cls(sym, i) -> classes, src: {id: key to grow from}, dim (grey all),
   *   label (written to the left), gap}
   * Returns {items, box, key(id), mid(i)}.
   */
  CF.form = function (G, form, o) {
    o = o || {};
    const P = o.prefix || 'f', H = o.h || 42, x0 = o.x || 0, y0 = o.y || 0;
    const hot = new Set(o.hot || []);
    const items = [];
    const key = (id) => P + ':' + id;
    let x = x0;
    const mids = [];
    if (o.label) items.push({ key: P + ':label', kind: 'text', x: x0 - 12, y: y0 + H / 2 + 5, text: o.label, anchor: 'end', cls: o.labelCls || 'title' });
    if (!form.length) {
      items.push({ key: P + ':eps', kind: 'cell', x, y: y0, w: 40, h: H, text: 'ε', cls: 'mono empty' + (o.dim ? ' read' : '') });
      x += 40;
    }
    form.forEach((f, i) => {
      const w = o.cw || symW(f.s);
      const nt = CF.isN(G, f.s);
      const cls = ['mono', nt ? 'nt' : 't', hot.has(f.id) ? 'hot' : '', o.dim ? 'read' : '', o.cls ? o.cls(f, i) || '' : ''].filter(Boolean).join(' ');
      const it = { key: key(f.id), kind: 'cell', x, y: y0, w, h: H, text: f.s, cls, pick: true };
      if (o.src && o.src[f.id]) { it.enter = 'from'; it.src = o.src[f.id]; }
      items.push(it);
      mids.push(x + w / 2);
      x += w + (o.gap === undefined ? 0 : o.gap);
    });
    return { items, box: { x: x0, y: y0, w: Math.max(40, x - x0), h: H }, key, mid: (i) => mids[i] };
  };
  /**
   * Replay a derivation (steps [{prod, pos}]) keeping an id on every symbol occurrence. Returns
   * {forms: [[{s, id}]], born: [{id: parent id}] (for each step, the new symbols and the one they replace)}.
   */
  CF.track = function (G, steps) {
    let n = 0;
    let form = [{ s: G.start, id: 'n0' }];
    const forms = [form], born = [{}], replaced = [null];
    for (const st of steps) {
      const p = G.productions[st.prod];
      const old = form[st.pos];
      const kids = p.rhs.map((s) => ({ s, id: 'n' + ++n }));
      const b = {};
      for (const k of kids) b[k.id] = old.id;
      form = form.slice(0, st.pos).concat(kids, form.slice(st.pos + 1));
      forms.push(form); born.push(b); replaced.push(old.id);
    }
    return { forms, born, replaced };
  };

  // ---- trees -------------------------------------------------------------------------------------------------
  /**
   * The engine's tree {sym, prod, children} as kit nodes {id, label, cls, children}, named by their path from
   * the root so a tree that grows keeps its old nodes. An ε-rule gets one ε leaf. o: {root (id), cls(node, id),
   * label(node, id), w(node, id)}
   */
  CF.kitTree = function (G, t, o) {
    o = o || {};
    const go = (n, id) => {
      const nt = CF.isN(G, n.sym);
      const k = { id, label: o.label ? o.label(n, id) : n.sym, cls: [nt ? 'nt' : 't', o.cls ? o.cls(n, id) || '' : ''].filter(Boolean).join(' '), mono: !nt };
      if (o.w) { const w = o.w(n, id); if (w) k.w = w; }
      if (n.children === null || n.children === undefined) return k;
      k.children = n.children.length ? n.children.map((c, i) => go(c, id + '.' + i)) : [{ id: id + '.e', label: 'ε', cls: 't eps' + (o.cls ? ' ' + (o.cls({ sym: 'ε', children: null }, id + '.e') || '') : ''), mono: true }];
      return k;
    };
    return go(t, o.root || 'r');
  };
  /** Every node of an engine tree with its path id and the span of the word it covers: [{node, id, from, to, depth}] */
  CF.nodes = function (t, root) {
    const out = [];
    let pos = 0;
    const go = (n, id, d) => {
      const from = pos;
      const rec = { node: n, id, from, to: from, depth: d };
      out.push(rec);
      if (n.children === null) { pos++; rec.to = pos; return; }
      n.children.forEach((c, i) => go(c, id + '.' + i, d + 1));
      rec.to = pos;
    };
    go(t, root || 'r', 0);
    return out;
  };

  // ---- grammars as rule chips --------------------------------------------------------------------------------
  const chipW = (text) => Math.max(44, Math.ceil(Geo.textWidth(text, 15, { mono: true })) + 22);
  const rk = (A, rhs) => A + '→' + rhs.join(' ');
  CF.ruleKey = rk;
  /**
   * A grammar drawn as one row per nonterminal: the left side, an arrow, then a chip per alternative.
   * Chips are named by their rule, so a rule that survives a rewrite stays put or glides, a new one grows
   * (out of o.from[ruleKey] when given) and a dropped one fades.
   * o: {x, y, prefix, order: [nonterminals], cls(A, rhs) -> classes, lhsCls(A), from: {ruleKey: key or [keys]},
   *   maxW (wrap the chips past this width), cols: [{head, text(A), cls(A)}] (status cells after the left side),
   *   exit: {ruleKey: 'into'|...}, ghost: [[A, rhs]] (rules drawn dashed although not in G), title}
   * Returns {items, box, chip(A, rhs) -> key, lhs(A) -> key, row(A) -> y}
   */
  CF.rules = function (G, o) {
    o = o || {};
    const P = o.prefix || 'g', x0 = o.x || 0;
    let y = o.y || 0;
    const H = 36, GAP = 10, ROW = 12;
    const by = new Map();
    const order = [...new Set(o.order || G.nonterminals)];
    for (const p of G.productions) { if (!by.has(p.A)) by.set(p.A, []); by.get(p.A).push(p.rhs); }
    for (const [A, rhs] of o.ghost || []) { if (!by.has(A)) by.set(A, []); if (!by.get(A).some((r) => r.join(' ') === rhs.join(' '))) by.get(A).push(rhs); }
    for (const A of by.keys()) if (!order.includes(A)) order.push(A);
    const ghost = new Set((o.ghost || []).map(([A, rhs]) => rk(A, rhs)));
    const items = [];
    const lw = Math.max(44, ...order.map((A) => Math.ceil(Geo.textWidth(A, 16, { mono: true, bold: true })) + 22));
    const cols = o.cols || [];
    // headings are drawn in capitals with letter spacing, so measure them that way
    const colW = cols.map((c) => Math.max(52, Math.ceil(Geo.textWidth((c.head || '').toUpperCase(), 13, { bold: true }) * 1.12) + 14));
    if (o.title) { items.push({ key: P + ':title', kind: 'text', x: x0, y: y + 4, text: o.title, cls: 'title' }); y += 22; }
    if (cols.length) {
      let cx = x0 + lw + 8;
      cols.forEach((c, i) => { items.push({ key: P + ':ch:' + i, kind: 'text', x: cx + colW[i] / 2, y: y + 6, text: c.head, anchor: 'middle', cls: 'title' }); cx += colW[i] + 6; });
      y += 18;
    }
    const rows = {};
    let maxX = x0 + lw;
    const startX = x0 + lw + 8 + colW.reduce((a, w) => a + w + 6, 0) + 30;
    const lim = o.maxW ? x0 + o.maxW : Infinity;
    for (const A of order) {
      const alts = by.get(A) || [];
      if (!alts.length && !o.keepEmpty) continue;
      rows[A] = y;
      items.push({ key: P + ':l:' + A, kind: 'cell', x: x0, y, w: lw, h: H, text: A, cls: 'mono nt lhs' + (o.lhsCls ? ' ' + (o.lhsCls(A) || '') : ''), pick: true });
      let cx = x0 + lw + 8;
      cols.forEach((c, i) => {
        const t = c.text(A);
        items.push({ key: P + ':cc:' + i + ':' + A, kind: 'cell', x: cx, y, w: colW[i], h: H, text: t === undefined || t === null ? '' : t, cls: 'mono status ' + (c.cls ? c.cls(A) || '' : '') });
        cx += colW[i] + 6;
      });
      items.push({ key: P + ':ar:' + A, kind: 'text', x: startX - 15, y: y + H / 2 + 6, text: '→', anchor: 'middle', cls: 'strong' });
      let x = startX, lines = 1;
      for (const rhs of alts) {
        const text = rhs.length ? T.grammar.showRhs(G, rhs) : 'ε';
        const w = chipW(text);
        if (x > startX && x + w > lim) { x = startX; y += H + 8; lines++; }
        const k = rk(A, rhs);
        const it = { key: P + ':c:' + k, kind: 'cell', x, y, w, h: H, text, size: 15, cls: ['mono chip', rhs.length ? '' : 'empty', ghost.has(k) ? 'gone' : '', o.cls ? o.cls(A, rhs) || '' : ''].filter(Boolean).join(' '), pick: true };
        if (o.from && o.from[k]) { it.enter = 'from'; it.src = o.from[k]; }
        items.push(it);
        x += w + GAP;
        maxX = Math.max(maxX, x - GAP);
      }
      void lines;
      y += H + ROW;
    }
    return { items, box: { x: x0, y: o.y || 0, w: maxX - x0, h: y - (o.y || 0) - ROW }, chip: (A, rhs) => P + ':c:' + rk(A, rhs), lhs: (A) => P + ':l:' + A, row: (A) => rows[A] };
  };
  /** Rules of G as [A, rhs] pairs keyed for quick lookups */
  CF.ruleSet = (G) => new Set(G.productions.map((p) => rk(p.A, p.rhs)));

  /**
   * Give each run of frames its own camera: frames [cuts[i], cuts[i+1]) share the box around them, so a scene
   * that changes completely halfway (a construction, then a run) is not shrunk to fit both at once.
   */
  CF.phaseViews = function (frames, cuts) {
    const ends = cuts.concat([frames.length]);
    for (let i = 0; i + 1 < ends.length; i++) {
      let box = null;
      for (let k = ends[i]; k < ends[i + 1]; k++) { const b = T.stageBounds(frames[k].items); if (b) box = box ? Geo.union([box, b]) : b; }
      for (let k = ends[i]; k < ends[i + 1]; k++) frames[k].view = box;
    }
    return frames;
  };

  // ---- machines ----------------------------------------------------------------------------------------------
  /** A pushdown automaton from machine text: {P (engine), M (diagram form)} or an error */
  CF.pda = function (text) {
    const M = T.Machine.parse(text);
    if (M.kind !== 'pda') throw new Error('this is not a pushdown automaton: write moves like q0, a, Z -> q1, A Z');
    const P = T.pda.parse(T.Machine.format(M));
    return { P, M };
  };
  CF.checkPda = function (text, o) {
    o = o || {};
    try { const { P } = CF.pda(text); if (o.maxStates && P.states.length > o.maxStates) return (o.label || 'Machine') + ': at most ' + o.maxStates + ' states'; } catch (e) { return (o.label || 'Machine') + ': ' + e.message; }
    return null;
  };
  /** The diagram edge a transition is drawn on */
  CF.edgeOf = (t) => t.from + '>' + t.to;
  /** The transition table for the definition panel */
  CF.pdaTable = (P, id, title) => ({ id: id || 'delta', kind: 'table', title: title || 'Moves (state, read, pop) → (state, push)', colHead: ['#', 'state', 'read', 'pop', '→ state', 'push'], rows: P.transitions.map((t) => [String(t.id + 1), t.from, t.read || 'ε', t.pop || 'ε', t.to, T.pda.showStack(t.push)]) });
  CF.pdaTuple = (P) => ({ id: 'tuple', kind: 'math', title: 'The machine', text: 'Q  = {' + P.states.join(', ') + '}\nΣ  = {' + P.input.join(', ') + '}\nΓ  = {' + P.stack.join(', ') + '}\nq₀ = ' + P.start + ',  Z₀ = ' + (P.startStack || 'ε') + '\n' + (P.acceptBy === 'empty' ? 'accepts by empty stack' : 'F  = {' + P.accept.join(', ') + '}  (accepts by final state)') });
  /** A configuration as text: (state, rest of input, stack top first) */
  CF.config = (P, c, w) => '(' + c.state + ', ' + (w.slice(c.pos).join('') || 'ε') + ', ' + T.pda.showStack(c.stack) + ')';
  /** A stack drawn as a column (top up) from a top-first list */
  CF.stack = (stack, o) => T.Kit.stack.draw(Object.assign({ items: stack.slice().reverse(), label: 'stack' }, o || {}));
})();
