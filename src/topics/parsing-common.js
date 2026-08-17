// Shared pieces for the parsing topics (part 4): reading and checking grammar inputs, the grammar section
// of the definition panel, parse trees drawn top down (from the core's tree objects) or grown bottom up
// over the input (a forest whose leaves are the tokens), lists of lines in a panel (item sets, chart sets,
// code), and the row of input tokens with its end marker. Every function here is called while a topic
// runs, never while the files load, so the order the topic files load in does not matter.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const PX = (T.PX = {});
  const K = () => T.Kit;
  const Geo = () => T.geom;

  // ---- grammars --------------------------------------------------------------------------------------------
  /** A context-free grammar from its text (the core's reader) */
  PX.G = (text) => T.grammar.parse(text);
  PX.show = (w) => T.grammar.show(w);
  PX.prod = (G, id) => T.grammar.showProd(G, G.productions[id]);
  PX.rhs = (G, id) => T.grammar.showRhs(G, G.productions[id].rhs);
  PX.word = (G, s) => T.grammar.input(G, s);
  PX.set = (xs) => { const a = [...xs]; return a.length ? '{' + a.join(', ') + '}' : '∅'; };

  /**
   * A check for a grammar input: a friendly message, or null. opts: {maxRules, maxN, cnf (must be in
   * Chomsky normal form), noLeftRec, noEps, operator (an operator grammar)}
   */
  PX.checkGrammar = (opts) => (v) => {
    opts = opts || {};
    let G;
    try { G = PX.G(v); } catch (e) { return 'Grammar: ' + (e.plain || e.message); }
    if (!T.grammar.info(G).cf) return 'Grammar: every rule needs a single nonterminal on its left (a context-free grammar)';
    if (!G.productions.length) return 'Grammar: it has no rules';
    const max = opts.maxRules || 12;
    if (G.productions.length > max) return 'Grammar: at most ' + max + ' rules (alternatives count one each), so the picture stays readable';
    if (G.nonterminals.length > (opts.maxN || 6)) return 'Grammar: at most ' + (opts.maxN || 6) + ' nonterminals';
    if (!G.terminals.length) return 'Grammar: it has no terminals, so it makes no strings';
    if (opts.cnf) {
      const bad = G.productions.find((p) => !((p.rhs.length === 1 && !T.grammar.isN(G, p.rhs[0])) || (p.rhs.length === 2 && p.rhs.every((s) => T.grammar.isN(G, s)))));
      if (bad) return 'Grammar: this needs Chomsky normal form (A → B C or A → a), but ' + T.grammar.showProd(G, bad) + ' is neither';
    }
    if (opts.noEps) { const e = G.productions.find((p) => !p.rhs.length); if (e) return 'Grammar: ' + T.grammar.showProd(G, e) + ' is an ε-rule, which this picture does not take'; }
    if (opts.noLeftRec) { const lr = T.cfg.leftRecursive(G); if (lr.length) return 'Grammar: ' + lr.map((x) => x.A).join(', ') + ' is left-recursive, which this parser cannot take (see “Removing left recursion”)'; }
    if (opts.operator) { const c = T.opp.operatorCheck(G); if (!c.ok) return 'Grammar: not an operator grammar: ' + c.problems[0].say; }
    if (opts.extra) return opts.extra(G);
    return null;
  };
  /** A topic-level check that the string uses only the grammar's terminals */
  PX.checkWord = (gid, wid, max) => (inp) => {
    let G;
    try { G = PX.G(inp[gid]); } catch (e) { return null; }
    const w = PX.word(G, inp[wid]);
    const bad = w.find((c) => !G.terminals.includes(c));
    if (bad !== undefined) return 'String: "' + bad + '" is not a terminal of the grammar (its terminals are ' + G.terminals.join(' ') + ')';
    if (max && w.length > max) return 'String: at most ' + max + ' symbols, so the picture stays readable';
    return null;
  };

  /** The grammar section of the definition panel: one line per rule, so hl {g: [rule ids]} lights rules */
  PX.gdef = (G, opts) => {
    opts = opts || {};
    return { id: opts.id || 'g', kind: 'grammar', title: opts.title || 'Grammar', rules: G.productions.map((p) => (opts.numbered ? '(' + (p.id + (opts.base || 0)) + ')  ' : '') + T.grammar.showProd(G, p)), nonterminals: G.nonterminals };
  };

  // ---- trees, top down ---------------------------------------------------------------------------------------
  /**
   * A core tree ({sym, prod, children: null for a leaf}) as kit nodes with ids from their paths, so a tree
   * that grows keeps its old nodes. opts: {G (to tell an unexpanded nonterminal from a terminal), cls(node,
   * path) -> classes, label(node)}
   */
  PX.kitTree = (t, opts) => {
    opts = opts || {};
    const go = (n, path) => {
      const leaf = n.children === null || n.children === undefined;
      const isT = leaf && (opts.G ? !T.grammar.isN(opts.G, n.sym) : n.prod === null && !n.nt);
      const kids = leaf ? [] : n.children.length ? n.children.map((c, i) => go(c, path + '.' + i)) : [{ id: path + '.e', label: 'ε', cls: 'eps leaf' }];
      const cls = [isT ? 'term' : 'nt', n.error ? 'bad' : '', n.missing ? 'bad' : '', opts.cls ? opts.cls(n, path) || '' : ''].filter(Boolean).join(' ');
      return { id: path, label: opts.label ? opts.label(n) : n.sym, children: kids, cls };
    };
    return go(t, 'r');
  };

  // ---- trees, bottom up --------------------------------------------------------------------------------------
  /**
   * A forest over the input: leaves sit on a baseline at their token's place, each parent rises one level
   * above its tallest child, centred over its children. nodes: {id, label, children: [nodes], at (the token
   * index of a leaf; a fraction for an ε leaf), cls}. opts: {roots, x, y (the baseline), gap, gy, prefix,
   * hot: [ids], good: [ids], xAt(i) (where token i is, instead of x + i * gap)}
   * Returns {items, box, pos}.
   */
  PX.forest = (opts) => {
    const P = opts.prefix || 'fo', gap = opts.gap || 64, gy = opts.gy || 64, x0 = opts.x || 0, y0 = opts.y || 0;
    const pos = new Map(), items = [], boxes = [];
    const hot = new Set(opts.hot || []), good = new Set(opts.good || []);
    const place = (n) => {
      if (pos.has(n.id)) return pos.get(n.id);
      let p;
      if (!n.children || !n.children.length) p = { x: opts.xAt ? (Number.isInteger(n.at) ? opts.xAt(n.at) : ((n.at < 0 ? opts.xAt(0) - 120 : opts.xAt(Math.floor(n.at))) + opts.xAt(Math.ceil(n.at))) / 2) : x0 + (n.at || 0) * gap, lvl: /\beps\b/.test(n.cls || '') ? 0.8 : 0 };
      else {
        const ps = n.children.map(place);
        p = { x: (ps[0].x + ps[ps.length - 1].x) / 2, lvl: 1 + Math.max(...ps.map((q) => q.lvl)) };
      }
      pos.set(n.id, p);
      return p;
    };
    for (const r of opts.roots) place(r);
    const draw = (n) => {
      const p = pos.get(n.id), sz = K().tree.size(n), y = y0 - p.lvl * gy;
      const leaf = !n.children || !n.children.length;
      const cls = ['tnode', n.cls || '', leaf ? 'leaf' : '', hot.has(n.id) ? 'hot' : '', good.has(n.id) ? 'accept-path' : ''].filter(Boolean).join(' ');
      items.push({ key: P + ':n:' + n.id, kind: 'state', x: p.x, y, w: sz.w, h: sz.h, rx: sz.rx, text: String(n.label), cls, pick: true, enter: n.enter || 'rise', dim: !!n.dim });
      boxes.push({ x: p.x - sz.w / 2, y: y - sz.h / 2, w: sz.w, h: sz.h });
      for (const c of n.children || []) {
        draw(c);
        items.push({ key: P + ':e:' + n.id + '>' + c.id, kind: 'edge', from: P + ':n:' + n.id, to: P + ':n:' + c.id, head: false, gapB: 0, cls: 'tree' + (hot.has(n.id) ? ' hot' : '') });
      }
    };
    for (const r of opts.roots) draw(r);
    // a straight edge from a high parent down to a token can pass through a node in between: bend it away
    PX.unblock(items, { crossing: true });
    return { items, box: Geo().union(boxes), pos: (id) => { const p = pos.get(id); return p ? { x: p.x, y: y0 - p.lvl * gy } : null; } };
  };

  /**
   * Bend edges that pass through (or graze) a state item they do not join, trying a few bends and keeping the
   * one with the most room. opts: {crossing: also avoid crossing other edges, bends: [..]}. Changes items.
   */
  PX.unblock = (items, opts) => {
    opts = opts || {};
    const byKey = new Map(items.map((it) => [it.key, it])), nodes = items.filter((it) => it.kind === 'state');
    const clearance = (e) => {
      const g = T.edgeGeom(e, (k) => byKey.get(k) || null);
      if (!g) return Infinity;
      let best = Infinity;
      for (let i = 0; i <= 60; i++) { const pt = g.at(i / 60); for (const n of nodes) if (n.key !== e.from && n.key !== e.to) best = Math.min(best, Math.max(Math.abs(pt.x - n.x) - n.w / 2, Math.abs(pt.y - n.y - (n.sub ? 12 : 0)) - n.h / 2 - (n.sub ? 12 : 0))); }
      return best;
    };
    const poly = (e) => { const g = T.edgeGeom(e, (k) => byKey.get(k) || null); const out = []; if (g) for (let i = 0; i <= 24; i++) out.push(g.at(i / 24)); return out; };
    const crosses = (e) => {
      const a = poly(e);
      for (const f of items) {
        if (f === e || f.kind !== 'edge' || f.from === e.from || f.to === e.to || f.from === e.to || f.to === e.from) continue;
        const b = poly(f);
        for (let i = 0; i + 1 < a.length; i++) for (let j = 0; j + 1 < b.length; j++) if (Geo().segCross(a[i], a[i + 1], b[j], b[j + 1])) return true;
      }
      return false;
    };
    const score = (e) => clearance(e) - (opts.crossing && crosses(e) ? 100 : 0);
    for (const e of items) {
      if (e.kind !== 'edge' || clearance(e) > 12) continue;
      let pick = { b: e.bend || 0, c: score(e) };
      for (const b of opts.bends || [24, -24, 40, -40, 60, -60, 90, -90]) { const c = score(Object.assign({}, e, { bend: b })); if (c > pick.c + 0.5) pick = { b, c }; }
      e.bend = pick.b;
    }
    return items;
  };

  // ---- a panel of lines --------------------------------------------------------------------------------------
  /**
   * Lines in a panel: item sets, chart sets, code. opts: {prefix, x, y (top-left), w, title, rows: [{id,
   * text, cls, tag}], rowH, size, mono (default true), align: 'left' | 'center', pad}
   * Each row is a cell keyed by its id, so a row that moves glides. A tag is a short note at the right end
   * of the row (the origin of an Earley item, a lookahead). Returns {items, box, rowBox(id)}.
   */
  PX.panel = (opts) => {
    const P = opts.prefix || 'pn', rows = opts.rows || [], rh = opts.rowH || 34, fs = opts.size || 15;
    const mono = opts.mono !== false;
    const textW = (s) => Geo().textWidth(s, fs, { mono });
    const tagW = Math.max(0, ...rows.map((r) => (r.tag ? Geo().textWidth(r.tag, 13, { mono: true }) + 18 : 0)));
    const w = opts.w || Math.max(140, ...rows.map((r) => textW(r.text) + 28 + tagW), opts.title ? Geo().textWidth(opts.title, 13, { bold: true }) * 1.2 + 30 : 0);
    const x = opts.x || 0, y = opts.y || 0, top = opts.title ? 30 : 10;
    const items = [];
    const H = top + rows.length * (rh + 4) + 8;
    items.push({ key: P + ':bg', kind: 'region', x, y, w, h: Math.max(H, opts.minH || 0), cls: 'panel ' + (opts.cls || ''), text: '', audit: 'group' });
    if (opts.title) items.push({ key: P + ':title', kind: 'text', x: x + 12, y: y + 21, text: opts.title, cls: 'strong', size: 15 });
    const at = {};
    rows.forEach((r, i) => {
      const ry = y + top + i * (rh + 4);
      at[r.id] = { x: x + 8, y: ry, w: w - 16, h: rh };
      const left = opts.align === 'left' || (opts.align === undefined && mono);
      const cell = { key: P + ':r:' + r.id, kind: 'cell', x: x + 8, y: ry, w: w - 16 - (r.tag ? tagW : 0), h: rh, rx: 6, cls: ['prow', mono ? 'mono' : '', r.cls || ''].filter(Boolean).join(' '), text: r.text, size: fs, align: left ? 'left' : undefined, enter: r.enter || 'fade', pick: r.pick !== false };
      if (r.src) cell.src = r.src;
      items.push(cell);
      if (r.tag) items.push({ key: P + ':t:' + r.id, kind: 'cell', x: x + w - 8 - tagW + 4, y: ry, w: tagW - 4, h: rh, rx: 6, cls: 'prow tag mono ' + (r.tagCls || ''), text: r.tag, size: 13 });
    });
    return { items, box: { x, y, w, h: Math.max(H, opts.minH || 0) }, rowBox: (id) => at[id] || null, w };
  };

  // ---- the input --------------------------------------------------------------------------------------------
  /**
   * The input tokens with the end marker $ and a head under the next one. opts: {tokens, pos, x, y, cw,
   * prefix, label, consumed, cls(i, t), headText, end (default true: append $)}
   */
  PX.input = (opts) => {
    const toks = opts.tokens.concat(opts.end === false ? [] : ['$']);
    const cw = opts.cw || Math.max(44, ...toks.map((t) => Geo().textWidth(t, 17, { mono: true }) + 18));
    return K().string.draw({ text: toks, pos: opts.pos, x: opts.x || 0, y: opts.y || 0, cw, prefix: opts.prefix || 'in', label: opts.label, head: opts.head, headText: opts.headText, headCls: opts.headCls, cls: (i, t) => [i === toks.length - 1 && opts.end !== false ? 'endmark' : '', opts.cls ? opts.cls(i, t) || '' : ''].filter(Boolean).join(' ') });
  };

  /** A set's members in a fixed order: terminals, then ε, then $ */
  PX.sortSet = (xs) => [...xs].sort((a, b) => (a === 'ε') - (b === 'ε') || (a === '$') - (b === '$') || (a < b ? -1 : a > b ? 1 : 0));
  /** Set notation for a list of symbols in a cell: X Y (or ∅) */
  PX.cellSet = (xs) => (xs.length ? xs.join(' ') : '∅');
})();
