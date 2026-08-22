// Earley's parser on any context-free grammar: one chart set per position in the input, filled by predict
// (a dot before a nonterminal calls for its rules), scan (a dot before the next input symbol moves into
// the next set) and complete (a finished item moves on the items that were waiting for it). The sets
// are drawn as columns with the input symbols between them, and each new item arrives with an arrow from
// the item or items it came from. A second topic reads the parse trees off the completed items.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'earley', part: 'parsing', order: 64, title: 'Earley parsing', blurb: 'A chart of item sets, one per position: predict, scan and complete work for every context-free grammar, left-recursive, ambiguous or with ε-rules.' });

  const SENT = 'S → N V\nN → d n | n\nV → v N | v';
  const SUMS = 'S → S + S | x';
  const OPT = 'S → A b\nA → a A | ε';
  const LEFT = 'E → E + n | n';
  const GAP = 46, ROW = 32;

  const itemText = (G, it) => { const p = G.productions[it.prod]; return p.A + ' → ' + [...p.rhs.slice(0, it.dot), '•', ...p.rhs.slice(it.dot)].join(' '); };
  const done = (G, it) => it.dot === G.productions[it.prod].rhs.length;

  /**
   * The chart. Two layouts: 'bands' (the default), one horizontal band per set stacked downwards with the
   * input symbol read between two bands at the left, items in a grid inside the band; 'columns', a column
   * per set with the symbols between them (an empty column is drawn narrow). shown[j]: how many items of
   * set j are drawn; opts: {layout, cls(j, q) -> classes, colCls(j), filter(j, q), arrows: [{from: [j, q],
   * to: [j, q], cls}], tok(j) -> classes}
   * Positions come from the finished chart, so nothing moves while it fills.
   */
  function chart(G, r, shown, opts) {
    const n = r.word.length, items = [], FS = 15, TAG = 30;
    const keep = (j, q) => !opts.filter || opts.filter(j, q);
    const finalRows = (j) => r.sets[j].map((it, q) => q).filter((q) => keep(j, q));
    const textW = (it) => T.geom.textWidth(itemText(G, it), FS, { mono: true }) + 26;
    const itemW = Math.ceil(Math.max(140, ...r.sets.flat().map(textW))), cellW = itemW + TAG;
    const where = {}, at = {};
    const rowCell = (j, q, x, y) => {
      const it = r.sets[j][q], cls = ['prow', 'mono', done(G, it) ? 'kernel' : '', opts.cls ? opts.cls(j, q) || '' : ''].filter(Boolean).join(' ');
      items.push({ key: 'es' + j + ':r:' + q, kind: 'cell', x, y, w: itemW, h: ROW, rx: 6, cls, text: itemText(G, it), size: FS, align: 'left', pick: true });
      items.push({ key: 'es' + j + ':t:' + q, kind: 'cell', x: x + itemW + 2, y, w: TAG - 2, h: ROW, rx: 6, cls: 'prow tag mono', text: String(it.origin), size: 13 });
      where[j + ',' + q] = true;
    };
    let tokX, box;
    if (opts.layout === 'columns') {
      // columns: a set with nothing to show is narrow
      const widths = r.sets.map((S, j) => (finalRows(j).length ? cellW + 16 : 76));
      const xs = []; widths.reduce((x, w, j) => { xs[j] = x; return x + w + GAP; }, 0);
      const maxRows = Math.max(1, ...r.sets.map((S, j) => finalRows(j).length));
      const H = 34 + maxRows * (ROW + 4) + 6;
      for (let j = 0; j <= n; j++) {
        items.push({ key: 'es' + j + ':bg', kind: 'region', x: xs[j], y: 54, w: widths[j], h: H, cls: 'panel ' + (opts.colCls ? opts.colCls(j) : ''), text: '', audit: 'group' });
        items.push({ key: 'es' + j + ':title', kind: 'text', x: xs[j] + 10, y: 54 + 22, text: 'Set ' + j, cls: 'strong', size: 15 });
        finalRows(j).forEach((q, k) => { if (q < shown[j]) rowCell(j, q, xs[j] + 8, 54 + 32 + k * (ROW + 4)); });
      }
      tokX = (j) => xs[j] + widths[j] + GAP / 2;
      r.word.forEach((a, j) => items.push({ key: 'ew:' + j, kind: 'cell', x: tokX(j) - 22, y: 0, w: 44, h: 40, text: a, cls: 'mono' + (opts.tok && opts.tok(j) ? ' ' + opts.tok(j) : ''), pick: true }));
      box = { h: 54 + H };
    } else {
      // bands: up to three items to a line
      const per = cellW * 3 + 24 > 760 ? 2 : 3, BX = 64, TITLE = 70;
      const W = TITLE + per * (cellW + 8) + 8;
      let y = 0;
      for (let j = 0; j <= n; j++) {
        const rows = finalRows(j), lines = Math.max(1, Math.ceil(rows.length / per));
        const H = lines * (ROW + 6) + 10;
        items.push({ key: 'es' + j + ':bg', kind: 'region', x: BX, y, w: W, h: H, cls: 'panel ' + (opts.colCls ? opts.colCls(j) : ''), text: '', audit: 'group' });
        items.push({ key: 'es' + j + ':title', kind: 'text', x: BX + 12, y: y + 27, text: 'Set ' + j, cls: 'strong', size: 15 });
        rows.forEach((q, k) => { if (q < shown[j]) rowCell(j, q, BX + TITLE + (k % per) * (cellW + 8), y + 8 + Math.floor(k / per) * (ROW + 6)); });
        at[j] = { y, H };
        y += H + 44;
      }
      // symbol j is read between band j and band j + 1
      r.word.forEach((a, j) => items.push({ key: 'ew:' + j, kind: 'cell', x: 4, y: at[j].y + at[j].H + 22 - 20, w: 44, h: 40, text: a, cls: 'mono' + (opts.tok && opts.tok(j) ? ' ' + opts.tok(j) : ''), pick: true }));
      tokX = () => 0;
      box = { h: y };
    }
    for (const a of opts.arrows || []) {
      if (!where[a.from.join(',')] || !where[a.to.join(',')]) continue;
      const same = a.from[0] === a.to[0];
      items.push({ key: 'ea:' + a.from.join(',') + '>' + a.to.join(','), kind: 'edge', from: 'es' + a.from[0] + ':r:' + a.from[1], to: 'es' + a.to[0] + ':r:' + a.to[1], bend: same ? -40 : -24, cls: a.cls, audit: 'ignore', layer: 'top' });
    }
    return { items, height: box.h, tokX, pitch: 0 };
  }
  const defOf = (G) => ({ sections: [
    T.PX.gdef(G),
    { id: 'ops', kind: 'math', title: 'The three moves (an item is [A → α • β, origin])', text: 'predict:  • before B in set j  →  add [B → • γ, j] to set j\nscan:     • before a, and a is symbol j+1  →  move the dot, into set j+1\ncomplete: [B → γ •, i] in set j  →  every [A → α • B β, k] in set i\n          moves on: add [A → α B • β, k] to set j\naccept:   [S → γ •, 0] in the last set' },
  ] });
  const checkGrammar = (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 5 })(v);

  T.topic({
    id: 'earley-chart', family: 'earley', order: 10, title: 'Earley\'s chart: predict, scan, complete',
    blurb: 'One set of items per position in the input. Predict calls for a nonterminal\'s rules, scan reads the next symbol into the next set, complete moves on whatever was waiting for a finished nonterminal.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: SENT, check: checkGrammar },
      { id: 'w', kind: 'string', label: 'String', def: 'dnvn', max: 5 },
    ],
    presets: [
      { label: 'A sentence: d n v n', values: { g: SENT, w: 'dnvn' } },
      { label: 'Rejected early: d v n', values: { g: SENT, w: 'dvn' } },
      { label: 'Left recursion: n+n+n', values: { g: LEFT, w: 'n+n+n' } },
      { label: 'An ε-rule: ab', values: { g: OPT, w: 'ab' } },
      { label: 'Ambiguous: x+x+x', values: { g: SUMS, w: 'x+x+x' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 5)(inp),
    counters: [{ id: 'items', label: 'items' }, { id: 'predict', label: 'predicted' }, { id: 'scan', label: 'scanned' }, { id: 'complete', label: 'completed' }],
    run(inp) {
      const G = T.PX.G(inp.g), r = T.parse.earley(G, inp.w), n = r.word.length;
      const shown = new Array(n + 1).fill(0);
      const F = new T.Frames(['items', 'predict', 'scan', 'complete']);
      let cur = 0;
      const scene = (opts) => chart(G, r, shown, Object.assign({ colCls: (j) => (j === cur ? 'hot' : ''), tok: (j) => (j < cur ? 'read' : j === cur ? 'act' : '') }, opts)).items;
      const lr = T.cfg.leftRecursive(G).map((x) => x.A);
      F.add({ items: scene({}), say: 'The input ' + T.PX.show(r.word) + ' sits between ' + (n + 1) + ' empty sets: set j will hold the items that are possible after reading j symbols.' + (lr.length ? ' The grammar is left-recursive (' + lr.join(', ') + '); watch Earley take that in its stride.' : '') });
      let emptyAt = -1;
      for (const st of r.trace) {
        if (st.kind === 'set') {
          if (emptyAt >= 0) continue;
          cur = st.set;
          if (!r.sets[st.set].length) { emptyAt = st.set; F.add({ items: scene({ colCls: (j) => (j === st.set ? 'bad' : '') }), say: 'Set ' + st.set + ' is empty: no item in set ' + (st.set - 1) + ' expected ' + r.word[st.set - 1] + ' next, so nothing can continue. The string is rejected here, before the rest of the input is even looked at.', meta: { empty: true } }); continue; }
          F.add({ items: scene({}), say: 'Now work through set ' + st.set + (st.set < n ? ', with ' + r.word[st.set] + ' as the next input symbol.' : ', at the end of the input.'), meta: { set: st.set } });
          continue;
        }
        if (emptyAt >= 0) continue;
        if (st.kind === 'accept' || st.kind === 'reject') continue;
        const to = [st.set, st.item];
        let arrows = [], cls = (j, q) => (j === to[0] && q === to[1] ? 'hot' : '');
        if (st.kind === 'init' || st.kind === 'predict' || st.kind === 'scan' || st.kind === 'complete') { shown[st.set] = Math.max(shown[st.set], st.item + 1); F.count('items'); }
        const L = st.link || {};
        if (st.kind === 'predict') { arrows = [{ from: L.by, to, cls: 'predict' }]; F.count('predict'); cls = (j, q) => (j === to[0] && q === to[1] ? 'hot' : j === L.by[0] && q === L.by[1] ? 'act' : ''); }
        if (st.kind === 'scan' || (st.kind === 'link' && L.kind === 'scan')) { arrows = [{ from: L.pred, to, cls: 'scan' }]; if (st.kind === 'scan') F.count('scan'); cls = (j, q) => (j === to[0] && q === to[1] ? 'hot' : j === L.pred[0] && q === L.pred[1] ? 'act' : ''); }
        if (st.kind === 'complete' || (st.kind === 'link' && L.kind === 'complete')) { arrows = [{ from: L.child, to, cls: 'complete' }, { from: L.pred, to, cls: 'predict' }]; if (st.kind === 'complete') F.count('complete'); cls = (j, q) => (j === to[0] && q === to[1] ? 'hot' : j === L.child[0] && q === L.child[1] ? 'good' : j === L.pred[0] && q === L.pred[1] ? 'act' : ''); }
        const say = st.kind === 'link' ? st.say.replace(/\(scan\)/, '(by a scan)').replace(/\(complete\)/, '(by another completion)') + ' The set keeps one copy; the extra link is what makes a second tree possible.' : st.say;
        F.add({ items: scene({ arrows, cls }), say, hl: { g: [st.prod !== undefined ? st.prod : r.sets[st.set][st.item].prod] }, meta: { kind: st.kind, to, from: st.kind === 'scan' ? L.pred : st.kind === 'complete' ? L.pred : null } });
      }
      const fin = r.sets[n].map((it, q) => [it, q]).filter(([it]) => done(G, it) && it.origin === 0 && G.productions[it.prod].A === G.start).map(([, q]) => q);
      cur = n + 1;
      if (emptyAt >= 0) F.add({ items: scene({ colCls: (j) => (j === emptyAt ? 'bad' : '') }), say: 'Reject: the chart died at set ' + emptyAt + ', so ' + T.PX.show(r.word) + ' is not in the language.', mark: 'rejected', meta: { yes: false } });
      else F.add({ items: scene({ cls: (j, q) => (j === n && fin.includes(q) ? 'good' : '') }), say: r.accepted ? 'The last set holds ' + fin.map((q) => '[' + itemText(G, r.sets[n][q]) + ', 0]').join(' and ') + ': the start symbol finished over the whole input, starting at 0. Accept' + (r.ambiguous ? ', and since that item can be reached in more than one way, there is more than one tree.' : '.') : 'No item [' + G.start + ' → … •, 0] is in the last set, so ' + T.PX.show(r.word) + ' is not in the language.', mark: r.accepted ? 'accepted' : 'rejected', meta: { yes: r.accepted } });
      return { frames: F.list, def: defOf(G), result: r.accepted };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'scan', once: true, pick: 'item', ask: 'The next step is a scan. Click the item whose dot will move over the next input symbol.',
        answer: (fr, i) => { const m = fr[i + 1].meta; return 'es' + m.from[0] + ':r:' + m.from[1]; }, explain: (fr, i) => 'A scan takes an item whose dot stands just before the next input symbol. ' + fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'complete' && fr[i + 1].meta.from[0] < fr[i + 1].meta.to[0], once: true, pick: 'item', ask: 'An item has just finished. Which earlier item was waiting for its nonterminal? Click it.',
        answer: (fr, i) => { const m = fr[i + 1].meta; return 'es' + m.from[0] + ':r:' + m.from[1]; }, explain: (fr, i) => 'Look in the set named by the finished item\'s origin for an item with the dot before that nonterminal. ' + fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the parser accept the string?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What does the number after an Earley item, as in [N → d • n, 2], mean?', options: ['How many symbols are left', 'The set where this rule\'s work began', 'The rule number', 'How often the item was added'], answer: 1, why: 'The origin: the input position where the parser started looking for this N, so a completion knows where to find the items waiting for it.' },
      { q: 'Why does a left-recursive rule like E → E + n not make Earley loop?', options: ['Earley rewrites the grammar first', 'Predicting E again in the same set adds an item that is already there, so nothing new happens', 'It does loop, but a limit stops it', 'Left recursion is turned into right recursion'], answer: 1, why: 'Sets never hold two copies of an item; a second prediction of the same item is simply ignored.' },
      { q: 'A set after the first one is empty. What follows?', options: ['The parser backtracks', 'Every later set is empty too, so the string is rejected', 'The parser predicts the start symbol again', 'Nothing; the next symbol may fix it'], answer: 1, why: 'Items only enter set j + 1 by scanning from set j or by moves inside set j + 1 that need something already there.' },
      { q: 'Which move is the only one that puts items into the next set?', options: ['Predict', 'Scan', 'Complete', 'All three'], answer: 1, why: 'Predict and complete add to the set being worked on; only a scan, reading an input symbol, crosses to the next set.' },
      { q: 'How does Earley\'s worst case compare with CYK\'s?', options: ['Earley is exponential', 'Both are cubic in the input length, but Earley needs no normal form and is faster on many grammars', 'Earley is always linear', 'CYK is always faster'], answer: 1, why: 'Earley is cubic in general, quadratic on unambiguous grammars and linear on many deterministic ones, and it takes the grammar as written.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'earley-trees', family: 'earley', order: 20, title: 'Two trees from one Earley chart',
    blurb: 'Every completed item [A → γ •, i] in set j says A derives the input from i to j. Those items are the nodes of the parse trees; when one can be built two ways, the sentence has two trees.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: SUMS, check: checkGrammar },
      { id: 'w', kind: 'string', label: 'String', def: 'x+x+x', min: 1, max: 5 },
    ],
    presets: [
      { label: 'Ambiguous: x+x+x', values: { g: SUMS, w: 'x+x+x' } },
      { label: 'Ambiguous: x+x (only one)', values: { g: SUMS, w: 'x+x' } },
      { label: 'Optional words: d n v', values: { g: SENT, w: 'dnv' } },
      { label: 'Dangling choice: a a b c b', values: { g: 'S → a S | a S c S | b', w: 'aabcb' } },
      { label: 'An ε-rule: aab', values: { g: OPT, w: 'aab' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 5)(inp),
    counters: [{ id: 'nodes', label: 'tree nodes' }, { id: 'trees', label: 'trees' }],
    run(inp) {
      const G = T.PX.G(inp.g), r = T.parse.earley(G, inp.w, { maxTrees: 2 }), n = r.word.length;
      const F = new T.Frames(['nodes', 'trees']);
      const isDone = (j, q) => done(G, r.sets[j][q]);
      const full = r.sets.map((S) => S.length);
      const base = chart(G, r, full, { filter: isDone, layout: 'columns' });
      // the tree hangs under the chart with its leaves under the input symbols they are
      const lvl = (t) => (t.children === null ? 0 : 1 + Math.max(0, ...t.children.map(lvl)));
      const top = base.height + 70;
      const forestOf = (t, opts) => {
        let k = 0, out;
        const go = (nd, path) => {
          if (nd.children === null) return { id: path, label: nd.sym, at: k++, cls: 'term' };
          const from = k;
          const kids = nd.children.length ? nd.children.map((c, j) => go(c, path + '.' + j)) : [{ id: path + '.e', label: 'ε', at: k - 0.5, cls: 'eps' }];
          return { id: path, label: nd.sym, from, to: k, prod: nd.prod, cls: ['nt', opts.lit && opts.lit === path ? 'hot' : '', opts.diff && opts.diff.includes(path) ? 'active' : ''].filter(Boolean).join(' '), children: kids };
        };
        out = go(t, 'r');
        return out;
      };
      // which completed item each node is: [A → γ •, from] in set to
      const itemOf = (nd) => r.sets[nd.to].findIndex((it) => it.prod === nd.prod && done(G, it) && it.origin === nd.from);
      const scene = (t, opts) => {
        const lit = opts.item;
        const ch = chart(G, r, full, { filter: isDone, layout: 'columns', cls: (j, q) => (lit && lit[0] === j && lit[1] === q ? 'hot' : opts.used && opts.used.has(j + ',' + q) ? 'act' : ''), tok: opts.tok });
        if (!t) return ch.items;
        const L = lvl(t);
        const fo = T.PX.forest({ prefix: 'eft', roots: [forestOf(t, opts)], x: 0, y: top + L * 62, gap: 1, gy: 62, xAt: ch.tokX });
        const keep = (it) => { if (!opts.show) return true; const m = /^eft:(?:n:(.*)|e:.*>(.*))$/.exec(it.key); return opts.show.has(m[1] || m[2]); };
        return ch.items.concat(fo.items.filter(keep));
      };
      if (!r.accepted) {
        F.add({ items: scene(null, {}), say: 'These are the completed items of the chart for ' + T.PX.show(r.word) + ': each says a nonterminal derives a piece of the input.', meta: { count: 0 } });
        F.add({ items: scene(null, {}), say: 'None of them is [' + G.start + ' → … •, 0] in the last set, so no tree covers the whole input: ' + T.PX.show(r.word) + ' is not in the language.', mark: 'rejected', meta: { count: 0 } });
        return { frames: F.list, def: defOf(G) };
      }
      const t0 = r.trees[0];
      const nodes = (t, path, out) => { if (t.children === null) return out; out.push([t, path]); t.children.forEach((c, j) => nodes(c, path + '.' + j, out)); return out; };
      // spans of every node, from the forest numbering
      const spanOf = (t) => { const m = new Map(); const walk = (f) => { if (f.from !== undefined) m.set(f.id, f); (f.children || []).forEach(walk); }; walk(forestOf(t, {})); return m; };
      const sp0 = spanOf(t0);
      F.add({ items: scene(null, {}), say: 'Only the completed items of the chart are shown: [A → γ •, i] in set j means A derives the input between positions i and j. A parse tree is made of exactly such items.', meta: { count: r.trees.length } });
      const show = new Set(['r']);
      const used = new Set();
      for (const [nd, path] of nodes(t0, 'r', [])) {
        const s = sp0.get(path), q = itemOf(s);
        used.add(s.to + ',' + q);
        nd.children.forEach((c, j) => show.add(path + '.' + j));
        if (!nd.children.length) show.add(path + '.e');
        F.count('nodes');
        const p = G.productions[nd.prod];
        F.add({ items: scene(t0, { item: [s.to, q], used, lit: path, show: new Set(show), tok: (j) => (j >= s.from && j < s.to ? 'act' : '') }), say: '[' + itemText(G, r.sets[s.to][q]) + ', ' + s.from + '] in set ' + s.to + ': ' + p.A + ' derives ' + (s.to > s.from ? T.PX.show(r.word.slice(s.from, s.to)) : 'ε') + ', so the node ' + p.A + ' gets the children ' + T.grammar.showRhs(G, p.rhs) + '.', hl: { g: [nd.prod] }, meta: { path } });
      }
      F.set('trees', 1);
      F.add({ items: scene(t0, { used }), say: r.ambiguous ? 'That is one tree. But the chart holds more: some completed item was made in two different ways.' : 'That is the only tree: every completed item on the way was made in exactly one way.', meta: { count: r.trees.length } });
      if (r.ambiguous) {
        const t1 = r.trees[1], sp1 = spanOf(t1);
        const had = new Set([...sp0.values()].map((x) => x.label + '@' + x.from + '-' + x.to + '#' + x.prod));
        const diff = [...sp1.values()].filter((x) => !had.has(x.label + '@' + x.from + '-' + x.to + '#' + x.prod)).map((x) => x.id);
        const used1 = new Set([...sp1.values()].map((x) => x.to + ',' + itemOf(x)));
        F.set('trees', 2);
        F.add({ items: scene(t1, { used: used1, diff }), say: 'Following the other way gives a second tree for the same ' + T.PX.show(r.word) + '. The purple nodes group the input differently: two trees, so the grammar is ambiguous.', mark: 'ambiguous' });
      }
      return { frames: F.list, def: defOf(G), result: r.trees.length };
    },
    predict: [
      { at: (f, i) => i === 0 && !!f.meta, once: true, pick: 'option', options: ['0', '1', '2 or more'], ask: 'How many parse trees does this string have?', answer: (fr) => { const c = fr[0].meta.count; return c >= 2 ? '2 or more' : String(c); }, explain: (fr) => (fr[0].meta.count >= 2 ? 'At least two: some completed item can be built in more than one way.' : fr[0].meta.count ? 'Just one.' : 'None: the string is not in the language.') },
      { at: (f, i, fr) => i >= 1 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.path === 'r.0', once: true, pick: 'item', ask: 'The root is placed. Which tree node gets its children next? Click it.', answer: () => 'eft:n:r.0', explain: (fr, i) => 'Nodes are filled depth first, leftmost first. ' + fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does a completed item [A → γ •, i] in set j tell you?', options: ['A will be predicted at j', 'A derives exactly the input between positions i and j', 'The input is accepted', 'γ is a terminal'], answer: 1, why: 'Its dot is at the end, so the whole of γ was recognised starting at i and ending at j.' },
      { q: 'Where does the root of every parse tree come from?', options: ['Any item in set 0', 'A completed start item with origin 0 in the last set', 'The first predicted item', 'The longest item'], answer: 1, why: 'It must derive the whole input, from position 0 to position n.' },
      { q: 'When does the chart give two different trees?', options: ['When a set has two items', 'When some completed item used by a tree can be built in two different ways', 'When the grammar has ε-rules', 'Never; Earley gives one tree'], answer: 1, why: 'Each item remembers every way it was made; choosing differently at one of them gives another tree.' },
      { q: 'Is ambiguity a problem for Earley\'s recogniser?', options: ['Yes, it loops', 'No: it still answers yes or no in cubic time; only listing every tree can take longer', 'Yes, it rejects ambiguous strings', 'Only with left recursion'], answer: 1, why: 'Sets hold each item once, however many ways it arises. There can be exponentially many trees, but the chart stays polynomial.' },
    ],
  });
})();
