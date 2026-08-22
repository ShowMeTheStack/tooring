// CYK: for a grammar in Chomsky normal form, which nonterminals derive each substring of the input. The
// table is drawn as a pyramid standing on the input, so the cell for a substring sits right above the
// symbols it covers; each entry is found from two smaller cells, and arrows show which two. A second
// topic walks back down from the top cell to read off the parse trees, two of them when the grammar is
// ambiguous.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'cyk', part: 'parsing', order: 60, title: 'CYK', blurb: 'Dynamic programming over substrings: for a grammar in Chomsky normal form, which nonterminals derive each piece of the input, and the parse trees read back from the table.' });

  // our own grammars, all in Chomsky normal form with the start symbol on no right side
  const SUMS = 'S → E R | x\nE → E R | x\nR → P E\nP → +';
  const ANBN = 'S → A T | A B\nT → M B\nM → A T | A B\nA → a\nB → b';
  const NOT_CNF = 'S → a S b | a b';
  const CH = 48, GAP = 6;

  /** Run the core's CYK (converting to Chomsky normal form first when the grammar is not in it) */
  function solve(inp) {
    const G0 = T.PX.G(inp.g);
    const r = T.parse.cyk(G0, inp.w, { convert: true });
    return Object.assign(r, { G0, converted: r.grammar !== G0 });
  }

  /**
   * The pyramid: cell (L, i) covers w[i .. i+L) and sits above those symbols. text(L, i) is what it shows
   * (null: not filled yet). opts: {hot: [L, i], a: [L, i], b: [L, i] (the two sources), cls(L, i), cw}
   */
  function pyramid(w, text, opts) {
    const n = w.length, CW = opts.cw, items = [];
    const key = (L, i) => 'cy:' + L + ',' + i;
    const at = (L, i) => ({ x: i * CW + (L - 1) * CW / 2, y: -L * (CH + GAP) });
    const same = (p, L, i) => p && p[0] === L && p[1] === i;
    for (let L = 1; L <= n; L++) {
      const p0 = at(L, 0);
      items.push({ key: 'cy:len' + L, kind: 'text', x: p0.x - 12, y: p0.y + CH / 2 + 5, text: L === 1 ? 'length 1' : String(L), anchor: 'end', cls: 'title' });
      for (let i = 0; i + L <= n; i++) {
        const p = at(L, i), t = text(L, i);
        const cls = ['mono', t === null ? 'pend' : '', t === '∅' ? 'empty' : '', same(opts.hot, L, i) ? 'hot' : same(opts.a, L, i) ? 'src-a' : same(opts.b, L, i) ? 'src-b' : '', opts.cls ? opts.cls(L, i) || '' : ''].filter(Boolean).join(' ');
        items.push({ key: key(L, i), kind: 'cell', x: p.x + 2, y: p.y, w: CW - 4, h: CH, text: t === null ? '' : t, cls, pick: true, size: 16 });
      }
    }
    if (opts.a && opts.hot) {
      items.push({ key: 'cy:arA', kind: 'edge', from: key(opts.a[0], opts.a[1]), to: key(opts.hot[0], opts.hot[1]), bend: -24, gapA: -10, gapB: -8, cls: 'prov', audit: 'ignore', layer: 'top' });
      items.push({ key: 'cy:arB', kind: 'edge', from: key(opts.b[0], opts.b[1]), to: key(opts.hot[0], opts.hot[1]), bend: 24, gapA: -10, gapB: -8, cls: 'prov b', audit: 'ignore', layer: 'top' });
    }
    // the input underneath, with brackets for the substring in hand (split in two when there is a split)
    const brackets = [];
    if (opts.hot) {
      const [L, i] = opts.hot;
      if (opts.a) {
        const k = opts.a[0];
        brackets.push({ id: 'l', from: i, to: i + k, text: T.PX.show(w.slice(i, i + k)), cls: 'sa' });
        brackets.push({ id: 'r', from: i + k, to: i + L, text: T.PX.show(w.slice(i + k, i + L)), cls: 'sb' });
      } else brackets.push({ id: 'all', from: i, to: i + L, text: T.PX.show(w.slice(i, i + L)), cls: 'y' });
    }
    const s = K.string.draw({ text: w, x: 0, y: 10, cw: CW, ch: 44, prefix: 'cyw', brackets, cls: (j) => (opts.hot && j >= opts.hot[1] && j < opts.hot[1] + opts.hot[0] ? 'act' : '') });
    return { items: items.concat(s.items), key, at, right: n * CW };
  }

  const widthFor = (cells) => {
    let w = 64;
    for (const row of cells) if (row) for (const c of row) w = Math.max(w, T.geom.textWidth(T.PX.cellSet(c.map((e) => e.A)), 16, { mono: true }) + 22);
    return Math.ceil(w);
  };
  const defOf = (r) => ({ sections: [
    T.PX.gdef(r.grammar, { title: r.converted ? 'Grammar (put into Chomsky normal form)' : 'Grammar (Chomsky normal form)' }),
    { id: 'rule', kind: 'text', title: 'The rule for a cell', text: 'A goes in the cell of a substring when the substring splits into a left part and a right part, and there is a rule A → B C with B in the left part\'s cell and C in the right part\'s cell. For one symbol a, A goes in when A → a is a rule.' },
  ] });
  const checkG = (v) => T.PX.checkGrammar({ maxRules: 10, maxN: 6 })(v);
  const inputs = (max) => [
    { id: 'g', kind: 'grammar', label: 'Grammar', def: SUMS, check: checkG },
    { id: 'w', kind: 'string', label: 'String', def: 'x+x+x', min: 1, max },
  ];

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cyk-fill', family: 'cyk', order: 10, title: 'CYK fills its pyramid',
    blurb: 'Short substrings first: each cell lists the nonterminals that derive its substring, built from the two cells of every way to split it. The string is in the language when the start symbol reaches the top.',
    inputs: inputs(6),
    presets: [
      { label: 'x+x+x: two ways to split', values: { g: SUMS, w: 'x+x+x' } },
      { label: 'aⁿbⁿ: aabb', values: { g: ANBN, w: 'aabb' } },
      { label: 'Rejected: abab', values: { g: ANBN, w: 'abab' } },
      { label: 'One symbol: x', values: { g: SUMS, w: 'x' } },
      { label: 'Not in CNF: converted first', values: { g: NOT_CNF, w: 'aabb' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 6)(inp),
    counters: [{ id: 'cells', label: 'cells filled' }, { id: 'splits', label: 'splits tried' }, { id: 'found', label: 'entries found' }],
    run(inp) {
      const r = solve(inp), G = r.grammar, w = r.word, n = w.length;
      const CW = widthFor(r.cells);
      const sofar = Array.from({ length: n + 1 }, (_, L) => (L ? new Array(n - L + 1).fill(null) : null));
      const text = (L, i) => (sofar[L][i] === null ? null : T.PX.cellSet(sofar[L][i]));
      const px = n * CW + 56;
      const F = new T.Frames(['cells', 'splits', 'found']);
      let panel = { title: '', rows: [] };
      const scene = (opts) => {
        const pm = pyramid(w, text, Object.assign({ cw: CW }, opts));
        const pn = T.PX.panel({ prefix: 'cyp', x: px, y: -n * (CH + GAP), w: 330, title: panel.title, rows: panel.rows, rowH: 32, size: 14 });
        return pm.items.concat(pn.items);
      };
      const sub = (i, L) => T.PX.show(w.slice(i, i + L));
      const ruleIds = (A, rhs) => G.productions.filter((p) => p.A === A && p.rhs.join(' ') === rhs.join(' ')).map((p) => p.id);
      const conv = r.converted ? ' The grammar was not in Chomsky normal form, so it was converted first: the definition panel shows the rules used.' : '';
      F.add({ items: scene({}), say: 'The input ' + T.PX.show(w) + ' has ' + n + ' symbol' + (n > 1 ? 's' : '') + '. Each cell of the pyramid stands over a substring and will hold the nonterminals that derive it; the shortest substrings come first.' + conv });
      for (const st of r.trace) {
        if (st.kind === 'cell' && st.len === 1) {
          sofar[1][st.i] = st.adds.slice();
          F.count('cells').count('found', st.adds.length);
          panel = { title: 'Cell for ' + w[st.i], rows: st.adds.length ? st.adds.map((A) => ({ id: 'u' + A, text: A + ' → ' + w[st.i], cls: 'good' })) : [{ id: 'none', text: 'no rule A → ' + w[st.i], cls: 'bad' }] };
          F.add({ items: scene({ hot: [1, st.i] }), say: st.adds.length ? w[st.i] + ' comes straight from ' + st.adds.map((A) => A + ' → ' + w[st.i]).join(' and ') + ', so its cell holds ' + T.PX.set(st.adds) + '.' : 'No rule A → ' + w[st.i] + ' exists, so the cell for ' + w[st.i] + ' is empty, ∅.', hl: { g: [].concat(...st.adds.map((A) => ruleIds(A, [w[st.i]]))) }, meta: { len: 1 } });
        } else if (st.kind === 'split') {
          const L = st.len, i = st.i, k = st.split;
          if (k === 1) { sofar[L][i] = []; panel = { title: 'Splits of ' + sub(i, L), rows: [] }; }
          const fresh = [...new Set(st.found.map((f) => f.A))].filter((A) => !sofar[L][i].includes(A));
          sofar[L][i].push(...fresh);
          F.count('splits').count('found', fresh.length);
          if (k === L - 1) F.count('cells');
          panel.rows = panel.rows.map((x) => Object.assign({}, x, { cls: x.cls.replace('hot', '').trim() }));
          const got = [...new Set(st.found.map((f) => f.A))];
          panel.rows.push({ id: 's' + k, text: sub(i, k) + ' · ' + sub(i + k, L - k) + '   ' + T.PX.cellSet(st.left) + ' × ' + T.PX.cellSet(st.right) + '  ⇒  ' + (got.length ? got.join(' ') : '–'), cls: 'hot ' + (got.length ? 'good' : '') });
          const left = sub(i, k), right = sub(i + k, L - k);
          const say = 'Split ' + sub(i, L) + ' as ' + left + ' · ' + right + ': the left part\'s cell has ' + T.PX.set(st.left) + ', the right part\'s ' + T.PX.set(st.right) + '. ' +
            (st.found.length ? 'The rule' + (st.found.length > 1 ? 's ' : ' ') + st.found.map((f) => f.A + ' → ' + f.B + ' ' + f.C).join(', ') + (st.found.length > 1 ? ' fit' : ' fits') + (fresh.length ? ', so ' + T.PX.set(fresh) + ' join' + (fresh.length > 1 ? '' : 's') + ' the cell.' : ', but the cell has ' + T.PX.set(got) + ' already.')
              : (!st.left.length || !st.right.length ? 'An empty cell on one side means this split can make nothing.' : 'No rule A → B C has B from the left and C from the right.'));
          F.add({ items: scene({ hot: [L, i], a: [k, i], b: [L - k, i + k] }), say, hl: { g: st.found.map((f) => f.prod) }, meta: { split: true, len: L, i, k, right: [L - k, i + k] } });
        }
      }
      const top = sofar[n][0], yes = r.accepted;
      panel = { title: 'The top cell', rows: [{ id: 'top', text: T.PX.show(w) + ':  ' + T.PX.cellSet(top), cls: yes ? 'good' : 'bad' }, { id: 'v', text: yes ? G.start + ' is there: accept' : G.start + ' is missing: reject', cls: yes ? 'good' : 'bad' }] };
      F.add({ items: scene({ hot: [n, 0], cls: (L, i) => (L === n && i === 0 ? (yes ? 'good' : 'bad') : '') }), say: 'The top cell covers the whole string and holds ' + T.PX.set(top) + '. ' + (yes ? 'It contains the start symbol ' + G.start + ', so ' + T.PX.show(w) + ' is in the language' + (r.count > 1 ? ', in ' + r.count + ' different ways (the grammar is ambiguous)' : '') + '.' : 'The start symbol ' + G.start + ' is not there, so ' + T.PX.show(w) + ' is not in the language' + (top.length ? ', even though ' + T.PX.set(top) + ' derive it' : '') + '.'), mark: yes ? 'accepted' : 'rejected', meta: { yes } });
      return { frames: F.list, result: yes, def: defOf(r) };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.split && fr[i + 1].meta.len === 3 && fr[i + 1].meta.k === 1, once: true, pick: 'item',
        ask: (fr, i) => { const m = fr[i + 1].meta; return 'Next, a substring of length 3 is split as 1 + 2 symbols. Click the cell that holds the nonterminals of the right part (the last two symbols).'; },
        answer: (fr, i) => { const m = fr[i + 1].meta; return 'cy:' + m.right[0] + ',' + m.right[1]; }, explain: (fr, i) => 'The right part is two symbols long, so its cell is in the row of length 2, standing over exactly those two symbols. ' + fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'One cell is left: the whole string. Will the start symbol be in it?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'How many cells does CYK fill for a string of length n?', options: ['n', '2n', 'n(n + 1) / 2', 'n²'], answer: 2, why: 'One per substring: n of length 1, n − 1 of length 2, and so on up to 1 of length n.' },
      { q: 'How many ways are there to split a substring of length 5 into two non-empty parts?', options: ['2', '4', '5', '10'], answer: 1, why: 'The cut can go after the 1st, 2nd, 3rd or 4th symbol: L − 1 splits for length L.' },
      { q: 'Why does CYK need Chomsky normal form?', options: ['So every longer substring comes from exactly two smaller pieces', 'To remove ambiguity', 'Because CNF grammars are regular', 'To make the grammar shorter'], answer: 0, why: 'With A → B C and A → a only, a substring of two or more symbols is always made of two non-empty parts, each found in a smaller cell.' },
      { q: 'The top cell holds {E, R} but not S, the start symbol. What does that mean?', options: ['The string is in the language', 'The string is not in the language', 'The grammar is ambiguous', 'The table was filled wrongly'], answer: 1, why: 'E and R derive the whole string, but only S counts: the string is in the language exactly when S derives it.' },
      { q: 'Roughly how does the work of CYK grow with the length n of the string?', options: ['Like n', 'Like n²', 'Like n³', 'Like 2ⁿ'], answer: 2, why: 'About n²/2 cells, each with up to n − 1 splits, and each split checks the grammar\'s rules: n³ times the grammar\'s size.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  // Trees from the table: every entry remembers where it came from, so following those sources down from the
  // start symbol in the top cell spells out a parse tree. Two sources for one entry mean two trees.
  function treesOf(r, max) {
    const cells = r.cells, G = r.grammar;
    const entry = (L, i, A) => (cells[L][i] || []).find((e) => e.A === A);
    // all trees (up to max) for A over w[i .. i+L), each as {sym, prod, children, cell, split}
    const all = (A, i, L) => {
      const out = [];
      for (const s of entry(L, i, A).sources) {
        if (out.length >= max) break;
        if (s.terminal !== undefined) { out.push({ sym: A, prod: s.prod, cell: [L, i], children: [{ sym: s.terminal, prod: null, children: null }] }); continue; }
        for (const l of all(s.B, i, s.split)) for (const rr of all(s.C, i + s.split, L - s.split)) { if (out.length < max) out.push({ sym: A, prod: s.prod, cell: [L, i], split: s.split, children: [l, rr] }); }
      }
      return out;
    };
    void G;
    return all(r.grammar.start, 0, r.word.length);
  }

  T.topic({
    id: 'cyk-tree', family: 'cyk', order: 20, title: 'Reading trees out of the CYK table',
    blurb: 'Each entry remembers the split and the rule that made it. Walking down from the start symbol in the top cell rebuilds a parse tree; an entry with two sources gives a second tree.',
    inputs: inputs(7),
    presets: [
      { label: 'x+x+x: two trees', values: { g: SUMS, w: 'x+x+x' } },
      { label: 'aⁿbⁿ: one tree', values: { g: ANBN, w: 'aaabbb' } },
      { label: 'x+x: only one', values: { g: SUMS, w: 'x+x' } },
      { label: 'x+x+x+x: five trees', values: { g: SUMS, w: 'x+x+x+x' } },
      { label: 'Rejected: no tree', values: { g: ANBN, w: 'aab' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 7)(inp),
    counters: [{ id: 'nodes', label: 'tree nodes' }, { id: 'trees', label: 'trees' }],
    run(inp) {
      const r = solve(inp), G = r.grammar, w = r.word, n = w.length;
      const CW = widthFor(r.cells);
      const text = (L, i) => T.PX.cellSet(r.cells[L][i].map((e) => e.A));
      const F = new T.Frames(['nodes', 'trees']);
      const tx = n * CW + 70;
      const pyrH = n * (CH + GAP);
      const trees = r.accepted ? treesOf(r, 2) : [];
      // the tree stands to the right of the pyramid with its leaves on the input's baseline, so the leaves
      // read the string again; nodes not reached yet are left out (show: a set of paths)
      const forestOf = (t, opts) => {
        let k = 0;
        const go = (nd, path) => {
          if (nd.prod === null) return { id: path, label: nd.sym, at: k++, cls: 'term' };
          return { id: path, label: nd.sym, cls: ['nt', opts.lit && opts.lit.includes(path) ? 'hot' : '', opts.diff && opts.diff.includes(path) ? 'active' : ''].filter(Boolean).join(' '), children: nd.children.map((c, j) => go(c, path + '.' + j)) };
        };
        return go(t, 'r');
      };
      const lvl = (t) => (t.prod === null ? 0 : 1 + Math.max(...t.children.map(lvl)));
      const scene = (tree, opts) => {
        const pm = pyramid(w, text, Object.assign({ cw: CW }, opts));
        if (!tree) return pm.items;
        const gy = Math.min(72, (pyrH + 10) / Math.max(1, lvl(tree)));
        const fo = T.PX.forest({ prefix: 'cyt', roots: [forestOf(tree, opts)], x: tx, y: 32, gap: 52, gy });
        const keep = (it) => { if (!opts.show) return true; const m = /^cyt:(?:n:(.*)|e:.*>(.*))$/.exec(it.key); return opts.show.has(m[1] || m[2]); };
        return pm.items.concat(fo.items.filter(keep));
      };
      if (!r.accepted) {
        F.add({ items: scene(null, {}), say: 'The filled table for ' + T.PX.show(w) + '. The top cell holds ' + T.PX.set(r.cells[n][0].map((e) => e.A)) + '.' });
        F.add({ items: scene(null, { hot: [n, 0], cls: (L, i) => (L === n && i === 0 ? 'bad' : '') }), say: 'The start symbol ' + G.start + ' is not in the top cell, so there is nothing to walk back from: no parse tree exists, and ' + T.PX.show(w) + ' is not in the language.', mark: 'rejected', meta: { count: 0 } });
        return { frames: F.list, def: defOf(r) };
      }
      const t0 = trees[0];
      F.add({ items: scene(t0, { hot: [n, 0], lit: ['r'], show: new Set(['r']) }), say: 'The table is full and the top cell holds the start symbol ' + G.start + '. Every entry remembers the split and the rule that put it there, so we can walk back down and rebuild a tree.', meta: { count: r.count } });
      // grow the first tree in depth-first order, one entry at a time
      const show = new Set(['r']);
      const order = [];
      (function walk(t, path) { if (t.prod === null) return; order.push([t, path]); t.children.forEach((c, k) => walk(c, path + '.' + k)); })(t0, 'r');
      for (const [nd, path] of order) {
        nd.children.forEach((c, k) => show.add(path + '.' + k));
        F.count('nodes', nd.children.length);
        const [L, i] = nd.cell;
        const p = G.productions[nd.prod];
        let say, opts;
        if (nd.split) {
          opts = { hot: [L, i], a: [nd.split, i], b: [L - nd.split, i + nd.split], lit: [path], show: new Set(show) };
          say = nd.sym + ' over ' + T.PX.show(w.slice(i, i + L)) + ' came from the split ' + T.PX.show(w.slice(i, i + nd.split)) + ' · ' + T.PX.show(w.slice(i + nd.split, i + L)) + ' by ' + T.grammar.showProd(G, p) + ', so it gets the children ' + p.rhs.join(' and ') + '.';
        } else {
          opts = { hot: [L, i], lit: [path], show: new Set(show) };
          say = nd.sym + ' over ' + w[i] + ' came from the rule ' + T.grammar.showProd(G, p) + ': its child is the leaf ' + w[i] + '.';
        }
        F.add({ items: scene(t0, opts), say, hl: { g: [nd.prod] }, meta: { path } });
      }
      F.set('trees', 1);
      F.add({ items: scene(t0, {}), say: 'The first parse tree of ' + T.PX.show(w) + ' is complete; its leaves read the input from left to right.' + (r.count > 1 ? '' : ' No entry on the way had a second source, so this is the only tree.'), meta: { count: r.count } });
      if (trees.length > 1) {
        const t1 = trees[1];
        const diff = [];
        // a node of the second tree is new when the first tree has no node with its symbol over the same span
        const spans = (t, path, out, from) => { if (t.prod === null) return 1; let k = from, len = 0; t.children.forEach((c, j) => { const l = spans(c, path + '.' + j, out, k); k += l; len += l; }); out.push({ path, key: t.sym + '@' + from + '+' + len }); return len; };
        const s0 = [], s1 = [];
        spans(t0, 'r', s0, 0); spans(t1, 'r', s1, 0);
        const had = new Set(s0.map((x) => x.key));
        for (const x of s1) if (!had.has(x.key)) diff.push(x.path);
        const top = r.cells[n][0].find((e) => e.A === G.start);
        F.add({ items: scene(t0, { hot: [n, 0], cls: (L, i) => (L === n && i === 0 ? 'act' : '') }), say: 'But the walk could have gone another way: ' + G.start + ' in the top cell has ' + top.sources.length + ' sources' + (top.sources.length > 1 ? ' (splits after symbol ' + top.sources.map((s) => s.split).join(' and after symbol ') + ')' : '') + ', or some entry below it does.' });
        F.set('trees', 2);
        F.add({ items: scene(t1, { hot: t1.split ? [n, 0] : undefined, a: t1.split ? [t1.split, 0] : undefined, b: t1.split ? [n - t1.split, t1.split] : undefined, diff }), say: 'Taking the other source gives a second tree; the purple nodes cover pieces of the string the first tree did not group this way. Two trees for one string means the grammar is ambiguous.' + (r.count > 2 ? ' In all, the table holds ' + r.count + ' trees for ' + T.PX.show(w) + '.' : ''), mark: 'ambiguous' });
      }
      return { frames: F.list, def: defOf(r), result: r.count };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && fr[0].meta && fr[0].meta.count > 0, once: true, pick: 'option', options: ['0', '1', '2', 'More than 2'], ask: 'How many parse trees will the table give for this string?',
        answer: (fr) => { const c = fr[0].meta.count; return c > 2 ? 'More than 2' : String(c); }, explain: (fr) => 'The number of trees is the number of ways to pick a source at every entry on the way down: here ' + fr[0].meta.count + '.' },
      { at: (f, i, fr) => i >= 1 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.path && fr[i + 1].meta.path.split('.').length === 2, once: true, pick: 'item', ask: 'The walk moves down to the next entry. Click the tree node that is expanded next.',
        answer: (fr, i) => 'cyt:n:' + fr[i + 1].meta.path, explain: (fr, i) => 'The walk is depth first, left to right: the leftmost unexpanded nonterminal goes next. ' + fr[i + 1].say },
    ],
    quiz: [
      { q: 'What must each CYK entry store so that a tree can be read back?', options: ['Only the nonterminal', 'The split point and the rule that produced it', 'The whole substring', 'The number of the step that found it'], answer: 1, why: 'With the split and the rule A → B C, the walk knows which two cells to visit next and which nonterminals to look for there.' },
      { q: 'An entry for S in the top cell has two different sources. What follows?', options: ['The string is rejected', 'The grammar is ambiguous for this string', 'The table has an error', 'The string has two different lengths'], answer: 1, why: 'Each source gives a different tree for the same string.' },
      { q: 'How many leaves does a parse tree read from a CYK table for a string of length n have?', options: ['n', 'n − 1', '2n − 1', 'It depends on the grammar'], answer: 0, why: 'The leaves are the terminals of the string, one per symbol (Chomsky normal form has no ε-rules except possibly for the start).' },
      { q: 'In a CNF parse tree for a string of length n, how many nodes use a rule A → B C?', options: ['n', 'n − 1', '2n', 'n²'], answer: 1, why: 'Each A → B C node splits one piece into two; going from 1 piece to n pieces takes n − 1 splits.' },
    ],
  });
})();
