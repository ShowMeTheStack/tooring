// Grammars and derivations (part 3): a derivation as a ladder of sentential forms where each rewritten
// nonterminal splits into the symbols that replace it, a parse tree growing with its yield, one tree read
// off as different derivations, a grammar designer that tests a grammar against the language it is meant
// to describe, and the Chomsky hierarchy as nested regions a grammar's marker walks out of rule by rule.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CF = (T.CF = T.CF || {});
  // every stage item of these topics carries the class cf, so the styles in styles-cf.css stay with them
  const topic = (t) => { const run = t.run; t.run = (inp) => CF.mark(run(inp)); return T.topic(t); };
  const Geo = T.geom;

  T.family({ id: 'cfg', part: 'context-free', order: 10, title: 'Grammars and derivations', blurb: 'Rules that rewrite one nonterminal at a time: derivations, parse trees, and how to design a grammar for a language.' });

  const AB = 'S → A B\nA → a A | a\nB → b B | b';
  const EXPR = 'E → E + T | T\nT → T * F | F\nF → ( E ) | x';
  const ANBN = 'S → a S b | ε';
  const PAL = 'S → a S a | b S b | a | b | ε';
  const NEST = 'S → a S d | B\nB → b B c | ε';

  /** The first parse tree of w, or null */
  const treeOf = (G, w) => { const ts = T.grammar.parseTrees(G, w, 1); return ts.length ? ts[0] : null; };
  const countNodes = (t) => (t.children ? 1 + t.children.reduce((a, c) => a + countNodes(c), 0) : 0);
  const checkGW = (opts) => (inp) => {
    const G = CF.grammar(inp.g);
    const e = CF.checkWord(G, inp.w);
    if (e) return e;
    if (opts && opts.steps) { const t = treeOf(G, CF.word(G, inp.w)); if (t && countNodes(t) > opts.steps) return 'Word: its derivation has ' + countNodes(t) + ' steps; pick a shorter word (at most ' + opts.steps + ' steps) so every row stays readable'; }
    return null;
  };
  const ordName = { leftmost: 'leftmost', rightmost: 'rightmost', breadth: 'level-by-level' };

  /** Frames for a word that is not in the language: the start symbol, then the words that are */
  function notInLanguage(G, w, F, draw) {
    const words = T.grammar.language(G, Math.max(2, w.length + 1)).slice(0, 8);
    F.add({ items: draw([]), say: 'Start from ' + G.start + ' and try to reach ' + CF.show(w) + '.' });
    const items = draw(words);
    F.add({ items, say: 'No sequence of rules turns ' + G.start + ' into ' + CF.show(w) + ': it is not in the language, so it has no derivation and no parse tree. ' + (words.length ? 'The shortest words the grammar does make are listed underneath.' : 'This grammar makes no words that short.'), mark: 'rejected' });
  }
  const wordChips = (words, x, y, P) => {
    const items = [];
    let cx = x;
    words.forEach((wd, i) => { const t = CF.show(wd); const wdt = Math.max(40, Geo.textWidth(t, 16, { mono: true }) + 20); items.push({ key: P + ':w:' + i, kind: 'cell', x: cx, y, w: wdt, h: 38, text: t, cls: 'mono chip good' }); cx += wdt + 10; });
    if (words.length) items.push({ key: P + ':wl', kind: 'text', x: x, y: y - 12, text: 'words it does make', cls: 'title' });
    return items;
  };

  // ---- a derivation as a ladder ----------------------------------------------------------------------------
  topic({
    id: 'cfg-derive', family: 'cfg', order: 10, title: 'Derivations, step by step',
    blurb: 'Each step rewrites one nonterminal by one rule. A leftmost derivation always picks the leftmost nonterminal, a rightmost one the rightmost: watch both ladders reach the same word.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: AB, check: (v) => CF.checkGrammar(v, { maxRules: 12 }) },
      { id: 'w', kind: 'string', label: 'Word', def: 'aabb', max: 9 },
      { id: 'order', kind: 'choice', label: 'Order', def: 'both', options: [{ value: 'leftmost', label: 'Leftmost' }, { value: 'rightmost', label: 'Rightmost' }, { value: 'both', label: 'Both, side by side' }] },
    ],
    presets: [
      { label: 'Both orders: aabb', values: { g: AB, w: 'aabb', order: 'both' } },
      { label: 'Leftmost: x+x*x', values: { g: EXPR, w: 'x+x*x', order: 'leftmost' } },
      { label: 'Rightmost: x*(x)', values: { g: EXPR, w: 'x*(x)', order: 'rightmost' } },
      { label: 'Nested: abbccd', values: { g: NEST, w: 'abbccd', order: 'both' } },
      { label: 'The empty word ε', values: { g: ANBN, w: '', order: 'leftmost' } },
      { label: 'Not in the language: aba', values: { g: AB, w: 'aba', order: 'leftmost' } },
    ],
    check: checkGW({ steps: 13 }),
    counters: [{ id: 'steps', label: 'steps' }, { id: 'len', label: 'symbols in the form' }, { id: 'nts', label: 'nonterminals left' }],
    run(inp) {
      const G = CF.grammar(inp.g), w = CF.word(G, inp.w);
      const F = new T.Frames(['steps', 'len', 'nts']);
      const tree = treeOf(G, w);
      const def = { sections: [CF.gsec(G, 'g', 'Grammar')] };
      if (!tree) {
        notInLanguage(G, w, F, (words) => CF.form(G, [{ s: G.start, id: 'n0' }], { prefix: 'L0' }).items.concat(wordChips(words, 0, 110, 'nil')));
        return { frames: F.list, def };
      }
      const orders = inp.order === 'both' ? ['leftmost', 'rightmost'] : [inp.order];
      const lads = orders.map((o) => { const d = T.grammar.derivationOf(G, tree, o); return { o, d, tr: CF.track(G, d.steps) }; });
      const n = lads[0].d.steps.length;
      // geometry: each ladder is a column of rows; rule names sit to the right of each row
      const ROW = 60;
      let x = 0;
      for (const L of lads) {
        L.x = x;
        L.formW = Math.max(...L.tr.forms.map((f) => CF.form(G, f, {}).box.w));
        L.ruleW = Math.max(0, ...L.d.steps.map((s) => Geo.textWidth('by ' + CF.prod(G, s.prod), 14, { mono: true }))) + 10;
        x += 52 + L.formW + 18 + L.ruleW + 70;
      }
      def.sections.push(...lads.map((L, j) => ({ id: 'der' + j, kind: 'math', title: (lads.length > 1 ? (j ? 'Rightmost' : 'Leftmost') : ordName[L.o].replace(/^./, (c) => c.toUpperCase())) + ' derivation', text: L.tr.forms.map((f, k) => (k ? '⇒ ' : '  ') + CF.show(f.map((s) => s.s))).join('\n') })));
      const scene = (k) => {
        const items = [];
        for (const L of lads) {
          const P = L.o.slice(0, 1);
          items.push({ key: P + ':head', kind: 'text', x: L.x, y: -26, text: ordName[L.o] + ' derivation', cls: 'title' });
          for (let r = 0; r <= k; r++) {
            const form = L.tr.forms[r];
            const cur = r === k;
            const next = r < n ? L.d.steps[r] : null;
            const rewritten = next && r < k ? form[next.pos].id : null;
            const src = {};
            if (cur && r > 0) for (const s of form) src[s.id] = P + (r - 1) + ':' + (L.tr.born[r][s.id] || s.id);
            const born = r > 0 ? L.tr.born[r] : {};
            const f = CF.form(G, form, { prefix: P + r, x: L.x + 52, y: r * ROW, dim: !cur, src: cur ? src : null, cls: (s) => (s.id === rewritten ? 'act' : cur && born[s.id] ? 'new' : '') });
            items.push(...f.items);
            items.push({ key: P + r + ':arr', kind: 'text', x: L.x + 30, y: r * ROW + 27, text: r ? '⇒' : '', anchor: 'middle', cls: 'strong' });
            if (r > 0) items.push({ key: P + r + ':rule', kind: 'text', x: L.x + 52 + L.formW + 18, y: r * ROW + 26, text: 'by ' + CF.prod(G, L.d.steps[r - 1].prod), cls: cur ? 'mono' : '' });
          }
        }
        return items;
      };
      const form0 = lads[0].tr.forms;
      const nts = (f) => f.filter((s) => CF.isN(G, s.s)).length;
      F.set('len', 1).set('nts', 1);
      F.add({ items: scene(0), say: 'Every derivation starts from the start symbol ' + G.start + '. ' + (lads.length > 1 ? 'The left ladder will always rewrite the leftmost nonterminal, the right one the rightmost.' : 'This one always rewrites the ' + (lads[0].o === 'leftmost' ? 'leftmost' : 'rightmost') + ' nonterminal.') + ' The target is ' + CF.show(w) + '.', hl: { g: [], der0: [0], der1: [0] }, meta: { next: lads[0].o[0] + '0:n0', order: lads[0].o, nextR: lads[1] ? 'r0:n0' : null } });
      for (let k = 1; k <= n; k++) {
        const says = lads.map((L) => {
          const st = L.d.steps[k - 1], p = G.productions[st.prod];
          const before = CF.show(L.tr.forms[k - 1].map((s) => s.s)), after = CF.show(L.tr.forms[k].map((s) => s.s));
          return (lads.length > 1 ? (L.o === 'leftmost' ? 'Leftmost' : 'Rightmost') + ': ' : '') + 'the ' + L.o + ' nonterminal is ' + p.A + ' (position ' + (st.pos + 1) + '); ' + CF.prod(G, p) + ' turns ' + before + ' into ' + after + '.';
        });
        F.count('steps').set('len', form0[k].length).set('nts', nts(form0[k]));
        const nx = (L, j) => (k < n ? L.o[0] + k + ':' + L.tr.forms[k][L.d.steps[k].pos].id : null);
        F.add({ items: scene(k), say: says.join(' '), hl: { g: lads.map((L) => L.d.steps[k - 1].prod), der0: [k], der1: [k] }, meta: { next: nx(lads[0], 0), order: lads[0].o, nextR: lads[1] ? nx(lads[1], 1) : null } });
      }
      const sameRules = lads.length > 1;
      F.add({ items: scene(n), say: 'No nonterminals are left: the form is the word ' + CF.show(w) + ', after ' + n + ' step' + (n === 1 ? '' : 's') + '. ' + (sameRules ? 'Both ladders used exactly the same rules the same number of times, only in another order: they describe one and the same parse tree.' : 'A word of the language is exactly a form with nothing left to rewrite.'), mark: 'accepted', hl: { der0: [n], der1: [n] } });
      return { frames: F.list, def };
    },
    predict: [
      { at: (f, i) => i < 3 && f.meta && f.meta.next, pick: 'item', ask: (fr, i) => 'Which symbol does the ' + (fr[i].meta.order || 'leftmost') + ' derivation rewrite next? Click it' + (fr[i].meta.nextR ? ' in the left ladder.' : '.'), answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i) => i === 3 && f.meta && f.meta.nextR, once: true, pick: 'item', ask: 'And the rightmost derivation: which symbol does it rewrite next? Click it in the right ladder.', answer: (fr, i) => fr[i].meta.nextR, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A sentential form is a A B. What does a leftmost derivation rewrite next?', options: ['a', 'A', 'B', 'Whichever has a rule'], answer: 1, why: 'Terminals are never rewritten; the leftmost nonterminal is A.' },
      { q: 'A leftmost and a rightmost derivation of the same word from the same parse tree…', options: ['have the same number of steps', 'can use different rules', 'always differ in length', 'are always identical'], answer: 0, why: 'Each step expands one node of the tree, so both take one step per internal node; only the order changes.' },
      { q: 'A word is in the language of a grammar when…', options: ['some derivation from the start symbol ends in it', 'every derivation ends in it', 'it has a rightmost derivation only', 'it contains a nonterminal'], answer: 0, why: 'One derivation is enough; a word has no nonterminals left.' },
      { q: 'With S → a S b | ε, how many steps derive aabb?', options: ['2', '3', '4', '5'], answer: 1, why: 'S ⇒ aSb ⇒ aaSbb ⇒ aabb: two uses of S → aSb and one of S → ε.' },
      { q: 'Why can a derivation choose which nonterminal to rewrite at all?', options: ['In a context-free grammar a rule applies to a nonterminal wherever it stands', 'Because the grammar is ambiguous', 'Only regular grammars allow it', 'It cannot: the order is fixed'], answer: 0, why: 'Context-free means the surroundings do not matter, so the nonterminals can be rewritten in any order.' },
    ],
  });

  // ---- the tree grows ------------------------------------------------------------------------------------------
  /** The final tree with every node's path id, and the step at which each node is expanded in a given order */
  function growth(G, tree, order) {
    const d = T.grammar.derivationOf(G, tree, order);
    const tb = T.grammar.treeOf(G, d.steps);
    const ids = new Map(CF.nodes(tb.tree).map((r) => [r.node, r.id]));
    const at = new Map();
    tb.trace.forEach((s, k) => { if (s.kind === 'grow') at.set(s.node, k - 1); });
    const partial = (k) => {
      const cp = (n) => ({ sym: n.sym, prod: n.prod, children: n.children === null || !(at.get(n) < k) ? null : n.children.map(cp) });
      return cp(tb.tree);
    };
    const nodeAt = (k) => { for (const [n, s] of at) if (s === k) return ids.get(n); return null; };
    return { d, tree: tb.tree, partial, nodeAt, steps: d.steps.length };
  }

  topic({
    id: 'cfg-tree', family: 'cfg', order: 20, title: 'A parse tree grows with its yield',
    blurb: 'Every rewrite gives a nonterminal leaf its children. Read the leaves left to right, the yield, and you get the sentential form of that moment; at the end, the word.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: EXPR, check: (v) => CF.checkGrammar(v, { maxRules: 12 }) },
      { id: 'w', kind: 'string', label: 'Word', def: 'x+x*x', max: 9 },
      { id: 'order', kind: 'choice', label: 'Order of growth', def: 'leftmost', options: [{ value: 'leftmost', label: 'Leftmost first' }, { value: 'rightmost', label: 'Rightmost first' }, { value: 'breadth', label: 'Level by level' }] },
    ],
    presets: [
      { label: 'x+x*x, leftmost first', values: { g: EXPR, w: 'x+x*x', order: 'leftmost' } },
      { label: 'x+x*x, level by level', values: { g: EXPR, w: 'x+x*x', order: 'breadth' } },
      { label: 'aabb with an ε leaf', values: { g: ANBN, w: 'aabb', order: 'leftmost' } },
      { label: 'Palindrome abbba, rightmost', values: { g: PAL, w: 'abbba', order: 'rightmost' } },
      { label: 'Not in the language: x+', values: { g: EXPR, w: 'x+', order: 'leftmost' } },
    ],
    check: checkGW({ steps: 14 }),
    counters: [{ id: 'steps', label: 'nodes expanded' }, { id: 'leaves', label: 'leaves' }, { id: 'open', label: 'nonterminal leaves' }],
    run(inp) {
      const G = CF.grammar(inp.g), w = CF.word(G, inp.w);
      const F = new T.Frames(['steps', 'leaves', 'open']);
      const def = { sections: [CF.gsec(G, 'g', 'Grammar')] };
      const tree = treeOf(G, w);
      if (!tree) {
        notInLanguage(G, w, F, (words) => K.tree.draw(CF.kitTree(G, { sym: G.start, children: null }), { yield: true, yieldLabel: 'yield', prefix: 'tr' }).items.concat(wordChips(words, -80, 190, 'nil')));
        return { frames: F.list, def };
      }
      const gr = growth(G, tree, inp.order);
      const n = gr.steps;
      def.sections.push({ id: 'der', kind: 'math', title: 'The derivation it follows (' + ordName[inp.order] + ')', text: gr.d.forms.map((f, k) => (k ? '⇒ ' : '  ') + CF.show(f)).join('\n') });
      const scene = (k, hot) => {
        const t = CF.kitTree(G, gr.partial(k), { cls: (nd, id) => (id === hot ? 'hot' : '') });
        const d = K.tree.draw(t, { yield: true, yieldLabel: 'yield', prefix: 'tr', gapX: 26, hot: hot ? [hot] : [] });
        const items = d.items;
        if (k > 0) items.push({ key: 'rule', kind: 'text', x: d.box.x, y: d.box.y - 26, text: 'step ' + k + ':  ' + CF.prod(G, gr.d.steps[k - 1].prod), cls: 'mono' });
        return items;
      };
      const stats = (k) => { const fr = gr.d.forms[k]; F.set('leaves', fr.length).set('open', fr.filter((s) => CF.isN(G, s)).length); };
      stats(0);
      F.add({ items: scene(0, null), say: 'The tree starts as its root, the start symbol ' + G.start + '. Its yield, the leaves read left to right, is just ' + G.start + '.', hl: { der: [0] }, meta: { next: 'tr:n:' + gr.nodeAt(0) } });
      for (let k = 1; k <= n; k++) {
        const st = gr.d.steps[k - 1], p = G.productions[st.prod];
        const id = gr.nodeAt(k - 1);
        F.count('steps'); stats(k);
        const yieldNow = CF.show(gr.d.forms[k]);
        F.add({ items: scene(k, id), say: 'The leaf ' + p.A + ' gets the children ' + (p.rhs.length ? p.rhs.join(' ') : 'ε') + ' by ' + CF.prod(G, p) + '. ' + (p.rhs.length ? '' : 'An ε child adds nothing to the yield. ') + 'The yield is now ' + yieldNow + (k === n ? ', the word itself.' : '.'), hl: { g: [st.prod], der: [k] }, meta: { next: k < n ? 'tr:n:' + gr.nodeAt(k) : null } });
      }
      F.add({ items: scene(n, null), say: 'Every leaf is a terminal (or ε), so the tree is complete and its yield is ' + CF.show(w) + '. Growing it ' + (inp.order === 'breadth' ? 'level by level' : inp.order + ' first') + ' or in any other order gives this same tree.', mark: 'accepted', hl: { der: [n] } });
      return { frames: F.list, def };
    },
    predict: [
      { at: (f, i) => i >= 1 && i <= 3 && f.meta && f.meta.next, pick: 'item', ask: 'Which leaf grows next? Click it in the tree.', answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'The yield of a partly grown parse tree is…', options: ['a sentential form of a derivation', 'always a word of the language', 'the list of rules used', 'the root'], answer: 0, why: 'The leaves, left to right, are exactly the form reached by the steps taken so far.' },
      { q: 'A node labelled A has the children a, B, c. Which rule must the grammar have?', options: ['A → a B c', 'A → B', 'B → a c', 'A → a | B | c'], answer: 0, why: 'An internal node and its children, left to right, are one rule.' },
      { q: 'How does an ε-rule show in a tree?', options: ['As a leaf labelled ε under the nonterminal', 'It does not appear', 'As a missing node', 'As the root'], answer: 0, why: 'The nonterminal gets a single child ε, which contributes nothing to the yield.' },
      { q: 'Growing the same tree leftmost first or level by level changes…', options: ['only the order in which nodes appear', 'the final tree', 'the word', 'the rules used'], answer: 0, why: 'Each order is a different derivation of the same tree.' },
    ],
  });

  // ---- one tree, many derivations -----------------------------------------------------------------------------
  topic({
    id: 'cfg-orders', family: 'cfg', order: 30, title: 'One tree, many derivations',
    blurb: 'Number the nodes of a finished parse tree in the order a leftmost derivation expands them, then in rightmost order. The numbers differ; the tree does not.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: AB, check: (v) => CF.checkGrammar(v, { maxRules: 12 }) },
      { id: 'w', kind: 'string', label: 'Word', def: 'aabb', max: 8 },
    ],
    presets: [
      { label: 'aabb', values: { g: AB, w: 'aabb' } },
      { label: 'x*x+x', values: { g: EXPR, w: 'x*x+x' } },
      { label: 'Nested: abcd', values: { g: NEST, w: 'abcd' } },
      { label: 'Only one nonterminal to pick each time: aabb', values: { g: ANBN, w: 'aabb' } },
    ],
    check: (inp) => { const e = checkGW({ steps: 12 })(inp); if (e) return e; const G = CF.grammar(inp.g); return treeOf(G, CF.word(G, inp.w)) ? null : 'Word: ' + (inp.w || 'ε') + ' is not in the language, so it has no tree'; },
    counters: [{ id: 'lm', label: 'leftmost steps' }, { id: 'rm', label: 'rightmost steps' }],
    run(inp) {
      const G = CF.grammar(inp.g), w = CF.word(G, inp.w);
      const tree = treeOf(G, w);
      const L = growth(G, tree, 'leftmost'), R = growth(G, tree, 'rightmost');
      const n = L.steps;
      const lmAt = {}, rmAt = {};
      for (let k = 0; k < n; k++) { lmAt[L.nodeAt(k)] = k + 1; rmAt[R.nodeAt(k)] = k + 1; }
      const F = new T.Frames(['lm', 'rm']);
      // each nonterminal node is a pill wide enough for two order badges at its ends: leftmost on the left
      const wide = Math.max(...G.nonterminals.map((A) => Geo.textWidth(A, 16, { bold: true }))) + 74;
      const fullT = L.tree;
      const trL = CF.track(G, L.d.steps), trR = CF.track(G, R.d.steps);
      const scene = (kl, kr, hot, phase) => {
        const t = CF.kitTree(G, fullT, { w: (nd) => (CF.isN(G, nd.sym) ? wide : 0), cls: (nd, id) => (id === hot ? 'hot' : '') });
        const d = K.tree.draw(t, { prefix: 'tr', gapX: 16, hot: hot ? [hot] : [] });
        const items = d.items;
        for (const [id, p] of d.pos) {
          if (lmAt[id] && lmAt[id] <= kl) items.push({ key: 'lm:' + id, kind: 'token', x: p.x - wide / 2 + 17, y: p.y, r: 12, text: String(lmAt[id]), cls: 'lm', audit: 'overlap-ok', enter: 'grow' });
          if (rmAt[id] && rmAt[id] <= kr) items.push({ key: 'rm:' + id, kind: 'token', x: p.x + wide / 2 - 17, y: p.y, r: 12, text: String(rmAt[id]), cls: 'rm', audit: 'overlap-ok', enter: 'grow' });
        }
        const by = d.box.y + d.box.h + 46;
        const f = CF.form(G, (phase === 'r' ? trR : trL).forms[phase === 'r' ? kr : kl], { prefix: 'form' + phase, x: d.box.x + 120, y: by, label: phase === 'r' ? 'rightmost form' : 'leftmost form' });
        return items.concat(f.items);
      };
      const key = (id) => 'tr:n:' + id;
      F.add({ items: scene(0, 0, null, 'l'), say: 'Here is the parse tree of ' + CF.show(w) + '. A derivation is a way of building it one node at a time. An orange badge on the left of a node will say when the leftmost derivation expands it; a blue one on the right, when the rightmost one does.', meta: { nextL: key(L.nodeAt(0)) } });
      for (let k = 1; k <= n; k++) {
        const id = L.nodeAt(k - 1), p = G.productions[L.d.steps[k - 1].prod];
        F.count('lm');
        F.add({ items: scene(k, 0, id, 'l'), say: 'Leftmost step ' + k + ': expand ' + p.A + ' by ' + CF.prod(G, p) + ', the leftmost nonterminal of ' + CF.show(L.d.forms[k - 1]) + '.', hl: { lm: [k], g: [p.id] }, meta: { nextL: k < n ? key(L.nodeAt(k)) : null } });
      }
      for (let k = 1; k <= n; k++) {
        const id = R.nodeAt(k - 1), p = G.productions[R.d.steps[k - 1].prod];
        F.count('rm');
        F.add({ items: scene(n, k, id, 'r'), say: 'Rightmost step ' + k + ': expand ' + p.A + ' by ' + CF.prod(G, p) + ', the rightmost nonterminal of ' + CF.show(R.d.forms[k - 1]) + (lmAt[id] === k ? '. It is expanded at the same moment in both orders.' : '; the leftmost derivation expanded it at step ' + lmAt[id] + '.'), hl: { rm: [k], g: [p.id] }, meta: { nextR: k < n ? key(R.nodeAt(k)) : null } });
      }
      const same = Object.keys(lmAt).every((id) => lmAt[id] === rmAt[id]);
      F.add({ items: scene(n, n, null, 'r'), say: same ? 'Every node got the same number twice: each form here had only one nonterminal, so leftmost and rightmost cannot differ. The tree still stands for both derivations.' : 'Both derivations used the same ' + n + ' rules on the same nodes, in a different order. A parse tree fixes the rules; the order is a free choice. So a word has one leftmost derivation per parse tree, and two trees mean two leftmost derivations: that is ambiguity.' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'),
        { id: 'lm', kind: 'math', title: 'Leftmost derivation', text: L.d.forms.map((f, k) => (k ? '⇒ ' : '  ') + CF.show(f)).join('\n') },
        { id: 'rm', kind: 'math', title: 'Rightmost derivation', text: R.d.forms.map((f, k) => (k ? '⇒ ' : '  ') + CF.show(f)).join('\n') }] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.nextR && fr[i + 1] && /Rightmost step 2/.test(fr[i + 1].say), once: true, pick: 'item', ask: 'Which node does the rightmost derivation expand next? Click it.', answer: (fr, i) => fr[i].meta.nextR, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i) => f.meta && f.meta.nextL && i === 1, once: true, pick: 'item', ask: 'Which node does the leftmost derivation expand next? Click it.', answer: (fr, i) => fr[i].meta.nextL, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'One parse tree has how many leftmost derivations?', options: ['Exactly one', 'One per node', 'As many as rightmost ones plus one', 'It depends on the word'], answer: 0, why: 'The leftmost rule fixes which node to expand at every step, so the tree determines the derivation.' },
      { q: 'A word has two different leftmost derivations. Then…', options: ['it has two different parse trees', 'the grammar is not context-free', 'the word is not in the language', 'it has exactly one tree'], answer: 0, why: 'Leftmost derivations and parse trees match one to one, so two of one mean two of the other: the grammar is ambiguous.' },
      { q: 'Why might the leftmost and rightmost numbers agree on every node?', options: ['Every form along the way has at most one nonterminal', 'The grammar is ambiguous', 'The word is empty', 'They never agree'], answer: 0, why: 'With one nonterminal there is only one choice, so every order is the same.' },
      { q: 'A tree has 7 internal nodes. How many steps does any derivation from it take?', options: ['7', '6', '8', 'It depends on the order'], answer: 0, why: 'Each step expands one internal node.' },
    ],
  });

  // ---- designing a grammar -------------------------------------------------------------------------------------
  const balanced = (w) => { let d = 0; for (const c of w) { d += c === '(' ? 1 : -1; if (d < 0) return false; } return d === 0; };
  const exprOK = (w) => { let i = 0; const E = () => T_() && (w[i] === '+' ? (i++, E()) : true); const T_ = () => F_() && (w[i] === '*' ? (i++, T_()) : true); const F_ = () => { if (w[i] === 'x') { i++; return true; } if (w[i] === '(') { i++; if (!E()) return false; if (w[i] !== ')') return false; i++; return true; } return false; }; return E() && i === w.length; };
  const blocks = (w) => { const m = /^(a*)(b*)$/.exec(w.join('')); return m ? [m[1].length, m[2].length] : null; };
  const TARGETS = {
    brackets: { name: 'balanced brackets', alphabet: ['(', ')'], n: 6, member: balanced, grammar: 'S → ( S ) S | ε',
      notes: { '( S ) S': 'a balanced string that is not empty starts with a pair: a balanced inside, then a balanced rest', 'ε': 'the empty string is balanced, and it lets the recursion stop', '( S )': 'wrap a balanced string in one more pair', 'S S': 'put two balanced strings side by side' } },
    anbn: { name: 'aⁿbⁿ (n ≥ 0)', alphabet: ['a', 'b'], n: 8, member: (w) => { const b = blocks(w); return !!b && b[0] === b[1]; }, grammar: 'S → a S b | ε',
      notes: { 'a S b': 'add one a in front and one b behind, so the counts stay equal', 'ε': 'n = 0 is allowed', 'a b': 'the smallest word with n = 1' } },
    pal: { name: 'palindromes over a and b', alphabet: ['a', 'b'], n: 5, member: (w) => w.join('') === w.slice().reverse().join(''), grammar: PAL,
      notes: { 'a S a': 'a palindrome stays one when the same letter is added at both ends', 'b S b': 'the same with b', 'a': 'a single letter is the middle of an odd palindrome', 'b': 'the other odd middle', 'ε': 'the middle of an even palindrome is empty' } },
    expr: { name: 'arithmetic expressions with x, +, * and brackets', alphabet: ['x', '+', '*', '(', ')'], n: 5, member: exprOK, grammar: EXPR,
      notes: { 'E + T': 'a sum: an expression, plus, a term', 'T': 'an expression may be a single term', 'T * F': 'a product: a term, times, a factor', 'F': 'a term may be a single factor', '( E )': 'brackets hold any expression', 'x': 'the variable is the smallest factor' } },
    atmost: { name: 'aⁱbʲ with i ≤ j', alphabet: ['a', 'b'], n: 6, member: (w) => { const b = blocks(w); return !!b && b[0] <= b[1]; }, grammar: 'S → a S b | S b | ε',
      notes: { 'a S b': 'match one a with one b', 'S b': 'extra b may follow, never extra a', 'ε': 'the empty word has i = j = 0' } },
  };
  topic({
    id: 'cfg-design', family: 'cfg', order: 40, title: 'Designing a grammar',
    blurb: 'Write rules with an idea behind each, then test: every word of the target up to some length should be generated, and nothing else. Missing and extra words show up in red.',
    inputs: [
      { id: 'lang', kind: 'choice', label: 'Target language', def: 'brackets', options: Object.entries(TARGETS).map(([k, v]) => ({ value: k, label: v.name })) },
      { id: 'g', kind: 'grammar', label: 'Your grammar', def: TARGETS.brackets.grammar, check: (v) => CF.checkGrammar(v, { maxRules: 12 }) },
      { id: 'n', kind: 'number', label: 'Test up to length', def: 6, min: 1, max: 8 },
    ],
    presets: [
      { label: 'Balanced brackets', values: { lang: 'brackets', g: TARGETS.brackets.grammar, n: 6 } },
      { label: 'Brackets, too few rules', values: { lang: 'brackets', g: 'S → ( S ) | ε', n: 6 } },
      { label: 'aⁿbⁿ with an extra rule', values: { lang: 'anbn', g: 'S → a S b | S S | ε', n: 6 } },
      { label: 'Palindromes, odd ones forgotten', values: { lang: 'pal', g: 'S → a S a | b S b | ε', n: 5 } },
      { label: 'Expressions', values: { lang: 'expr', g: EXPR, n: 5 } },
      { label: 'i ≤ j', values: { lang: 'atmost', g: TARGETS.atmost.grammar, n: 6 } },
    ],
    check: (inp) => {
      const G = CF.grammar(inp.g), L = TARGETS[inp.lang];
      const bad = G.terminals.find((t) => !L.alphabet.includes(t));
      if (bad) return 'Your grammar: "' + bad + '" is not in the alphabet of the target {' + L.alphabet.join(' ') + '}';
      if (Math.pow(L.alphabet.length, inp.n) > 40000) return 'Test up to length: at most ' + Math.floor(Math.log(40000) / Math.log(L.alphabet.length)) + ' for this alphabet';
      return null;
    },
    counters: [{ id: 'ok', label: 'words right' }, { id: 'miss', label: 'missing' }, { id: 'extra', label: 'extra' }],
    run(inp) {
      const G = CF.grammar(inp.g), L = TARGETS[inp.lang], n = inp.n;
      const F = new T.Frames(['ok', 'miss', 'extra']);
      const gen = new Set(T.grammar.language(G, n).map((w) => w.join('\u0001')));
      const target = T.grammar.allWords(L.alphabet, n).filter((w) => L.member(w));
      const tset = new Set(target.map((w) => w.join('\u0001')));
      const extras = [...gen].filter((k) => !tset.has(k)).map((k) => (k === '' ? [] : k.split('\u0001')));
      const rules = CF.rules(G, { prefix: 'g', x: 0, y: 0, maxW: 560 });
      const ry = rules.box.y + rules.box.h + 56;
      const rowsBy = [];
      for (let len = 0; len <= n; len++) {
        const t = target.filter((w) => w.length === len), x = extras.filter((w) => w.length === len);
        if (!t.length && !x.length) continue;
        rowsBy.push({ len, words: t.map((w) => ({ w, kind: gen.has(w.join('\u0001')) ? 'ok' : 'miss' })).concat(x.map((w) => ({ w, kind: 'extra' }))) });
      }
      const MAXC = 7;
      const testItems = (upto, lit) => {
        const items = [];
        let y = ry;
        items.push({ key: 't:head', kind: 'text', x: 0, y: ry - 22, text: 'target words, length by length', cls: 'title' });
        rowsBy.slice(0, upto).forEach((r) => {
          items.push({ key: 't:len:' + r.len, kind: 'text', x: 52, y: y + 24, text: 'len ' + r.len, anchor: 'end', cls: 'strong' });
          let x = 66;
          const shown = r.words.filter((v) => v.kind !== 'ok').concat(r.words.filter((v) => v.kind === 'ok')).slice(0, MAXC);
          shown.sort((a, b) => (a.w.join('') < b.w.join('') ? -1 : 1));
          for (const v of shown) {
            const text = CF.show(v.w);
            const w = Math.max(44, Geo.textWidth(text, 15, { mono: true }) + 20);
            items.push({ key: 't:w:' + r.len + ':' + v.w.join(''), kind: 'cell', x, y, w, h: 36, text, cls: 'mono chip ' + (v.kind === 'ok' ? 'good' : v.kind === 'miss' ? 'gone drop' : 'bad') + (lit === r.len && v.kind !== 'ok' ? ' hot' : ''), pick: true });
            x += w + 8;
          }
          if (r.words.length > MAXC) items.push({ key: 't:more:' + r.len, kind: 'text', x: x + 4, y: y + 24, text: '+' + (r.words.length - MAXC) + ' more', cls: '' });
          y += 46;
        });
        return items;
      };
      F.add({ items: rules.items, say: 'The target: ' + L.name + '. Up to length ' + n + ' it has ' + target.length + ' word' + (target.length === 1 ? '' : 's') + '. First, what each rule is for.' });
      G.productions.forEach((p) => {
        const r = CF.rhs(G, p.rhs);
        const note = L.notes[p.rhs.length ? r : 'ε'];
        const hot = CF.rules(G, { prefix: 'g', x: 0, y: 0, maxW: 560, cls: (A, rhs) => (A === p.A && rhs.join(' ') === p.rhs.join(' ') ? 'hot' : '') });
        F.add({ items: hot.items, say: CF.prod(G, p) + ': ' + (note ? note + '.' : 'a rule of your own; the test will show what it adds.'), hl: { g: [p.id] } });
      });
      let ok = 0, miss = 0, extra = 0;
      rowsBy.forEach((r, k) => {
        const o = r.words.filter((v) => v.kind === 'ok').length, m = r.words.filter((v) => v.kind === 'miss').length, x = r.words.filter((v) => v.kind === 'extra').length;
        ok += o; miss += m; extra += x;
        F.set('ok', ok).set('miss', miss).set('extra', extra);
        const missW = r.words.filter((v) => v.kind === 'miss').map((v) => CF.show(v.w)), extraW = r.words.filter((v) => v.kind === 'extra').map((v) => CF.show(v.w));
        F.add({ items: rules.items.concat(testItems(k + 1, r.len)), say: 'Length ' + r.len + ': ' + (o ? o + ' target word' + (o === 1 ? ' is' : 's are') + ' generated' : 'no target word is generated') + (m ? '; missing: ' + missW.slice(0, 4).join(', ') + (m > 4 ? ' and more' : '') : '') + (x ? '; generated but not in the target: ' + extraW.slice(0, 4).join(', ') + (x > 4 ? ' and more' : '') : '') + (!m && !x ? ', and nothing else.' : '.'), meta: { len: r.len, miss: m, extra: x, keys: r.words.filter((v) => v.kind !== 'ok').map((v) => 't:w:' + r.len + ':' + v.w.join('')) } });
      });
      const good = !miss && !extra;
      F.add({ items: rules.items.concat(testItems(rowsBy.length, -1)), say: good ? 'Every target word up to length ' + n + ' is generated and nothing else is. That is strong evidence, not a proof: a proof shows by induction that every rule keeps the words in the target, and that every target word has a derivation.' : 'The grammar ' + (miss ? 'misses ' + miss + ' target word' + (miss === 1 ? '' : 's') : '') + (miss && extra ? ' and ' : '') + (extra ? 'makes ' + extra + ' word' + (extra === 1 ? '' : 's') + ' outside the target' : '') + '. ' + (miss ? 'A missing word needs a rule that builds it.' : '') + (extra ? ' An extra word means some rule is too generous.' : ''), mark: good ? 'accepted' : 'rejected', meta: { good, miss, extra } });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Your grammar'), { id: 'goal', kind: 'text', title: 'Target', text: L.name + '. Suggested grammar: ' + L.grammar.replace(/\n/g, '; ') + '.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.len !== undefined && !fr.slice(i + 2).some((x) => x.meta && x.meta.len !== undefined), once: true, pick: 'option', options: ['All generated, nothing extra', 'Some are missing', 'Some extra words appear', 'Both missing and extra words'], ask: (fr, i) => 'The test now looks at length ' + fr[i + 1].meta.len + '. What will it find?', answer: (fr, i) => { const m = fr[i + 1].meta; return m.miss && m.extra ? 'Both missing and extra words' : m.miss ? 'Some are missing' : m.extra ? 'Some extra words appear' : 'All generated, nothing extra'; }, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2 && fr[i].meta && fr[i].meta.keys && fr[i].meta.keys.length, once: true, pick: 'item', ask: 'Click a word the grammar gets wrong.', answer: (fr, i) => fr[i].meta.keys, explain: 'Red words are made but not wanted; dashed ones are wanted but not made.' },
    ],
    quiz: [
      { q: 'Your grammar for balanced brackets is S → ( S ) | ε. Which word does it miss?', options: ['()()', '(())', '()', 'ε'], answer: 0, why: 'It only nests; nothing puts two balanced strings side by side.' },
      { q: 'Adding S → S S to S → a S b | ε…', options: ['adds words like abab that are not aⁿbⁿ', 'changes nothing', 'removes ε', 'makes the grammar regular'], answer: 0, why: 'Two words of aⁿbⁿ side by side are generally not of that form.' },
      { q: 'A grammar matches the target on every word up to length 8. Does that prove they are equal?', options: ['No, a difference may only show on longer words', 'Yes, always', 'Yes, if the grammar has no ε-rules', 'Only for regular languages'], answer: 0, why: 'Testing is evidence; equality of context-free grammars cannot be decided in general, so a proof needs an argument.' },
      { q: 'For palindromes, why does S → a S a | b S b | ε miss aba?', options: ['Nothing makes an odd middle', 'ε cannot be in the middle', 'b S b is wrong', 'It does not miss it'], answer: 0, why: 'Every step adds two letters and ε adds none, so only even lengths come out.' },
      { q: 'In E → E + T | T, T → T * F | F, F → ( E ) | x, why is * on a lower level than +?', options: ['So that products are built first and bind tighter', 'To make the grammar shorter', 'Because * is rarer', 'It does not matter'], answer: 0, why: 'Each level groups more tightly than the one above it: that is how a grammar expresses precedence.' },
    ],
  });

  // ---- the Chomsky hierarchy -----------------------------------------------------------------------------------
  const LEVELS = [
    { id: 't0', n: 0, label: 'Type 0: unrestricted' },
    { id: 't1', n: 1, label: 'Type 1: context-sensitive' },
    { id: 't2', n: 2, label: 'Type 2: context-free' },
    { id: 't3', n: 3, label: 'Type 3: regular' },
  ];
  const H_RIGHT = 'S → a S | b A\nA → b A | ε';
  const H_MIXED = 'S → a A | ε\nA → S b';
  const H_CS = 'S → a S B C | a B C\nC B → B C\na B → a b\nb B → b b\nb C → b c\nc C → c c';
  const H_SWAP = 'S → A S B | ε\nA B → B A\nA → a\nB → b';
  topic({
    id: 'cfg-hierarchy', family: 'cfg', order: 50, title: 'Where a grammar sits in the Chomsky hierarchy',
    blurb: 'Check the rules one by one. The grammar starts in the innermost class and walks outwards whenever a rule breaks that class\'s form.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar (any rules)', def: H_CS, check: (v) => CF.checkGrammar(v, { cf: false, maxRules: 9 }) }],
    presets: [
      { label: 'Right-linear (regular)', values: { g: H_RIGHT } },
      { label: 'Linear but mixed sides', values: { g: H_MIXED } },
      { label: 'Context-free: aⁿbⁿ', values: { g: 'S → a S b | a b' } },
      { label: 'Context-sensitive: aⁿbⁿcⁿ', values: { g: H_CS } },
      { label: 'Unrestricted rules, simple language', values: { g: H_SWAP } },
    ],
    counters: [{ id: 'rules', label: 'rules checked' }, { id: 'type', label: 'type so far' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const F = new T.Frames(['rules', 'type']);
      // concentric boxes, the outermost first; each has a strip at the bottom for the grammar's marker
      const W0 = 470, H0 = 380, IN = 26, TOP = 34, STRIP = 46;
      const boxes = LEVELS.map((L, i) => ({ L, x: i * IN, y: i * TOP, w: W0 - 2 * i * IN, h: H0 - i * (TOP + STRIP) }));
      const spot = (lv) => { const b = boxes[lv]; return lv === 3 ? { x: b.x + b.w / 2, y: b.y + b.h / 2 + 18 } : { x: b.x + b.w / 2, y: b.y + b.h - STRIP / 2 - 2 }; };
      const RX = W0 + 50;
      const ruleTexts = G.productions.map((p) => CF.prod(G, p));
      const cw = Math.max(...ruleTexts.map((t) => Geo.textWidth(t, 15, { mono: true }))) + 26;
      const verdicts = [];
      const scene = (k, level, hotRegion) => {
        const items = [];
        boxes.forEach((b, i) => items.push({ key: 'reg:' + b.L.id, kind: 'region', x: b.x, y: b.y, w: b.w, h: b.h, text: b.L.label, cls: 'r' + i + (hotRegion === i ? ' hot' : ''), pick: true }));
        const s = spot(level);
        items.push({ key: 'mark', kind: 'token', x: s.x - 52, y: s.y, r: 9, cls: 'act' });
        items.push({ key: 'markl', kind: 'text', x: s.x - 36, y: s.y + 5, text: 'this grammar', cls: 'strong' });
        items.push({ key: 'rh', kind: 'text', x: RX, y: -8, text: 'rules', cls: 'title' });
        ruleTexts.forEach((t, i) => {
          const v = verdicts[i];
          items.push({ key: 'rule:' + i, kind: 'cell', x: RX, y: 8 + i * 46, w: cw, h: 36, text: t, cls: 'mono chip' + (i === k - 1 ? ' hot' : '') + (v && i < k ? (v.level >= 2 ? '' : v.level === 1 ? ' lead-n' : ' bad') : '') });
          if (v && i < k) items.push({ key: 'tag:' + i, kind: 'text', x: RX + cw + 12, y: 8 + i * 46 + 23, text: v.tag, cls: v.level === 0 ? 'bad' : v.level === 3 ? 'good' : 'hot' });
        });
        return items;
      };
      const ruleLevel = (p) => {
        const c = T.grammar.classify(T.grammar.make(G.start, [{ lhs: p.lhs, rhs: p.rhs }], { nonterminals: G.nonterminals, terminals: G.terminals }));
        const tr = c.trace[0];
        const tag = !tr.contextFree ? (tr.monotone ? 'not context-free, but never shrinks' : 'shrinks: ' + p.lhs.length + ' symbols become ' + p.rhs.length) : tr.rightLinear && tr.leftLinear ? 'linear at both ends' : tr.rightLinear ? 'right-linear' : tr.leftLinear ? 'left-linear' : 'context-free';
        return { level: c.level, tag };
      };
      F.set('type', 3);
      F.add({ items: scene(0, 3, null), say: 'Every grammar is type 0. The question is how far in it goes. Start optimistic: in the innermost class, regular, and test the ' + G.productions.length + ' rules one at a time.' });
      let level = 3;
      G.productions.forEach((p, i) => {
        verdicts[i] = ruleLevel(p);
        const prefix = T.grammar.make(G.start, G.productions.slice(0, i + 1).map((q) => ({ lhs: q.lhs, rhs: q.rhs })), { nonterminals: G.nonterminals, terminals: G.terminals });
        const c = T.grammar.classify(prefix);
        const was = level;
        level = c.level;
        F.count('rules').set('type', level);
        let why = CF.prod(G, p) + ': ' + c.trace[i].say.replace(/^.*?: /, '');
        if (level < was) {
          if (was === 3 && level === 2 && (c.trace.slice(0, i + 1).every((t) => t.rightLinear || t.leftLinear))) why += ' Each rule is linear, but right-linear and left-linear rules are mixed, and together they can count: out to context-free.';
          else if (level === 2) why += ' So the grammar leaves the regular class: context-free at best.';
          else if (level === 1) why += ' A left side with several symbols is not context-free; since the rule never shrinks the form, the grammar is still context-sensitive.';
          else why += ' A rule that shrinks the form breaks the context-sensitive (non-contracting) form: type 0.';
        } else why += ' The grammar stays where it is.';
        F.add({ items: scene(i + 1, level, null), say: why, hl: { g: [p.id] }, meta: { level } });
      });
      const cls = T.grammar.classify(G);
      let extra = '';
      if (inp.g === H_SWAP) extra = ' Note that the type belongs to the grammar, not the language: these rules make exactly the words with as many a as b, which a context-free grammar also describes.';
      if (inp.g === H_MIXED) extra = ' Indeed it makes aⁿbⁿ, which no regular grammar can.';
      F.add({ items: scene(G.productions.length, cls.level, cls.level), say: cls.trace[cls.trace.length - 1].say + extra, meta: { final: 'reg:' + LEVELS[cls.level].id } });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), { id: 'forms', kind: 'math', title: 'The forms', text: 'Type 3: A → w B or A → w (or all left-linear)\nType 2: A → α (one nonterminal on the left)\nType 1: α → β with |α| ≤ |β| (S → ε allowed\n        when S is on no right side)\nType 0: any α → β' }] } };
    },
    predict: [
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'item', ask: 'All rules checked. Click the class the grammar belongs to (its innermost one).', answer: (fr) => fr[fr.length - 1].meta.final, explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => i === 0 && fr[2] && fr[2].meta, once: true, pick: 'option', options: ['Type 3', 'Type 2', 'Type 1', 'Type 0'], ask: 'After the first rule, which type will the grammar be at?', answer: (fr) => 'Type ' + fr[1].meta.level, explain: (fr) => fr[1].say },
    ],
    quiz: [
      { q: 'S → a A, A → S b. Every rule is linear. Is the grammar regular?', options: ['No: right- and left-linear rules are mixed, and it makes aⁿbⁿ', 'Yes, linear rules are regular', 'Yes, it has no ε', 'It is type 0'], answer: 0, why: 'A regular grammar must be all right-linear or all left-linear.' },
      { q: 'Which rule keeps a grammar context-sensitive but not context-free?', options: ['C B → B C', 'A → ε (A on a right side)', 'A → a B', 'a B → ε'], answer: 0, why: 'Two symbols on the left is not context-free; two become two, so it does not shrink.' },
      { q: 'A grammar has a rule A B → B A and generates the words with as many a as b. The language is…', options: ['context-free, though this grammar is not', 'only context-sensitive', 'regular', 'not recursively enumerable'], answer: 0, why: 'A grammar\'s type is an upper bound on its language; S → a S b S | b S a S | ε describes the same words.' },
      { q: 'Why is S → ε allowed in a type 1 grammar only when S is on no right side?', options: ['So ε can be in the language without any form shrinking inside a derivation', 'Because ε is not a word', 'To keep it regular', 'It is never allowed'], answer: 0, why: 'Non-contracting rules can never produce ε, so this one exception lets ε in without letting forms shrink later.' },
    ],
  });
})();
