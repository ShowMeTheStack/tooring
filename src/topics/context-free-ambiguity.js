// Ambiguity (part 3): a search that tries the words of a grammar shortest first until one has two parse
// trees, drawn side by side with the nodes where they part lit; precedence and associativity as the cure,
// with every node of an expression tree showing the value it computes; and inherent ambiguity, where two
// ways of counting meet in one word that no grammar can give a single tree.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CF = (T.CF = T.CF || {});
  // every stage item of these topics carries the class cf, so the styles in styles-cf.css stay with them
  const topic = (t) => { const run = t.run; t.run = (inp) => CF.mark(run(inp)); return T.topic(t); };
  const Geo = T.geom;

  T.family({ id: 'ambiguity', part: 'context-free', order: 20, title: 'Ambiguity', blurb: 'One word, two parse trees: how to find them, why they matter, how a grammar is rewritten to avoid them, and languages where no grammar can.' });

  /** Two trees side by side, the second shifted right of the first; returns items and the shift */
  function pair(G, t1, t2, o) {
    o = o || {};
    const d1 = K.tree.draw(CF.kitTree(G, t1, o.o1 || {}), Object.assign({ prefix: 'A', yield: true, gapX: 18 }, o.d1 || {}));
    const probe = t2 ? K.tree.draw(CF.kitTree(G, t2, o.o2 || {}), Object.assign({ prefix: 'B', yield: true, gapX: 18 }, o.d2 || {})) : null;
    const dx = probe ? d1.box.x + d1.box.w + (o.gap || 90) - probe.box.x : 0;
    const d2 = t2 ? K.tree.draw(CF.kitTree(G, t2, o.o2 || {}), Object.assign({ prefix: 'B', yield: true, gapX: 18, x: dx }, o.d2 || {})) : null;
    return { d1, d2, dx };
  }
  /** Nodes of tree a that tree b does not have (same symbol, span and rule) */
  function diff(a, b) {
    const sig = (r) => r.node.sym + '|' + r.from + '|' + r.to + '|' + r.node.prod;
    const nb = new Set(CF.nodes(b).filter((r) => r.node.children !== null).map(sig));
    return CF.nodes(a).filter((r) => r.node.children !== null && !nb.has(sig(r)));
  }

  // ---- the ambiguity finder -------------------------------------------------------------------------------------
  const PLUS_TIMES = 'E → E + E | E * E | x';
  const IFELSE = 'S → i S | i S e S | o';
  const PAREN_SS = 'S → S S | ( S ) | ε';
  const PAREN_OK = 'S → ( S ) S | ε';
  topic({
    id: 'amb-find', family: 'ambiguity', order: 10, title: 'The ambiguity finder',
    blurb: 'Try the words of the language from the shortest up, counting parse trees. The first word with two trees proves the grammar ambiguous; here are both, with the nodes where they disagree lit.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: PLUS_TIMES, check: (v) => CF.checkGrammar(v, { maxRules: 10 }) },
      { id: 'n', kind: 'number', label: 'Search words up to length', def: 5, min: 1, max: 7 },
    ],
    presets: [
      { label: 'E → E + E | E * E | x', values: { g: PLUS_TIMES, n: 5 } },
      { label: 'Dangling else', values: { g: IFELSE, n: 5 } },
      { label: 'Ambiguous on ε itself', values: { g: PAREN_SS, n: 4 } },
      { label: 'Two sides to grow: a', values: { g: 'S → a S | S a | a', n: 3 } },
      { label: 'Unambiguous brackets', values: { g: PAREN_OK, n: 6 } },
    ],
    counters: [{ id: 'words', label: 'words tried' }, { id: 'trees', label: 'trees of the last word' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const F = new T.Frames(['words', 'trees']);
      const res = T.grammar.ambiguity(G, inp.n, { traceLimit: 400 });
      const tried = res.trace.filter((s) => s.kind === 'try').map((s) => ({ w: s.word, k: s.trees }));
      if (res.ambiguous) tried.push({ w: res.word, k: 2 });
      const byLen = [];
      for (const t of tried) { (byLen[t.w.length] = byLen[t.w.length] || []).push(t); }
      const lens = byLen.map((x, i) => (x ? i : -1)).filter((i) => i >= 0);
      const MAXC = 6;
      const strip = (upto, hotWord) => {
        const items = [{ key: 's:head', kind: 'text', x: 0, y: -18, text: 'words of the language, shortest first', cls: 'title' }];
        let y = 0;
        lens.filter((l) => l <= upto).forEach((l) => {
          items.push({ key: 's:l:' + l, kind: 'text', x: 44, y: y + 24, text: 'len ' + l, anchor: 'end', cls: 'strong' });
          let x = 58;
          const list = byLen[l];
          const shown = list.length > MAXC ? list.slice(0, MAXC - 1).concat(list.filter((t) => t.k > 1)) : list;
          for (const t of shown.slice(0, MAXC)) {
            const text = CF.show(t.w) + (t.k > 1 ? '  2 trees' : '');
            const w = Math.max(48, Geo.textWidth(text, 15, { mono: true }) + 20);
            items.push({ key: 's:w:' + t.w.join(' '), kind: 'cell', x, y, w, h: 36, text, cls: 'mono chip ' + (t.k > 1 ? 'bad' : 'good') + (hotWord && t.w.join(' ') === hotWord ? ' hot' : '') });
            x += w + 8;
          }
          if (list.length > MAXC) items.push({ key: 's:more:' + l, kind: 'text', x: x + 2, y: y + 24, text: '+' + (list.length - MAXC) + ' more', cls: '' });
          y += 46;
        });
        return { items, h: y };
      };
      F.add({ items: strip(-1).items, say: 'Is the grammar ambiguous? Look for a word with two parse trees: list the words of the language by length, up to ' + inp.n + ', and count the trees of each.', meta: { amb: res.ambiguous } });
      let count = 0;
      for (const l of lens) {
        const list = byLen[l];
        count += list.length;
        F.set('words', count).set('trees', list[list.length - 1].k > 1 ? 2 : 1);
        const two = list.find((t) => t.k > 1);
        F.add({ items: strip(l, two ? two.w.join(' ') : null).items, say: 'Length ' + l + ': ' + list.map((t) => CF.show(t.w)).slice(0, 5).join(', ') + (list.length > 5 ? ' and ' + (list.length - 5) + ' more' : '') + '. ' + (two ? CF.show(two.w) + ' has two parse trees!' : (list.length === 1 ? 'It has' : 'Each has') + ' exactly one parse tree.') });
      }
      const def = { sections: [CF.gsec(G, 'g', 'Grammar')] };
      if (!res.ambiguous) {
        F.add({ items: strip(inp.n).items, say: 'No word up to length ' + inp.n + ' has two trees. That is not a proof: a longer word might. (Whether a grammar is ambiguous cannot be decided in general, so a search can only find ambiguity, never rule it out.)', mark: 'unambiguous so far' });
        return { frames: F.list, def };
      }
      const [t1, t2] = res.trees;
      const s = strip(inp.n, res.word.join(' '));
      const top = s.h + 90;
      const d1only = diff(t1, t2), d2only = diff(t2, t1);
      const ids1 = new Set(d1only.map((r) => r.id)), ids2 = new Set(d2only.map((r) => r.id));
      const topDiff = (list) => { const m = Math.min(...list.map((r) => r.depth)); return list.filter((r) => r.depth === m).map((r) => r.id); };
      const scene = (show2, lit) => {
        const p = pair(G, t1, show2 ? t2 : null, { d1: { y: top, yieldLabel: 'tree 1' }, d2: { y: top, yieldLabel: 'tree 2' }, o1: { cls: (n, id) => (lit && ids1.has(id) ? 'diff' : '') }, o2: { cls: (n, id) => (lit && ids2.has(id) ? 'diff' : '') } });
        return s.items.concat(p.d1.items, p.d2 ? p.d2.items : []);
      };
      F.add({ items: scene(false, false), say: 'Here is one parse tree of ' + CF.show(res.word) + '. Its leftmost derivation: ' + res.derivations[0].forms.map(CF.show).join(' ⇒ ') + '.', hl: { g: [...new Set(CF.nodes(t1).map((r) => r.node.prod).filter((x) => x !== null))] }, meta: { diffTop: topDiff(d1only).map((id) => 'A:n:' + id) } });
      F.add({ items: scene(true, false), say: 'And a second one, for the same word: ' + res.derivations[1].forms.map(CF.show).join(' ⇒ ') + '. Two parse trees, so two leftmost derivations: the grammar is ambiguous.', hl: { g: [...new Set(CF.nodes(t2).map((r) => r.node.prod).filter((x) => x !== null))] } });
      const r0 = d1only.sort((a, b) => a.depth - b.depth)[0];
      F.add({ items: scene(true, true), say: 'The red nodes are where the trees part: tree 1 has ' + r0.node.sym + ' over ' + CF.show(res.word.slice(r0.from, r0.to)) + ' built by ' + CF.prod(G, r0.node.prod) + ', which tree 2 never builds. Same word, different structure, and a compiler would read a different meaning from each.', mark: 'ambiguous' });
      return { frames: F.list, def };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Yes, a word will have two trees', 'No word in the search will have two trees'], ask: 'Will the search find a word with two parse trees?', answer: (fr) => (fr[0].meta.amb ? 'Yes, a word will have two trees' : 'No word in the search will have two trees'), explain: (fr) => fr[fr.length - 1].say },
      { at: (f) => f.meta && f.meta.diffTop, once: true, pick: 'item', ask: 'A second tree is coming. Click the highest node of this tree that the second tree will not have.', answer: (fr, i) => fr[i].meta.diffTop, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A grammar is ambiguous when…', options: ['some word has two parse trees', 'some word has two derivations', 'it has two rules for one nonterminal', 'it has ε-rules'], answer: 0, why: 'Many derivations share one tree; only two trees (equivalently two leftmost derivations) count.' },
      { q: 'The search tried every word up to length 7 and found one tree each. So…', options: ['the grammar may still be ambiguous', 'the grammar is unambiguous', 'the language is regular', 'the grammar is in normal form'], answer: 0, why: 'Ambiguity is undecidable in general; a longer word could still have two trees.' },
      { q: 'In the dangling else, i i o e o has two trees because…', options: ['the e can belong to either i', 'there are two o', 'the grammar has ε', 'i is a nonterminal'], answer: 0, why: 'The else may close the inner or the outer if: two structures for one word.' },
      { q: 'With S → S S | ( S ) | ε, even ε has two trees. Which?', options: ['S → ε, and S → S S with both children ε', 'S → ( S ) and S → ε', 'Only one', 'None, ε is not in the language'], answer: 0, why: 'S S can derive ε when both halves vanish, so ε has (infinitely) many trees.' },
    ],
  });

  // ---- precedence and associativity ---------------------------------------------------------------------------
  const digitsOf = (e) => [...new Set([...e].filter((c) => /[0-9]/.test(c)))].sort();
  const ambG = (e) => 'E → E + E | E - E | E * E | ( E ) | ' + digitsOf(e).join(' | ');
  const layG = (e) => 'E → E + T | E - T | T\nT → T * F | F\nF → ( E ) | ' + digitsOf(e).join(' | ');
  const valueOf = (t) => {
    if (t.children === null) return /[0-9]/.test(t.sym) ? +t.sym : null;
    const ch = t.children;
    if (ch.length === 1) return valueOf(ch[0]);
    if (ch.length === 3 && ch[0].sym === '(') return valueOf(ch[1]);
    const a = valueOf(ch[0]), b = valueOf(ch[2]), op = ch[1].sym;
    return op === '+' ? a + b : op === '-' ? a - b : a * b;
  };
  const opAtRoot = (t) => { let n = t; while (n.children && n.children.length === 1) n = n.children[0]; return n.children && n.children.length === 3 && n.children[0].sym !== '(' ? n.children[1].sym : null; };
  topic({
    id: 'amb-fix', family: 'ambiguity', order: 20, title: 'Precedence and associativity fix it',
    blurb: 'An ambiguous expression grammar gives one expression two trees, and the trees compute different numbers. A layered grammar leaves only one tree: products deeper than sums, and each operator grouping to the left.',
    inputs: [{ id: 'e', kind: 'string', label: 'Expression (digits, + - * and brackets)', def: '2+3*4', max: 9, alphabet: '0123456789+-*()' }],
    presets: [
      { label: 'Precedence: 2+3*4', values: { e: '2+3*4' } },
      { label: 'Associativity: 8-4-2', values: { e: '8-4-2' } },
      { label: 'Same value, still two trees: 1+2+3', values: { e: '1+2+3' } },
      { label: 'Brackets decide: (2+3)*4', values: { e: '(2+3)*4' } },
      { label: 'One operator, one tree: 7-5', values: { e: '7-5' } },
    ],
    check: (inp) => { if (!digitsOf(inp.e).length) return 'Expression: use at least one digit'; const G = CF.grammar(layG(inp.e)); return T.grammar.parseTrees(G, CF.word(G, inp.e), 1).length ? null : 'Expression: "' + inp.e + '" is not a well-formed expression'; },
    counters: [{ id: 'trees', label: 'trees in the ambiguous grammar' }, { id: 'values', label: 'different values' }],
    run(inp) {
      const A = CF.grammar(ambG(inp.e)), L = CF.grammar(layG(inp.e));
      const w = CF.word(A, inp.e);
      const all = T.grammar.parseTrees(A, w, 8);
      // two trees that compute different values, if there are such
      let t1 = all[0], t2 = all.find((t) => valueOf(t) !== valueOf(t1)) || all[1] || null;
      const tl = T.grammar.parseTrees(L, CF.word(L, inp.e), 1)[0];
      const F = new T.Frames(['trees', 'values']);
      const vals = new Set(all.map(valueOf));
      const nW = (G) => (n) => (CF.isN(G, n.sym) ? Math.max(...G.nonterminals.map((X) => Geo.textWidth(X + ' = 999', 16, { bold: true }))) + 22 : 0);
      const lab = (on) => (n) => (on && n.children !== null ? n.sym + ' = ' + valueOf(n) : n.sym);
      const word = CF.form(A, w.map((s, i) => ({ s, id: 'w' + i })), { prefix: 'expr', x: 0, y: -110, label: 'expression' }).items;
      const sceneA = (show2, vals1, vals2) => {
        const p = pair(A, t1, show2 ? t2 : null, { o1: { label: lab(vals1), w: nW(A) }, o2: { label: lab(vals2), w: nW(A) }, d1: { yield: false }, d2: { yield: false }, gap: 70 });
        const items = word.concat(p.d1.items, p.d2 ? p.d2.items : []);
        items.push({ key: 'capA', kind: 'text', x: p.d1.box.x, y: p.d1.box.y - 20, text: 'ambiguous grammar, tree 1', cls: 'title' });
        if (p.d2) items.push({ key: 'capB', kind: 'text', x: p.d2.box.x, y: p.d2.box.y - 20, text: 'tree 2', cls: 'title' });
        return items;
      };
      const sceneL = (on) => {
        const d = K.tree.draw(CF.kitTree(L, tl, { label: lab(on), w: nW(L) }), { prefix: 'L', gapX: 16 });
        return word.concat(d.items, [{ key: 'capL', kind: 'text', x: d.box.x, y: d.box.y - 20, text: 'layered grammar: the only tree', cls: 'title' }]);
      };
      F.set('trees', all.length >= 8 ? 8 : all.length).set('values', vals.size);
      F.add({ items: word, say: 'The expression ' + inp.e + ' in the grammar E → E + E | E - E | E * E | ( E ) | digit. Every operator rule has the same shape, E → E op E, so nothing says which operator to apply first.' });
      F.add({ items: sceneA(false, false, false), say: 'One parse tree. Its root rule is E → E ' + (opAtRoot(t1) || '…') + ' E, so ' + (opAtRoot(t1) || 'that operator') + ' is applied last.', hl: { amb: [] } });
      F.add({ items: sceneA(false, true, false), say: 'Evaluate bottom up: every E shows the number it stands for. Tree 1 computes ' + valueOf(t1) + '.', meta: { v2: t2 ? valueOf(t2) : null, opts: [...new Set([valueOf(t1), t2 ? valueOf(t2) : valueOf(t1) + 1, valueOf(t1) * 2, valueOf(t1) - 1])] } });
      if (t2) {
        F.add({ items: sceneA(true, true, false), say: 'A second parse tree of the same expression, with ' + (opAtRoot(t2) || 'another operator') + ' at the root.' });
        const same = valueOf(t1) === valueOf(t2);
        F.add({ items: sceneA(true, true, true), say: 'Tree 2 computes ' + valueOf(t2) + (same ? ', the same number, because ' + (opAtRoot(t1) === '+' ? '+' : 'the operator') + ' is associative. The grammar is still ambiguous: the structure differs, and with - in place of + the values would too.' : ', not ' + valueOf(t1) + '. Which tree a parser builds decides what the program means.'), mark: same ? undefined : 'ambiguous' });
      } else {
        F.add({ items: sceneA(false, true, false), say: 'This expression has only one tree even in the ambiguous grammar: with ' + (w.filter((s) => /[-+*]/.test(s)).length <= 1 ? 'one operator' : 'brackets fixing every choice') + ' there is nothing to choose. Two operators without brackets are what cause trouble.' });
      }
      F.add({ items: sceneL(false), say: 'The fix: one nonterminal per level. E → E + T | E - T | T, T → T * F | F, F → ( E ) | digit. A * can only be built inside a T, below every + and -, so products bind tighter. And E → E - T keeps the recursion on the left, so 8-4-2 groups as (8-4)-2.', meta: { root: opAtRoot(tl) } });
      F.add({ items: sceneL(true), say: 'The layered grammar has exactly one tree for ' + inp.e + ', and it computes ' + valueOf(tl) + ', the value the usual rules give. ' + (opAtRoot(tl) ? 'The root operator, applied last, is ' + opAtRoot(tl) + '.' : ''), mark: 'one tree' });
      return { frames: F.list, def: { sections: [CF.gsec(A, 'amb', 'Ambiguous grammar'), CF.gsec(L, 'lay', 'Layered grammar')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.v2 !== null && f.meta.v2 !== undefined && f.meta.opts, once: true, pick: 'option', ask: 'A second tree is coming. What will it compute?', options: (fr, i) => fr[i].meta.opts.map(String), answer: (fr, i) => String(fr[i].meta.v2), explain: (fr, i) => fr[i + 2] ? fr[i + 2].say : fr[i + 1].say },
      { at: (f) => f.meta && f.meta.root, once: true, pick: 'option', options: ['+', '-', '*'], ask: 'In the layered tree, which operator sits at the root (is applied last)?', answer: (fr, i) => fr[i].meta.root, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does putting * in T → T * F (below E → E + T) give * higher precedence?', options: ['A product can only be built inside a T, so it ends up deeper in the tree and is computed first', 'Because * comes later in the grammar', 'Because T is shorter than E', 'It gives + higher precedence'], answer: 0, why: 'Deeper nodes are evaluated before their parents.' },
      { q: 'E → E - T makes - group…', options: ['to the left: 8-4-2 = (8-4)-2', 'to the right', 'either way', 'not at all'], answer: 0, why: 'The recursion is on the left, so the leftmost operations sit deepest.' },
      { q: 'How would you make ^ (power) group to the right?', options: ['P → B ^ P | B', 'P → P ^ B | B', 'P → P ^ P | B', 'You cannot'], answer: 0, why: 'Right recursion puts the rightmost operation deepest: 2^3^2 = 2^(3^2).' },
      { q: '1+2+3 has two trees with the same value in the ambiguous grammar. Is that a problem?', options: ['Yes: the grammar is ambiguous whatever the values', 'No, equal values make it unambiguous', 'Only if the trees differ in height', 'Only for subtraction'], answer: 0, why: 'Ambiguity is about structure; with - the same shape gives different values.' },
      { q: 'Does the layered grammar describe the same language as the ambiguous one?', options: ['Yes, the same expressions with one tree each', 'No, it loses some expressions', 'No, it adds new ones', 'Only without brackets'], answer: 0, why: 'Rewriting a grammar to remove ambiguity keeps the words and changes only the trees.' },
    ],
  });

  // ---- inherent ambiguity --------------------------------------------------------------------------------------
  const IJK = 'S → X C | A Y\nX → a X b | ε\nC → c C | ε\nA → a A | ε\nY → b Y c | ε';
  topic({
    id: 'amb-inherent', family: 'ambiguity', order: 30, title: 'Inherent ambiguity: two ways of counting meet',
    blurb: 'aⁱbʲcᵏ with i = j or j = k. One half of a grammar counts a against b, the other b against c. Where both are true, aⁿbⁿcⁿ, they both apply, and no grammar can avoid it.',
    inputs: [{ id: 'j', kind: 'number', label: 'Number of b (j)', def: 2, min: 1, max: 3 }],
    presets: [{ label: 'j = 1', values: { j: 1 } }, { label: 'j = 2', values: { j: 2 } }, { label: 'j = 3', values: { j: 3 } }],
    counters: [{ id: 'one', label: 'words with one tree' }, { id: 'two', label: 'words with two trees' }],
    run(inp) {
      const G = CF.grammar(IJK), j = inp.j, m = j + 2;
      const F = new T.Frames(['one', 'two']);
      const wordOf = (i, k) => 'a'.repeat(i) + 'b'.repeat(j) + 'c'.repeat(k);
      const trees = (i, k) => T.grammar.parseTrees(G, [...wordOf(i, k)], 3).length;
      const counts = Array.from({ length: m }, (_, i) => Array.from({ length: m }, (_, k) => trees(i, k)));
      const cellKey = (i, k) => 'tb:' + i + ',' + k;
      const grid = (stage) => {
        const rows = counts.map((row, i) => row.map((c, k) => {
          const shown = stage >= 3 || (stage >= 1 && i === j) || (stage >= 2 && k === j);
          return { lines: [wordOf(i, k) || 'ε', shown ? (c === 0 ? 'not in L' : c + (c === 1 ? ' tree' : ' trees')) : '?'] };
        }));
        return K.table.draw({ rows, rowHead: rows.map((_, i) => 'i = ' + i), colHead: rows.map((_, k) => 'k = ' + k), corner: 'j = ' + j, mono: true, size: 14, cw: Math.max(96, Geo.textWidth(wordOf(m - 1, m - 1), 14, { mono: true }) + 20),
          cls: (i, k) => (i === j && k === j && stage >= 3 ? 'hot' : i === j && stage >= 1 ? 'src-a' : k === j && stage >= 2 ? 'src-b' : stage >= 3 && counts[i][k] === 0 ? 'empty' : '') });
      };
      const g0 = grid(0);
      F.add({ items: g0.items, say: 'The words aⁱb' + (j === 1 ? '' : 'ʲ') + 'cᵏ with j = ' + j + ' b in the middle, for i and k from 0 to ' + (m - 1) + '. L keeps those with i = j or j = k. The grammar has two halves: S → X C counts a against b (and allows any c), S → A Y counts b against c.' });
      F.set('one', counts[j].filter((c, k) => k !== j && c === 1).length);
      F.add({ items: grid(1).items, say: 'Row i = ' + j + ': as many a as b. These words come from S → X C, where X → a X b pairs each a with a b. One tree each, except where the column below also lights up.', hl: { g: [0, 1, 2] } });
      F.set('one', counts[j].filter((c, k) => k !== j && c === 1).length + counts.filter((r, i) => i !== j && r[j] === 1).length);
      F.add({ items: grid(2).items, say: 'Column k = ' + j + ': as many b as c, from S → A Y, where Y → b Y c pairs each b with a c.', hl: { g: [1, 5, 6] }, meta: { cross: cellKey(j, j) } });
      F.set('two', 1);
      F.add({ items: grid(3).items, say: 'The row and the column cross at ' + wordOf(j, j) + ', which is aⁿbⁿcⁿ with n = ' + j + '. It satisfies both conditions, so both halves derive it: two parse trees.' });
      const ts = T.grammar.parseTrees(G, [...wordOf(j, j)], 2);
      const p = pair(G, ts[0], ts[1], { d1: { y: 0, yieldLabel: 'via X C' }, d2: { y: 0, yieldLabel: 'via A Y' }, o1: { cls: (n) => (n.sym === 'X' ? 'pv' : '') }, o2: { cls: (n) => (n.sym === 'Y' ? 'px' : '') } });
      F.add({ items: p.d1.items.concat(p.d2.items), say: 'Both trees of ' + wordOf(j, j) + '. On the left, X matches every a with a b (orange) and the c come separately; on the right, Y matches every b with a c (blue) and the a come separately.' });
      F.add({ items: p.d1.items.concat(p.d2.items), say: 'Could a cleverer grammar give aⁿbⁿcⁿ one tree? No. To make the words with i = j it must pump a and b together, and for j = k, b and c together; for large n, aⁿbⁿcⁿ is reachable both ways, and the two kinds of tree cannot coincide (a stronger pumping lemma, which lets you mark the positions that must be pumped, makes this exact). A language like this is inherently ambiguous: every grammar for it is ambiguous.' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), { id: 'lang', kind: 'math', title: 'The language', text: 'L = { aⁱbʲcᵏ : i = j or j = k }\n  = { aⁿbⁿcᵏ } ∪ { aⁱbⁿcⁿ }' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.cross, once: true, pick: 'item', ask: 'Click the word that has two parse trees.', answer: (fr, i) => fr[i].meta.cross, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does "inherently ambiguous" mean?', options: ['Every grammar for the language is ambiguous', 'The given grammar is ambiguous', 'The language is not context-free', 'The language is finite'], answer: 0, why: 'It is a property of the language: no unambiguous grammar exists.' },
      { q: 'In aⁱbʲcᵏ with i = j or j = k, which words have two trees in the usual grammar?', options: ['aⁿbⁿcⁿ', 'aⁿbⁿ', 'all of them', 'none'], answer: 0, why: 'Only where both conditions hold do both halves of the grammar apply.' },
      { q: 'Is every ambiguous grammar\'s language inherently ambiguous?', options: ['No; E → E + E | x is ambiguous but a layered grammar describes the same language unambiguously', 'Yes', 'Only for finite languages', 'Only for regular languages'], answer: 0, why: 'Most ambiguity can be removed by rewriting; inherent ambiguity is the exception.' },
      { q: 'Can a regular language be inherently ambiguous?', options: ['No: a DFA gives an unambiguous right-linear grammar', 'Yes, often', 'Only if it is infinite', 'Only with ε'], answer: 0, why: 'One state per nonterminal, one move per symbol: each word has exactly one derivation.' },
    ],
  });
})();
