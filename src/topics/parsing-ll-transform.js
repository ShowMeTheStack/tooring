// Making a grammar fit for top-down parsing: removing left recursion (the same strings, but trees that lean
// right instead of left) and left factoring (alternatives that share a beginning are merged, so the choice
// waits until the symbols that differ). Each shows the grammar before and after and checks the LL(1) table.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'll-transform', part: 'parsing', order: 30, title: 'Rewriting for top-down parsing', blurb: 'Left recursion and shared prefixes stop a predictive parser; rewriting the grammar removes them without changing the language.' });

  const LISTS = 'L → L ; x | x';
  const SIGNS = 'E → E + n | E - n | n';
  const INDIRECT = 'S → A a | b\nA → S c | d';
  const FINE = 'L → x R\nR → ; x R | ε';
  const checkG = (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 4, noEps: false })(v);
  // the core writes a fresh primed name in quotes before it exists in a grammar; here it is a nonterminal
  const unquote = (s) => s.replace(/"([A-Za-z][A-Za-z0-9_]*'+)"/g, '$1');
  const rows = (G, cls) => G.productions.map((p) => ({ id: T.grammar.showProd(G, p), text: T.grammar.showProd(G, p), cls: cls ? cls(p) || '' : '' }));
  const ll1Note = (G) => { const t = T.ll.ll1Table(G); return { t, text: t.ll1 ? 'Its LL(1) table has no conflicts.' : 'Its LL(1) table still has ' + t.conflicts.length + ' conflict' + (t.conflicts.length > 1 ? 's' : '') + '.' }; };

  /** A word of the language with a few symbols, to show the shape of its tree */
  function sample(G) {
    const ws = T.grammar.language(G, 5);
    let best = null;
    for (const w of ws) if (w.length <= 5 && (!best || w.length > best.length)) best = w;
    return best;
  }

  T.topic({
    id: 'left-recursion', family: 'll-transform', order: 10, title: 'Removing left recursion',
    blurb: 'A → A α | β makes a top-down parser call A forever. Rewritten as A → β A\', A\' → α A\' | ε, the grammar makes the same strings, but its trees lean right instead of left.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: LISTS, check: checkG }],
    presets: [
      { label: 'Lists: L → L ; x | x', values: { g: LISTS } },
      { label: 'Two operators', values: { g: SIGNS } },
      { label: 'Indirect: S → A a, A → S c', values: { g: INDIRECT } },
      { label: 'Nothing to remove', values: { g: FINE } },
    ],
    counters: [{ id: 'steps', label: 'rewriting steps' }, { id: 'added', label: 'new nonterminals' }],
    run(inp) {
      const G = T.PX.G(inp.g), lr = T.cfg.leftRecursive(G), F = new T.Frames(['steps', 'added']);
      const res = lr.length ? T.cfg.removeLeftRecursion(G) : { grammar: G, trace: [], added: [] };
      const H = res.grammar, w = sample(G);
      const lrSet = new Set(lr.map((x) => x.A));
      const beforeW = T.PX.panel({ rows: rows(G) }).w;
      const treeOf = (g) => { if (!w) return null; const r = T.parse.earley(g, w, { maxTrees: 1 }); return r.tree; };
      const t0 = treeOf(G), t1 = treeOf(H);
      const tw = (t) => (t ? T.PX.kitTree(t, { G }) : null);
      const ty = Math.max(G.productions.length, H.productions.length) * 38 + 90;
      // the second tree starts to the right of the first one
      const span = (t, g) => { if (!t) return 0; const d = K.tree.draw(T.PX.kitTree(t, { G: g }), { prefix: 'x', gapY: 56, gapX: 10 }); const xs = [...d.pos.values()].map((p) => p.x); return Math.max(...xs) - Math.min(...xs) + 50; };
      const x1 = Math.max(beforeW + 60, span(t0, G) + 80);
      const scene = (o) => {
        o = o || {};
        const items = T.PX.panel({ prefix: 'bf', x: 0, y: 0, title: 'Before', rows: rows(G, (p) => (lrSet.has(p.A) && p.rhs[0] === p.A ? 'bad' : o.lit && o.lit.includes(p.A) ? 'hot' : '')), rowH: 32, size: 16 }).items;
        if (o.after) items.push(...T.PX.panel({ prefix: 'af', x: beforeW + 60, y: 0, title: o.afterTitle || 'After', rows: o.after, rowH: 32, size: 16 }).items);
        if (o.tree0 && t0) {
          items.push({ key: 'lr:cap0', kind: 'text', x: 0, y: ty, text: 'A tree for ' + T.PX.show(w) + ' before', cls: 'strong', size: 15 });
          const d = K.tree.draw(T.PX.kitTree(t0, { G }), { prefix: 'lt0', gapY: 56, gapX: 10 });
          const minx = Math.min(...[...d.pos.values()].map((p) => p.x));
          items.push(...K.tree.draw(T.PX.kitTree(t0, { G }), { prefix: 'lt0', gapY: 56, gapX: 10, x: -minx + 20, y: ty + 40 }).items);
        }
        if (o.tree1 && t1) {
          items.push({ key: 'lr:cap1', kind: 'text', x: x1, y: ty, text: 'and after', cls: 'strong', size: 15 });
          const d = K.tree.draw(T.PX.kitTree(t1, { G: H }), { prefix: 'lt1', gapY: 56, gapX: 10 });
          const minx = Math.min(...[...d.pos.values()].map((p) => p.x));
          items.push(...K.tree.draw(T.PX.kitTree(t1, { G: H }), { prefix: 'lt1', gapY: 56, gapX: 10, x: x1 + 20 - minx, y: ty + 40 }).items);
        }
        void tw;
        return items;
      };
      if (!lr.length) {
        F.add({ items: scene({ tree0: true }), say: 'No nonterminal can derive a string that starts with itself, so there is no left recursion to remove. ' + ll1Note(G).text });
        F.add({ items: scene({ tree0: true }), say: 'Right recursion, as in R → ; x R, is harmless for a top-down parser: it reads ; and x before it calls R again, so every call makes progress.', mark: 'nothing to do', meta: { none: true } });
        return { frames: F.list, def: { sections: [T.PX.gdef(G)] } };
      }
      const pre = ll1Note(G);
      F.add({ items: scene({}), say: lr.map((x) => x.A).join(', ') + (lr.length > 1 ? ' are' : ' is') + ' left-recursive' + (lr.some((x) => !x.immediate) ? ' (through another nonterminal)' : '') + ': a procedure for ' + lr[0].A + ' would call ' + (lr[0].immediate ? 'itself' : 'round the loop back to itself') + ' before reading anything. ' + pre.text, hl: { g: G.productions.filter((p) => lrSet.has(p.A) && p.rhs[0] === p.A).map((p) => p.id) } });
      if (t0) F.add({ items: scene({ tree0: true }), say: 'Its tree for ' + T.PX.show(w) + ' leans to the left: each ' + lr[0].A + ' grows out of the ' + lr[0].A + ' below it, and the first symbol read sits deepest of all.' });
      const working = new Map();
      for (const st of res.trace) {
        if (!/order|substitute|immediate/.test(st.kind)) continue;
        F.count('steps');
        if (st.kind === 'substitute') working.set(st.A, st.rules.map((r) => st.A + ' → ' + T.grammar.showRhs(G, r)));
        if (st.kind === 'immediate') {
          F.count('added');
          for (const X of [st.A, st.B]) working.set(X, H.productions.filter((p) => p.A === X).map((p) => T.grammar.showProd(H, p)));
        }
        const after = [...working.values()].flat().map((t) => ({ id: t, text: t, cls: st.kind === 'immediate' && (t.startsWith(st.A + ' ') || t.startsWith(st.B + ' ')) ? 'hot' : st.kind === 'substitute' && t.startsWith(st.A + ' ') ? 'act' : '' }));
        F.add({ items: scene({ after, afterTitle: 'Rewriting', lit: [st.A] }), say: unquote(st.say), meta: { kind: st.kind } });
      }
      const post = ll1Note(H);
      F.add({ items: scene({ after: rows(H, (p) => (res.added.includes(p.A) ? 'good' : '')), tree0: true, tree1: true }), say: 'The new grammar has no left recursion and makes exactly the same strings. ' + (t1 ? 'Its tree for ' + T.PX.show(w) + ' leans right instead, with ε at the bottom where the repetition stops. ' : '') + post.text, mark: post.t.ll1 ? 'LL(1)' : 'done', meta: { ll1: post.t.ll1 } });
      return { frames: F.list, def: { sections: [T.PX.gdef(G, { title: 'Before' }), T.PX.gdef(H, { id: 'h', title: 'After' }), { id: 'rule', kind: 'text', title: 'The rewrite', text: 'A → A α1 | … | A αm | β1 | … | βn becomes A → β1 A\' | … | βn A\' and A\' → α1 A\' | … | αm A\' | ε. For indirect recursion, order the nonterminals and first substitute earlier ones at the front of later ones\' rules.' }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Yes, the same strings', 'No, it loses some strings', 'No, it adds strings'], ask: 'After the rewrite, will the grammar generate the same language?', answer: () => 'Yes, the same strings', explain: 'The rewrite only changes how the strings are built: β followed by any number of α\'s, either way.' },
      { at: (f, i, fr) => i === fr.length - 2 && fr[fr.length - 1].meta && fr[fr.length - 1].meta.ll1 !== undefined, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will the rewritten grammar be LL(1)?', answer: (fr) => (fr[fr.length - 1].meta.ll1 ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Remove the left recursion from L → L ; x | x.', options: ['L → x L\', L\' → ; x L\' | ε', 'L → ; x L | x', 'L → x ; L', 'L → L x | ;'], answer: 0, why: 'β = x starts every string; the repeated part α = ; x moves into L\'.' },
      { q: 'What happens to the shape of the parse trees?', options: ['Nothing', 'They lean right instead of left', 'They become flat', 'They get one level shorter'], answer: 1, why: 'Repetitions are now built by a rule that recurses at its right end.' },
      { q: 'Why does left-associativity need care after the rewrite?', options: ['The grammar is ambiguous', 'The tree for n − n − n now groups to the right, so a compiler must rebuild the left grouping itself', 'Subtraction is lost', 'It does not'], answer: 1, why: 'The language is the same, but the natural reading of the tree changes.' },
      { q: 'S → A a | b and A → S c | d. Is S left-recursive?', options: ['No, no rule starts with S', 'Yes, S ⇒ A a ⇒ S c a', 'Only A is', 'Only with ε'], answer: 1, why: 'Indirect left recursion: S reaches itself at the left through A.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  const CMDS = 'C → d o x | d o y | d z';
  const OPT = 'T → x y | x y z';
  const MIX = 'A → a b c | a b d | a e\nB → b';
  const checkF = (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 4 })(v);

  T.topic({
    id: 'left-factor', family: 'll-transform', order: 20, title: 'Left factoring',
    blurb: 'Alternatives that begin the same way force a guess. Factoring keeps the shared beginning once and moves the choice to a new nonterminal that decides where the alternatives differ.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: CMDS, check: checkF }],
    presets: [
      { label: 'Commands: d o x | d o y | d z', values: { g: CMDS } },
      { label: 'An optional ending: x y | x y z', values: { g: OPT } },
      { label: 'Two levels of sharing', values: { g: MIX } },
      { label: 'Nothing to factor', values: { g: 'L → x R\nR → ; x R | ε' } },
    ],
    counters: [{ id: 'steps', label: 'factoring steps' }, { id: 'added', label: 'new nonterminals' }],
    run(inp) {
      const G = T.PX.G(inp.g), res = T.cfg.leftFactor(G), H = res.grammar, F = new T.Frames(['steps', 'added']);
      const steps = res.trace.filter((s) => s.kind === 'factor');
      const A0 = steps.length ? steps[0].A : G.start;
      // replay the rewriting to know the rules after every step
      const rules = new Map(G.nonterminals.map((A) => [A, (T.grammar.info(G).byA.get(A) || []).map((p) => p.rhs.slice())]));
      const isNew = new Set();
      // the choices of A as a tree: each alternative a chain of its symbols; a new nonterminal at the end of a
      // chain is a branch point with its own alternatives under it
      const trie = (A, key, depth) => ({ id: key, label: A, cls: isNew.has(A) ? 'nt active' : 'nt', children: (rules.get(A) || []).map((rhs, k) => {
        let chain = null, tail = null;
        const syms = rhs.length ? rhs : ['ε'];
        syms.forEach((s, i) => {
          const id = key + '/' + k + '.' + i;
          const n = isNew.has(s) && i === syms.length - 1 && depth < 4 ? trie(s, id, depth + 1) : { id, label: s, cls: s === 'ε' ? 'eps' : T.grammar.isN(H, s) || T.grammar.isN(G, s) ? 'nt' : 'term', children: [] };
          if (!chain) chain = n; else tail.children.push(n);
          tail = n;
        });
        return chain;
      }) });
      const pw = Math.max(T.PX.panel({ rows: rows(G) }).w, T.PX.panel({ rows: rows(H) }).w);
      const gy = Math.max(G.productions.length, H.productions.length) * 38 + 70;
      const scene = (o) => {
        o = o || {};
        const items = T.PX.panel({ prefix: 'gf', x: 0, y: 0, title: o.title || 'Grammar', rows: o.rows, rowH: 32, size: 16, w: pw }).items;
        const tr = trie(A0, 'q', 0);
        const d = K.tree.draw(tr, { prefix: 'tf', gapY: 62, gapX: 14 });
        const minx = Math.min(...[...d.pos.values()].map((p) => p.x));
        items.push({ key: 'tf:cap', kind: 'text', x: pw + 60, y: -6, text: 'The choices of ' + A0 + ', symbol by symbol', cls: 'strong', size: 15 });
        items.push(...K.tree.draw(tr, { prefix: 'tf', gapY: 62, gapX: 14, x: pw + 80 - minx, y: 40 }).items);
        void gy;
        return items;
      };
      const showRows = (hot) => [...rules].flatMap(([A, rs]) => rs.map((r) => { const t = A + ' → ' + T.grammar.showRhs(H, r); return { id: t, text: t, cls: hot && hot(A, r) ? 'hot' : isNew.has(A) ? 'good' : '' }; }));
      const pre = ll1Note(G);
      if (!steps.length) {
        F.add({ items: scene({ rows: showRows() }), say: 'No two alternatives of a nonterminal begin with the same symbol, so there is nothing to factor. ' + pre.text });
        F.add({ items: scene({ rows: showRows() }), say: 'From its very first symbol, each alternative can be told apart from the others: the choices fan out at the root.', mark: 'nothing to do', meta: { none: true } });
        return { frames: F.list, def: { sections: [T.PX.gdef(G)] } };
      }
      F.add({ items: scene({ rows: showRows((A, r) => A === A0) }), say: A0 + ' has alternatives that begin the same way, so after reading their first symbol the parser still cannot tell which rule it is in. ' + pre.text, hl: { g: G.productions.filter((p) => p.A === A0).map((p) => p.id) } });
      for (const st of steps) {
        const pre2 = st.prefix.join('\u0001');
        const rs = rules.get(st.A), group = rs.filter((r) => r.slice(0, st.prefix.length).join('\u0001') === pre2), rest = rs.filter((r) => !group.includes(r));
        rules.set(st.A, [st.prefix.concat([st.B]), ...rest]);
        rules.set(st.B, group.map((r) => r.slice(st.prefix.length)));
        isNew.add(st.B);
        F.count('steps').count('added');
        F.add({ items: scene({ rows: showRows((A) => A === st.A || A === st.B), title: 'Grammar, step ' + F.counts.steps }), say: unquote(st.say) + (group.some((r) => r.length === st.prefix.length) ? ' One alternative ends right after the prefix, so ' + st.B + ' gets an ε-rule.' : ''), meta: { kind: 'factor' } });
      }
      const post = ll1Note(H);
      F.add({ items: scene({ rows: showRows(), title: 'Factored' }), say: 'Now each choice is made only where the alternatives differ: the shared symbols are read once, and the new nonterminal' + (res.added.length > 1 ? 's decide' : ' decides') + ' after them. ' + post.text, mark: post.t.ll1 ? 'LL(1)' : 'done', meta: { ll1: post.t.ll1 } });
      return { frames: F.list, def: { sections: [T.PX.gdef(G, { title: 'Before' }), T.PX.gdef(H, { id: 'h', title: 'After' }), { id: 'rule', kind: 'text', title: 'The rewrite', text: 'A → α β1 | α β2 | γ, with α the longest prefix shared by two or more alternatives, becomes A → α A\' | γ and A\' → β1 | β2. Repeat until no two alternatives of any nonterminal share a first symbol.' }] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && !(fr[1] && fr[1].meta && fr[1].meta.none), once: true, pick: 'option', options: ['1', '2', '3'], ask: 'How many new nonterminals will factoring add?', answer: (fr) => String(fr[fr.length - 1].counters.added), explain: (fr) => 'One for each prefix that gets factored: ' + fr[fr.length - 1].counters.added + ' here.' },
      { at: (f, i, fr) => i === fr.length - 2 && fr[fr.length - 1].meta && fr[fr.length - 1].meta.ll1 !== undefined, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will the factored grammar be LL(1)?', answer: (fr) => (fr[fr.length - 1].meta.ll1 ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Factor T → x y | x y z.', options: ['T → x y T\', T\' → ε | z', 'T → x T\', T\' → y | z', 'T → x y z', 'T → T z | x y'], answer: 0, why: 'The shared prefix is x y; after it, either nothing or z.' },
      { q: 'Which conflict does left factoring cure?', options: ['FIRST/FOLLOW', 'FIRST/FIRST between alternatives with a common prefix', 'Shift/reduce', 'Reduce/reduce'], answer: 1, why: 'After factoring, the alternatives of the new nonterminal start differently.' },
      { q: 'Does left factoring change the language?', options: ['Yes', 'No', 'Only when ε appears', 'Only for ambiguous grammars'], answer: 1, why: 'α β1 | α β2 and α (β1 | β2) make the same strings.' },
      { q: 'C → d o x | d o y | d z. Which prefix is factored first?', options: ['d', 'd o', 'o', 'x'], answer: 1, why: 'The longest prefix shared by two alternatives, d o; then d is shared by d o C\' and d z.' },
    ],
  });
})();
