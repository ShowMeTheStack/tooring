// Unsolvable questions about context-free grammars. Ambiguity: from a set of dominoes build a grammar
// whose ambiguous strings are exactly the matches, so deciding ambiguity would solve the domino puzzle.
// Equivalence: a search for a string one grammar makes and the other does not finds a difference when
// there is one, but when the grammars are equal it can never stop and say so.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'grammar-undecidable', part: 'computability', order: 60, title: 'Unsolvable problems about grammars', blurb: 'Is this grammar ambiguous? Do these two grammars make the same strings? Simple questions with no algorithm, because dominoes hide inside them.' });

  const eps = (s) => (s === '' ? 'ε' : s);
  function card(key, x, y, lines, opts) {
    opts = opts || {};
    lines = [].concat(lines);
    const w = opts.w || Math.ceil(Math.max(...lines.map((l) => Geo.textWidth(l, 15, { bold: true }))) + 34);
    const h = opts.h || lines.length * 22 + 22;
    const it = { key, kind: 'cell', x, y, w, h, size: 15, rx: 12, cls: 'card ' + (opts.cls || ''), pick: !!opts.pick };
    if (lines.length > 1) it.lines = lines; else it.text = lines[0];
    return it;
  }

  // ---------- ambiguity from dominoes ----------
  const parseDominoes = (text) => String(text).split(/[\s,]+/).filter(Boolean).map((p) => { const [top, bottom] = p.split('/'); return { top: top || '', bottom: bottom || '' }; });
  const checkDominoes = (text) => {
    const parts = String(text).split(/[\s,]+/).filter(Boolean);
    if (parts.length < 1) return 'Dominoes: write them like ab/a, b/bb';
    if (parts.length > 4) return 'Dominoes: at most 4, so the trees stay readable';
    for (const p of parts) {
      if (!/^[a-z]{1,3}\/[a-z]{1,3}$/.test(p)) return 'Dominoes: "' + p + '" should be top/bottom, each one to three letters a–z, like ab/a';
    }
    return null;
  };
  /** The derivation tree in the T half (side 'top') or the B half (side 'bottom') for an index sequence */
  function derivTree(dom, seq, side, depth) {
    const V = side === 'top' ? 'T' : 'B';
    const build = (k) => {
      const id = V + k;
      if (k >= depth) return { id, label: V, cls: 'nt' };
      const i = seq[k];
      const piece = { id: id + 's', label: dom[i][side], cls: 'term' };
      const idx = { id: id + 'i', label: String(i + 1), cls: 'term' };
      if (k === seq.length - 1) return { id, label: V, children: [piece, idx] };
      return { id, label: V, children: [piece, build(k + 1), idx] };
    };
    return { id: V + 'S', label: 'S', children: [build(0)] };
  }

  T.topic({
    id: 'ugram-ambiguity', family: 'grammar-undecidable', order: 10, title: 'Ambiguity hides a domino puzzle',
    blurb: 'Turn dominoes into a grammar: one half spells the tops, the other the bottoms, each followed by the domino numbers in reverse. A string with two parse trees is exactly a matching row of dominoes, so no algorithm can decide ambiguity.',
    camera: 'follow',
    inputs: [{ id: 'd', kind: 'text', label: 'Dominoes (top/bottom)', def: 'a/aab, ab/b, bb/b', check: checkDominoes }],
    presets: [
      { label: 'Three dominoes, a match of three', values: { d: 'a/aab, ab/b, bb/b' } },
      { label: 'A match of two', values: { d: 'aa/a, b/ab, ba/b' } },
      { label: 'No match at all: unambiguous', values: { d: 'ab/aba, ba/a, a/ba' } },
      { label: 'No match within the bound', values: { d: 'aa/a, ab/abb' } },
    ],
    counters: [{ id: 'dom', label: 'dominoes laid' }],
    run(inp) {
      const dom = parseDominoes(inp.d);
      const n = dom.length;
      const sol = T.pcp.solve(dom, { maxNodes: 4000, maxOver: 12, trace: false });
      const F = new T.Frames(['dom']);
      const set = K.dominoes.set({ tiles: dom, x: 0, y: 0, prefix: 'pcp' });
      const SW = Math.max(set.box.w, 420);
      const rT = 'T → ' + dom.map((d, i) => d.top + ' T ' + (i + 1) + ' | ' + d.top + ' ' + (i + 1)).join(' | ');
      const rB = 'B → ' + dom.map((d, i) => d.bottom + ' B ' + (i + 1) + ' | ' + d.bottom + ' ' + (i + 1)).join(' | ');
      const gLines = ['S → T | B'].concat(n > 2 ? [rT.split(' | ').slice(0, 4).join(' | ') + ' |', '      ' + rT.split(' | ').slice(4).join(' | '), rB.split(' | ').slice(0, 4).join(' | ') + ' |', '      ' + rB.split(' | ').slice(4).join(' | ')] : [rT, rB]);
      const gram = { key: 'gram', kind: 'cell', x: 0, y: set.box.h + 24, w: Math.max(SW, ...gLines.map((l) => Geo.textWidth(l, 15, { mono: true }) + 40)), h: gLines.length * 24 + 22, lines: gLines, size: 15, rx: 12, cls: 'card mono' };
      F.add({ phase: 1, items: set.items, say: n + ' dominoes, each with a string on top and one below. A match is a row of them (repeats allowed) whose tops and bottoms spell the same string.', hl: { g: [] } });
      F.add({ phase: 1, items: set.items.concat(gram), meta: { verdict: sol.verdict === 'match' ? 'Yes: a match exists' : sol.verdict === 'none' ? 'No: no match exists' : 'The search gives up' }, say: 'The grammar: T spells tops and B spells bottoms. Each step writes a domino\'s string on the left and its number on the right, so the numbers come out in reverse order at the end.', hl: { g: [0, 1, 2] } });
      if (sol.verdict === 'match') {
        const seq = sol.seq;
        const word = sol.top + seq.slice().reverse().map((i) => i + 1).join('');
        const draw = (k, extra) => {
          const cx = SW / 2;
          const full = K.dominoes.sequence({ tiles: dom, seq, x: 0, y: 0, prefix: 'seq' }).box.w;
          const sq = K.dominoes.sequence({ tiles: dom, seq: seq.slice(0, k), x: Math.max(60, cx - full / 2), y: set.box.h + 60, prefix: 'seq' });
          const ty = sq.box.y + sq.box.h + 50;
          const opt = (x) => ({ x, y: ty, gapY: 70, yield: k === seq.length, yieldLabel: '' });
          const tt0 = K.tree.draw(derivTree(dom, seq, 'top', seq.length), Object.assign(opt(0), { yield: true }));
          const tb0 = K.tree.draw(derivTree(dom, seq, 'bottom', seq.length), Object.assign(opt(0), { yield: true }));
          const left = cx - (tt0.box.w + 60 + tb0.box.w) / 2;
          const tt = K.tree.draw(derivTree(dom, seq, 'top', k), Object.assign(opt(left - tt0.box.x), { prefix: 'tt' }));
          const tb = K.tree.draw(derivTree(dom, seq, 'bottom', k), Object.assign(opt(left + tt0.box.w + 60 - tb0.box.x), { prefix: 'tb' }));
          const lt = { key: 'ltt', kind: 'text', x: tt.box.x + tt.box.w / 2, y: ty - 26, text: 'tops (T)', anchor: 'middle', cls: 'title' };
          const lb = { key: 'ltb', kind: 'text', x: tb.box.x + tb.box.w / 2, y: ty - 26, text: 'bottoms (B)', anchor: 'middle', cls: 'title' };
          return { items: set.items.concat(sq.items, tt.items, tb.items, [lt, lb], extra || []), bottom: Math.max(tt.box.y + tt.box.h, tb.box.y + tb.box.h), left: tt.box.x };
        };
        for (let k = 1; k <= seq.length; k++) {
          F.count('dom');
          const i = seq[k - 1];
          F.add({ phase: 2, items: draw(k).items, say: 'Lay domino ' + (i + 1) + ' (' + dom[i].top + ' over ' + dom[i].bottom + '). In step: the T tree uses T → ' + dom[i].top + ' T ' + (i + 1) + ', the B tree uses B → ' + dom[i].bottom + ' B ' + (i + 1) + (k === seq.length ? ', and both close with the rule that has no T or B.' : '.'), meta: { next: k < seq.length ? 'pcp:d' + seq[k] : null }, hl: { g: [0] } });
        }
        const last = draw(seq.length);
        F.add({ phase: 2, items: last.items, say: 'Both trees yield ' + word + ': the tops and bottoms agree (' + sol.top + ') and the numbers are the same list read backwards. One string, two different parse trees: the grammar is ambiguous.', mark: 'accepted' });
        const c = card('why', SW / 2 - 230, last.bottom + 30, ['Each half alone has one tree per string: the numbers', 'at the end say which rules were used. So two trees', 'means one T tree and one B tree: a match.'], { cls: 'act', w: 460 });
        F.add({ phase: 2, items: last.items.concat(c), say: 'And the other way: T alone and B alone are unambiguous, since the numbers fix every rule. So the grammar is ambiguous exactly when the dominoes have a match. A decider for ambiguity would decide the domino puzzle (PCP), and PCP is undecidable.' });
      } else {
        const none = sol.verdict === 'none';
        const c = card('nomatch', 0, gram.y + gram.h + 30, none ? ['Every partial row dies: no match exists.', 'So no string has two trees: unambiguous.'] : ['No match found within the search bound.', 'Ambiguous? The search cannot tell.'], { w: gram.w, cls: none ? 'good' : 'hot' });
        F.add({ phase: 1, items: set.items.concat(gram, c), say: none ? 'A search through every way to start a row finds that each one disagrees sooner or later, so these dominoes have no match, and the grammar is unambiguous. Here we were lucky: the search ran out of rows.' : 'The search tried ' + sol.nodes + ' ways to extend a row and found no match, yet rows can always get longer. Without a match we cannot say the grammar is ambiguous; without a proof of none, we cannot say it is not.', mark: none ? 'rejected' : undefined });
        const c2 = card('moral', 0, c.y + c.h + 20, ['A match ⇔ a string with two trees.', 'No algorithm decides either one.'], { w: gram.w, cls: 'act' });
        F.add({ phase: 1, items: set.items.concat(gram, c, c2), say: 'In general, ambiguity is exactly as hard as finding a match: some instances can be settled, but no single algorithm settles them all.' });
      }
      const views = new Map();
      for (const f of F.list) { const b = T.stageBounds(f.items); views.set(f.phase, views.has(f.phase) ? Geo.union([views.get(f.phase), b]) : b); }
      for (const f of F.list) f.view = views.get(f.phase);
      return { frames: F.list, def: { sections: [
        { id: 'g', kind: 'grammar', title: 'The grammar', rules: ['S → T | B', rT, rB], nonterminals: ['S', 'T', 'B'] },
        { id: 'pcp', kind: 'text', title: 'Why it works', text: 'T and B are each unambiguous: the trailing numbers spell out which rules were used. A string has two trees exactly when a T-tree and a B-tree give it, that is, when some row of dominoes has the same top and bottom.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.verdict, once: true, pick: 'option', options: ['Yes: a match exists', 'No: no match exists', 'The search gives up'], ask: 'Will a search find a row of dominoes whose top and bottom agree (and so a string with two trees)?', answer: (fr, i) => fr[i].meta.verdict, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.next && f.phase === 2, once: true, pick: 'item', ask: 'Which domino must come next to keep the tops and bottoms agreeing? Click it.', answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why are the domino numbers written at the end of each string?', options: ['To make the strings longer', 'So each half of the grammar has only one tree per string', 'To make the grammar regular', 'They are not needed'], answer: 1, why: 'Reading the numbers backwards tells exactly which rule each step used, so T alone and B alone are unambiguous.' },
      { q: 'A string has two parse trees in this grammar. What does that give?', options: ['Nothing', 'A match for the dominoes', 'A proof there is no match', 'A shorter grammar'], answer: 1, why: 'One tree must come from T and one from B; the same string means the tops and bottoms agree, with the same domino list.' },
      { q: 'What follows from "ambiguity of CFGs is undecidable"?', options: ['No grammar is unambiguous', 'No algorithm answers "is G ambiguous?" for every G', 'Every grammar is ambiguous', 'Parsers cannot exist'], answer: 1, why: 'Particular grammars can still be shown ambiguous or not; only a single method for all of them is impossible.' },
      { q: 'If the search for a match gives up at its bound, what do we know?', options: ['The grammar is unambiguous', 'The grammar is ambiguous', 'Nothing yet: a longer match may exist', 'The dominoes are invalid'], answer: 2, why: 'A bounded search can find a match, but failing to find one within a bound proves nothing.' },
    ],
  });

  // ---------- equivalence: a search that cannot stop on a yes ----------
  const checkGrammar = (label) => (v) => {
    let G;
    try { G = T.comp.parseCFG(v); } catch (e) { return label + ': write rules like S -> a S b | ε'; }
    if (!G.rules.length) return label + ': at least one rule, like S -> a S b | ε';
    if (G.variables.length > 4) return label + ': at most 4 variables';
    const bad = G.terminals.find((t) => !/^[a-z]$/.test(t));
    if (bad !== undefined) return label + ': "' + bad + '" is not a variable (a left side) nor a single letter a–z';
    return null;
  };
  T.topic({
    id: 'ugram-equivalence', family: 'grammar-undecidable', order: 20, title: 'Do two grammars make the same strings?',
    blurb: 'List the strings of each grammar, shortest first, and compare. A difference, once found, settles it. But if the grammars are equal the search goes on for ever: no algorithm decides equivalence.',
    camera: 'follow',
    inputs: [
      { id: 'g1', kind: 'grammar', label: 'Grammar G₁', def: 'S -> a S b | ε', check: checkGrammar('Grammar G₁') },
      { id: 'g2', kind: 'grammar', label: 'Grammar G₂', def: 'S -> a S b | S S | ε', check: checkGrammar('Grammar G₂') },
      { id: 'n', kind: 'number', label: 'Longest length to try', def: 6, min: 2, max: 8 },
    ],
    presets: [
      { label: 'Different at length 4', values: { g1: 'S -> a S b | ε', g2: 'S -> a S b | S S | ε', n: 6 } },
      { label: 'Different only on ε', values: { g1: 'S -> a S | a | ε', g2: 'S -> a S | a', n: 5 } },
      { label: 'Equal, written two ways', values: { g1: 'S -> a S b | ε', g2: 'S -> a A | ε\nA -> S b', n: 6 } },
      { label: 'Equal: a and b in any order', values: { g1: 'S -> a S | b S | ε', g2: 'S -> S S | a | b | ε', n: 4 } },
    ],
    counters: [{ id: 'len', label: 'lengths compared' }, { id: 'strings', label: 'strings listed' }],
    run(inp) {
      const G1 = T.comp.parseCFG(inp.g1), G2 = T.comp.parseCFG(inp.g2);
      const N = inp.n;
      const L1 = T.comp.cfgLanguage(G1, N), L2 = T.comp.cfgLanguage(G2, N);
      const F = new T.Frames(['len', 'strings']);
      const items = [];
      const CH = 34, X0 = 120;
      let y = 0, diff = null;
      const head = [{ key: 'h1', kind: 'text', x: 0, y: -14, text: 'strings of each length, shortest first', cls: 'title' }];
      F.add({ items: head.slice(), say: 'Two grammars: G₁ (' + inp.g1.replace(/\n/g, '; ') + ') and G₂ (' + inp.g2.replace(/\n/g, '; ') + '). List the strings each one makes, one length at a time, and compare.', hl: { g1: [], g2: [] } });
      for (let l = 0; l <= N; l++) {
        const a = [...L1].filter((s) => s.length === l).sort(), b = [...L2].filter((s) => s.length === l).sort();
        const only = [...a.filter((s) => !b.includes(s)), ...b.filter((s) => !a.includes(s))];
        F.count('len').count('strings', a.length + b.length);
        const band = [];
        if (!a.length && !b.length) {
          band.push({ key: 'len' + l, kind: 'text', x: 0, y: y + 20, text: 'length ' + l + ': none from either', cls: 'strong' });
          y += 36;
        } else {
          band.push({ key: 'len' + l, kind: 'text', x: 0, y: y + 22, text: 'length ' + l, cls: 'strong' });
          const row = (list, g, ry) => {
            band.push({ key: 'g' + g + ':' + l, kind: 'text', x: X0 - 12, y: ry + 22, text: 'G' + (g === 1 ? '₁' : '₂'), anchor: 'end', cls: 'title' });
            if (!list.length) band.push({ key: 'g' + g + ':' + l + ':none', kind: 'text', x: X0, y: ry + 22, text: 'nothing', cls: 'bad' });
            let x = X0;
            for (const s of list) {
              const w = Math.max(44, Geo.textWidth(eps(s), 15, { mono: true }) + 20);
              band.push({ key: 'c' + g + ':' + (s || 'ε'), kind: 'cell', x, y: ry, w, h: CH, text: eps(s), size: 15, rx: 6, cls: 'mono ' + (only.includes(s) ? 'bad' : 'good'), pick: true, enter: 'drop' });
              x += w + 6;
            }
          };
          row(a, 1, y); row(b, 2, y + CH + 6);
          y += 2 * CH + 30;
        }
        items.push(...band);
        if (only.length) {
          diff = { l, s: only[0], in1: a.includes(only[0]), keys: only.map((s) => 'c' + (a.includes(s) ? 1 : 2) + ':' + (s || 'ε')) };
          F.add({ items: head.concat(items), say: 'Length ' + l + ': ' + only.map(eps).join(', ') + (only.length > 1 ? ' are' : ' is') + ' made by only one of the grammars.', meta: { pickDiff: diff.keys }, hl: { g1: [0], g2: [0] } });
          const c = card('verdict', 0, y + 10, ['Not equal: ' + eps(diff.s) + ' is in L(G' + (diff.in1 ? '₁' : '₂') + ') only.'], { cls: 'bad' });
          F.add({ items: head.concat(items, c), say: 'A difference ends the search: ' + eps(diff.s) + ' is made by G' + (diff.in1 ? '₁' : '₂') + ' but not by G' + (diff.in1 ? '₂' : '₁') + ', so the grammars are not equivalent. When they differ, this search always finds out.', mark: 'rejected' });
          break;
        }
        F.add({ items: head.concat(items), say: !a.length && !b.length ? 'Length ' + l + ': neither grammar makes a string this long. Still the same.' : 'Length ' + l + ': both make the same ' + a.length + ' string' + (a.length === 1 ? '' : 's') + ' (' + a.map(eps).join(', ') + '). No difference yet.', meta: { last: l === N } });
      }
      if (!diff) {
        const c = card('verdict', 0, y + 10, ['Equal up to length ' + N + '. And at ' + (N + 1) + '? ' + (N + 2) + '? …', 'The search could go on for ever and never say "equal".'], { cls: 'hot' });
        F.add({ items: head.concat(items, c), say: 'No difference up to length ' + N + '. That proves nothing about longer strings: the search can find a difference but can never certify equality. Equivalence of grammars is undecidable; only "not equal" can be recognised.', mark: 'limit' });
      }
      const gl = (G) => G.variables.map((v) => v + ' → ' + G.rules.filter((r) => r.lhs === v).map((r) => r.rhs.join(' ') || 'ε').join(' | '));
      return { frames: F.list, def: { sections: [
        { id: 'g1', kind: 'grammar', title: 'G₁', rules: gl(G1), nonterminals: G1.variables },
        { id: 'g2', kind: 'grammar', title: 'G₂', rules: gl(G2), nonterminals: G2.variables },
        { id: 'eq', kind: 'math', title: 'The problem', text: 'EQ_CFG = {⟨G₁, G₂⟩ : L(G₁) = L(G₂)}\nundecidable; its complement is recognisable:\nsearch for a string in one and not the other' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.pickDiff, once: true, pick: 'item', ask: 'Click a string that only one grammar makes.', answer: (fr, i) => fr[i].meta.pickDiff, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === 0, once: true, pick: 'option', options: ['Yes, within the lengths tried', 'No difference will show up'], ask: 'Will this search find a string that tells the grammars apart?', answer: (fr) => (fr.some((f) => f.meta && f.meta.pickDiff) ? 'Yes, within the lengths tried' : 'No difference will show up'), explain: 'Watch the lengths fill in one by one.' },
    ],
    quiz: [
      { q: 'The search finds a string in L(G₁) but not L(G₂). What can it conclude?', options: ['Nothing', 'The grammars are not equivalent', 'G₁ is ambiguous', 'They are equivalent'], answer: 1, why: 'One string in one language and not the other is a certificate of difference.' },
      { q: 'No difference up to length 8. What can it conclude?', options: ['They are equivalent', 'Nothing about longer strings', 'They differ', 'Both are regular'], answer: 1, why: 'A difference may first appear at any length; a finite search never proves equality.' },
      { q: 'Which part of grammar equivalence can a machine recognise?', options: ['"Equal"', '"Not equal"', 'Both', 'Neither'], answer: 1, why: 'Searching by length finds every difference eventually, so inequivalence is recognisable; equivalence is not.' },
      { q: 'S → a S b | ε and S → a S b | S S | ε first differ at which string?', options: ['ε', 'ab', 'abab', 'aabb'], answer: 2, why: 'The second grammar can put two balanced blocks side by side; abab is the shortest such string.' },
    ],
  });
})();
