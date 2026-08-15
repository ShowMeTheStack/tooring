// The limits of context-free languages (part 3): the pumping lemma read off a parse tree (a long path must
// repeat a nonterminal, and the repeat can be cut out or copied in), the pumping game against an adversary
// who tries every split, closure by gluing grammars, intersection with a regular language as a machine
// product, and the demonstration that intersection and complement escape the class.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CF = (T.CF = T.CF || {});
  // every stage item of these topics carries the class cf, so the styles in styles-cf.css stay with them
  const topic = (t) => { const run = t.run; t.run = (inp) => CF.mark(run(inp)); return T.topic(t); };
  const Geo = T.geom;

  T.family({ id: 'cf-limits', part: 'context-free', order: 50, title: 'Limits and closure', blurb: 'The context-free pumping lemma on a tree and as a game, which operations keep a language context-free, and which do not.' });

  const showW = (s) => (s === '' ? 'ε' : s);

  // ---- the pumping lemma on a parse tree -----------------------------------------------------------------------
  const ANBN_CNF = 'S → A T | A B\nT → S B\nA → a\nB → b';
  const PAL_CNF = 'S → A X | B Y | A A | B B | a | b\nX → S A\nY → S B\nA → a\nB → b';
  /** Copy a tree, tagging every node with a part ('v' for R1 outside R2, 'x' inside R2) */
  const clone = (n, part) => ({ sym: n.sym, prod: n.prod, part: n.part || part, children: n.children === null ? null : n.children.map((c) => clone(c, part)) });
  topic({
    id: 'cfpump-tree', family: 'cf-limits', order: 10, title: 'The pumping lemma on a parse tree',
    blurb: 'A long enough word has a tall parse tree, and a tall tree has a path where some nonterminal repeats. The part between the two copies can be cut out or stacked again: u vⁱ x yⁱ z stays in the language.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar (Chomsky normal form)', def: ANBN_CNF, check: (v) => CF.checkGrammar(v, { cnf: true, maxRules: 12 }) },
      { id: 'w', kind: 'string', label: 'Word', def: 'aabb', max: 6 },
    ],
    presets: [
      { label: 'aⁿbⁿ: aabb', values: { g: ANBN_CNF, w: 'aabb' } },
      { label: 'aⁿbⁿ: aaabbb', values: { g: ANBN_CNF, w: 'aaabbb' } },
      { label: 'Palindromes: abba', values: { g: PAL_CNF, w: 'abba' } },
      { label: 'Too short to promise a repeat: ab', values: { g: ANBN_CNF, w: 'ab' } },
    ],
    check: (inp) => { const G = CF.grammar(inp.g); const e = CF.checkWord(G, inp.w); if (e) return e; return T.grammar.parseTrees(G, CF.word(G, inp.w), 1).length ? null : 'Word: not in the language, so it has no tree'; },
    counters: [{ id: 'path', label: 'nonterminals on the path' }, { id: 'N', label: 'nonterminals in the grammar' }, { id: 'i', label: 'i' }],
    run(inp) {
      const G = CF.grammar(inp.g), w = CF.word(G, inp.w), n = w.length;
      const tree = T.grammar.parseTrees(G, w, 1)[0];
      const F = new T.Frames(['path', 'N', 'i']);
      F.set('N', G.nonterminals.length).set('i', 1);
      const recs = CF.nodes(tree);
      const byId = new Map(recs.map((r) => [r.id, r]));
      const deepest = recs.reduce((a, r) => (r.depth > a.depth ? r : a), recs[0]);
      const path = [];
      for (let id = deepest.id; ; id = id.slice(0, id.lastIndexOf('.'))) { path.unshift(id); if (id === 'r') break; }
      const ntPath = path.filter((id) => byId.get(id).node.children !== null);
      // walk up from the bottom until a nonterminal is seen twice
      const seen = new Map();
      let lo = null, hi = null, walked = [];
      for (let k = ntPath.length - 1; k >= 0; k--) {
        const id = ntPath[k], A = byId.get(id).node.sym;
        walked.push(id);
        if (seen.has(A)) { lo = seen.get(A); hi = id; break; }
        seen.set(A, id);
      }
      const pTree = (t, o) => K.tree.draw(CF.kitTree(G, t, o), Object.assign({ prefix: 'tr', gapX: 16, gapY: 72 }, o.d || {}));
      const draw = (o) => { const d = pTree(tree, o); return d; };
      const d0 = draw({});
      const sy = d0.box.y + d0.box.h + 60;
      const strX = (len) => d0.box.x + d0.box.w / 2 - (len * 44) / 2;
      const plain = K.string.draw({ text: w, x: strX(n), y: sy, cw: 44, prefix: 'pm' });
      F.set('path', 0);
      F.add({ items: d0.items.concat(plain.items), say: 'The parse tree of ' + CF.show(w) + ' in a grammar in Chomsky normal form, so every inner node has two children or one terminal. With ' + G.nonterminals.length + ' nonterminals, a path with more than ' + G.nonterminals.length + ' of them must repeat one: that is guaranteed once the word is at least p = 2^' + G.nonterminals.length + ' = ' + Math.pow(2, G.nonterminals.length) + ' long, but shorter words may have one too.' });
      F.set('path', ntPath.length);
      F.add({ items: draw({ d: { path } }).items.concat(plain.items), say: 'Take a longest path from the root to a leaf: ' + ntPath.map((id) => byId.get(id).node.sym).join(' → ') + ' → ' + byId.get(path[path.length - 1]).node.sym + ', with ' + ntPath.length + ' nonterminals.', meta: { repeat: hi ? ['tr:n:' + hi, 'tr:n:' + lo] : null } });
      walked.forEach((id, k) => {
        if (k === walked.length - 1 && hi) return;
        F.add({ items: draw({ d: { path, hot: walked.slice(0, k + 1) } }).items.concat(plain.items), say: 'Walking up from the bottom: ' + walked.slice(0, k + 1).map((x) => byId.get(x).node.sym).join(', ') + '. ' + (k < walked.length - 1 ? 'No repeat yet.' : '') });
      });
      if (!hi) {
        F.add({ items: draw({ d: { path } }).items.concat(plain.items), say: 'No nonterminal repeats on this path: the word is too short for the lemma to promise anything (it speaks only of words of length ≥ p). Try a longer word.', mark: 'no repeat' });
        return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar')] } };
      }
      const A = byId.get(hi).node.sym, R1 = byId.get(hi), R2 = byId.get(lo);
      const inR = (id, R) => id === R.id || id.startsWith(R.id + '.');
      const partCls = (nd, id) => (inR(id, R2) ? 'px' : inR(id, R1) ? 'pv' : '');
      const u = w.slice(0, R1.from).join(''), v = w.slice(R1.from, R2.from).join(''), x = w.slice(R2.from, R2.to).join(''), y = w.slice(R2.to, R1.to).join(''), z = w.slice(R1.to).join('');
      const parts = (i) => [{ name: 'u', text: u }, { name: 'v', text: v, pump: true }, { name: 'x', text: x }, { name: 'y', text: y, pump: true }, { name: 'z', text: z }];
      F.add({ items: draw({ d: { path, hot: [hi, lo] } }).items.concat(plain.items), say: A + ' again! The upper ' + A + ' and the lower ' + A + ' both lie within the lowest ' + (G.nonterminals.length + 1) + ' nonterminals of the path, which is why |vxy| ≤ p.' });
      const pumpAt = (i, yy) => K.string.pump({ parts: parts(i), i, at: { x: strX(u.length + x.length + z.length + i * (v.length + y.length)), y: yy === undefined ? sy : yy }, prefix: 'pm', cw: 44 });
      F.add({ items: draw({ cls: partCls, d: { path: [] } }).items.concat(pumpAt(1).items), say: 'The lower ' + A + ' (blue) yields x = ' + showW(x) + '. The upper ' + A + ' yields v x y = ' + showW(v + x + y) + ': its part outside the blue subtree (orange) gives v = ' + showW(v) + ' on the left and y = ' + showW(y) + ' on the right. The rest is u = ' + showW(u) + ' and z = ' + showW(z) + '.', meta: { pumpOpts: true } });
      // rebuild trees with the upper subtree replaced by i nested copies
      const sub = (t, id) => { let n0 = t; for (const k of id.split('.').slice(1)) n0 = n0.children[+k]; return n0; };
      const lowerRel = lo.slice(hi.length);
      const R1t = clone(sub(tree, hi), 'v'), R2t = clone(sub(tree, lo), 'x');
      const replaceAt = (t, rel, rep) => { if (!rel) return rep; const ks = rel.split('.').slice(1); const c = clone(t); let n0 = c; for (let j = 0; j < ks.length - 1; j++) n0 = n0.children[+ks[j]]; n0.children[+ks[ks.length - 1]] = rep; return c; };
      const nest = (i) => (i === 0 ? R2t : replaceAt(R1t, lowerRel, nest(i - 1)));
      const pumped = (i) => replaceAt(clone(tree), hi.slice(1) ? hi.slice(1) : '', nest(i));
      const show = (i, say, mark) => {
        const t = hi === 'r' ? nest(i) : pumped(i);
        const ww = u + v.repeat(i) + x + y.repeat(i) + z;
        F.set('i', i);
        const dt = pTree(t, { cls: (nd) => (nd.part === 'x' ? 'px' : nd.part === 'v' ? 'pv' : '') });
        F.add({ items: dt.items.concat(pumpAt(i, dt.box.y + dt.box.h + 60).items), say: say + ' The yield: ' + showW(ww) + (T.grammar.parseTrees(G, [...ww], 1).length || ww === '' && T.grammar.nullableSet(G).has(G.start) ? ', in the language.' : '.'), mark });
      };
      show(2, 'i = 2: put a copy of the upper ' + A + '-subtree where the lower ' + A + ' was. It is still a legal tree, since an ' + A + ' may sit there, and v and y appear twice.');
      if (u.length + x.length + z.length + 3 * (v.length + y.length) <= 10) show(3, 'i = 3: nest one more copy.');
      show(0, 'i = 0: replace the upper ' + A + '-subtree by the lower one, cutting v and y out.', 'pumped');
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), { id: 'lemma', kind: 'math', title: 'The lemma', text: 'For a context-free L there is p such that\nevery s in L with |s| ≥ p splits s = u v x y z\nwith |vxy| ≤ p and |vy| ≥ 1, and\nu vⁱ x yⁱ z is in L for every i ≥ 0.' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.repeat, once: true, pick: 'item', ask: 'Walking up this path from the leaf, which nonterminal will be the first to repeat? Click either copy of it.', answer: (fr, i) => fr[i].meta.repeat, explain: 'The first nonterminal met twice going up gives the two nested subtrees.' },
      { at: (f) => f.meta && f.meta.pumpOpts, once: true, pick: 'option', options: ['Still in the language', 'Out of the language'], ask: 'If we copy the upper subtree into the lower one (i = 2), is the new yield in the language?', answer: () => 'Still in the language', explain: 'The copy is rooted at the same nonterminal, so the new tree uses only rules of the grammar.' },
    ],
    quiz: [
      { q: 'Why must a long path repeat a nonterminal?', options: ['There are only |N| nonterminals; a path with more than |N| of them repeats one (pigeonhole)', 'Because the grammar is ambiguous', 'Only in CNF', 'It need not'], answer: 0, why: 'More nonterminal slots than different nonterminals.' },
      { q: 'Why do we need Chomsky normal form here?', options: ['Binary trees: a word of length ≥ 2^|N| forces a path with more than |N| nonterminals, and |vy| ≥ 1', 'CNF grammars are not ambiguous', 'Only CNF grammars have trees', 'To remove ε from the word'], answer: 0, why: 'A binary tree of height h has at most 2^h leaves, and with no unit rules the pumped part is not empty.' },
      { q: 'What happens with i = 0?', options: ['The upper subtree is replaced by the lower one: v and y vanish', 'Nothing changes', 'The word becomes ε', 'The tree is invalid'], answer: 0, why: 'The lower subtree has the same root symbol, so it can stand in for the upper one.' },
      { q: 'Why is |vxy| ≤ p?', options: ['The repeat is found among the lowest |N| + 1 nonterminals of a longest path, so the upper subtree is short', 'Because v and y are single letters', 'By definition of p only', 'It is not'], answer: 0, why: 'That subtree has height at most |N| + 1, hence a yield of at most 2^|N| = p symbols.' },
    ],
  });

  // ---- the pumping game ----------------------------------------------------------------------------------------
  const LANGS = ['anbncn', 'ww', 'squares', 'abcd-cross', 'anbn', 'evenpal'];
  topic({
    id: 'cfpump-game', family: 'cf-limits', order: 20, title: 'The context-free pumping game',
    blurb: 'The adversary claims the language is context-free and names p. You pick a word; the adversary splits it as u v x y z with |vxy| ≤ p; you pick i. If u vⁱ x yⁱ z leaves the language, you win, and the language is not context-free.',
    inputs: [
      { id: 'lang', kind: 'choice', label: 'Language', def: 'anbncn', options: LANGS.map((id) => { const L = T.cfpump.byId(id); return { value: id, label: L.notation + (L.cf ? '' : '') }; }) },
      { id: 'p', kind: 'number', label: 'The adversary\'s p', def: 3, min: 2, max: 4 },
      { id: 's', kind: 'string', label: 'Your word (empty: a good choice)', def: '', max: 16 },
    ],
    presets: [
      { label: 'aⁿbⁿcⁿ', values: { lang: 'anbncn', p: 3, s: '' } },
      { label: 'w w', values: { lang: 'ww', p: 2, s: '' } },
      { label: 'Square lengths', values: { lang: 'squares', p: 3, s: '' } },
      { label: 'A weak word for w w: abab', values: { lang: 'ww', p: 3, s: 'abab' } },
      { label: 'aⁿbⁿ is context-free: the adversary survives', values: { lang: 'anbn', p: 3, s: '' } },
    ],
    check: (inp) => { const L = T.cfpump.byId(inp.lang); const s = inp.s || L.sample(inp.p); if (!L.member(s)) return 'Your word: ' + showW(s) + ' is not in ' + L.notation; if (s.length < inp.p) return 'Your word: it must be at least p = ' + inp.p + ' long'; if (s.length > 16) return 'Your word: at most 16 symbols'; return null; },
    counters: [{ id: 'tried', label: 'splits tried' }, { id: 'i', label: 'i' }],
    run(inp) {
      const L = T.cfpump.byId(inp.lang), p = inp.p;
      const s = inp.s || L.sample(p);
      const F = new T.Frames(['tried', 'i']);
      const r = T.cfpump.adversarySplit(L, s, p);
      const CW = s.length > 12 ? 34 : 40;
      const word = (d, extra) => {
        const br = [];
        if (d) {
          const [a, b, c, e] = d.at;
          const add = (f, t, txt, cls) => { if (t > f) br.push({ id: txt, from: f, to: t, text: txt, cls }); };
          add(0, a, 'u', 'x'); add(a, b, 'v', 'y'); add(b, c, 'x', 'z'); add(c, e, 'y', 'y'); add(e, s.length, 'z', 'x');
        }
        return K.string.draw({ text: s, x: -s.length * CW / 2, y: 0, cw: CW, prefix: 'w', brackets: br, cls: (i) => (d && ((i >= d.at[0] && i < d.at[1]) || (i >= d.at[2] && i < d.at[3])) ? 'part-v' : '') }).items.concat(extra || []);
      };
      const claim = { key: 'claim', kind: 'text', x: 0, y: -40, text: 'p = ' + p + ',  |vxy| ≤ ' + p + ',  |vy| ≥ 1', anchor: 'middle', cls: 'mono' };
      F.add({ items: [claim], say: 'The adversary claims ' + L.notation + ' is context-free with pumping constant p = ' + p + '.' });
      F.add({ items: word(null, [claim]), say: 'You pick s = ' + s + ' (length ' + s.length + ', in the language, at least p long).' + (inp.s ? '' : ' A good word makes every short window vxy hurt.') });
      const tries = r.trace.filter((t) => t.kind === 'try').slice(0, 4);
      tries.forEach((t, k) => {
        F.set('tried', k + 1);
        F.add({ items: word(t.split, [claim]), say: 'The adversary tries ' + t.say });
      });
      F.set('tried', r.tried);
      // cornered, the adversary still has to offer something: a split with both v and y non-empty around a block
      // boundary makes the most instructive one
      let split = r.split;
      if (!r.survives) {
        const all = [...T.cfpump.splits(s, p)].filter((d) => d.v && d.y);
        const b = s.search(/(.)(?!\1)./) + 1 || Math.floor(s.length / 2);
        all.sort((d1, d2) => Math.abs(d1.at[1] + (d1.at[2] - d1.at[1]) / 2 - b) - Math.abs(d2.at[1] + (d2.at[2] - d2.at[1]) / 2 - b) || (d2.v + d2.x + d2.y).length - (d1.v + d1.x + d1.y).length);
        split = all[0] || (tries.length ? tries[0].split : T.cfpump.splits(s, p).next().value);
      }
      const killer = T.cfpump.refute(L, split, r.range);
      F.add({ items: word(split, [claim]), say: r.survives ? 'The adversary finds a split that survives every i it checks: ' + T.cfpump.adversarySplit(L, s, p).trace.slice(-1)[0].say.replace(/^Split /, '') : 'All ' + r.tried + ' legal splits fail for some i. Cornered, the adversary offers u = ' + showW(split.u) + ', v = ' + showW(split.v) + ', x = ' + showW(split.x) + ', y = ' + showW(split.y) + ', z = ' + showW(split.z) + '. Your move: pick i.', meta: { killer: killer === null ? 'No i works' : 'i = ' + killer } });
      const pumpFrame = (i) => {
        const ww = T.cfpump.pump(split, i), inL = L.member(ww);
        const pm = K.string.pump({ parts: [{ name: 'u', text: split.u }, { name: 'v', text: split.v, pump: true }, { name: 'x', text: split.x }, { name: 'y', text: split.y, pump: true }, { name: 'z', text: split.z }], i, at: { x: -ww.length * CW / 2, y: 0 }, cw: CW, prefix: 'pm' });
        F.set('i', i);
        F.add({ items: pm.items.concat([claim, { key: 'verdict', kind: 'text', x: 0, y: 130, text: showW(ww).length > 22 ? (inL ? 'in the language' : 'not in the language') : showW(ww) + (inL ? '  ∈ L' : '  ∉ L'), anchor: 'middle', cls: inL ? 'good' : 'bad' }]), say: 'i = ' + i + ': u v' + (i === 1 ? '' : '^' + i) + ' x y' + (i === 1 ? '' : '^' + i) + ' z = ' + showW(ww) + (inL ? ', still in ' + L.notation + '.' : ', which is not in ' + L.notation + '. You win this split.'), mark: inL ? undefined : 'student wins' });
        return inL;
      };
      const order = killer === null ? [0, 2] : [killer].concat([0, 2].filter((x) => x !== killer)).slice(0, 2);
      order.forEach(pumpFrame);
      const say = r.survives
        ? (L.cf ? L.notation + ' really is context-free (' + L.why + ') The adversary can always answer, so the game cannot be won: the lemma never proves a language context-free, but here no word will beat it.' : 'Your word let the adversary escape. Try a word where every window of length p is trapped: ' + L.why)
        : 'Whatever split the adversary chooses, some i pushes the word out, so no p works and ' + L.notation + ' is not context-free. Why: ' + L.why;
      F.add({ items: word(split, [claim]), say, mark: r.survives ? 'adversary survives' : 'not context-free' });
      return { frames: F.list, def: { sections: [{ id: 'lang', kind: 'math', title: 'The language', text: L.notation + '  (' + L.name + ')' + (L.grammar ? '\ngrammar: ' + L.grammar.replace(/\n/g, '; ') : '') }, { id: 'rules', kind: 'math', title: 'The game', text: '1. adversary: p\n2. you: s in L, |s| ≥ p\n3. adversary: s = u v x y z,\n   |vxy| ≤ p, |vy| ≥ 1\n4. you: i ≥ 0\nYou win if u vⁱ x yⁱ z ∉ L.' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.killer, once: true, pick: 'option', options: ['i = 0', 'i = 2', 'i = 3', 'No i works'], ask: 'Which i knocks this split out of the language?', answer: (fr, i) => (/^i = [023]$|No i works/.test(fr[i].meta.killer) ? fr[i].meta.killer : 'i = 0'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'In aᵖbᵖcᵖ, why can no split survive?', options: ['vxy has length ≤ p, so it touches at most two of the three blocks', 'v must be a', 'p is too small', 'It can survive'], answer: 0, why: 'Pumping changes at most two of the counts and leaves the third behind.' },
      { q: 'You picked s = abc for aⁿbⁿcⁿ with p = 3. What can go wrong?', options: ['The adversary may take vxy = abc and v = abc... no: any split still fails, but short words give less room', 'Nothing', 'abc is not in the language', 'The adversary wins every time'], answer: 0, why: 'For this language even short words work, but choosing aᵖbᵖcᵖ makes the argument clean for every p.' },
      { q: 'The adversary survives on aⁿbⁿ. What follows?', options: ['Nothing about non-context-freeness; aⁿbⁿ is in fact context-free', 'aⁿbⁿ is not context-free', 'The lemma is wrong', 'p was too large'], answer: 0, why: 'The lemma only gives a necessary condition.' },
      { q: 'How does the context-free lemma differ from the regular one?', options: ['Two pieces v and y are pumped together, anywhere in the word, within a window of length p', 'Only one piece is pumped', 'There is no length bound', 'i must be positive'], answer: 0, why: 'They come from the two sides of a repeated nonterminal in a tree.' },
    ],
  });

  // ---- closure by gluing grammars ------------------------------------------------------------------------------
  const G1 = 'S → a S b | ε';
  const G2 = 'S → c S | c';
  topic({
    id: 'cf-closure', family: 'cf-limits', order: 30, title: 'Closure: union, concatenation and star by gluing grammars',
    blurb: 'Rename the nonterminals of two grammars apart, then add one new start rule: S → S₁ | S₂ for union, S → S₁ S₂ for concatenation, S → S₁ S | ε for star.',
    inputs: [
      { id: 'op', kind: 'choice', label: 'Operation', def: 'union', options: [{ value: 'union', label: 'Union' }, { value: 'concat', label: 'Concatenation' }, { value: 'star', label: 'Star (first grammar)' }] },
      { id: 'g1', kind: 'grammar', label: 'First grammar', def: G1, check: (v) => CF.checkGrammar(v, { maxRules: 6, label: 'First grammar' }) },
      { id: 'g2', kind: 'grammar', label: 'Second grammar', def: G2, check: (v) => CF.checkGrammar(v, { maxRules: 6, label: 'Second grammar' }) },
    ],
    presets: [
      { label: 'aⁿbⁿ ∪ c⁺', values: { op: 'union', g1: G1, g2: G2 } },
      { label: 'aⁿbⁿ · c⁺', values: { op: 'concat', g1: G1, g2: G2 } },
      { label: '(aⁿbⁿ)*', values: { op: 'star', g1: G1, g2: G2 } },
      { label: 'Same names in both: union', values: { op: 'union', g1: 'S → a A\nA → b | ε', g2: 'S → A A\nA → c' } },
    ],
    counters: [{ id: 'rules', label: 'rules' }, { id: 'words', label: 'words shown' }],
    run(inp) {
      const A = CF.grammar(inp.g1), B = CF.grammar(inp.g2);
      const star = inp.op === 'star';
      const res = star ? T.cfpump.star(A) : inp.op === 'union' ? T.cfpump.union(A, B) : T.cfpump.concat(A, B);
      const H = res.grammar;
      const F = new T.Frames(['rules', 'words']);
      const avoid = new Set([...A.terminals, ...B.terminals, ...A.nonterminals, ...B.nonterminals]);
      const ra = T.cfpump.renameApart(A, '1', avoid), rb = star ? null : T.cfpump.renameApart(B, '2', avoid);
      const Ar = T.grammar.make(ra.start, ra.prods, { nonterminals: [...ra.map.values()], terminals: A.terminals });
      const Br = star ? null : T.grammar.make(rb.start, rb.prods, { nonterminals: [...rb.map.values()], terminals: B.terminals });
      const panels = (ga, gb, y) => {
        const pa = CF.rules(ga, { prefix: 'pa', x: 0, y, title: 'first grammar' });
        const items = pa.items.slice();
        if (gb) { const pb = CF.rules(gb, { prefix: 'pb', x: pa.box.w + 90, y, title: 'second grammar' }); items.push(...pb.items); }
        return items;
      };
      F.set('rules', A.productions.length + (star ? 0 : B.productions.length));
      F.add({ items: panels(A, star ? null : B, 100), say: star ? 'One grammar; the star of its language is any number of its words in a row.' : 'Two grammars. ' + (A.nonterminals.some((x) => B.nonterminals.includes(x)) ? 'They share nonterminal names (' + A.nonterminals.filter((x) => B.nonterminals.includes(x)).join(', ') + '), so the rules would mix if we just put them together.' : 'Put their rules together without letting them mix.') });
      F.add({ items: panels(Ar, Br, 100), say: res.trace[0].say });
      const top = T.grammar.make(H.start, H.productions.filter((p) => p.A === H.start).map((p) => [p.A, p.rhs]), { nonterminals: H.nonterminals, terminals: H.terminals });
      const glue = CF.rules(top, { prefix: 'new', x: 0, y: 0, title: 'new start', cls: () => 'new' });
      F.set('rules', H.productions.length);
      F.add({ items: glue.items.concat(panels(Ar, Br, 100)), say: res.trace[1].say, meta: { op: inp.op } });
      const words = T.grammar.language(H, 5).slice(0, 14);
      const inA = new Set(T.grammar.language(A, 5).map((x) => x.join(''))), inB = star ? new Set() : new Set(T.grammar.language(B, 5).map((x) => x.join('')));
      let x = 0, y = 0;
      const wy = Math.max(glue.box.h, 0) + 100 + Math.max(CF.rules(Ar, {}).box.h, Br ? CF.rules(Br, {}).box.h : 0) + 80;
      const chips = [{ key: 'wt', kind: 'text', x: 0, y: wy - 14, text: 'shortest words of the result', cls: 'title' }];
      for (const wd of words) {
        const t = CF.show(wd), ww = Geo.textWidth(t, 15, { mono: true }) + 22;
        if (x + ww > 560) { x = 0; y += 44; }
        const k = wd.join('');
        chips.push({ key: 'w:' + k, kind: 'cell', x, y: wy + y, w: ww, h: 36, text: t, cls: 'mono chip ' + (inp.op === 'union' ? (inA.has(k) && inB.has(k) ? 'good' : inA.has(k) ? 'part-v' : 'part-xx') : 'good') });
        x += ww + 8;
      }
      F.set('words', words.length);
      F.add({ items: glue.items.concat(panels(Ar, Br, 100), chips), say: 'The glued grammar\'s shortest words: ' + words.slice(0, 8).map(CF.show).join(', ') + '. ' + (inp.op === 'union' ? 'Orange ones come from the first language, blue ones from the second.' : inp.op === 'concat' ? 'Each is a word of the first followed by a word of the second.' : 'Each is some words of the language in a row; ε is the empty row.') + ' So context-free languages are closed under ' + (inp.op === 'union' ? 'union' : inp.op === 'concat' ? 'concatenation' : 'star') + '.', mark: 'closed' });
      return { frames: F.list, def: { sections: [CF.gsec(H, 'g', 'The glued grammar')] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.op, once: true, pick: 'option', options: ['S → S1 | S2', 'S → S1 S2', 'S → S1 S | ε', 'S → S1 S2 S1'], ask: (fr, i) => 'Which new start rule glues them for ' + ({ union: 'union', concat: 'concatenation', star: 'star' })[fr[i + 1].meta.op] + '?', answer: (fr, i) => ({ union: 'S → S1 | S2', concat: 'S → S1 S2', star: 'S → S1 S | ε' })[fr[i + 1].meta.op], explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why rename the nonterminals apart first?', options: ['Otherwise a rule of one grammar could be used inside a derivation of the other', 'To make it shorter', 'Context-free grammars require it', 'It is optional and changes nothing'], answer: 0, why: 'Two different A\'s with the same name would mix their rules and create new words.' },
      { q: 'Which rule makes the star of L(S₁)?', options: ['S → S₁ S | ε', 'S → S₁ S₁', 'S → S S₁', 'S → S₁ | ε'], answer: 0, why: 'Any number of S₁-words, including none.' },
      { q: 'Are context-free languages closed under intersection?', options: ['No', 'Yes, by S → S₁ S₂', 'Yes, by renaming', 'Only for finite languages'], answer: 0, why: 'aⁿbⁿcᵐ and aᵐbⁿcⁿ are context-free, their intersection aⁿbⁿcⁿ is not.' },
    ],
  });

  // ---- intersection with a regular language --------------------------------------------------------------------
  const PDA_AB = 'start q0\nstack-start Z\naccept q2\nq0, a, Z -> q0, A Z\nq0, a, A -> q0, A A\nq0, b, A -> q1, ε\nq1, b, A -> q1, ε\nq1, ε, Z -> q2, Z';
  const DFA_EVEN = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const DFA_NOT3 = 'start s0\naccept s0 s1 s2\ns0 -a,b-> s1\ns1 -a,b-> s2\ns2 -a,b-> s3\ns3 -a,b-> s3';
  topic({
    id: 'cf-intersect', family: 'cf-limits', order: 40, title: 'Intersection with a regular language: run both at once',
    blurb: 'A PDA and a DFA can run side by side on the same input: the product\'s states are pairs, the stack is the PDA\'s. So a context-free language intersected with a regular one is context-free.',
    inputs: [
      { id: 'm', kind: 'machine', machine: 'pda', label: 'PDA', def: PDA_AB, check: (v) => CF.checkPda(v, { maxStates: 4 }) },
      { id: 'd', kind: 'machine', machine: 'dfa', label: 'DFA', def: DFA_EVEN, check: (v) => { try { const M = T.Machine.parse(v); if (!T.Machine.isDeterministic(M)) return 'DFA: one move per state and symbol, no ε'; if (M.states.length > 4) return 'DFA: at most 4 states'; } catch (e) { return 'DFA: ' + e.message; } return null; } },
      { id: 'w', kind: 'string', label: 'Input', def: 'aabb', max: 6 },
    ],
    presets: [
      { label: 'aⁿbⁿ ∩ even number of a', values: { m: PDA_AB, d: DFA_EVEN, w: 'aabb' } },
      { label: 'Rejected by the DFA: ab', values: { m: PDA_AB, d: DFA_EVEN, w: 'ab' } },
      { label: 'aⁿbⁿ ∩ length ≤ 2', values: { m: PDA_AB, d: DFA_NOT3, w: 'ab' } },
    ],
    check: wordCheck2,
    counters: [{ id: 'pairs', label: 'reachable pairs' }, { id: 'moves', label: 'product moves' }],
    run(inp) {
      const { P, M } = CF.pda(inp.m);
      const D = T.Machine.parse(inp.d);
      const DF = { states: D.states, alphabet: T.Machine.alphabet(D), start: D.start, accept: D.accept, trans: T.Machine.moves(D) };
      const res = T.pda.productDFA(P, DF);
      let Q = res.pda;
      // keep only the pairs reachable from the start (ignoring the stack), so the picture stays small
      const reach = new Set([Q.start]);
      for (let ch = true; ch;) { ch = false; for (const t of Q.transitions) if (reach.has(t.from) && !reach.has(t.to)) { reach.add(t.to); ch = true; } }
      Q = T.pda.make({ states: Q.states.filter((q) => reach.has(q)), input: Q.input, stack: Q.stack, start: Q.start, startStack: Q.startStack, accept: Q.accept.filter((q) => reach.has(q)), acceptBy: 'final', transitions: Q.transitions.filter((t) => reach.has(t.from)) });
      const MQ = T.Machine.parse(T.pda.toString(Q));
      // a grid: the PDA's states across, the DFA's down, each pair where its row and column meet; the two
      // machines sit along the top and the left edge like the axes of a table
      const GX = 230, GY = 150;
      const pi = (q) => P.states.indexOf(q.split('|')[0]), di = (q) => D.states.indexOf(q.slice(q.indexOf('|') + 1));
      const pos = {}; for (const q of MQ.states) pos[q] = { x: pi(q) * GX, y: di(q) * GY };
      const F = new T.Frames(['pairs', 'moves']);
      const gq = K.graph.draw(MQ, { pos });
      const pp = {}; P.states.forEach((q, i) => { pp[q] = { x: i * GX, y: -GY - 40 }; });
      const dp = {}; D.states.forEach((q, j) => { dp[q] = { x: -GX - 30, y: j * GY }; });
      const gp = K.graph.draw(M, { pos: pp, prefix: 'p' });
      const gd = K.graph.draw(D, { pos: dp, prefix: 'd' });
      const heads = [{ key: 'hp', kind: 'text', x: gp.box.x, y: gp.box.y - 16, text: 'PDA', cls: 'title' }, { key: 'hd', kind: 'text', x: gd.box.x, y: gd.box.y - 16, text: 'DFA', cls: 'title' }];
      const both = gp.items.concat(gd.items, heads);
      F.add({ items: both, say: 'A PDA for one language and a DFA for a regular one. To accept the words in both, run them together: the DFA needs no stack, so it can ride along in the finite control.' });
      F.set('pairs', Q.states.length).set('moves', Q.transitions.length);
      F.add({ items: both.concat(K.graph.draw(MQ, { pos, enter: 'grow' }).items), say: res.trace.find((s) => s.kind === 'pair').say.replace(/\d+ moves\./, Q.transitions.length + ' moves between the ' + Q.states.length + ' reachable pairs.') });
      F.add({ items: both.concat(K.graph.draw(MQ, { pos, good: Q.accept }).items), say: 'A pair accepts when both halves do: ' + (Q.accept.join(', ') || 'none is reachable, so the intersection is empty') + '.', meta: { acc: Q.accept.map((q) => 'g:s:' + q) } });
      const w = T.pda.word(Q, inp.w);
      const sim = T.pda.simulate(Q, w, { maxConfigs: 2000 });
      let path;
      if (sim.accepted) path = sim.paths[0]; else { let b = sim.configs[0]; for (const c of sim.configs) if (c.pos > b.pos || (c.pos === b.pos && c.depth > b.depth)) b = c; path = T.pda.pathTo(sim, b.id); }
      const scene = (c, o) => {
        const g = K.graph.draw(MQ, Object.assign({ pos, active: [c.state] }, o || {}));
        const st = CF.stack(c.stack, { x: gq.box.x + gq.box.w + 60, y: gq.box.y + gq.box.h, prefix: 'k', max: 7 });
        const s = K.string.draw({ text: w, pos: c.pos, x: gq.box.x, y: gq.box.y + gq.box.h + 50, cw: 44, label: 'input', prefix: 'in' });
        return both.concat(g.items, st.items, s.items);
      };
      F.add({ items: scene(path[0]), say: 'Run ' + CF.show(w) + ' on the product, from ' + Q.start + '.' });
      path.slice(1).forEach((c, i) => { const t = Q.transitions[c.via]; F.add({ items: scene(c, { taken: [CF.edgeOf(t)] }), say: T.pda.showT(t) + (t.read ? ': the PDA reads ' + t.read + ' and the DFA steps on ' + t.read + ' too.' : ': an ε-move of the PDA; the DFA stays where it is.') }); });
      const end = path[path.length - 1];
      F.add({ items: scene(end, sim.accepted ? { active: [], good: [end.state] } : { active: [], bad: [end.state] }), say: sim.accepted ? CF.show(w) + ' is accepted: both machines agree.' : CF.show(w) + ' is rejected: ' + (T.pda.accepts(P, T.pda.word(P, inp.w)).accepted ? 'the PDA alone would accept it, but the DFA does not.' : 'the PDA already rejects it.') + ' The product is still one PDA, so the intersection is context-free.', mark: sim.accepted ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [CF.pdaTable(P, 'p', 'PDA moves'), CF.pdaTable(Q, 'delta', 'Product moves (reachable)')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.acc && f.meta.acc.length, once: true, pick: 'item', ask: 'Click a pair that accepts.', answer: (fr, i) => fr[i].meta.acc, explain: 'Both the PDA state and the DFA state must be accepting.' },
    ],
    quiz: [
      { q: 'Why can a PDA be combined with a DFA but not with another PDA this way?', options: ['Two stacks cannot be merged into one', 'DFAs have no ε', 'PDAs have no states', 'It works for two PDAs too'], answer: 0, why: 'A pair of states is fine; a pair of stacks is not a stack (two stacks are as strong as a Turing machine).' },
      { q: 'When the PDA makes an ε-move, the DFA…', options: ['stays in its state', 'reads ε', 'moves to its start', 'rejects'], answer: 0, why: 'No input is read, so the DFA has nothing to step on.' },
      { q: 'L context-free, R regular. Is L − R context-free?', options: ['Yes: L ∩ complement(R), and complement(R) is regular', 'No', 'Only if L is regular', 'Only if R is finite'], answer: 0, why: 'Regular languages are closed under complement, so this is an intersection with a regular language.' },
    ],
  });
  function wordCheck2(inp) { const { P } = CF.pda(inp.m); const bad = [...inp.w].find((c) => !P.input.includes(c)); return bad !== undefined ? 'Input: "' + bad + '" is not in the PDA\'s alphabet' : null; }

  // ---- non-closure ---------------------------------------------------------------------------------------------
  topic({
    id: 'cf-nonclosure', family: 'cf-limits', order: 50, title: 'Not closed under intersection or complement',
    blurb: 'aⁿbⁿcᵐ and aᵐbⁿcⁿ are both context-free. Their common words are aⁿbⁿcⁿ, which is not. And since union is closed, complement cannot be.',
    inputs: [{ id: 'n', kind: 'number', label: 'Show words up to length', def: 6, min: 3, max: 9 }],
    presets: [{ label: 'Up to length 6', values: { n: 6 } }, { label: 'Up to length 9', values: { n: 9 } }],
    counters: [{ id: 'l1', label: 'words of L₁' }, { id: 'l2', label: 'words of L₂' }, { id: 'both', label: 'in both' }],
    run(inp) {
      const D = T.cfpump.intersectionDemo(inp.n, 3);
      const F = new T.Frames(['l1', 'l2', 'both']);
      const both = new Set(D.both);
      const pick = (ws) => ws.filter((x) => !both.has(x)).sort((a, b) => b.length - a.length).slice(0, 5);
      const sets = [{ id: 'A', label: 'L₁ = aⁿbⁿcᵐ' }, { id: 'B', label: 'L₂ = aᵐbⁿcⁿ' }];
      const venn = (stage, hot) => K.set.venn({ sets, r: 150, members: Object.assign({}, stage >= 1 ? { A: pick(D.words1) } : {}, stage >= 2 ? { B: pick(D.words2) } : {}, stage >= 3 ? { AB: D.both.slice(0, 5) } : {}), hot, universe: 'words over a, b, c' }).items;
      F.add({ items: venn(0), say: 'Two languages over a, b, c. L₁ has as many a as b and any number of c; L₂ any number of a and as many b as c.' });
      F.set('l1', D.words1.length);
      F.add({ items: venn(1, ['A']), say: D.trace[0].say });
      F.set('l2', D.words2.length);
      F.add({ items: venn(2, ['B']), say: D.trace[1].say, meta: { q: true } });
      F.set('both', D.both.length);
      F.add({ items: venn(3, ['A', 'B']), say: D.trace[2].say });
      const s = 'aaabbbccc';
      const sp = D.game.trace.filter((t) => t.kind === 'try')[0].split;
      const ww = T.cfpump.pump(sp, 2);
      const pm = K.string.pump({ parts: [{ name: 'u', text: sp.u }, { name: 'v', text: sp.v, pump: true }, { name: 'x', text: sp.x }, { name: 'y', text: sp.y, pump: true }, { name: 'z', text: sp.z }], i: 2, at: { x: -ww.length * 20, y: 300 }, cw: 40, prefix: 'pm' });
      F.add({ items: venn(3, ['A', 'B']).concat(pm.items), say: 'Is aⁿbⁿcⁿ context-free? In the pumping game on ' + s + ' with p = 3, every one of the ' + D.game.tried + ' splits fails: here the first one, pumped with i = 2, gives ' + ww + ', outside aⁿbⁿcⁿ. So the intersection of two context-free languages is not context-free.', mark: 'not closed under ∩' });
      const lines = ['L₁ ∩ L₂  =  complement( complement(L₁) ∪ complement(L₂) )'];
      const formula = lines.map((t, i) => ({ key: 'dm' + i, kind: 'text', x: 0, y: 300 + i * 30, text: t, anchor: 'middle', cls: 'mono' }));
      F.add({ items: venn(3, ['A', 'B']).concat(formula), say: 'And complement: by De Morgan, an intersection is a complement of a union of complements. Union keeps languages context-free. If complement did too, so would intersection, which we just saw fail. So context-free languages are not closed under complement either (though deterministic ones are).', mark: 'not closed under complement' });
      return { frames: F.list, def: { sections: [{ id: 'g1', kind: 'math', title: 'L₁', text: 'S → X C\nX → a X b | ε\nC → c C | ε' }, { id: 'g2', kind: 'math', title: 'L₂', text: 'S → A Y\nA → a A | ε\nY → b Y c | ε' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.q, once: true, pick: 'option', options: ['aⁿbⁿcⁿ', 'aⁿbⁿ', 'a*b*c*', 'Nothing'], ask: 'Which words are in both L₁ and L₂?', answer: () => 'aⁿbⁿcⁿ', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Under which operation are context-free languages closed?', options: ['Union', 'Intersection', 'Complement', 'Difference'], answer: 0, why: 'S → S₁ | S₂. The other three can leave the class.' },
      { q: 'Why does non-closure under intersection imply non-closure under complement?', options: ['L₁ ∩ L₂ is the complement of the union of the complements, and union is closed', 'Complement is a kind of intersection', 'It does not', 'By the pumping lemma directly'], answer: 0, why: 'If complement were closed, De Morgan would make intersection closed.' },
      { q: 'The intersection of a context-free and a regular language is…', options: ['always context-free', 'never context-free', 'always regular', 'undecidable'], answer: 0, why: 'Run a DFA alongside the PDA.' },
      { q: 'Is the complement of aⁿbⁿcⁿ context-free?', options: ['Yes, surprisingly: it is a union of simple context-free pieces', 'No', 'It is regular', 'It is empty'], answer: 0, why: 'Words not of the form a*b*c*, or with #a ≠ #b, or #b ≠ #c: each piece is context-free. Complement can leave the class, but need not.' },
    ],
  });
})();
