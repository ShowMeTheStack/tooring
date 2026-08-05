// Languages no DFA accepts: the pumping lemma seen on a DFA's own run (the first repeated state makes a
// loop, and the loop is y), the pumping game played against the computer, and the Myhill–Nerode
// distinguisher game, where the classes of strings are colours, and aⁿbⁿ needs a new colour for ever.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg, FA = T.FA;
  const P = () => T.Pump;

  T.family({ id: 'nonreg', part: 'regular', order: 60, title: 'Non-regular languages', blurb: 'What a finite memory cannot do: the pumping lemma, read off a DFA and played as a game, and the Myhill–Nerode classes of strings.' });

  const sup = (n) => String(n).split('').map((d) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[+d]).join('');
  const chipW = (q) => Math.max(34, Geo.textWidth(q, 14, { bold: true }) + 18);

  // ---- the lemma on a DFA ---------------------------------------------------------------------------------------
  const MOD3A = 'start z0\naccept z0\nz0 -a-> z1\nz1 -a-> z2\nz2 -a-> z0\nz0 -b-> z0\nz1 -b-> z1\nz2 -b-> z2';
  const ENDS_AB = 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x';
  const ABSTAR = 'start p\naccept p\np -a-> q\nq -b-> p';
  const LEN3 = 'start l0\naccept l0\nl0 -a,b-> l1\nl1 -a,b-> l2\nl2 -a,b-> l0';
  T.topic({
    id: 'pump-dfa', family: 'nonreg', order: 10, title: 'The pumping lemma, read off a DFA',
    blurb: 'A DFA with p states reading a string of length p visits p + 1 states, so one repeats. The symbols read between the two visits form a loop, y, which can be skipped or repeated as often as you like.',
    inputs: [
      R.machineInput({ id: 'm', label: 'DFA', def: MOD3A, kind: 'dfa', max: 6 }),
      { id: 's', kind: 'string', label: 'An accepted string s', def: 'abaab', max: 9 },
    ],
    presets: [
      { label: 'a\'s a multiple of 3: y is a self-loop', values: { m: MOD3A, s: 'abaab' } },
      { label: 'Ends in ab', values: { m: ENDS_AB, s: 'aabab' } },
      { label: '(ab)*: the loop starts at once, x = ε', values: { m: ABSTAR, s: 'abab' } },
      { label: 'Length a multiple of 3: y is the whole string', values: { m: LEN3, s: 'aba' } },
      { label: 'Too short: no state has to repeat', values: { m: ENDS_AB, s: 'ab' } },
    ],
    check: (inp) => { const e = R.alphaCheck('m', 's', 'String')(inp); if (e) return e; const fa = R.fa(inp.m); return R.runDFA(fa, inp.s).accept ? null : 'String: ' + R.w(inp.s) + ' is not accepted by the machine; the lemma is about strings in the language'; },
    counters: [{ id: 'read', label: 'symbols read' }, { id: 'seen', label: 'states seen' }],
    run(inp) {
      const fa = R.fa(inp.m), m = R.dia(fa);
      const w = [...inp.s], p = fa.states.length;
      const run = R.runDFA(fa, inp.s);
      const ps = FA.pumpSplit(fa, inp.s);
      const pos = K.graph.layout(m).pos;
      const g0 = K.graph.draw(m, { pos });
      const cw = Math.max(46, ...fa.states.map((q) => chipW(q) + 12));
      const longest = ps.ok ? [...ps.x].length + 3 * [...ps.y].length + [...ps.z].length : w.length;
      const width = Math.max(w.length, longest) * cw;
      const cx = g0.box.x + g0.box.w / 2;
      const sx = cx - (w.length * cw) / 2, sy = g0.box.y + g0.box.h + 60, ty = sy + 44 + 40 + 34;
      void width;
      const F = new T.Frames(['read', 'seen']);
      const trail = (k, hot) => {
        const out = [{ key: 'run:label', kind: 'text', x: sx - chipW(fa.start) / 2 - 12, y: ty + 5, text: 'run', anchor: 'end', cls: 'title' }];
        for (let i = 0; i <= k; i++) out.push({ key: 'run:' + i, kind: 'state', x: sx + i * cw, y: ty, w: chipW(run.path[i]), h: 32, rx: 16, text: run.path[i], size: 14, cls: hot && hot.includes(i) ? 'hot' : i === k ? 'act' : '', enter: 'grow' });
        return out;
      };
      const str = (i, brackets) => K.string.draw({ text: w, pos: i, x: sx, y: sy, cw, label: 's', head: brackets ? false : 'below', headText: i >= w.length ? 'end' : 'next', brackets }).items;
      F.set('seen', 1);
      F.add({ items: g0.items.concat(str(0), trail(0)), say: 'This DFA has p = ' + p + ' states. s = ' + R.w(inp.s) + ' has length ' + w.length + (w.length >= p ? ' ≥ p, so its run lists ' + (w.length + 1) + ' states: more than there are. Some state must come twice.' : ' < p: its run lists ' + (w.length + 1) + ' states, and nothing forces a repeat.') });
      const stop = ps.ok ? ps.positions[1] : w.length;
      for (let i = 0; i < stop; i++) {
        F.count('read').set('seen', new Set(run.path.slice(0, i + 2)).size);
        const rep = ps.ok && i + 1 === ps.positions[1];
        F.add({ items: K.graph.draw(m, { pos, active: [run.path[i + 1]], taken: [run.path[i] + '>' + run.path[i + 1]], hot: rep ? [ps.state] : [] }).items.concat(str(i + 1), trail(i + 1, rep ? ps.positions : null)), say: rep ? 'Read ' + w[i] + ': back in ' + ps.state + ', first seen after ' + ps.positions[0] + ' symbol' + (ps.positions[0] === 1 ? '' : 's') + '. The pigeonhole principle at work: a loop.' : 'Read ' + w[i] + ': ' + run.path[i] + ' → ' + run.path[i + 1] + '.', meta: { i, next: run.path[i + 2], repeatNext: ps.ok && i + 2 === ps.positions[1] ? ps.state : null } });
      }
      if (!ps.ok) {
        F.add({ items: K.graph.draw(m, { pos, good: [run.end] }).items.concat(str(w.length), trail(w.length)), say: 'No state repeated: ' + R.w(inp.s) + ' is shorter than p. The lemma promises a loop only for strings of length at least p, so there is nothing to pump here.', mark: 'no loop' });
        return { frames: F.list, def: { sections: [R.tuple(fa), R.delta(fa).section] } };
      }
      const [a, b] = ps.positions;
      const loopEdges = [];
      for (let i = a; i < b; i++) loopEdges.push(run.path[i] + '>' + run.path[i + 1]);
      const loopStates = run.path.slice(a, b);
      const br = [{ from: 0, to: a, text: 'x = ' + R.w(ps.x), cls: 'x' }, { from: a, to: b, text: 'y = ' + ps.y, cls: 'y' }, { from: b, to: w.length, text: 'z = ' + R.w(ps.z), cls: 'z' }].filter((x) => x.to > x.from);
      F.add({ items: K.graph.draw(m, { pos, hot: loopStates, taken: loopEdges }).items.concat(str(w.length, br), trail(b, [a, b])), say: 'Cut s there: x = ' + R.w(ps.x) + ' leads to ' + ps.state + ', y = ' + ps.y + ' goes round the loop back to ' + ps.state + ', and z = ' + R.w(ps.z) + ' finishes the run. |xy| = ' + b + ' ≤ p = ' + p + ' and |y| = ' + (b - a) + ' ≥ 1.', meta: { split: true } });
      // pumped versions: the copies of y slide in, the run goes round the loop that many times
      const px = cx - ([...ps.x].length + [...ps.z].length) * cw / 2;
      for (const i of [0, 2, 3]) {
        const pumped = ps.x + ps.y.repeat(i) + ps.z;
        const len = [...pumped].length;
        const pm = K.string.pump({ x: ps.x, y: ps.y, z: ps.z, i, at: { x: cx - (len * cw) / 2, y: sy }, cw, prefix: 'pm' });
        const ok = R.runDFA(fa, pumped);
        F.add({ items: K.graph.draw(m, { pos, hot: loopStates, taken: i ? loopEdges : [], good: ok.accept ? [ok.end] : [] }).items.concat(pm.items, [R.caption('pcap', cx, sy - 22, 'x y' + sup(i) + ' z = ' + R.w(pumped), 'strong')]), say: i === 0 ? 'i = 0: drop y. x leads to ' + ps.state + ' and z finishes from ' + ps.state + ' as before, so ' + R.w(pumped) + ' is accepted too.' : 'i = ' + i + ': the run goes round the loop ' + i + ' times and still ends in ' + ok.end + ': ' + pumped + ' is accepted.', meta: { pumpI: i, accepted: ok.accept } });
      }
      void px;
      F.add({ items: K.graph.draw(m, { pos, hot: loopStates }).items.concat(str(w.length, br)), say: 'So x yⁱ z is in the language for every i. Any regular language has such a p; to show a language is NOT regular, find long strings of it where every short loop, pumped, falls out of the language.', mark: 'pumped' });
      return { frames: F.list, def: { sections: [R.tuple(fa), R.delta(fa).section, { id: 'lemma', kind: 'math', title: 'The lemma', text: 'L regular ⇒ ∃p ∀s ∈ L, |s| ≥ p:\n  s = xyz, |xy| ≤ p, |y| ≥ 1,\n  ∀i ≥ 0: xyⁱz ∈ L' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.repeatNext, once: true, pick: 'item', ask: 'The next symbol brings back a state seen before. Which? Click it.', answer: (fr, i) => 'g:s:' + fr[i].meta.repeatNext, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.split, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Drop y altogether (i = 0). Is x z still accepted?', answer: () => 'Yes', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A DFA has 5 states. How long must an accepted string be to be sure its run repeats a state?', options: ['4', '5', '6', '10'], answer: 1, why: 'A string of length 5 gives a run of 6 states, more than 5: some state repeats.' },
      { q: 'Why is |xy| ≤ p?', options: ['To make y short', 'Because the first repeat happens within the first p + 1 states of the run', 'Because z must be long', 'It is a convention'], answer: 1, why: 'Among the first p + 1 states some state repeats, so the loop is closed after at most p symbols.' },
      { q: 'Why must y be non-empty?', options: ['A loop reads at least one symbol', 'So that x is short', 'Because ε is not in the language', 'It need not be'], answer: 0, why: 'The two visits to the repeated state are at different positions, so at least one symbol is read between them.' },
      { q: 'The lemma holds for language L. Is L regular?', options: ['Yes, always', 'Not necessarily: some non-regular languages pump too', 'Only if it is finite', 'Only if p = 1'], answer: 1, why: 'The lemma is a necessary condition only; it can prove non-regularity, never regularity.' },
    ],
  });

  // ---- the game ----------------------------------------------------------------------------------------------------
  const langOptions = () => P().catalogue.filter((l) => !['prime', 'pow2', 'a-ne-b', 'anbmcnm'].includes(l.id)).map((l) => ({ value: l.id, label: l.name + (l.regular ? ' (regular)' : '') }));
  const MAXLEN = 22;
  const setup = (inp) => {
    const lang = P().get(inp.lang);
    const g = P().game(lang, { p: inp.p, maxI: 8 });
    g.pickP(lang.regular ? undefined : inp.p);
    const s = g.pickString(inp.s);
    if (!s.ok) return { error: s.say };
    const sp = g.pickSplit();
    const out = g.pickI(inp.i);
    return { lang, g, sp, out };
  };
  T.topic({
    id: 'pump-game', family: 'nonreg', order: 20, title: 'The pumping game',
    blurb: 'To prove a language is not regular, win a game: the computer picks p, you pick a string s, the computer splits it as xyz, and you pick i. You win if xyⁱz leaves the language.',
    inputs: [
      { id: 'lang', kind: 'choice', label: 'Language', def: 'anbn', options: langOptions() },
      { id: 'p', kind: 'number', label: 'The computer\'s p (non-regular languages)', def: 3, min: 1, max: 5 },
      { id: 's', kind: 'string', label: 'Your string s', def: 'aaabbb', max: 14 },
      { id: 'i', kind: 'number', label: 'Your i', def: 2, min: 0, max: 5 },
    ],
    presets: [
      { label: 'aⁿbⁿ: aaabbb and i = 2 wins', values: { lang: 'anbn', p: 3, s: 'aaabbb', i: 2 } },
      { label: '#a = #b: ababab is a poor choice', values: { lang: 'equal-ab', p: 3, s: 'ababab', i: 2 } },
      { label: '#a = #b: aaabbb and pump down, i = 0', values: { lang: 'equal-ab', p: 3, s: 'aaabbb', i: 0 } },
      { label: 'Palindromes: aaabaaa', values: { lang: 'pal', p: 3, s: 'aaabaaa', i: 2 } },
      { label: 'a^(n²): aaaaaaaaa, i = 2', values: { lang: 'square', p: 3, s: 'aaaaaaaaa', i: 2 } },
      { label: 'A regular language: the computer always survives', values: { lang: 'no-bb', p: 3, s: 'ababa', i: 3 } },
    ],
    check: (inp) => {
      const r = setup(inp);
      if (r.error) return 'Your string: ' + r.error;
      const len = [...r.out.pumped].length;
      if (len > MAXLEN) return 'Your i: xyⁱz would have ' + len + ' symbols; choose a smaller i or a shorter s so it fits the picture';
      return null;
    },
    counters: [{ id: 'splits', label: 'splits the computer tried' }, { id: 'losing', label: 'splits you defeat' }],
    run(inp) {
      const { lang, g, sp, out } = setup(inp);
      const p = g.p, s = [...inp.s];
      const cw = 40;
      const F = new T.Frames(['splits', 'losing']);
      const card = R.note('card', { x: -330, y: 0, title: 'the language', lines: [lang.name, lang.desc], size: 15 });
      const sx = -300, sy = card.box.h + 60;
      const turn = (k) => ['the computer: p', 'you: s', 'the computer: x y z', 'you: i'].map((t, j) => ({ key: 'turn:' + j, kind: 'cell', x: -330 + j * 168, y: -70, w: 158, h: 34, rx: 17, text: t, size: 14, cls: j === k ? 'hot' : j < k ? 'read' : '' }));
      const pBadge = (cls) => ({ key: 'pbadge', kind: 'cell', x: card.box.x + card.box.w + 24, y: card.box.y + card.box.h / 2 - 20, w: 120, h: 40, rx: 10, text: 'p = ' + p, size: 18, cls: cls || 'act' });
      const base = (k, extra) => card.items.concat(turn(k), [pBadge()], extra || []);
      F.add({ items: card.items.concat(turn(0), [pBadge('hot')]), say: lang.regular ? 'The computer picks p = ' + p + ': its smallest DFA for ' + lang.name + ' has ' + p + ' useful states.' : 'The computer picks p = ' + p + '. (It could pick any p: a winning plan must work for every p, so think of s in terms of p.)' });
      F.add({ items: base(1, K.string.draw({ text: s, x: sx, y: sy, cw, label: 's', sub: true }).items), say: 'You pick s = ' + inp.s + ': it is in the language and has length ' + s.length + ' ≥ p = ' + p + '.' });
      // every legal split, and how many pumps knock it out
      const all = P().splits(lang, p, inp.s, sp.maxI);
      F.set('splits', all.length).set('losing', all.filter((c) => c.failing.length).length);
      const chosen = all.findIndex((c) => c.x === sp.x && c.y === sp.y);
      const rows = all.map((c) => [R.w(c.x), c.y, R.w(c.z), c.failing.length ? c.failing.slice(0, 4).join(', ') + (c.failing.length > 4 ? ', …' : '') : 'none']);
      const tb = K.table.draw({ rows, colHead: ['x', 'y', 'z', 'out for i ='], x: sx, y: sy + 80, mono: true, size: 14, ch: 34, maxRows: 7, focus: [chosen, 0], cls: (r) => (r === chosen ? 'hot' : all[r].failing.length ? '' : 'bad') });
      F.add({ items: base(2, K.string.draw({ text: s, x: sx, y: sy, cw, label: 's', sub: true }).items.concat(tb.items)), say: 'The computer tries all ' + all.length + ' splits with |xy| ≤ ' + p + ' and |y| ≥ 1, testing i = 0 to ' + sp.maxI + '. ' + (all.every((c) => c.failing.length) ? 'Every split can be knocked out for some i, so it picks the one that is hardest to beat.' : 'Split' + (all.filter((c) => !c.failing.length).length > 1 ? 's' : '') + ' in red survive every i: it picks one of those.'), meta: { survives: sp.survives } });
      const br = [{ from: 0, to: [...sp.x].length, text: 'x', cls: 'x' }, { from: [...sp.x].length, to: [...sp.x].length + [...sp.y].length, text: 'y', cls: 'y' }, { from: [...sp.x].length + [...sp.y].length, to: s.length, text: 'z', cls: 'z' }].filter((b) => b.to > b.from);
      F.add({ items: base(2, K.string.draw({ text: s, x: sx, y: sy, cw, label: 's', brackets: br }).items), say: 'It splits s as x = ' + R.w(sp.x) + ', y = ' + sp.y + ', z = ' + R.w(sp.z) + (sp.survives ? ': this split stays in the language for every i up to ' + sp.maxI + '.' : '.'), meta: { inL: out.inL, i: inp.i } });
      const pm = K.string.pump({ x: sp.x, y: sp.y, z: sp.z, i: inp.i, at: { x: sx, y: sy }, cw, prefix: 'pm' });
      F.add({ items: base(3, pm.items.concat([{ key: 'verdict', kind: 'text', x: sx, y: sy + 130, text: 'x y' + sup(inp.i) + ' z ' + (out.inL ? '∈ L' : '∉ L'), cls: 'big ' + (out.inL ? 'bad' : 'good') }])), say: 'You pick i = ' + inp.i + ': x y' + sup(inp.i) + ' z = ' + R.w(out.pumped) + ' is ' + (out.inL ? 'still in the language. The computer survives.' : 'not in the language. You win this round!') });
      const w = P().wins(lang, p, inp.s, sp.maxI);
      let end;
      if (lang.regular) end = 'The computer cannot lose here: ' + lang.name + ' is regular, and its split is a loop of its own DFA, which can be pumped any number of times. No choice of s and i will ever win.';
      else if (!out.inL && w.wins) end = 'And s wins against every split, not just this one: each row of the table can be knocked out. Since this works whatever p is, ' + lang.name + ' is not regular.' + (lang.hint ? ' (' + lang.hint + ')' : '');
      else if (!out.inL) end = 'This split is beaten, but some splits of s survive every i: a cleverer computer would pick one. Choose s so that every split loses. ' + (lang.hint || '');
      else if (g.winningI() !== null) end = 'Another i beats this split: try i = ' + g.winningI() + '.';
      else end = 'No i beats this split, so s was a poor choice: the computer can pump y and stay in the language. ' + (lang.hint || '');
      F.add({ items: base(3, pm.items), say: end, mark: lang.regular || out.inL ? 'computer survives' : 'you win' });
      return { frames: F.list, def: { sections: [{ id: 'lang', kind: 'math', title: 'The language', text: lang.name + '\n' + lang.desc }, { id: 'rules', kind: 'math', title: 'The game', text: '1. computer: p ≥ 1\n2. you: s ∈ L, |s| ≥ p\n3. computer: s = xyz, |xy| ≤ p, |y| ≥ 1\n4. you: i ≥ 0\nyou win if xyⁱz ∉ L' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.survives !== undefined, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Can the computer find a split of s that survives every i?', answer: (fr, i) => (fr[i + 1].meta.survives ? 'Yes' : 'No'), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.inL !== undefined, once: true, pick: 'option', options: ['In L', 'Not in L'], ask: (fr, i) => 'Pump with i = ' + fr[i].meta.i + '. Is x yⁱ z in the language?', answer: (fr, i) => (fr[i].meta.inL ? 'In L' : 'Not in L'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'In the game for aⁿbⁿ, why choose s = aᵖbᵖ?', options: ['It is the shortest string', 'Because |xy| ≤ p forces y to be all a\'s', 'Because it is a palindrome', 'Any string works'], answer: 1, why: 'The first p symbols are a\'s, so pumping changes the a\'s and not the b\'s.' },
      { q: 'Why does the student not get to choose p?', options: ['p is always 3', 'The lemma says "there exists p": the proof must work for every p the language could have', 'p is the length of s', 'To make the game fair'], answer: 1, why: 'The opponent chooses what the lemma claims exists; you must handle any choice.' },
      { q: 'For #a = #b, the student picks s = (ab)ᵖ. What goes wrong?', options: ['Nothing', 'y = ab keeps the counts equal for every i', 's is not in the language', 's is too short'], answer: 1, why: 'Pumping ab adds as many a\'s as b\'s, so the split survives.' },
      { q: 'If the student cannot win for some language, is it regular?', options: ['Yes', 'Not necessarily', 'Only if it is finite', 'Only over one letter'], answer: 1, why: 'Some non-regular languages satisfy the pumping conditions; then other tools (Myhill–Nerode, closure) are needed.' },
      { q: 'Why may the student pick i = 0?', options: ['It is forbidden', 'The lemma promises xyⁱz ∈ L for all i ≥ 0, including removing y', 'Only for finite languages', 'Only when y is long'], answer: 1, why: 'Pumping down is often the easiest win, e.g. for aⁿbᵐ with n > m.' },
    ],
  });

  // ---- Myhill–Nerode ---------------------------------------------------------------------------------------------
  const NERODE = [
    { value: 'ends-bb', label: 'ends in bb (regular)' },
    { value: 'no-bb', label: 'no bb (regular)' },
    { value: 'diff3', label: '#a − #b ≡ 0 mod 3 (regular)' },
    { value: 'anbn', label: 'aⁿbⁿ (not regular)' },
    { value: 'parens', label: 'balanced ( ) (not regular)' },
  ];
  T.topic({
    id: 'nerode-game', family: 'nonreg', order: 30, title: 'Myhill–Nerode: telling strings apart',
    blurb: 'Two strings are equivalent when every suffix treats them alike. A DFA needs one state per class; colour the strings by class, and see aⁿbⁿ need a new colour for ever.',
    inputs: [
      { id: 'lang', kind: 'choice', label: 'Language', def: 'ends-bb', options: NERODE },
      { id: 'n', kind: 'number', label: 'Prefixes to try (non-regular)', def: 5, min: 3, max: 6 },
    ],
    presets: [
      { label: 'Ends in bb: three classes', values: { lang: 'ends-bb' } },
      { label: 'No bb: a class that can never accept', values: { lang: 'no-bb' } },
      { label: '#a − #b mod 3', values: { lang: 'diff3' } },
      { label: 'aⁿbⁿ: a new class for every aⁿ', values: { lang: 'anbn', n: 5 } },
      { label: 'Balanced brackets', values: { lang: 'parens', n: 5 } },
    ],
    counters: [{ id: 'classes', label: 'classes found' }, { id: 'duels', label: 'pairs separated' }],
    run(inp) {
      const lang = P().get(inp.lang);
      const F = new T.Frames(['classes', 'duels']);
      const al = lang.alphabet;
      if (lang.regular) {
        const d = P().dfa(lang), dd = R.dia(d);
        const ner = FA.nerode(d);
        const cls = {}; d.states.forEach((q, k) => { cls[q] = 'rk' + (k % 8); });
        const pos = K.graph.layout(dd).pos;
        // a complete minimal DFA may need crossing edges
        const g = (o) => { const r = K.graph.draw(dd, Object.assign({ pos, cls }, o || {})); r.items = r.items.map((it) => (it.kind === 'edge' && /\btr\b/.test(it.cls || '') ? Object.assign({}, it, { audit: 'edge-x' }) : it)); return r; };
        const gb = R.bounds(g().items);
        const where = (w) => R.runDFA(d, w).end;
        const pyr = R.pyramid({ alphabet: al, maxLen: 3, member: (w) => cls[where(w)], x: gb.x + gb.w + 230, y: gb.y + 20, label: 'strings coloured by class' });
        const dx = gb.x + gb.w + 230;
        F.set('classes', d.states.length);
        F.add({ items: g().items.concat(pyr.items), say: 'Colour each string by the state its run ends in. Strings of one colour lead to one state, so every suffix treats them alike: they are equivalent. ' + lang.name + ' has ' + d.states.length + ' colours.' });
        // duels between representatives of different classes
        const pairs = [];
        for (let i = 0; i < ner.classes.length; i++) for (let j = i + 1; j < ner.classes.length; j++) pairs.push([ner.classes[i], ner.classes[j]]);
        pairs.slice(0, 4).forEach(([A, B]) => {
          const z = ner.distinguish[A.state + '|' + B.state];
          const xa = A.rep + z, xb = B.rep + z, ia = lang.member(xa), ib = lang.member(xb);
          const y0 = pyr.box.y + pyr.box.h + 40;
          const duel = [
            R.caption('d:t', dx, y0, 'append z = ' + R.w(z), 'strong'),
            { key: 'd:a', kind: 'cell', x: dx - 150, y: y0 + 16, w: 130, h: 38, text: R.w(A.rep) + ' · ' + R.w(z), cls: 'mono ' + cls[A.state], size: 15 },
            { key: 'd:av', kind: 'text', x: dx - 85, y: y0 + 80, text: ia ? 'accepted' : 'rejected', anchor: 'middle', cls: ia ? 'good' : 'bad' },
            { key: 'd:b', kind: 'cell', x: dx + 20, y: y0 + 16, w: 130, h: 38, text: R.w(B.rep) + ' · ' + R.w(z), cls: 'mono ' + cls[B.state], size: 15 },
            { key: 'd:bv', kind: 'text', x: dx + 85, y: y0 + 80, text: ib ? 'accepted' : 'rejected', anchor: 'middle', cls: ib ? 'good' : 'bad' },
          ];
          F.count('duels');
          F.add({ items: g({ hot: [A.state, B.state] }).items.concat(pyr.items, duel), say: R.w(A.rep) + ' and ' + R.w(B.rep) + ' have different colours. The suffix z = ' + R.w(z) + ' tells them apart: ' + R.w(xa) + ' is ' + (ia ? 'in' : 'not in') + ' the language, ' + R.w(xb) + ' is ' + (ib ? 'in' : 'not in') + ' it.', meta: { z, a: A.rep, b: B.rep } });
        });
        // two strings of one colour
        const strs = R.upTo(al, 3);
        const twin = strs.find((x) => strs.some((y) => y !== x && y.length > 0 && x.length > 0 && where(x) === where(y)));
        const twin2 = strs.find((y) => y !== twin && y.length > 0 && where(y) === where(twin));
        if (twin && twin2) F.add({ items: g({ hot: [where(twin)] }).items.concat(pyr.items.map((it) => (it.key === pyr.key(twin) || it.key === pyr.key(twin2) ? Object.assign({}, it, { cls: it.cls + ' hot' }) : it))), say: twin + ' and ' + twin2 + ' share a colour: both runs end in ' + where(twin) + ', so after any suffix they end in the same state again. No suffix can ever separate them.' });
        F.add({ items: g({ good: d.accept }).items.concat(pyr.items), say: d.states.length + ' classes, pairwise separable: any DFA for ' + lang.name + ' needs at least ' + d.states.length + ' states, and the minimal one has exactly that many, one per class.', mark: 'classes' });
        return { frames: F.list, def: { sections: [R.tuple(d, 'The minimal DFA'), { id: 'cls', kind: 'math', title: 'The classes', text: ner.classes.map((c) => '[' + R.w(c.rep) + '] → ' + c.state + (c.accepting ? ' (accepting)' : '')).join('\n') }] } };
      }
      // non-regular: a staircase of prefixes, each separated from all earlier ones
      const c0 = lang.id === 'parens' ? '(' : 'a';
      const pre = Array.from({ length: inp.n }, (_, k) => c0.repeat(k + 1));
      const n = pre.length;
      const sep = (x, y) => FA.distinguishing(lang.member, al, x, y, 8);
      const tab = (k, hot) => {
        const rows = pre.map((x, r) => pre.map((y, c) => (r < k && c < k && c < r ? R.w(sep(x, y)) : r < k && c === r ? '' : '')));
        return K.table.draw({ rows, rowHead: pre, colHead: pre, x: 0, y: 0, mono: true, size: 15, cw: 74, ch: 38, skip: (r, c) => c >= r, hot: hot ? [hot] : [], cls: (r, c) => (r < k && c < k ? 'rk' + (r % 8) : '') });
      };
      const stair = (k) => pre.slice(0, k).map((x, i) => ({ key: 'st:' + i, kind: 'cell', x: -230 + 0, y: 40 + i * 44, w: Math.max(60, Geo.textWidth(x, 15, { mono: true }) + 20), h: 36, text: x, cls: 'mono rk' + (i % 8), size: 15, enter: 'grow' }));
      F.add({ items: tab(0).items.concat([R.caption('st:t', -230, 22, 'prefixes', 'title', 'start')]), say: 'For ' + lang.name + ', try the prefixes ' + pre.join(', ') + '. Could some of them share a class?' });
      for (let k = 1; k <= n; k++) {
        F.set('classes', k);
        if (k > 1) F.count('duels', k - 1);
        const x = pre[k - 1];
        const zs = pre.slice(0, k - 1).map((y) => sep(x, y));
        F.add({ items: tab(k).items.concat([R.caption('st:t', -230, 22, 'prefixes', 'title', 'start')], stair(k)), say: k === 1 ? x + ' gets the first colour.' : x + ' is separated from every earlier prefix: from ' + pre[k - 2] + ' by ' + R.w(zs[k - 2]) + ' (' + x + R.w(zs[k - 2]).replace('ε', '') + ' and ' + pre[k - 2] + zs[k - 2] + ' differ). So it needs a new colour: ' + k + ' classes so far.', meta: { k, z: k > 1 ? zs[k - 2] : null, x, y: k > 1 ? pre[k - 2] : null } });
      }
      F.add({ items: tab(n).items.concat([R.caption('st:t', -230, 22, 'prefixes', 'title', 'start')], stair(n)), say: 'The pattern never stops: ' + c0 + 'ⁱ and ' + c0 + 'ʲ (i ≠ j) are always separated, so there are infinitely many classes. A DFA has finitely many states, so no DFA accepts ' + lang.name + ': it is not regular.', mark: 'infinite' });
      return { frames: F.list, def: { sections: [{ id: 'lang', kind: 'math', title: 'The language', text: lang.name + '\n' + lang.desc }, { id: 'thm', kind: 'text', title: 'Myhill–Nerode', text: 'x ≡ y when for every z, xz ∈ L exactly when yz ∈ L. L is regular exactly when there are finitely many classes, and then the minimal DFA has one state per class.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.z !== undefined && fr[i + 1].meta.a !== undefined, once: true, pick: 'option', options: (fr, i) => [...new Set([R.w(fr[i + 1].meta.z), 'ε', 'a', 'b', 'bb', 'ab'])].slice(0, 5), ask: (fr, i) => 'Which suffix tells ' + R.w(fr[i + 1].meta.a) + ' and ' + R.w(fr[i + 1].meta.b) + ' apart (the shortest)?', answer: (fr, i) => R.w(fr[i + 1].meta.z), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 3, once: true, pick: 'option', options: (fr, i) => [...new Set([R.w(fr[i + 1].meta.z), 'ε', 'b', 'bb', 'bbb', ')', '))', ')))'])].filter((x) => x !== undefined).slice(0, 5), ask: (fr, i) => 'Which suffix separates ' + fr[i + 1].meta.x + ' from ' + fr[i + 1].meta.y + '?', answer: (fr, i) => R.w(fr[i + 1].meta.z), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Strings x and y lead a DFA to the same state. Are they equivalent?', options: ['Yes: every suffix then ends in the same state for both', 'No', 'Only if the state accepts', 'Only if |x| = |y|'], answer: 0, why: 'From one state, the same suffix leads to the same end state, so the verdicts agree.' },
      { q: 'How many classes has "ends in bb" over {a, b}?', options: ['2', '3', '4', 'infinitely many'], answer: 1, why: 'Strings not ending in b, ending in exactly one b, and ending in bb behave differently; nothing else matters.' },
      { q: 'Which suffix separates aa from aaa for aⁿbⁿ?', options: ['b', 'bb', 'ab', 'ε'], answer: 1, why: 'aabb is in the language and aaabb is not.' },
      { q: 'What does Myhill–Nerode give that the pumping lemma does not?', options: ['Nothing more', 'An exact test: regular if and only if finitely many classes', 'Faster DFAs', 'A grammar'], answer: 1, why: 'The pumping lemma is only necessary; finitely many classes is necessary and sufficient.' },
    ],
  });
})();
