// The subset construction: each DFA state is a set of NFA states, born as a box out of the states it came
// from, with its moves added one at a time while the NFA beside it lights the states and moves being
// combined; every subset the construction could have made is shown as a chip, and only the reachable ones
// light up. Then the family where the blow-up is real (the k-th symbol from the end), with a growth chart,
// and the ε-NFA version, where every box first holds the states the moves reach and then swells to their
// ε-closure.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg;

  T.family({ id: 'subset', part: 'regular', order: 30, title: 'The subset construction', blurb: 'Turn an NFA into a DFA: a state of the DFA is the set of NFA states a run could be in. Only the reachable sets are built, but there can be exponentially many.' });

  const showSet = (names) => (names.length ? '{' + names.join(', ') + '}' : '∅');
  // box text is drawn in a monospaced face, wider than the kit's estimate: pad it so it never touches the border
  const pad = (t) => '\u00a0' + t + '\u00a0';
  // edges of a generated machine may have to cross
  const crossOk = (items, P) => items.map((it) => (it.kind === 'edge' && it.key.startsWith(P + ':e:') ? Object.assign({}, it, { audit: 'edge-x' }) : it));

  /**
   * The frames of a subset construction. o: {chips: show all 2ⁿ subsets, eps: show each closure as its own
   * step}. Returns {frames, def}.
   */
  function construction(fa, o) {
    const res = T.FA.subset(fa);
    const dfa = res.fa;
    const disp = (S) => showSet(res.sets[S] || []);
    const boxes = {};
    for (const S of dfa.states) boxes[S] = [pad(disp(S))];
    const nd = R.dia(fa), dd = R.dia(dfa);
    const posN = K.graph.layout(nd, { r: 22 }).pos;
    const gN = K.graph.draw(nd, { prefix: 'n', pos: posN, r: 22 });
    const bN = R.bounds(gN.items);
    // the chips: every subset of the NFA's states, made ones lit
    let chips = () => [], chipBox = null;
    if (o.chips) {
      const n = fa.states.length;
      const all = [];
      for (let mask = 0; mask < 1 << n; mask++) all.push(fa.states.filter((_, i) => mask & (1 << i)));
      all.sort((a, b) => a.length - b.length);
      const cols = n <= 2 ? 1 << n : 4;
      const cw = Math.max(46, ...all.map((s) => Geo.textWidth(showSet(s), 13, { mono: true }) + 14)), ch = 30, gap = 6;
      const rowsN = Math.ceil(all.length / cols);
      const x0 = bN.x + bN.w + 70, y0 = bN.y + bN.h / 2 - (rowsN * (ch + gap) - gap) / 2 + 12;
      chipBox = { x: x0, y: y0 - 24, w: cols * (cw + gap), h: Math.ceil(all.length / cols) * (ch + gap) + 24 };
      chips = (made) => [{ key: 'ch:title', kind: 'text', x: x0 + (cols * (cw + gap) - gap) / 2, y: y0 - 12, text: 'all ' + all.length + ' subsets: ' + made.length + ' made', anchor: 'middle', cls: 'title' }].concat(all.map((s, i) => {
        const name = T.FA.setName(s);
        const on = made.includes(name);
        return { key: 'ch:' + name, kind: 'cell', x: x0 + (i % cols) * (cw + gap), y: y0 + Math.floor(i / cols) * (ch + gap), w: cw, h: ch, text: showSet(s), size: 13, cls: 'mono ' + (on ? 'good' : 'empty') };
      }));
    }
    // the DFA, laid out once (as it will end up) and placed to the right of the NFA
    const p0 = K.graph.layout(dd, { boxes }).pos;
    const b0 = R.bounds(K.graph.draw(dd, { prefix: 'd', pos: p0, boxes }).items);
    // below the NFA (and the chips), centred under them
    const topRight = chipBox ? chipBox.x + chipBox.w : bN.x + bN.w;
    const topBottom = Math.max(bN.y + bN.h, chipBox ? chipBox.y + chipBox.h : -Infinity);
    const left = (bN.x + topRight) / 2 - b0.w / 2, dTop = topBottom + 80;
    const posD = {};
    for (const S of dfa.states) posD[S] = { x: p0[S].x - b0.x + left, y: p0[S].y - b0.y + dTop };
    const made = [], edges = [];
    const nfaDraw = (g) => K.graph.draw(nd, Object.assign({ prefix: 'n', pos: posN, r: 22 }, g)).items;
    const dfaDraw = (g, bx) => {
      const m = { kind: 'dfa', states: made.slice(), start: dfa.start, accept: dfa.accept.filter((S) => made.includes(S)), trans: edges.slice(), pos: {} };
      return crossOk(K.graph.draw(m, Object.assign({ prefix: 'd', pos: posD, boxes: Object.assign({}, boxes, bx || {}), dead: made.includes('∅') ? ['∅'] : [] }, g)).items, 'd');
    };
    const caps = [R.caption('cap:n', bN.x + bN.w / 2, bN.y - 18, 'the NFA', 'title'), R.caption('cap:d', left + b0.w / 2, dTop - 22, 'the DFA being built', 'title')];
    const dtD = R.delta(dfa, { title: 'DFA moves (on subsets)' }), dtN = R.delta(fa, { id: 'nd', title: 'NFA moves' });
    const epsIn = (set) => fa.trans.filter((e) => e.sym === '' && set.includes(e.from) && set.includes(e.to)).map((e) => e.from + '>' + e.to);
    const F = new T.Frames(['subsets', 'moves']);
    const tr = res.trace;
    let i = 0;
    // the start subset
    const st = tr[i++];
    made.push(st.name);
    F.count('subsets');
    const startMembers = st.set;
    if (o.eps && startMembers.length > 1) {
      F.add({ items: caps.concat(nfaDraw({ active: [fa.start] }), dfaDraw({ from: { [st.name]: 'n:s:' + fa.start }, hot: [st.name] }, { [st.name]: [pad('{' + fa.start + '}')] }), chips(made)), say: 'The DFA starts where the NFA starts: in ' + fa.start + '. But the NFA can move by ε before reading anything…', meta: { stage: 'start', total: dfa.states.length } });
      F.add({ items: caps.concat(nfaDraw({ active: startMembers, taken: epsIn(startMembers) }), dfaDraw({ hot: [st.name] }), chips(made)), say: '…so the start box swells to the ε-closure of ' + fa.start + ': ' + disp(st.name) + (st.accepting ? '. It holds an accepting state, so it accepts.' : '.'), hl: { nd: startMembers.map(dtN.row) }, meta: { total: dfa.states.length } });
    } else {
      F.add({ items: caps.concat(nfaDraw({ active: startMembers }), dfaDraw({ from: { [st.name]: 'n:s:' + fa.start }, hot: [st.name] }), chips(made)), say: st.say + ' A DFA state is a set of NFA states: the states a run could be in.' + (st.accepting ? ' It holds an accepting state, so it accepts.' : ''), hl: { nd: startMembers.map(dtN.row) }, meta: { total: dfa.states.length } });
    }
    let fresh = null;
    for (; i < tr.length; i++) {
      const s = tr[i];
      if (s.kind === 'subset-new') { fresh = s; continue; }
      if (s.kind !== 'subset-edge') continue;
      const S = s.from, a = s.sym, Tn = s.to;
      const members = res.sets[S];
      const nTaken = fa.trans.filter((e) => e.sym === a && members.includes(e.from)).map((e) => e.from + '>' + e.to);
      const closure = res.sets[Tn];
      const grew = closure.length > s.moved.length;
      if (fresh) { made.push(Tn); F.count('subsets'); }
      edges.push({ from: S, to: Tn, label: a });
      F.count('moves');
      const hl = { delta: [dtD.rc(S, a)], nd: members.map((q) => dtN.rc(q, a)) };
      if (fresh && o.eps && grew) {
        F.add({ items: caps.concat(nfaDraw({ active: members, hot: s.moved, taken: nTaken }), dfaDraw({ hot: [S], taken: [S + '>' + Tn], from: { [Tn]: 'd:s:' + S } }, { [Tn]: [pad(showSet(s.moved))] }), chips(made)), say: 'From ' + disp(S) + ' on ' + a + ': the moves on ' + a + ' reach ' + showSet(s.moved) + '.', hl, meta: { edge: true } });
        F.add({ items: caps.concat(nfaDraw({ active: closure, taken: epsIn(closure) }), dfaDraw({ hot: [Tn] }), chips(made)), say: 'Then follow the ε-moves: the ε-closure is ' + disp(Tn) + ', a new DFA state' + (fresh.accepting ? ', accepting.' : '.'), hl: { nd: closure.map(dtN.row) }, meta: { closure: true } });
      } else {
        const why = fresh ? (Tn === '∅' ? ' No NFA state has a move on ' + a + ': the empty set ∅ is born, the dead state.' : ' New subset' + (fresh.accepting ? ', accepting (it holds an accepting NFA state).' : '.')) : ' That subset exists already: just draw the arrow.';
        F.add({ items: caps.concat(nfaDraw({ active: members, hot: s.moved, taken: nTaken }), dfaDraw({ hot: [S], taken: [S + '>' + Tn], from: fresh ? { [Tn]: 'd:s:' + S } : undefined }), chips(made)), say: 'From ' + disp(S) + ' on ' + a + ': ' + (members.length ? 'the moves of ' + members.join(', ') + ' on ' + a + ' reach ' + showSet(s.moved) : '∅ reaches nothing') + (grew ? ', with ε-closure ' + disp(Tn) : '') + '.' + why, hl, meta: { edge: true, from: S, fromD: disp(S), sym: a, to: Tn, fresh: !!fresh } });
      }
      fresh = null;
    }
    const n = fa.states.length;
    F.add({ items: caps.concat(nfaDraw({}), dfaDraw({ good: dfa.accept }), chips(made)), say: 'Every subset made has all its moves: the DFA has ' + dfa.states.length + ' state' + (dfa.states.length === 1 ? '' : 's') + ' out of the 2^' + n + ' = ' + (1 << n) + ' subsets there could be. The others are never reached from the start, so they are never made. The accepting boxes are those holding an accepting NFA state.', mark: 'done' });
    return { frames: F.list, def: { sections: [dtD.section, dtN.section, { id: 'rule', kind: 'math', title: 'The construction', text: 'start = ε-closure({q₀})\nδ′(S, a) = ε-closure(⋃ δ(q, a), q ∈ S)\nS accepts ⇔ S ∩ F ≠ ∅' }] } };
  }

  const subsetPredict = [
    { at: (f, i) => i === 0, once: true, pick: 'option', options: (fr) => R.numberOptions(fr[0].meta.total), ask: 'How many DFA states (subsets) do you expect the construction to build?', answer: (fr) => String(fr[0].meta.total), explain: (fr) => fr[fr.length - 1].say },
    { at: (f, i, fr) => i > 1 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.edge && fr[i + 1].meta.fresh === false, once: true, pick: 'item', ask: (fr, i) => 'From ' + fr[i + 1].meta.fromD + ' on ' + fr[i + 1].meta.sym + ': which existing box does the arrow go to? Click it.', answer: (fr, i) => 'd:s:' + fr[i + 1].meta.to, explain: (fr, i) => fr[i + 1].say },
  ];

  const ENDS_AB = 'start p\naccept r\np -a,b-> p\np -a-> q\nq -b-> r';
  const HAS_BB = 'start a\naccept c\na -a,b-> a\na -b-> b\nb -b-> c\nc -a,b-> c';
  const TWO_WAYS = 'start s\naccept f\ns -a-> x\ns -a-> y\nx -b-> f\ny -a-> f';
  const ABSTAR = 'start s\naccept s\ns -a-> t\nt -b-> s';
  const SECOND_LAST = 'start p\naccept r\np -a,b-> p\np -a-> q\nq -a,b-> r';
  T.topic({
    id: 'subset-build', family: 'subset', order: 10, title: 'Subsets become states',
    blurb: 'Each DFA state is a box holding a set of NFA states. Boxes are born only when a move reaches them, so most of the possible subsets are never built.',
    inputs: [R.machineInput({ id: 'm', label: 'NFA (no ε-moves)', def: HAS_BB, kind: 'nfa', max: 4, eps: false })],
    presets: [
      { label: 'Contains bb: 4 of 8 subsets', values: { m: HAS_BB } },
      { label: 'Ends in ab', values: { m: ENDS_AB } },
      { label: 'Second from last is a', values: { m: SECOND_LAST } },
      { label: 'Missing moves give the dead subset ∅', values: { m: TWO_WAYS } },
      { label: '(ab)*: the start accepts ε', values: { m: ABSTAR } },
    ],
    counters: [{ id: 'subsets', label: 'subsets made' }, { id: 'moves', label: 'DFA moves' }],
    run: (inp) => construction(R.fa(inp.m), { chips: true }),
    predict: subsetPredict,
    quiz: [
      { q: 'What is a state of the DFA built by the subset construction?', options: ['One NFA state', 'A set of NFA states the run could be in', 'A pair of NFA states', 'A string'], answer: 1, why: 'After any prefix, the NFA could be in several states; the DFA remembers exactly that set.' },
      { q: 'When is a subset an accepting state of the DFA?', options: ['When all its states accept', 'When it holds at least one accepting NFA state', 'When it is the largest subset', 'Never'], answer: 1, why: 'The NFA accepts when some branch accepts, so one accepting state in the set is enough.' },
      { q: 'What does the subset ∅ mean?', options: ['The start state', 'No branch is alive: a dead state', 'Every state at once', 'An error'], answer: 1, why: 'Once no NFA state is live, nothing can revive it: ∅ moves to ∅ on every symbol.' },
      { q: 'An NFA has 4 states. Must its DFA have 16 states?', options: ['Yes, always', 'No: only the subsets reachable from the start are built', 'It has exactly 4', 'It has 8'], answer: 1, why: '16 is the most there could be; the construction builds only those a run can actually reach.' },
      { q: 'Why does the construction stop?', options: ['After n steps', 'There are finitely many subsets, and each is processed once', 'When it reaches ∅', 'It might not'], answer: 1, why: 'At most 2ⁿ subsets, each handled once with one move per symbol.' },
    ],
  });

  // ---- the blow-up ----------------------------------------------------------------------------------------------
  const kthNFA = (k) => {
    const trans = [{ from: 'q0', sym: 'a', to: 'q0' }, { from: 'q0', sym: 'b', to: 'q0' }, { from: 'q0', sym: 'a', to: 'q1' }];
    for (let j = 1; j < k; j++) for (const c of ['a', 'b']) trans.push({ from: 'q' + j, sym: c, to: 'q' + (j + 1) });
    return T.FA.make({ states: Array.from({ length: k + 1 }, (_, j) => 'q' + j), alphabet: ['a', 'b'], start: 'q0', accept: ['q' + k], trans });
  };
  const KMAX = 6;
  T.topic({
    id: 'subset-blowup', family: 'subset', order: 20, title: 'The exponential blow-up',
    blurb: 'For "the k-th symbol from the end is a" the NFA grows by one state per k, but the DFA doubles: it must remember the whole window of the last k symbols.',
    inputs: [{ id: 'k', kind: 'number', label: 'k (for the DFA drawn)', def: 2, min: 1, max: 3 }],
    presets: [
      { label: 'k = 1: the last symbol is a', values: { k: 1 } },
      { label: 'k = 2', values: { k: 2 } },
      { label: 'k = 3: 8 states', values: { k: 3 } },
    ],
    counters: [{ id: 'nfa', label: 'NFA states' }, { id: 'dfa', label: 'DFA states' }],
    run(inp) {
      const k = inp.k;
      const nfa = kthNFA(k);
      const nd = R.dia(nfa);
      const posN = R.row(nfa.states, 0, 0, 130);
      const gN = K.graph.draw(nd, { prefix: 'n', pos: posN, r: 24 });
      const bN = R.bounds(gN.items);
      // the chart: two bars per k, scaled so 64 states is 256 units tall
      const sizes = [];
      for (let j = 1; j <= KMAX; j++) { const d = T.FA.subset(kthNFA(j)).fa; sizes.push({ k: j, nfa: j + 1, dfa: d.states.length, min: T.FA.minimizeHopcroft(d).fa.states.length }); }
      const base = bN.y + bN.h + 60 + 256 + 20, unit = 4, gw = 84, bw = 30;
      const cx0 = bN.x + bN.w / 2 - (KMAX * gw) / 2;
      const chart = (upto, lit) => {
        const out = [
          { key: 'ax', kind: 'line', x1: cx0 - 10, y1: base, x2: cx0 + KMAX * gw, y2: base },
          { key: 'lg:n', kind: 'cell', x: cx0 + KMAX * gw + 20, y: base - 250, w: 22, h: 22, text: '', cls: 'act' },
          { key: 'lg:nt', kind: 'text', x: cx0 + KMAX * gw + 50, y: base - 234, text: 'NFA states', cls: 'strong' },
          { key: 'lg:d', kind: 'cell', x: cx0 + KMAX * gw + 20, y: base - 214, w: 22, h: 22, text: '', cls: 'hot' },
          { key: 'lg:dt', kind: 'text', x: cx0 + KMAX * gw + 50, y: base - 198, text: 'DFA states', cls: 'strong' },
        ];
        sizes.slice(0, upto).forEach((s, i) => {
          const x = cx0 + i * gw + 8;
          const hn = s.nfa * unit, hd = s.dfa * unit;
          out.push({ key: 'bn:' + s.k, kind: 'cell', x, y: base - hn, w: bw, h: hn, text: '', cls: 'act', enter: 'grow' });
          out.push({ key: 'bd:' + s.k, kind: 'cell', x: x + bw + 4, y: base - hd, w: bw, h: hd, text: '', cls: 'hot', enter: 'grow' });
          out.push({ key: 'vn:' + s.k, kind: 'text', x: x + bw / 2, y: base - hn - 8, text: String(s.nfa), anchor: 'middle', cls: 'strong' });
          out.push({ key: 'vd:' + s.k, kind: 'text', x: x + bw * 1.5 + 4, y: base - hd - 8, text: String(s.dfa), anchor: 'middle', cls: 'strong' });
          out.push({ key: 'kx:' + s.k, kind: 'text', x: x + bw + 2, y: base + 22, text: 'k = ' + s.k, anchor: 'middle', cls: s.k === lit ? 'hot' : 'strong' });
        });
        return out;
      };
      const F = new T.Frames(['nfa', 'dfa']);
      F.set('nfa', k + 1);
      F.add({ items: gN.items.concat([R.caption('cap', bN.x + bN.w / 2, bN.y - 16, 'NFA for k = ' + k, 'title')]), say: 'The NFA for "the ' + k + (k === 1 ? 'st' : k === 2 ? 'nd' : 'rd') + ' symbol from the end is a" has ' + (k + 1) + ' states: q0 waits, guesses an a, and q1 … q' + k + ' count what follows. How big is its DFA?' });
      for (let j = 1; j <= KMAX; j++) {
        const s = sizes[j - 1];
        F.set('nfa', s.nfa).set('dfa', s.dfa);
        F.add({ items: gN.items.concat([R.caption('cap', bN.x + bN.w / 2, bN.y - 16, 'NFA for k = ' + k, 'title')], chart(j, j)), say: 'k = ' + j + ': the NFA has ' + s.nfa + ' states, the subset construction builds ' + s.dfa + (s.min === s.dfa ? ', and none can be merged: ' + s.dfa + ' = 2^' + j + ' is the smallest possible.' : ' (minimal: ' + s.min + ').'), meta: { k: j, dfa: s.dfa } });
      }
      // the DFA for the chosen k: each state is the window of the last k symbols
      const res = T.FA.subset(nfa);
      const dfa = res.fa;
      const windowOf = (S) => { const set = res.sets[S]; let w = ''; for (let idx = 0; idx < k; idx++) w += set.includes('q' + (k - idx)) ? 'a' : 'b'; return w; };
      const boxes = {};
      for (const S of dfa.states) boxes[S] = [pad('…' + windowOf(S)), pad(showSet(res.sets[S]))];
      const dd = R.dia(dfa);
      const p0 = k === 1 ? { [dfa.states[0]]: { x: 0, y: 0 }, [dfa.states[1]]: { x: 220, y: 0 } } : K.graph.layout(dd, { boxes }).pos;
      const b0 = R.bounds(K.graph.draw(dd, { prefix: 'd', pos: p0, boxes }).items);
      const posD = {};
      const cy = base - 140;
      for (const S of dfa.states) posD[S] = { x: p0[S].x - (b0.x + b0.w / 2) + bN.x + bN.w / 2, y: p0[S].y - (b0.y + b0.h / 2) + cy };
      const gD = crossOk(K.graph.draw(dd, { prefix: 'd', pos: posD, boxes, enter: 'grow' }).items, 'd');
      F.set('nfa', k + 1).set('dfa', dfa.states.length);
      F.add({ items: gN.items.concat([R.caption('cap', bN.x + bN.w / 2, bN.y - 16, 'NFA for k = ' + k, 'title')], gD), say: 'The DFA for k = ' + k + ' has ' + dfa.states.length + ' states. Each subset says which of the last ' + k + ' symbols were a: q' + 1 + ' in the set means the last symbol was a, q' + k + ' means the ' + k + (k === 1 ? 'st' : k === 2 ? 'nd' : 'rd') + ' from the end was. So each box is a window …' + 'a'.repeat(k).replace(/a/g, 'x') + ' of the input, and it accepts when the window starts with a.' });
      F.add({ items: gN.items.concat([R.caption('cap', bN.x + bN.w / 2, bN.y - 16, 'NFA for k = ' + k, 'title')], chart(KMAX, k)), say: 'No DFA can do better: two different windows differ at some position j from the end, and adding k − j symbols makes that position the k-th from last, so one string is accepted and the other is not. All 2^k windows must be different states.', mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(nfa, 'The NFA'), R.delta(nfa).section, { id: 'count', kind: 'table', title: 'States for each k', colHead: ['k', 'NFA', 'DFA'], rows: sizes.map((s) => [String(s.k), String(s.nfa), String(s.dfa)]) }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 4, once: true, pick: 'option', options: ['5', '8', '16', '25'], ask: 'k = 1, 2, 3 gave DFAs with 2, 4, 8 states. How many for k = 4?', answer: (fr, i) => String(fr[i + 1].meta.dfa), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'For k = 10, how many states does the smallest DFA need?', options: ['11', '20', '100', '1024'], answer: 3, why: 'One per window of the last 10 symbols: 2¹⁰ = 1024.' },
      { q: 'And the NFA?', options: ['11', '20', '1024', '2'], answer: 0, why: 'k + 1 = 11 states: one to wait, k to count after the guess.' },
      { q: 'Does the subset construction always blow up exponentially?', options: ['Yes', 'No: often only a few subsets are reachable', 'Only with ε-moves', 'Never'], answer: 1, why: 'Many NFAs give small DFAs; this family is the worst case, where every subset with q0 is reachable.' },
      { q: 'Why must two different windows be different DFA states?', options: ['They have different lengths', 'Some suffix leads one to acceptance and the other not', 'DFAs cannot merge states', 'They are reached by different paths'], answer: 1, why: 'Pick a position where the windows differ and pad so that position becomes the k-th from last.' },
    ],
  });

  // ---- with ε-moves -----------------------------------------------------------------------------------------------
  const ASBS = 'start p\naccept r\np -a-> p\np -ε-> q\nq -b-> q\nq -ε-> r\nr -c-> r';
  const LATE = 'start s\naccept t\ns -a-> u\nu -ε-> v\nv -ε-> t\nv -b-> s';
  const ECYCLE = 'start p\naccept r\np -ε-> q\nq -ε-> p\np -a-> q\nq -b-> r';
  const OPT = 'start s\naccept f\ns -a-> m\ns -ε-> m\nm -b-> f';
  const UNION = 'start s\naccept a2 b2\ns -ε-> a1\ns -ε-> b1\na1 -a-> a2\nb1 -b-> b2\na2 -a-> a2\nb2 -b-> b2';
  T.topic({
    id: 'subset-enfa', family: 'subset', order: 30, title: 'From an ε-NFA to a DFA',
    blurb: 'With ε-moves, each new subset is found in two steps: the states the symbol reaches, then everything their ε-moves add. Watch each box swell to its ε-closure.',
    inputs: [R.machineInput({ id: 'm', label: 'ε-NFA', def: ASBS, kind: 'nfa', max: 5 })],
    presets: [
      { label: 'a*b*c*: ε-moves chain the parts', values: { m: ASBS } },
      { label: 'ε-moves after a symbol: the box swells', values: { m: LATE } },
      { label: 'An ε-cycle', values: { m: ECYCLE } },
      { label: 'An optional a, then b', values: { m: OPT } },
      { label: 'A union made with ε: a+ or b+', values: { m: UNION } },
    ],
    counters: [{ id: 'subsets', label: 'subsets made' }, { id: 'moves', label: 'DFA moves' }],
    run: (inp) => construction(R.fa(inp.m), { eps: true }),
    predict: [
      subsetPredict[0],
      subsetPredict[1],
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.closure, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'The moves reached the states in the new box. Will ε-moves add more states to it?', answer: () => 'Yes', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What is the start state of the DFA built from an ε-NFA?', options: ['{q₀}', 'The ε-closure of q₀', 'All states', '∅'], answer: 1, why: 'Before reading anything the NFA can already have moved along ε-arrows.' },
      { q: 'In which order are the two steps of one DFA move done?', options: ['ε-closure, then the symbol', 'The symbol, then the ε-closure of what it reaches', 'Either', 'Only the symbol'], answer: 1, why: 'Every subset made is already ε-closed, so a move reads the symbol and then closes the result.' },
      { q: 'Does the DFA built from an ε-NFA have ε-moves?', options: ['Yes, the same ones', 'No: they are absorbed into the subsets', 'Only on the start state', 'Only in ε-cycles'], answer: 1, why: 'Each subset already contains everything reachable by ε, so no ε-moves are needed.' },
      { q: 'An ε-NFA accepts ε exactly when…', options: ['its start state accepts', 'the ε-closure of its start state holds an accepting state', 'it has an ε-loop', 'never'], answer: 1, why: 'That closure is the DFA\'s start state, and ε is accepted when the start state accepts.' },
    ],
  });
})();
