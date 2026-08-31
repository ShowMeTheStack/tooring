// Decidable problems: deciders that take a description ⟨…⟩ and always stop. Each scene draws the decider as a
// machine box with its program, lights the line it is running, and draws inside it the object it was handed
// (a DFA, two DFAs and their product, a grammar and its CYK table) being worked on, with the answer lamps on
// the right. The point every scene makes: the work is bounded, so the machine always halts.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'decidable', part: 'computability', order: 10, title: 'Decidable problems', blurb: 'Questions about automata and grammars that a machine can always answer: it reads the description, does a bounded amount of work and halts with yes or no.' });

  // ---------- shared helpers ----------
  const set = (xs) => (xs.length ? '{' + xs.join(', ') + '}' : '∅');
  const show = (w) => (w === '' ? 'ε' : w);
  /** A finite automaton in diagram form as the deciders' DFA object (a missing move is a move to a dead state) */
  const dfaOf = (m) => {
    const delta = {};
    for (const q of m.states) delta[q] = {};
    for (const mv of T.Machine.moves(m)) delta[mv.from][mv.sym] = mv.to;
    return { states: m.states.slice(), alphabet: T.Machine.alphabet(m), start: m.start, accept: m.accept.slice(), delta };
  };
  const dfaCheck = (label, max) => (v) => {
    let m;
    try { m = T.Machine.parse(v); } catch (e) { return label + ': ' + e.message; }
    if (m.kind === 'tm' || m.kind === 'pda') return label + ': a DFA, with rules like p -a-> q';
    if (!m.start) return label + ': say which state is the start, e.g. start p';
    if (!T.Machine.isDeterministic(m)) return label + ': a DFA has at most one move per state and symbol and no ε moves';
    if (m.states.length > max) return label + ': at most ' + max + ' states, so the picture stays readable';
    if (!T.Machine.alphabet(m).length) return label + ': give the machine at least one move';
    return null;
  };
  const deltaSection = (D, id, title) => ({ id: id || 'delta', kind: 'table', title: title || 'δ (— is the dead state)', corner: 'δ', colHead: D.alphabet, rowHead: D.states.map((q) => (q === D.start ? '→ ' : '') + q + (D.accept.includes(q) ? ' *' : '')), rows: D.states.map((q) => D.alphabet.map((a) => (D.delta[q][a] != null ? D.delta[q][a] : '—'))) });
  const progSection = (lines) => ({ id: 'prog', kind: 'math', title: 'The decider', text: lines.join('\n') });
  /** Lay a machine out once and measure it, so a scene can reserve room for it inside a box */
  const measureGraph = (m, opts) => {
    const pos = K.graph.layout(m, opts && opts.layout).pos;
    const g = K.graph.draw(m, Object.assign({ pos }, opts || {}));
    const b = T.stageBounds(g.items, { margin: 0, minW: 1, minH: 1 });
    return { pos, box: b };
  };
  /** A graph drawn so its picture (start arrow included) starts at (x, y) */
  const placeGraph = (m, meas, x, y, opts) => {
    const pos = {};
    for (const q of m.states) pos[q] = { x: meas.pos[q].x - meas.box.x + x, y: meas.pos[q].y - meas.box.y + y };
    return K.graph.draw(m, Object.assign({}, opts || {}, { pos }));
  };

  // =====================================================================================================
  // A_DFA: simulate D on w
  // =====================================================================================================
  const NO_AA = 'start p\naccept p q\np -b-> p\np -a-> q\nq -b-> p';
  const ODD_B = 'start e\naccept o\ne -a-> e\ne -b-> o\no -a-> o\no -b-> e';
  const LAST_TWO = 'start s\naccept ab\ns -a-> a\ns -b-> s\na -a-> a\na -b-> ab\nab -a-> a\nab -b-> s';
  const ADFA_LINES = ['1. Decode ⟨D, w⟩; reject if it is not a DFA and a string.', '2. Simulate D on w, one move per symbol.', '3. Accept if D ends in an accepting state, else reject.'];

  T.topic({
    id: 'dec-adfa', family: 'decidable', order: 10, title: 'A_DFA: does this DFA accept this string?',
    blurb: 'The decider is handed one string of bits, ⟨D, w⟩. It decodes the DFA, runs it on w and reports. A DFA makes exactly one move per symbol, so the run ends after |w| moves: the decider can never get stuck.',
    inputs: [
      { id: 'm', kind: 'machine', machine: 'dfa', label: 'DFA D', def: LAST_TWO, check: dfaCheck('DFA D', 6) },
      { id: 'w', kind: 'string', label: 'String w', def: 'abab', max: 10 },
    ],
    presets: [
      { label: 'Ends in ab: abab (accepted)', values: { m: LAST_TWO, w: 'abab' } },
      { label: 'Ends in ab: abba (rejected at the end)', values: { m: LAST_TWO, w: 'abba' } },
      { label: 'No aa: baab falls into the dead state', values: { m: NO_AA, w: 'baab' } },
      { label: 'Odd number of b’s: the empty string', values: { m: ODD_B, w: '' } },
      { label: 'Odd number of b’s: babb', values: { m: ODD_B, w: 'babb' } },
    ],
    check: (inp) => { const m = T.Machine.parse(inp.m); const al = T.Machine.alphabet(m); const bad = [...inp.w].find((c) => !al.includes(c)); return bad !== undefined ? 'String w: "' + bad + '" is not in D’s alphabet {' + al.join(', ') + '}' : null; },
    counters: [{ id: 'moves', label: 'moves made' }, { id: 'bound', label: 'most moves possible (|w|)' }],
    run(inp) {
      const m = T.Machine.parse(inp.m), D = dfaOf(m), w = [...inp.w], n = w.length;
      const meas = measureGraph(m, { prefix: 'D' });
      const CW = 44, strW = Math.max(1, n) * CW;
      // the machine on the left, its input string on the right
      const room = { w: meas.box.w + 50 + strW, h: Math.max(meas.box.h + 10, 120) };
      const enc = T.enc.encodeDFA(D);
      const wcode = w.map((a) => '0'.repeat(D.alphabet.indexOf(a) + 1)).join('1');
      const clip = (s, k) => (s.length > k ? s.slice(0, k) + '…' : s || 'ε');
      const F = new T.Frames(['moves', 'bound']);
      F.set('bound', n);
      const lineOf = (st) => ({ input: -1, decode: 0, run: 1, end: 2 }[st]);
      const scene = (st) => {
        const ln = lineOf(st.stage);
        const done = [0, 1, 2].filter((i) => i < ln);
        const verdict = st.stage === 'end' ? (st.accept ? 'accept' : 'reject') : null;
        const mb = K.mbox.draw({ prefix: 'dec', x: 0, y: 130, title: 'Decider for A_DFA', tag: 'decider', lines: ADFA_LINES, hot: ln >= 0 ? [ln] : [], done, room, outs: K.mbox.answers(verdict), cls: 'r0' });
        const items = mb.items.slice();
        // the input: two pieces of one bit string, falling into the top of the box
        const cdW = Math.max(150, Geo.textWidth(clip(enc.code, 18), 14, { mono: true }) + 24), cwW = Math.max(90, Geo.textWidth(clip(wcode, 12), 14, { mono: true }) + 24);
        const cx0 = mb.box.x + mb.box.w / 2 - (cdW + cwW + 34) / 2;
        const inCls = st.stage === 'input' ? 'hot' : 'read';
        items.push({ key: 'code:D', kind: 'cell', x: cx0, y: 30, w: cdW, h: 40, text: clip(enc.code, 18), sub: '⟨D⟩: ' + enc.code.length + ' bits', cls: 'mono ' + inCls });
        items.push({ key: 'code:sep', kind: 'text', x: cx0 + cdW + 17, y: 56, text: '111', anchor: 'middle', cls: 'mono' });
        items.push({ key: 'code:w', kind: 'cell', x: cx0 + cdW + 34, y: 30, w: cwW, h: 40, text: clip(wcode, 12), sub: '⟨w⟩: ' + (n ? n + ' symbol' + (n > 1 ? 's' : '') : 'empty'), cls: 'mono ' + inCls });
        items.push(K.mbox.wire('code:in', { x: mb.box.x + mb.box.w / 2, y: 92 }, { x: mb.box.x + mb.box.w / 2, y: 128 }, { cls: st.stage === 'input' ? 'hot' : '' }));
        if (st.stage === 'input') return items;
        const gx = mb.room.x, gy = mb.room.y + Math.max(0, (mb.room.h - meas.box.h) / 2);
        const g = placeGraph(m, meas, gx, gy, { prefix: 'D', active: st.q != null && st.stage !== 'end' ? [st.q] : [], taken: st.taken ? [st.taken] : [], good: st.stage === 'end' && st.accept ? [st.q] : [], bad: st.stage === 'end' && !st.accept && st.q != null ? [st.q] : [], enter: 'fade' });
        items.push(...g.items);
        const sy = mb.room.y + mb.room.h / 2 - 40;
        const s = K.string.draw({ prefix: 'w', text: w, pos: st.stage === 'decode' ? 0 : st.pos, x: mb.room.x + meas.box.w + 50, y: sy, cw: CW, headText: st.dead ? 'stuck' : st.pos >= n ? 'end' : 'next', headCls: st.dead ? 'bad' : 'read', cls: (i) => (st.dead && i === st.pos ? 'bad' : '') });
        items.push(...s.items);
        return items;
      };
      const row = (q) => D.states.indexOf(q), col = (a) => D.alphabet.indexOf(a);
      F.add({ items: scene({ stage: 'input' }), say: 'The decider is handed a single string of bits: ⟨D⟩, the DFA written in 0s and 1s (' + enc.code.length + ' bits), then 111, then ⟨w⟩, the input ' + show(w.join('')) + '.' });
      F.add({ items: scene({ stage: 'decode', q: D.start }), say: 'Line 1: decode it. D has states ' + set(D.states) + ', starts in ' + D.start + ' and accepts in ' + set(D.accept) + '; w is ' + show(w.join('')) + '. A garbled string that encodes no DFA would be rejected right here.', hl: { prog: [0] } });
      let q = D.start, i = 0, dead = false;
      for (; i < n; i++) {
        const nx = D.delta[q][w[i]];
        if (F.last()) F.last().meta = Object.assign({}, F.last().meta, { nextState: nx == null ? null : nx, sym: w[i] });
        F.count('moves');
        if (nx == null) {
          dead = true;
          F.add({ items: scene({ stage: 'run', q, pos: i, dead: true }), say: 'Line 2: in ' + q + ' reading ' + w[i] + ' there is no move: D falls into its dead state and can never accept, so the rest of w need not be read.', hl: { prog: [1], delta: [row(q) + ',' + col(w[i])] } });
          break;
        }
        F.add({ items: scene({ stage: 'run', q: nx, pos: i + 1, taken: q + '>' + nx }), say: 'Line 2: in ' + q + ' reading ' + w[i] + ', D moves to ' + nx + '. That is move ' + (i + 1) + ' of at most ' + n + '.', hl: { prog: [1], delta: [row(q) + ',' + col(w[i])] } });
        q = nx;
      }
      const acc = !dead && D.accept.includes(q);
      if (n === 0) F.list[1].say += ' w is empty, so there is nothing to simulate: zero moves.';
      F.list[F.length - 1].meta = Object.assign({}, F.list[F.length - 1].meta, { verdict: acc ? 'accept' : 'reject' });
      F.add({ items: scene({ stage: 'end', q: dead ? null : q, pos: dead ? i : n, accept: acc, dead }), say: 'Line 3: ' + (dead ? 'the run died, so the decider rejects.' : q + (acc ? ' is accepting, so the decider accepts: ' : ' is not accepting, so the decider rejects: ') + 'D ' + (acc ? 'accepts ' : 'does not accept ') + show(w.join('')) + '.') + ' It halted after ' + F.counts.moves + ' simulated move' + (F.counts.moves === 1 ? '' : 's') + ', as it always must.', hl: { prog: [2] }, mark: acc ? 'accepted' : 'rejected', meta: { verdict: acc ? 'accept' : 'reject' } });
      return { frames: F.list, def: { sections: [
        progSection(ADFA_LINES),
        { id: 'tuple', kind: 'math', title: 'D, decoded', text: 'Q = ' + set(D.states) + '\nΣ = ' + set(D.alphabet) + '\nstart ' + D.start + ', accept ' + set(D.accept) + '\nw = ' + show(w.join('')) },
        deltaSection(D),
        { id: 'why', kind: 'text', title: 'Why it always halts', text: 'Each simulated move reads one symbol of w, and w is finite. So the loop in line 2 runs at most |w| times.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.nextState, once: true, pick: 'item', ask: (fr, i) => 'D is about to read ' + fr[i].meta.sym + '. Click the state it will be in next.', answer: (fr, i) => 'D:s:' + fr[i].meta.nextState, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'item', ask: 'The run is over. Click the lamp the decider will light.', answer: (fr) => 'dec:o:' + fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why does the decider for A_DFA always halt?', options: ['DFAs have few states', 'A DFA makes one move per input symbol, so the simulation takes |w| moves', 'It gives up after a fixed time', 'It only accepts short strings'], answer: 1, why: 'The loop reads one symbol per move. After |w| moves the input is used up and the decider looks at the state it is in.' },
      { q: 'What is the input to the decider?', options: ['The DFA D only', 'The string w only', 'One string ⟨D, w⟩ that encodes both', 'An infinite list of strings'], answer: 2, why: 'A decider is a machine that reads a string. The DFA and the input are both written into that one string.' },
      { q: 'The decider is handed a string that encodes no DFA at all. What should it do?', options: ['Loop forever', 'Reject', 'Accept', 'Ask for another string'], answer: 1, why: 'A_DFA is a set of strings; a string that is not a proper encoding is not in it, so the decider rejects it in its first step.' },
      { q: 'D falls into its dead state after two symbols of a ten-symbol w. What can the decider conclude?', options: ['Nothing until all ten symbols are read', 'D rejects w: no path out of a dead state reaches acceptance', 'D accepts w', 'D loops'], answer: 1, why: 'A dead state is non-accepting and every move from it stays there, so the answer is already fixed.' },
      { q: 'Does the same idea give a decider for "does NFA N accept w"?', options: ['No, NFAs can guess forever', 'Yes: convert N to a DFA first, or track the set of states N could be in', 'Only if N has no ε-moves', 'Only for short w'], answer: 1, why: 'The set of possible states after each symbol is finite to track, so the simulation still ends after |w| steps.' },
    ],
  });

  // =====================================================================================================
  // E_DFA: paint the reachable states
  // =====================================================================================================
  const EDFA_LINES = ['1. Mark the start state.', '2. Mark every state an arrow leads to from a marked state.', '3. Repeat 2 until nothing new gets marked.', '4. No accepting state marked: accept. Otherwise reject.'];
  const ISLAND = 'start a\naccept d\na -0-> b\na -1-> a\nb -0-> a\nb -1-> b\nc -0-> d\nc -1-> c\nd -0,1-> d';
  const REACH = 'start a\naccept d\na -0-> b\na -1-> a\nb -0-> c\nb -1-> a\nc -0-> c\nc -1-> d\nd -0,1-> d';
  const NOACC = 'start x\nx -a-> y\ny -a,b-> x\nx -b-> x';
  const STARTACC = 'start s\naccept s\ns -a-> t\nt -a,b-> t';
  const BACKDOOR = 'start a\naccept f\na -x-> b\nb -x-> a\nc -x-> f\nf -x-> c';

  T.topic({
    id: 'dec-edfa', family: 'decidable', order: 20, title: 'E_DFA: is the language empty?',
    blurb: 'L(D) is empty exactly when no accepting state can be reached from the start. The decider spreads marks along the arrows from the start state until they stop spreading, then looks at the accepting states.',
    inputs: [{ id: 'm', kind: 'machine', machine: 'dfa', label: 'DFA D', def: REACH, check: dfaCheck('DFA D', 7) }],
    presets: [
      { label: 'Not empty: the marks reach d', values: { m: REACH } },
      { label: 'Empty: the accepting state is on an island', values: { m: ISLAND } },
      { label: 'Empty: no accepting state at all', values: { m: NOACC } },
      { label: 'The start state accepts: ε is in L(D)', values: { m: STARTACC } },
      { label: 'Empty: arrows into f, but only from unreachable states', values: { m: BACKDOOR } },
    ],
    counters: [{ id: 'marked', label: 'states marked' }, { id: 'looked', label: 'arrows followed' }],
    run(inp) {
      const m = T.Machine.parse(inp.m), D = dfaOf(m);
      const meas = measureGraph(m, { prefix: 'D' });
      const room = { w: Math.max(meas.box.w + 20, 320), h: meas.box.h + 100 };
      const F = new T.Frames(['marked', 'looked']);
      const marked = [], parent = {};
      const scene = (st) => {
        const verdict = st.end ? (st.empty ? 'accept' : 'reject') : null;
        const mb = K.mbox.draw({ prefix: 'dec', x: 0, y: 0, title: 'Decider for E_DFA', tag: 'decider', lines: EDFA_LINES, hot: [st.line], done: [0, 1, 2, 3].filter((i) => i < st.line), room, outs: K.mbox.answers(verdict, { acceptText: 'accept: L(D) = ∅', rejectText: 'reject: L(D) ≠ ∅' }), cls: 'r0' });
        const items = mb.items.slice();
        const gx = mb.room.x + (mb.room.w - meas.box.w) / 2, gy = mb.room.y + 4;
        const mk = new Set(st.marked);
        const cls = {};
        for (const q of D.states) cls[q] = mk.has(q) ? 'active' : '';
        if (st.fresh) cls[st.fresh] = 'hot';
        const good = st.end && !st.empty ? st.path.slice(-1) : [];
        const bad = st.end && st.empty ? D.accept : [];
        const taken = st.end && !st.empty ? st.path.slice(1).map((q, k) => st.path[k] + '>' + q) : st.taken ? [st.taken] : [];
        const unreached = st.end ? D.states.filter((q) => !mk.has(q)) : [];
        const g = placeGraph(m, meas, gx, gy, { prefix: 'D', cls, good, bad, taken, dim: unreached.filter((q) => !D.accept.includes(q)), edgeCls: Object.fromEntries((st.end && !st.empty ? taken : []).map((k) => [k, 'good'])) });
        items.push(...g.items);
        // the set of marked states, written out under the machine
        const ry = gy + meas.box.h + 30;
        const lab = 'marked';
        items.push({ key: 'mk:lab', kind: 'text', x: mb.room.x + 4, y: ry + 22, text: lab, cls: 'title' });
        st.marked.forEach((q, k) => items.push({ key: 'mk:' + q, kind: 'cell', x: mb.room.x + 80 + k * 50, y: ry, w: 44, h: 34, text: q, cls: 'mono ' + (q === st.fresh ? 'hot' : D.accept.includes(q) ? 'good' : 'act'), enter: 'from', src: 'D:s:' + q }));
        if (st.end && !st.empty) items.push({ key: 'mk:wit', kind: 'text', x: mb.room.x + 4, y: ry + 70, text: 'a string in L(D): ' + show(st.word), cls: 'good' });
        if (st.end && st.empty) items.push({ key: 'mk:wit', kind: 'text', x: mb.room.x + 4, y: ry + 70, text: D.accept.length ? 'never marked: ' + D.accept.join(', ') : 'D has no accepting state', cls: 'bad' });
        return items;
      };
      const row = (q) => D.states.indexOf(q);
      marked.push(D.start); F.count('marked');
      F.add({ items: scene({ line: 0, marked: marked.slice(), fresh: D.start }), say: 'Line 1: mark the start state ' + D.start + '. The marks will show every state some input can lead to.', hl: { prog: [0] } });
      let k = 0;
      for (; k < marked.length; k++) {
        const p = marked[k];
        for (const a of D.alphabet) {
          const q = D.delta[p][a];
          if (q == null) continue;
          F.count('looked');
          if (marked.includes(q)) continue;
          F.last().meta = Object.assign({}, F.last().meta, { next: q });
          marked.push(q); parent[q] = { p, a }; F.count('marked');
          F.add({ items: scene({ line: 1, marked: marked.slice(), fresh: q, taken: p + '>' + q }), say: 'Line 2: ' + p + ' is marked and reads ' + a + ' into ' + q + ', so mark ' + q + (D.accept.includes(q) ? ', an accepting state.' : '.'), hl: { prog: [1], delta: [row(p) + ',' + D.alphabet.indexOf(a)] } });
        }
      }
      F.add({ items: scene({ line: 2, marked: marked.slice() }), say: 'Line 3: every arrow out of a marked state now leads to a marked state, so nothing new can be marked. At most ' + D.states.length + ' states can ever be marked, so this always ends.', hl: { prog: [2] } });
      const hit = D.accept.filter((q) => marked.includes(q));
      const empty = !hit.length;
      let path = [], word = '';
      if (!empty) { let q = hit[0]; path = [q]; while (parent[q]) { word = parent[q].a + word; q = parent[q].p; path.unshift(q); } }
      F.last().meta = Object.assign({}, F.last().meta, { verdict: empty ? 'accept' : 'reject' });
      const why = empty ? (D.accept.length ? 'No accepting state (' + D.accept.join(', ') + ') was marked: no input can ever reach one, so L(D) = ∅ and the decider accepts.' : 'D has no accepting state at all, so it accepts nothing: L(D) = ∅ and the decider accepts.') : (word === '' ? 'The start state ' + D.start + ' is itself accepting, so D accepts the empty string ε: L(D) ≠ ∅ and the decider rejects.' : 'The accepting state ' + hit[0] + ' is marked: following the marks back, the string ' + word + ' leads there. L(D) ≠ ∅, so the decider rejects.');
      F.add({ items: scene({ line: 3, marked: marked.slice(), end: true, empty, path, word }), say: 'Line 4: ' + why, hl: { prog: [3] }, mark: empty ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [progSection(EDFA_LINES), { id: 'tuple', kind: 'math', title: 'D', text: 'Q = ' + set(D.states) + '\nΣ = ' + set(D.alphabet) + '\nstart ' + D.start + ', accept ' + set(D.accept) }, deltaSection(D), { id: 'idea', kind: 'text', title: 'The idea', text: 'L(D) ≠ ∅ exactly when some path of arrows leads from the start state to an accepting state. Marking is a search for such a path; it never marks a state twice, so it stops.' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.next, once: true, pick: 'item', ask: 'Click the next state the marks will spread to.', answer: (fr, i) => 'D:s:' + fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.verdict, once: true, pick: 'item', ask: 'The marks have stopped spreading. Click the lamp the decider lights.', answer: (fr, i) => 'dec:o:' + fr[i].meta.verdict, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'The decider for E_DFA accepts ⟨D⟩. What does that say about D?', options: ['D accepts every string', 'D accepts no string at all', 'D has no accepting states', 'D is minimal'], answer: 1, why: 'E_DFA is the set of DFAs whose language is empty, so accepting means L(D) = ∅. (No accepting states is one way, but not the only one.)' },
      { q: 'An accepting state has arrows coming into it, yet L(D) = ∅. How?', options: ['Impossible', 'Those arrows come only from states the start cannot reach', 'The arrows are labelled ε', 'The state has a self-loop'], answer: 1, why: 'What matters is reachability from the start, not whether arrows point at the state.' },
      { q: 'Why does the marking always stop?', options: ['It stops after |w| steps', 'Each round marks a new state or ends, and there are finitely many states', 'It uses a step limit', 'DFAs have no cycles'], answer: 1, why: 'A state is marked at most once, so there are at most |Q| rounds that change anything.' },
      { q: 'Why not decide E_DFA by trying strings one by one until D accepts one?', options: ['It would be too slow but correct', 'If L(D) is empty the search never ends, so it is not a decider', 'DFAs cannot run on long strings', 'It would accept the wrong machines'], answer: 1, why: 'Trying strings finds a member when there is one, but never halts with "empty". (Strings shorter than |Q| would be enough, which is another bounded method.)' },
      { q: 'The start state is accepting. What must the decider answer?', options: ['Accept: L(D) is empty', 'Reject: ε is in L(D)', 'It depends on the other states', 'It loops'], answer: 1, why: 'The start state is marked first; if it accepts, D accepts the empty string, so the language is not empty.' },
    ],
  });

  // =====================================================================================================
  // EQ_DFA: the symmetric difference must be empty
  // =====================================================================================================
  const EVEN_A2 = 'start E\naccept E\nE -a-> O\nE -b-> E\nO -a-> E\nO -b-> O';
  const EVEN_A4 = 'start e0\naccept e0 e1\ne0 -a-> o0\ne0 -b-> e1\ne1 -a-> o1\ne1 -b-> e0\no0 -a-> e0\no0 -b-> o1\no1 -a-> e1\no1 -b-> o0';
  const ENDS_A = 'start n\naccept y\nn -a-> y\nn -b-> n\ny -a-> y\ny -b-> n';
  const HAS_A = 'start n\naccept y\nn -a-> y\nn -b-> n\ny -a,b-> y';
  const AB_STAR = 'start p\naccept p\np -a-> q\nq -b-> p';
  const AB_PLUS = 'start p\naccept r\np -a-> q\nq -b-> r\nr -a-> q';
  const EQ_LINES = ['1. Build C with L(C) = (L(D₁) − L(D₂)) ∪ (L(D₂) − L(D₁)).', '2. Run the E_DFA decider on ⟨C⟩.', '3. If it accepts, accept (equal); if it rejects, reject.'];

  T.topic({
    id: 'dec-eqdfa', family: 'decidable', order: 30, title: 'EQ_DFA: do two DFAs accept the same language?',
    blurb: 'Two languages are equal exactly when no string is in one but not the other. The decider builds a DFA C for that symmetric difference by running D₁ and D₂ side by side, then asks whether L(C) is empty.',
    inputs: [
      { id: 'a', kind: 'machine', machine: 'dfa', label: 'DFA D₁', def: EVEN_A2, check: dfaCheck('DFA D₁', 4) },
      { id: 'b', kind: 'machine', machine: 'dfa', label: 'DFA D₂', def: EVEN_A4, check: dfaCheck('DFA D₂', 4) },
    ],
    presets: [
      { label: 'Equal: even number of a’s, 2 states and 4 states', values: { a: EVEN_A2, b: EVEN_A4 } },
      { label: 'Different: ends in a, contains an a', values: { a: ENDS_A, b: HAS_A } },
      { label: 'Different only on ε: (ab)* and (ab)⁺', values: { a: AB_STAR, b: AB_PLUS } },
      { label: 'Dead states: (ab)⁺ against itself', values: { a: AB_PLUS, b: AB_PLUS } },
    ],
    counters: [{ id: 'pairs', label: 'pair states built' }, { id: 'diff', label: 'in the difference' }],
    run(inp) {
      const m1 = T.Machine.parse(inp.a), m2 = T.Machine.parse(inp.b);
      const D1 = dfaOf(m1), D2 = dfaOf(m2);
      const alpha = [...new Set([...D1.alphabet, ...D2.alphabet])].sort();
      // the product, breadth-first; ∅ stands for a dead state
      const nm = (p) => (p == null ? '∅' : p);
      const key = (p, q) => nm(p) + '|' + nm(q);
      const acc1 = (p) => p != null && D1.accept.includes(p), acc2 = (q) => q != null && D2.accept.includes(q);
      const order = [[D1.start, D2.start]], seen = new Map([[key(D1.start, D2.start), { from: null }]]), trans = [];
      for (let i = 0; i < order.length; i++) {
        const [p, q] = order[i];
        for (const a of alpha) {
          const np = p == null ? null : (D1.delta[p][a] ?? null), nq = q == null ? null : (D2.delta[q][a] ?? null);
          const k2 = key(np, nq);
          if (np == null && nq == null) continue; // both dead: a pair that can never accept, left out
          trans.push({ from: key(p, q), to: k2, a });
          if (!seen.has(k2)) { seen.set(k2, { from: key(p, q), a }); order.push([np, nq]); }
        }
      }
      const keys = order.map(([p, q]) => key(p, q));
      const inDiff = (k) => { const [p, q] = order[keys.indexOf(k)]; return acc1(p) !== acc2(q); };
      const C = { kind: 'dfa', states: keys, start: keys[0], accept: keys.filter(inDiff), trans: [] };
      const lab = new Map();
      for (const t of trans) { const k = t.from + '>' + t.to; if (!lab.has(k)) lab.set(k, []); lab.get(k).push(t.a); }
      for (const [k, l] of lab) { const [f, t] = k.split('>'); C.trans.push({ from: f, to: t, label: l.join(', ') }); }
      const labelOf = (k) => k.replace('|', ', ');
      const measC = measureGraph(C, { prefix: 'C', labelOf, layout: { labelOf } });
      const meas1 = measureGraph(m1, { prefix: 'A' }), meas2 = measureGraph(m2, { prefix: 'B' });
      // D₁ above D₂ on the left, the product C growing on the right
      const leftW = Math.max(meas1.box.w, meas2.box.w, 60), leftH = meas1.box.h + meas2.box.h + 70;
      const room = { w: leftW + 60 + Math.max(measC.box.w, 270), h: Math.max(leftH, measC.box.h + 40) + 40 };
      const F = new T.Frames(['pairs', 'diff']);
      const scene = (st) => {
        const verdict = st.end ? (st.equal ? 'accept' : 'reject') : null;
        const mb = K.mbox.draw({ prefix: 'dec', x: 0, y: 0, title: 'Decider for EQ_DFA', tag: 'decider', lines: EQ_LINES, hot: [st.line], done: [0, 1, 2].filter((i) => i < st.line), room, outs: K.mbox.answers(verdict, { acceptText: 'accept: equal', rejectText: 'reject: different' }), cls: 'r0' });
        const items = mb.items.slice();
        const R = mb.room;
        const x1 = R.x;
        items.push({ key: 'lab:1', kind: 'text', x: x1, y: R.y + 14, text: 'D₁', cls: 'title' });
        items.push({ key: 'lab:2', kind: 'text', x: x1, y: R.y + meas1.box.h + 54, text: 'D₂', cls: 'title' });
        const cur = st.cur ? order[keys.indexOf(st.cur)] : null;
        items.push(...placeGraph(m1, meas1, x1 + (leftW - meas1.box.w) / 2, R.y + 24, { prefix: 'A', active: cur && cur[0] != null ? [cur[0]] : [], taken: st.via && st.via[0] ? [st.via[0]] : [] }).items);
        items.push(...placeGraph(m2, meas2, x1 + (leftW - meas2.box.w) / 2, R.y + meas1.box.h + 64, { prefix: 'B', active: cur && cur[1] != null ? [cur[1]] : [], taken: st.via && st.via[1] ? [st.via[1]] : [] }).items);
        const cy = R.y + 14, cx = R.x + leftW + 60;
        items.push({ key: 'lab:C', kind: 'text', x: cx, y: cy, text: 'C: pairs (red: only one accepts)', cls: 'title' });
        if (st.built.length) {
          const sub = { kind: 'dfa', states: st.built, start: C.start, accept: C.accept.filter((k) => st.built.includes(k)), trans: C.trans.filter((t) => st.built.includes(t.from) && st.built.includes(t.to) && st.edges.has(t.from + '>' + t.to)) };
          const pos = {};
          for (const k of st.built) pos[k] = { x: measC.pos[k].x - measC.box.x + cx, y: measC.pos[k].y - measC.box.y + cy + 20 };
          const cls = {};
          for (const k of st.built) cls[k] = inDiff(k) ? 'bad' : '';
          if (st.fresh) cls[st.fresh] = (cls[st.fresh] ? cls[st.fresh] + ' ' : '') + 'hot';
          const path = st.path || [];
          const g = K.graph.draw(sub, { prefix: 'C', pos, labelOf, cls, active: st.cur && !st.end ? [st.cur] : [], taken: path.slice(1).map((k, i) => path[i] + '>' + k), from: st.fresh && st.cur ? { [st.fresh]: 'C:s:' + st.cur } : null });
          items.push(...g.items);
        }
        if (st.end) items.push({ key: 'res', kind: 'text', x: R.x + 4, y: R.y + R.h - 8, text: st.equal ? 'no red pair is reachable: L(C) = ∅' : 'witness ' + show(st.word) + ': ' + st.whoAcc, cls: st.equal ? 'good' : 'bad' });
        return items;
      };
      const built = [], edges = new Set();
      F.add({ items: scene({ line: 0, built: [], edges }), say: 'Line 1: build C. A state of C is a pair (p, q): where D₁ is and where D₂ is after the same input. C accepts when exactly one of them accepts.', hl: { prog: [0] } });
      built.push(keys[0]); F.count('pairs'); if (inDiff(keys[0])) F.count('diff');
      F.add({ items: scene({ line: 0, built: built.slice(), edges, cur: keys[0], fresh: keys[0] }), say: 'Both machines start: the pair (' + labelOf(keys[0]) + ').' + (inDiff(keys[0]) ? ' Already only one of them accepts, so ε is in exactly one language: this pair is red.' : ' Either both accept or neither does, so ε causes no disagreement.'), hl: { prog: [0] } });
      for (let i = 1; i < keys.length; i++) {
        const k = keys[i], s = seen.get(k);
        const [p0, q0] = order[keys.indexOf(s.from)], [p1, q1] = order[i];
        F.last().meta = Object.assign({}, F.last().meta, { nextDiff: inDiff(k) ? 'Yes' : 'No', nextName: labelOf(k) });
        built.push(k); edges.add(s.from + '>' + k); F.count('pairs'); if (inDiff(k)) F.count('diff');
        for (const t of C.trans) if (built.includes(t.from) && built.includes(t.to)) edges.add(t.from + '>' + t.to);
        const half = (p, D) => (p == null ? 'is dead' : D.accept.includes(p) ? 'accepts' : 'does not accept');
        F.add({ items: scene({ line: 0, built: built.slice(), edges: new Set(edges), cur: s.from, fresh: k, via: [p0 != null && p1 != null ? p0 + '>' + p1 : null, q0 != null && q1 != null ? q0 + '>' + q1 : null] }), say: 'From (' + labelOf(s.from) + ') on ' + s.a + ': D₁ goes to ' + nm(p1) + ', D₂ to ' + nm(q1) + '. D₁ ' + half(p1, D1) + ' there and D₂ ' + half(q1, D2) + (inDiff(k) ? ': they disagree, so (' + labelOf(k) + ') is red.' : ': they agree.'), hl: { prog: [0] } });
      }
      for (const t of C.trans) edges.add(t.from + '>' + t.to);
      F.add({ items: scene({ line: 1, built: built.slice(), edges: new Set(edges) }), say: 'C is complete: ' + keys.length + ' pair states, at most |Q₁| × |Q₂| plus dead ones, so building it always ends. Line 2: hand ⟨C⟩ to the E_DFA decider: is a red pair reachable?', hl: { prog: [1] } });
      const red = keys.find(inDiff);
      const equal = !red;
      let path = [], word = '', whoAcc = '';
      if (!equal) {
        for (let k = red; k; k = seen.get(k).from) { path.unshift(k); if (seen.get(k).a) word = seen.get(k).a + word; }
        const [p, q] = order[keys.indexOf(red)];
        whoAcc = acc1(p) ? 'D₁ accepts, D₂ does not' : acc2(q) ? 'D₂ accepts, D₁ does not' : '';
      }
      F.last().meta = Object.assign({}, F.last().meta, { verdict: equal ? 'accept' : 'reject' });
      F.add({ items: scene({ line: 2, built: built.slice(), edges: new Set(edges), end: true, equal, path, word, whoAcc }), say: equal ? 'Line 3: every reachable pair agrees, so L(C) = ∅: no string separates them. The decider accepts: L(D₁) = L(D₂), even though the machines look different.' : 'Line 3: the red pair (' + labelOf(red) + ') is reachable by ' + show(word) + ', so L(C) ≠ ∅: on ' + show(word) + ' ' + whoAcc + '. The decider rejects.', hl: { prog: [2] }, mark: equal ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [progSection(EQ_LINES), deltaSection(D1, 'd1', 'D₁'), deltaSection(D2, 'd2', 'D₂'), { id: 'c', kind: 'math', title: 'The product C', text: 'states: pairs (p, q)\nδ_C((p, q), a) = (δ₁(p, a), δ₂(q, a))\naccept (p, q) when exactly one of p, q accepts' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.nextDiff, once: true, pick: 'option', options: ['Yes', 'No'], ask: (fr, i) => 'The next pair is (' + fr[i].meta.nextName + '). Will it be red: does exactly one machine accept there?', answer: (fr, i) => fr[i].meta.nextDiff, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.verdict, once: true, pick: 'item', ask: 'C is built. Click the lamp the decider will light.', answer: (fr, i) => 'dec:o:' + fr[i].meta.verdict, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why build the symmetric difference rather than test strings?', options: ['It is shorter to write', 'Testing strings can confirm a difference but never confirm equality; emptiness of C can be decided', 'DFAs cannot run on strings', 'The difference is always finite'], answer: 1, why: 'Equality means "no string separates them", an infinite claim. Turning it into "L(C) = ∅" makes it a finite reachability check.' },
      { q: 'A pair state (p, q) of C is accepting when…', options: ['both p and q accept', 'p or q accepts', 'exactly one of p, q accepts', 'neither accepts'], answer: 2, why: 'That is the symmetric difference: strings in one language and not the other.' },
      { q: 'How many states can C have at most?', options: ['|Q₁| + |Q₂|', '|Q₁| × |Q₂| (more with dead states)', '2^(|Q₁| + |Q₂|)', 'Infinitely many'], answer: 1, why: 'Each state is a pair; with dead states added, at most (|Q₁| + 1)(|Q₂| + 1).' },
      { q: 'Two DFAs differ only on the empty string. Where does C show it?', options: ['Nowhere: ε does not count', 'The start pair is already red', 'At the dead state', 'Only after reading a symbol'], answer: 1, why: 'The start pair is where both machines are after reading ε, so it is red exactly when one of them accepts ε.' },
      { q: 'Does the same method decide equality for context-free grammars?', options: ['Yes, with a product of PDAs', 'No: equality of CFGs is undecidable, and CFLs are not closed under complement and intersection', 'Yes, but slowly', 'Only for unambiguous grammars'], answer: 1, why: 'The construction needs complement and intersection. Context-free languages lack both closures, and the equivalence problem for grammars is in fact undecidable.' },
    ],
  });

  // =====================================================================================================
  // A_CFG: Chomsky normal form, then CYK
  // =====================================================================================================
  const BAL = 'S → a S b | S S | ε';
  const LEFT = 'S → S a | b';
  const UNIT = 'S → A | a S\nA → b A | b';
  const PAL = 'S → a S a | b S b | a | b';
  const ACFG_LINES = ['1. Convert G to Chomsky normal form.', '2. Fill the CYK table for w.', '3. Accept if the start variable is in the top cell.'];
  const gramCheck = (label, maxVars) => (v) => {
    let G;
    try { G = T.comp.parseCFG(v); } catch (e) { return label + ': write one rule per line, like S → a S b | ε'; }
    if (!G.rules.length) return label + ': at least one rule, like S → a S b | ε';
    if (G.variables.length > maxVars) return label + ': at most ' + maxVars + ' variables, so the picture stays readable';
    const long = G.terminals.find((t) => [...t].length > 1);
    if (long) return label + ': "' + long + '" is used but has no rules; give every variable its rules, and keep terminals to one symbol';
    if (G.rules.length > 10) return label + ': at most 10 alternatives in all';
    return null;
  };
  const groupRules = (list) => {
    const m = new Map();
    for (const r of list) { const [l, rhs] = r.split('→'); if (!m.has(l)) m.set(l, []); m.get(l).push(rhs.trim() === '' ? 'ε' : rhs.trim()); }
    return [...m].map(([l, rs]) => l + ' → ' + rs.join(' | '));
  };

  T.topic({
    id: 'dec-acfg', family: 'decidable', order: 40, title: 'A_CFG: does this grammar generate this string?',
    blurb: 'Trying derivations one after another might never stop. The decider first rewrites G in Chomsky normal form, where every derivation of a string of length n has exactly 2n − 1 steps, then fills the CYK table, which is finite.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar G', def: BAL, check: gramCheck('Grammar G', 4) },
      { id: 'w', kind: 'string', label: 'String w', def: 'aabb', max: 5 },
    ],
    presets: [
      { label: 'Balanced: aabb is generated', values: { g: BAL, w: 'aabb' } },
      { label: 'Balanced: abba is not', values: { g: BAL, w: 'abba' } },
      { label: 'The empty string, where CYK has no cells', values: { g: BAL, w: '' } },
      { label: 'Left recursion: baa', values: { g: LEFT, w: 'baa' } },
      { label: 'Unit rules: abb', values: { g: UNIT, w: 'abb' } },
      { label: 'Odd palindromes: abbba', values: { g: PAL, w: 'abbba' } },
    ],
    check: (inp) => { const G = T.comp.parseCFG(inp.g); const bad = [...inp.w].find((c) => !G.terminals.includes(c)); return bad !== undefined ? 'String w: "' + bad + '" is not a terminal of G' : null; },
    counters: [{ id: 'rules', label: 'rules in the grammar' }, { id: 'cells', label: 'CYK cells filled' }],
    run(inp) {
      const G = T.comp.parseCFG(inp.g), w = [...inp.w], n = w.length;
      const conv = T.comp.toCNF(G);
      // the new variables get short names: S₀ for the new start, X₁, X₂, … for the pieces of long rules
      const ren = new Map();
      let nx = 0;
      for (const v of conv.cnf.variables) {
        if (G.variables.includes(v)) ren.set(v, v);
        else if (v === conv.cnf.start) ren.set(v, G.start + '₀');
        else if (/^T./.test(v) && conv.cnf.rules.some((r) => r.lhs === v && r.rhs.length === 1 && !conv.cnf.variables.includes(r.rhs[0]))) ren.set(v, v);
        else ren.set(v, 'X' + '₁₂₃₄₅₆₇₈₉'[nx++ % 9]);
      }
      const rn = (x) => (ren.has(x) ? ren.get(x) : x);
      const C = { start: rn(conv.cnf.start), variables: conv.cnf.variables.map(rn), terminals: conv.cnf.terminals, rules: conv.cnf.rules.map((r) => ({ lhs: rn(r.lhs), rhs: r.rhs.map(rn) })) };
      const cyk = T.comp.cyk(C, w);
      const stages = conv.trace.map((s) => Object.assign({}, s, { rules: s.rules.map((r) => { const [l, rhs] = r.split('→'); return rn(l) + '→' + rhs.split(' ').map(rn).join(' '); }), say: s.say.replace(/[A-Za-z][A-Za-z0-9_']*/g, (t) => (ren.has(t) && ren.get(t) !== t ? ren.get(t) : t)) }));
      const stageName = { start: 'new start variable', epsilon: 'remove ε-rules', unit: 'remove unit rules', terminals: 'terminals get variables', binary: 'break long rules' };
      // the widest rule list decides the panel's width
      const allLists = [G.rules.map((r) => r.lhs + '→' + r.rhs.join(' '))].concat(stages.map((s) => s.rules)).map(groupRules);
      const ruleW = Math.max(200, ...allLists.flat().map((l) => Geo.textWidth(l, 14, { mono: true }) + 30));
      const ruleH = Math.max(...allLists.map((l) => l.length)) * 24 + 44;
      // the cells are as wide as the widest set they will hold
      const finalSets = cyk.trace.filter((s) => s.kind === 'cell').map((s) => set(s.vars));
      const CW = Math.max(64, ...finalSets.map((t) => Geo.textWidth(t, 13, { mono: true }) + 18)), CH = 44;
      const tabW = Math.max(1, n) * CW + 70, tabH = Math.max(1, n) * CH + 60;
      // rules above, the table below: a tall picture reads better on a narrow screen
      const room = { w: Math.max(ruleW, tabW), h: ruleH + 30 + tabH };
      const F = new T.Frames(['rules', 'cells']);
      const table = Array.from({ length: n }, () => Array(n).fill(null)); // table[len-1][i]
      const scene = (st) => {
        const verdict = st.end ? (st.yes ? 'accept' : 'reject') : null;
        const mb = K.mbox.draw({ prefix: 'dec', x: 0, y: 0, title: 'Decider for A_CFG', tag: 'decider', lines: ACFG_LINES, hot: [st.line], done: [0, 1, 2].filter((i) => i < st.line), room, outs: K.mbox.answers(verdict), cls: 'r0' });
        const items = mb.items.slice();
        const R = mb.room;
        // the rules, grouped by variable; lines that just changed are lit
        items.push({ key: 'rp', kind: 'region', x: R.x, y: R.y, w: R.w, h: ruleH, text: st.ruleTitle, cls: 'r5', rx: 10 });
        st.rules.forEach((l, k) => items.push({ key: 'rl:' + l.split(' → ')[0], kind: 'text', x: R.x + 14, y: R.y + 50 + k * 24, text: l, cls: 'mcode mono' + (st.fresh && st.fresh.includes(l) ? ' hot' : '') }));
        // the CYK triangle: row len k holds the substrings of length k
        const tx = R.x + (R.w - tabW) / 2 + 70, ty = R.y + ruleH + 30 + 50;
        const rows = table.map((row, l) => row.map((c, i) => (i + l < n ? (c === null ? '' : set(c)) : null)));
        if (n) {
          const tb = K.table.draw({ prefix: 'cyk', rows, skip: (l, i) => i + l >= n, rowHead: table.map((_, l) => 'len ' + (l + 1)), cw: CW, ch: CH, mono: true, size: 13, x: tx - 60, y: ty, hot: st.hot ? [st.hot] : [], cls: (l, i) => (st.src && st.src.some((s) => s[0] === l && s[1] === i) ? 'src-a' : st.end && l === n - 1 ? (st.yes ? 'good' : 'bad') : table[l][i] && !table[l][i].length ? 'empty' : ''), arrows: st.src ? st.src.map((s, k) => ({ from: s, to: st.hot, bend: k ? 26 : -26, cls: k ? 'b' : '' })) : [] });
          items.push(...tb.items);
          items.push(...K.string.draw({ prefix: 'w', text: w, x: tx, y: ty - 48, cw: CW, ch: 38, head: false, cls: (i) => (st.hot && i >= st.hot[1] && i <= st.hot[1] + st.hot[0] ? 'hot' : '') }).items);
        } else {
          items.push({ key: 'cyk:eps', kind: 'cell', x: tx - 40, y: ty, w: 200, h: 48, text: 'w = ε: no cells', cls: 'mono empty' });
        }
        return items;
      };
      const g0 = groupRules(G.rules.map((r) => r.lhs + '→' + r.rhs.join(' ')));
      F.set('rules', G.rules.length);
      F.add({ items: scene({ line: 0, rules: g0, ruleTitle: 'G as given' }), say: 'The decider gets ⟨G, w⟩ with w = ' + show(w.join('')) + '. Searching all derivations could run for ever (a rule like ' + (G.rules.find((r) => r.rhs[0] === r.lhs) ? r2s(G.rules.find((r) => r.rhs[0] === r.lhs)) : 'S → S S') + ' can grow a derivation without end), so first: line 1, Chomsky normal form.', hl: { prog: [0] } });
      let prev = g0;
      for (const s of stages) {
        const cur = groupRules(s.rules);
        F.set('rules', s.rules.length);
        F.add({ items: scene({ line: 0, rules: cur, fresh: cur.filter((l) => !prev.includes(l)), ruleTitle: 'CNF: ' + stageName[s.kind] }), say: 'Line 1, ' + stageName[s.kind] + ': ' + s.say, hl: { prog: [0] } });
        prev = cur;
      }
      if (n === 0) {
        const yes = cyk.accepted;
        F.last().meta = { verdict: yes ? 'accept' : 'reject' };
        F.add({ items: scene({ line: 2, rules: prev, ruleTitle: 'G in CNF', end: true, yes }), say: 'Line 2: w is the empty string, so the CYK table has no cells. In Chomsky normal form only the start rule ' + C.start + ' → ε can make ε, and ' + (yes ? 'it is there: the decider accepts.' : 'it is not there: the decider rejects.'), hl: { prog: [2] }, mark: yes ? 'accepted' : 'rejected' });
      } else {
        for (const s of cyk.trace) {
          if (s.kind !== 'cell') continue;
          const l = s.len - 1;
          table[l][s.i] = s.vars;
          F.count('cells');
          let src = null;
          if (l > 0 && s.from && s.from.length) { const k = s.from[0].split; src = [[k - 1, s.i], [l - k, s.i + k]]; }
          const sub = w.slice(s.i, s.i + s.len).join('');
          const say = l === 0 ? sub + ' at position ' + (s.i + 1) + ': ' + (s.vars.length ? 'the rules ' + s.vars.map((v) => v + ' → ' + sub).join(', ') + ' put ' + set(s.vars) + ' in its cell.' : 'no rule makes it alone, so the cell is ∅.') : sub + ': ' + (s.vars.length ? set(s.vars) + ', from ' + s.from.map((f) => f.rule + ' (split after ' + f.split + ')').join(', ') + '.' : 'no split and rule fit, so ∅.');
          if (l === n - 1 && F.last()) F.last().meta = Object.assign({}, F.last().meta, { top: true });
          F.add({ items: scene({ line: 1, rules: prev, ruleTitle: 'G in CNF', hot: [l, s.i], src }), say: 'Line 2: ' + say, hl: { prog: [1] }, meta: src ? { src: src.map((x) => 'cyk:' + x[0] + ',' + x[1]) } : {} });
        }
        const yes = cyk.accepted;
        F.last().meta = Object.assign({}, F.last().meta, { verdict: yes ? 'accept' : 'reject' });
        F.add({ items: scene({ line: 2, rules: prev, ruleTitle: 'G in CNF', end: true, yes }), say: 'Line 3: the top cell, for all of ' + w.join('') + ', holds ' + set(table[n - 1][0]) + '. ' + (yes ? C.start + ' is there, so G generates ' + w.join('') + ' and the decider accepts.' : C.start + ' is not there, so G does not generate ' + w.join('') + ' and the decider rejects.') + ' It filled ' + (n * (n + 1)) / 2 + ' cells: a fixed amount of work.', hl: { prog: [2] }, mark: yes ? 'accepted' : 'rejected' });
      }
      return { frames: F.list, def: { sections: [progSection(ACFG_LINES), { id: 'g', kind: 'grammar', title: 'G', rules: g0, nonterminals: G.variables }, { id: 'cnf', kind: 'grammar', title: 'G in Chomsky normal form', rules: prev, nonterminals: C.variables }, { id: 'why', kind: 'text', title: 'Why it always halts', text: 'In Chomsky normal form every rule either splits a variable in two or makes one terminal, so any derivation of a string of length n ≥ 1 takes exactly 2n − 1 steps. CYK checks all of them at once in n(n + 1)/2 cells.' }] } };
      function r2s(r) { return r.lhs + ' → ' + r.rhs.join(' '); }
    },
    predict: [
      { at: (f) => f.meta && f.meta.top, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Only the top cell is left. Will the start variable be in it?', answer: (fr) => (fr[fr.length - 1].mark === 'accepted' ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.src && i > 0 && fr[i + 1].meta.src.length === 2, once: true, pick: 'item', ask: 'The next cell to fill is built from two smaller cells. Click one of them (a cell for a shorter piece of this substring).', answer: (fr, i) => fr[i + 1].meta.src, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why not decide A_CFG by trying derivations until one produces w?', options: ['It is too slow', 'If w is not generated, the search may never end', 'Grammars have no derivations', 'It gives wrong answers'], answer: 1, why: 'A search that only stops on success is a recogniser, not a decider. Chomsky normal form bounds the derivations that need checking.' },
      { q: 'In Chomsky normal form, how many steps does a derivation of a string of length n ≥ 1 take?', options: ['n', '2n − 1', 'n²', 'It varies without bound'], answer: 1, why: 'n − 1 steps of the form A → B C build n variables, then n steps of the form A → a turn them into terminals.' },
      { q: 'How does the decider handle w = ε?', options: ['It fills an empty table and rejects', 'It checks whether the start rule S₀ → ε is in the CNF grammar', 'It loops', 'It refuses the input'], answer: 1, why: 'In Chomsky normal form only the new start variable may derive ε, by a rule of its own.' },
      { q: 'Every context-free language L is decidable. Why?', options: ['Because PDAs always halt', 'Fix a grammar G for L; the machine "run the A_CFG decider on ⟨G, w⟩" decides L', 'Because L is regular', 'It is not true'], answer: 1, why: 'A nondeterministic PDA may have branches that never halt, so simulating one is no decider. The A_CFG decider with G built in is.' },
      { q: 'What does each CYK cell hold?', options: ['The number of derivations', 'The variables that derive that substring', 'The next symbol to read', 'A parse tree'], answer: 1, why: 'Cell (i, len) lists every variable that can derive the substring of w starting at i with that length.' },
    ],
  });

  // =====================================================================================================
  // E_CFG: mark the variables that generate something
  // =====================================================================================================
  const ECFG_LINES = ['1. Mark every terminal.', '2. Mark A if a rule A → X₁…Xₖ has every Xᵢ marked.', '3. Repeat 2 until nothing new gets marked.', '4. Start variable unmarked: accept. Otherwise reject.'];
  const GEN = 'S → A B | a S\nA → a A | b\nB → A A | c';
  const NOEXIT = 'S → a S | A b\nA → A a | S';
  const USELESS = 'S → a S b | B\nB → C c | b\nC → C C';
  const EPSG = 'S → A S A | a B\nA → ε\nB → B b';

  T.topic({
    id: 'dec-ecfg', family: 'decidable', order: 50, title: 'E_CFG: does the grammar generate anything?',
    blurb: 'A variable is useful for emptiness if it can turn into a string of terminals. Marks flow backwards: from the terminals, through every rule whose right side is all marked, to its left side. L(G) is empty when the marks never reach the start variable.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar G', def: GEN, check: gramCheck('Grammar G', 5) }],
    presets: [
      { label: 'Not empty: S is reached in three rounds', values: { g: GEN } },
      { label: 'Empty: every rule needs a variable that never finishes', values: { g: NOEXIT } },
      { label: 'A useless variable: C can never be finished', values: { g: USELESS } },
      { label: 'An ε-rule marks A with nothing to wait for', values: { g: EPSG } },
    ],
    counters: [{ id: 'marked', label: 'variables marked' }, { id: 'rounds', label: 'rounds' }],
    run(inp) {
      const G = T.comp.parseCFG(inp.g);
      const res = T.comp.E_CFG(G);
      const isVar = (s) => G.variables.includes(s);
      const CW = 40, CH = 36, GAP = 6;
      const maxLen = Math.max(1, ...G.rules.map((r) => r.rhs.length));
      const room = { w: 60 + 40 + maxLen * (CW + GAP) + 30, h: G.rules.length * (CH + 10) + 90 };
      const F = new T.Frames(['marked', 'rounds']);
      const scene = (st) => {
        const verdict = st.end ? (st.empty ? 'accept' : 'reject') : null;
        const mb = K.mbox.draw({ prefix: 'dec', x: 0, y: 0, title: 'Decider for E_CFG', tag: 'decider', lines: ECFG_LINES, hot: [st.line], done: [0, 1, 2, 3].filter((i) => i < st.line), room, outs: K.mbox.answers(verdict, { acceptText: 'accept: L(G) = ∅', rejectText: 'reject: L(G) ≠ ∅' }), cls: 'r0' });
        const items = mb.items.slice();
        const R = mb.room;
        const mk = new Set(st.marked);
        G.rules.forEach((r, k) => {
          const y = R.y + 4 + k * (CH + 10);
          const firing = st.rule === k;
          if (firing) items.push({ key: 'fire', kind: 'region', x: R.x - 6, y: y - 5, w: R.w + 12, h: CH + 10, text: '', cls: 'mline hot', rx: 8, audit: 'overlap-ok' });
          const lc = mk.has(r.lhs) ? (st.fresh === r.lhs ? 'hot' : 'good') : st.end && r.lhs === G.start ? 'bad' : '';
          items.push({ key: 'r' + k + ':l', kind: 'cell', x: R.x, y, w: 50, h: CH, text: r.lhs, cls: 'mono ' + lc, pick: true });
          items.push({ key: 'r' + k + ':ar', kind: 'text', x: R.x + 70, y: y + CH / 2 + 6, text: '→', anchor: 'middle', cls: 'strong' });
          if (!r.rhs.length) items.push({ key: 'r' + k + ':c0', kind: 'cell', x: R.x + 90, y, w: CW, h: CH, text: 'ε', cls: 'mono good' });
          r.rhs.forEach((s, j) => items.push({ key: 'r' + k + ':c' + j, kind: 'cell', x: R.x + 90 + j * (CW + GAP), y, w: CW, h: CH, text: s, cls: 'mono ' + (!isVar(s) ? (st.line >= 0 && st.started ? 'good' : '') : mk.has(s) ? 'good' : st.waiting && st.waiting.includes(s) ? 'bad' : '') }));
        });
        const by = R.y + G.rules.length * (CH + 10) + 22;
        items.push({ key: 'mk:t', kind: 'text', x: R.x, y: by + 6, text: 'marked: ' + set(st.marked), cls: 'strong' });
        if (st.end) items.push({ key: 'mk:w', kind: 'text', x: R.x, y: by + 38, text: st.empty ? G.start + ' never finishes: L(G) = ∅' : G.start + ' ⇒* ' + show(res.witness), cls: st.empty ? 'bad' : 'good' });
        return items;
      };
      const marked = [];
      F.add({ items: scene({ line: 0, marked, started: true }), say: 'Line 1: every terminal is marked: a terminal is already a finished string. (A rule with ε on the right needs nothing at all.)', hl: { prog: [0] } });
      let round = 0;
      for (let ch = true; ch;) {
        ch = false; round++;
        F.set('rounds', round);
        for (let k = 0; k < G.rules.length; k++) {
          const r = G.rules[k];
          if (marked.includes(r.lhs) || !r.rhs.every((s) => !isVar(s) || marked.includes(s))) continue;
          F.last().meta = Object.assign({}, F.last().meta, { next: r.lhs, nextKeys: G.rules.map((x, j) => (x.lhs === r.lhs ? 'r' + j + ':l' : null)).filter(Boolean) });
          marked.push(r.lhs); ch = true; F.count('marked');
          F.add({ items: scene({ line: 1, marked: marked.slice(), rule: k, fresh: r.lhs, started: true }), say: 'Line 2 (round ' + round + '): ' + r.lhs + ' → ' + (r.rhs.join(' ') || 'ε') + (r.rhs.length ? ' uses only marked symbols' : ' needs nothing') + ', so ' + r.lhs + ' can finish as a terminal string: mark ' + r.lhs + ' everywhere.', hl: { g: [k], prog: [1] } });
        }
      }
      const empty = !marked.includes(G.start);
      const waiting = G.variables.filter((v) => !marked.includes(v));
      F.add({ items: scene({ line: 2, marked: marked.slice(), started: true, waiting }), say: 'Line 3: a whole pass over the rules marks nothing new, so the marks have stopped. ' + (waiting.length ? 'Never marked: ' + waiting.join(', ') + '. Each of their rules waits for an unmarked variable, so no derivation from them ever finishes.' : 'Every variable is marked.') + ' With ' + G.variables.length + ' variables there can be at most ' + G.variables.length + ' useful rounds.', hl: { prog: [2] } });
      F.last().meta = Object.assign({}, F.last().meta, { verdict: empty ? 'accept' : 'reject' });
      F.add({ items: scene({ line: 3, marked: marked.slice(), started: true, waiting, end: true, empty }), say: 'Line 4: ' + (empty ? 'the start variable ' + G.start + ' is unmarked, so G generates no string at all: L(G) = ∅ and the decider accepts.' : G.start + ' is marked, so G generates something, for example ' + show(res.witness) + ' (built from the rules that did the marking). L(G) ≠ ∅: the decider rejects.'), hl: { prog: [3] }, mark: empty ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [progSection(ECFG_LINES), { id: 'g', kind: 'grammar', title: 'G', rules: G.rules.map((r) => r.lhs + ' → ' + (r.rhs.join(' ') || 'ε')), nonterminals: G.variables }, { id: 'idea', kind: 'text', title: 'The idea', text: 'A variable is marked exactly when it derives some string of terminals. The marks only grow, and there are finitely many variables, so the loop ends.' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.next, once: true, pick: 'item', ask: 'Which variable gets marked next? Click it on the left of one of its rules.', answer: (fr, i) => fr[i].meta.nextKeys, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.verdict, once: true, pick: 'item', ask: 'The marks have stopped. Click the lamp the decider lights.', answer: (fr, i) => 'dec:o:' + fr[i].meta.verdict, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does it mean when variable A is marked?', options: ['A appears in some rule', 'A can derive some string made only of terminals', 'A is reachable from the start', 'A has an ε-rule'], answer: 1, why: 'Marks start at terminals and move to a left side only when its whole right side can finish.' },
      { q: 'The marks reach every variable except the start variable. What is L(G)?', options: ['Σ*', '∅', 'Infinite', 'It cannot be told'], answer: 1, why: 'Only derivations from the start variable count. If the start variable cannot finish, G generates nothing.' },
      { q: 'Why does the marking always stop?', options: ['After |w| rounds', 'Each useful round marks a new variable, and there are finitely many', 'Grammars have no recursion', 'It uses a step limit'], answer: 1, why: 'A round that marks nothing ends the loop; otherwise one more of finitely many variables is marked.' },
      { q: 'In S → a S | A b and A → A a | S, why is nothing ever marked?', options: ['There are no terminals', 'Every rule needs S or A, and neither can finish first', 'The grammar is ambiguous', 'There are too many rules'], answer: 1, why: 'Each right side contains a variable; to mark it you would need it marked already. Derivations can grow but never end.' },
      { q: 'Is "L(G) = Σ*" (does G generate every string) decidable the same way?', options: ['Yes, by marking', 'No, it is undecidable for context-free grammars', 'Yes, with CYK on every string', 'Only for regular grammars, and never otherwise'], answer: 1, why: 'Emptiness is decidable, but "generates everything" is not: a decider would have to rule out infinitely many missing strings.' },
    ],
  });
  // =====================================================================================================
  // Every context-free language is decidable: a grammar built into a decider
  // =====================================================================================================
  const CFL_LINES = ['On input w:', '1. Run the A_CFG decider on ⟨G, w⟩.', '2. Answer as it does.'];

  T.topic({
    id: 'dec-cfl', family: 'decidable', order: 60, title: 'Every context-free language is decidable',
    blurb: 'Fix a grammar G and build it into a machine M_G that runs the A_CFG decider on ⟨G, w⟩. M_G halts on every w, so L(G) is decidable. Simulating a pushdown automaton instead could follow a branch that never ends.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar G', def: LEFT, check: gramCheck('Grammar G', 4) },
      { id: 'ws', kind: 'list', label: 'Strings to try', def: ['b', 'baa', 'ab', ''], min: 1, max: 5 },
    ],
    presets: [
      { label: 'Left recursion: S → S a | b', values: { g: LEFT, ws: ['b', 'baa', 'ab', ''] } },
      { label: 'Balanced, with S → S S', values: { g: BAL, ws: ['abab', 'ba', '', 'aabb'] } },
      { label: 'No left recursion: odd palindromes', values: { g: PAL, ws: ['aba', 'ab', 'babab'] } },
    ],
    check: (inp) => {
      const G = T.comp.parseCFG(inp.g);
      for (const w of inp.ws) { if ([...w].length > 6) return 'Strings: at most 6 symbols each'; const bad = [...w].find((c) => !G.terminals.includes(c)); if (bad !== undefined) return 'Strings: "' + bad + '" in ' + w + ' is not a terminal of G'; }
      return null;
    },
    counters: [{ id: 'decided', label: 'strings decided' }, { id: 'cells', label: 'CYK cells, all runs' }],
    run(inp) {
      const G = T.comp.parseCFG(inp.g), ws = inp.ws;
      const conv = T.comp.toCNF(G);
      const gl = groupRules(G.rules.map((r) => r.lhs + '→' + r.rhs.join(' ')));
      const results = ws.map((w) => ({ w, n: [...w].length, yes: T.comp.cyk(conv.cnf, [...w]).accepted }));
      // the trap: a pushdown automaton for G expands the variable on top of its stack without reading
      const lr = G.variables.filter((v) => G.rules.some((r) => r.lhs === v && r.rhs[0] === v));
      let nid = 0;
      const grow = (stack, depth) => {
        const node = { id: 'n' + nid++, label: stack.join(' ') || 'ε', mono: true };
        const top = stack[0];
        if (depth === 0 || top === undefined || !G.variables.includes(top)) { node.cls = top !== undefined && !G.variables.includes(top) ? 'reads' : ''; if (depth === 0 && top !== undefined && G.variables.includes(top)) node.cls = 'loops'; return node; }
        node.children = G.rules.filter((r) => r.lhs === top).slice(0, 3).map((r) => grow(r.rhs.concat(stack.slice(1)), depth - 1));
        return node;
      };
      const tree = grow([G.start], 3);
      const loopers = [];
      const walk = (n, path) => { const p = path.concat(n.id); if (n.cls === 'loops') loopers.push(p); (n.children || []).forEach((c) => walk(c, p)); };
      walk(tree, []);
      const F = new T.Frames(['decided', 'cells']);
      const TW = 300;
      const scene = (st) => {
        const verdict = st.cur != null && st.done ? (results[st.cur].yes ? 'accept' : 'reject') : null;
        const mb = K.mbox.draw({ prefix: 'mg', x: 0, y: 0, title: 'M_G', input: st.cur != null ? 'w = ' + show(ws[st.cur]) : 'w', lines: CFL_LINES, hot: st.cur != null ? [st.done ? 2 : 1] : [], cls: 'r0',
          inner: [{ prefix: 'mg:g', title: 'G, built in', cls: 'r5', mono: true, lines: gl }, { prefix: 'mg:d', title: 'Decider for A_CFG', tag: 'decider', cls: st.cur != null && !st.done ? 'r2 hot' : 'r2', lines: ['CNF, then CYK: always halts'] }],
          outs: K.mbox.answers(verdict) });
        const items = mb.items.slice();
        // the results so far
        const tx = mb.all.x + mb.all.w + 50, ty = 0;
        const rows = results.map((r, i) => (i < st.filled ? [show(r.w), r.n ? String((r.n * (r.n + 1)) / 2) : 'S₀ → ε?', r.yes ? 'accept' : 'reject'] : [show(r.w), '', '']));
        items.push(...K.table.draw({ prefix: 'res', x: tx, y: ty, colHead: ['w', 'CYK cells', 'M_G says'], rows, minW: 70, mono: true, size: 14, hot: st.cur != null ? [[st.cur, 0]] : [], cls: (r, c) => (c === 2 && r < st.filled ? (results[r].yes ? 'good' : 'bad') : '') }).items);
        if (st.tree) {
          const ty2 = Math.max(mb.all.y + mb.all.h, ty + 34 + results.length * 40) + 70;
          items.push({ key: 'tr:title', kind: 'text', x: 0, y: ty2 - 30, text: 'a pushdown automaton for G, expanding without reading', cls: 'title' });
          const shown = prune(tree, st.tree === 'all' ? 99 : st.tree, st.reveal);
          const t = K.tree.draw(shown, { prefix: 'pda', x: (tx + 300) / 2, y: ty2 + 20, gapY: 74, gapX: 22, hot: st.hot || [], edgeCls: (a, b) => (st.hot && st.hot.includes(a.id) && st.hot.includes(b.id) ? 'hot' : '') });
          items.push(...t.items);
        }
        return items;
      };
      // the branches that never read stay plain until the scene says why
      function prune(n, depth, reveal) { return Object.assign({}, n, { cls: n.cls === 'bad' && !reveal ? '' : n.cls, children: depth > 0 && n.children ? n.children.map((c) => prune(c, depth - 1, reveal)) : undefined }); }
      // a node is drawn as its stack; a stack topped by a terminal must read next, one topped by a variable can keep expanding
      const decorate = (n) => { n.cls = n.cls === 'loops' ? 'bad' : n.cls === 'reads' ? 'good' : ''; (n.children || []).forEach(decorate); };
      decorate(tree);
      F.add({ items: scene({ filled: 0 }), say: 'M_G has the grammar G written into it. On any input w it hands ⟨G, w⟩ to the A_CFG decider and repeats its answer. One machine per grammar, and each one always halts.' });
      results.forEach((r, i) => {
        F.add({ items: scene({ filled: i, cur: i }), say: 'Input ' + show(r.w) + ': line 1 runs the A_CFG decider on ⟨G, ' + show(r.w) + '⟩: ' + (r.n ? 'Chomsky normal form, then ' + (r.n * (r.n + 1)) / 2 + ' CYK cells.' : 'the empty string, so it only checks for the rule S₀ → ε.'), hl: { prog: [1] }, meta: { verdict: r.yes ? 'accept' : 'reject', w: r.w } });
        F.count('decided').count('cells', (r.n * (r.n + 1)) / 2);
        F.add({ items: scene({ filled: i + 1, cur: i, done: true }), say: 'The decider ' + (r.yes ? 'accepts' : 'rejects') + ', so M_G ' + (r.yes ? 'accepts ' : 'rejects ') + show(r.w) + (r.yes ? ': G generates it.' : ': G does not generate it.') + ' It halted, as it does on every input.', hl: { prog: [2] } });
      });
      F.add({ items: scene({ filled: results.length, tree: 1 }), say: 'Why not simply run a pushdown automaton for L(G)? It starts with ' + G.start + ' on its stack and may replace the top variable by any of its right sides without reading anything.' });
      F.add({ items: scene({ filled: results.length, tree: 'all' }), say: 'Each choice is a branch, drawn three expansions deep. A branch whose stack has a terminal on top (green) must read that symbol next, so it soon ends or moves on.' });
      if (lr.length) {
        F.last().meta = { loopKeys: loopers.map((p) => 'pda:n:' + p[p.length - 1]) };
        F.add({ items: scene({ filled: results.length, tree: 'all', reveal: true, hot: [...new Set(loopers.flat())] }), say: 'But ' + lr.join(', ') + ' starts one of its own right sides (' + G.rules.filter((r) => lr.includes(r.lhs) && r.rhs[0] === r.lhs).map((r) => r.lhs + ' → ' + r.rhs.join(' ')).join(', ') + '), so the red branch can expand for ever without reading a symbol. A simulator that follows it never halts: that is why M_G goes through Chomsky normal form instead.', mark: 'trap' });
      } else {
        F.add({ items: scene({ filled: results.length, tree: 'all', reveal: true }), say: 'In this G no variable starts one of its own right sides, so every branch reaches a terminal and must read. A grammar with a rule like S → S a would have a branch that expands for ever; the A_CFG decider is safe either way.', mark: 'safe' });
      }
      return { frames: F.list, def: { sections: [{ id: 'prog', kind: 'math', title: 'M_G', text: CFL_LINES.join('\n') }, { id: 'g', kind: 'grammar', title: 'G', rules: gl, nonterminals: G.variables }, { id: 'claim', kind: 'text', title: 'The theorem', text: 'Every context-free language is decidable: for L = L(G), the machine M_G decides L. Nothing is claimed about finding G from L; G is fixed in advance.' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.verdict, once: true, pick: 'item', ask: (fr, i) => 'Will M_G accept or reject ' + show(fr[i].meta.w) + '? Click the lamp.', answer: (fr, i) => 'mg:o:' + fr[i].meta.verdict, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.loopKeys, once: true, pick: 'item', ask: 'Click a branch that could keep expanding for ever without reading a symbol.', answer: (fr, i) => fr[i].meta.loopKeys, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why is every context-free language decidable?', options: ['Every PDA halts on every input', 'For L = L(G), a machine with G built in can run the A_CFG decider on ⟨G, w⟩', 'Context-free languages are finite', 'Because they are regular'], answer: 1, why: 'The A_CFG decider always halts, so the machine that fixes G and calls it is a decider for L(G).' },
      { q: 'What can go wrong if you decide L by simulating a nondeterministic PDA branch by branch?', options: ['Nothing', 'Some branch may expand the stack for ever without reading input, so the simulation may not halt', 'PDAs cannot be simulated', 'It accepts wrong strings'], answer: 1, why: 'ε-moves can repeat without end, as with a left-recursive rule. A decider must avoid unbounded searches.' },
      { q: 'M_G for a fixed G handles inputs of every length. Is the work bounded for each input?', options: ['No', 'Yes: about n(n + 1)/2 cells times the number of rules for length n', 'Only for short inputs', 'Only if G is unambiguous'], answer: 1, why: 'The work grows with n but is finite for each n, which is all a decider needs.' },
      { q: 'Is the converse true: every decidable language is context-free?', options: ['Yes', 'No: aⁿbⁿcⁿ is decidable but not context-free', 'Only for finite languages', 'Only over one letter'], answer: 1, why: 'Context-free languages are a proper part of the decidable languages.' },
    ],
  });
})();
