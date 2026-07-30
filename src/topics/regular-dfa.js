// Deterministic finite automata: a run on a string (with the run written out state by state under the
// input), designing a DFA by deciding what it must remember (remainders, the progress of a pattern, two
// parities as a product of two small machines), the dead state that completes a partial DFA, and the
// complement by flipping accepting states, which only works once the machine is complete.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg;

  T.family({ id: 'dfa', part: 'regular', order: 10, title: 'Deterministic finite automata', blurb: 'One state at a time, one move per symbol: a DFA reads its input left to right and accepts if it stops in an accepting state.' });

  const STARTS_A_ENDS_B = 'start s\naccept B\ns -a-> A\ns -b-> D\nA -a-> A\nA -b-> B\nB -a-> A\nB -b-> B\nD -a,b-> D';
  const MOD3 = 'start r0\naccept r0\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r0\nr2 -0-> r1\nr2 -1-> r2';
  const NO_BB = 'start ok\naccept ok sawb\nok -a-> ok\nok -b-> sawb\nsawb -a-> ok\nsawb -b-> stuck\nstuck -a,b-> stuck';
  const chipW = (q) => Math.max(34, Geo.textWidth(q, 14, { bold: true }) + 18);

  // ---- a run ----------------------------------------------------------------------------------------------------
  T.topic({
    id: 'dfa-run', family: 'dfa', order: 10, title: 'A DFA reads a string',
    blurb: 'Watch the one active state move along the edges as each symbol is read, and the run grow under the input. At the end, the state it stops in decides: accept or reject.',
    inputs: [
      { id: 'm', kind: 'machine', machine: 'dfa', label: 'Machine', def: STARTS_A_ENDS_B, check: (v) => { const m = T.Machine.parse(v); if (m.kind !== 'dfa' && !T.Machine.isDeterministic(m)) return 'Machine: a DFA has one move per state and symbol and no ε moves'; if (m.states.length > 9) return 'Machine: at most 9 states, so the picture stays readable'; return null; } },
      { id: 'w', kind: 'string', label: 'Input', def: 'aabab', max: 12 },
    ],
    presets: [
      { label: 'Accepted: abab', values: { m: STARTS_A_ENDS_B, w: 'abab' } },
      { label: 'Into the dead state: ba', values: { m: STARTS_A_ENDS_B, w: 'ba' } },
      { label: 'The empty string', values: { m: STARTS_A_ENDS_B, w: '' } },
      { label: 'Binary multiples of 3: 1001', values: { m: MOD3, w: '1001' } },
      { label: 'No bb: abbab', values: { m: NO_BB, w: 'abbab' } },
    ],
    check: (inp) => { const m = T.Machine.parse(inp.m); const al = T.Machine.alphabet(m); const bad = [...inp.w].find((c) => !al.includes(c)); return bad !== undefined ? 'Input: "' + bad + '" is not in the machine\'s alphabet {' + al.join(', ') + '}' : null; },
    counters: [{ id: 'read', label: 'symbols read' }, { id: 'moves', label: 'moves taken' }],
    run(inp) {
      const m = T.Machine.parse(inp.m);
      const fa = R.fa(m);
      const w = [...inp.w];
      const run = R.runDFA(fa, inp.w);
      const pos = K.graph.layout(m).pos;
      const g0 = K.graph.draw(m, { pos });
      const DEAD = 'dead';
      const cw = Math.max(46, ...m.states.concat([DEAD]).map((q) => chipW(q) + 12));
      const sx = g0.box.x + g0.box.w / 2 - (Math.max(1, w.length) * cw) / 2;
      const gy = g0.box.y + g0.box.h + 70;
      const ty = gy + 44 + 40 + 34;
      const F = new T.Frames(['read', 'moves']);
      const dt = R.delta(fa);
      // the run so far: one state at each boundary between symbols, the newest lit
      const trail = (states, last) => {
        const out = [{ key: 'run:label', kind: 'text', x: sx - chipW(states[0]) / 2 - 12, y: ty + 5, text: 'run', anchor: 'end', cls: 'title' }];
        states.forEach((q, i) => out.push({ key: 'run:' + i, kind: 'state', x: sx + i * cw, y: ty, w: chipW(q), h: 32, rx: 16, text: q, size: 14, cls: i === states.length - 1 ? last || 'hot' : '', enter: 'grow' }));
        return out;
      };
      const scene = (i, opts, states, last) => {
        const g = K.graph.draw(m, Object.assign({ pos }, opts));
        const s = K.string.draw({ text: w, pos: i, x: sx, y: gy, label: 'input', cw, headText: i >= w.length ? 'end' : 'next' });
        return g.items.concat(s.items, trail(states, last));
      };
      const row = (q) => fa.states.indexOf(q);
      F.add({ items: scene(0, { active: [m.start], startHot: true }, [m.start]), say: 'The machine starts in ' + m.start + ', the state the arrow from nowhere points to. ' + (w.length ? 'It will read ' + w.join('') + ', one symbol at a time.' : 'The input is the empty string ε: there is nothing to read.'), hl: { delta: [String(row(m.start))] }, meta: { q: m.start } });
      for (let i = 0; i < run.path.length - 1; i++) {
        const p = run.path[i], q = run.path[i + 1];
        F.count('read').count('moves');
        F.add({ items: scene(i + 1, { active: [q], taken: [p + '>' + q] }, run.path.slice(0, i + 2)), say: 'Read ' + w[i] + ' in ' + p + ': δ(' + p + ', ' + w[i] + ') = ' + q + '. The machine is now in ' + q + '.', hl: { delta: [dt.rc(p, w[i])] }, meta: { q: p, next: q } });
      }
      const end = run.path[run.path.length - 1];
      const shown = w.join('') || 'ε';
      if (run.stuck >= 0) {
        F.count('read');
        F.add({ items: scene(run.stuck + 1, { active: [], bad: [end] }, run.path.concat([DEAD]), 'bad dead'), say: 'In ' + end + ' there is no move on ' + w[run.stuck] + '. A missing move goes to a dead state that never accepts and never leaves, so ' + shown + ' is rejected without reading the rest.', mark: 'rejected', meta: { verdict: 'Reject' } });
      } else {
        const acc = run.accept;
        F.add({ items: scene(w.length, acc ? { good: [end] } : { bad: [end] }, run.path, acc ? 'good' : 'bad'), say: 'The input is used up and the machine is in ' + end + ', which is ' + (acc ? 'an accepting state (double ring). ' + shown + ' is accepted.' : 'not an accepting state. ' + shown + ' is rejected.') + ' The run ' + run.path.join(', ') + ' has ' + run.path.length + ' states for ' + w.length + ' symbol' + (w.length === 1 ? '' : 's') + '.', mark: acc ? 'accepted' : 'rejected', meta: { verdict: acc ? 'Accept' : 'Reject' } });
      }
      return { frames: F.list, def: { sections: [R.tuple(fa), dt.section] } };
    },
    predict: [
      { at: (f, i) => (i === 0 || i === 2) && f.meta && f.meta.q !== undefined, pick: 'item', ask: () => 'Which state will the machine be in after the next symbol? Click it.', answer: (fr, i) => (fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.next ? 'g:s:' + fr[i + 1].meta.next : null), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2 && i > 0, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'One symbol is left (or the input is used up). Will the machine accept?', answer: (fr) => fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A DFA has 4 states and its alphabet has 2 symbols. How many moves does its transition function have?', options: ['4', '6', '8', '16'], answer: 2, why: 'One move for every state and every symbol: 4 × 2 = 8.' },
      { q: 'When does a DFA accept the empty string ε?', options: ['Never', 'When its start state is accepting', 'When it has a loop on the start state', 'Always'], answer: 1, why: 'Reading ε makes no moves, so the machine stops where it started.' },
      { q: 'A DFA reads a string of length n. How many states does its run list, counting the start?', options: ['n − 1', 'n', 'n + 1', 'It depends on the machine'], answer: 2, why: 'One move per symbol, so n moves and n + 1 states, some of which may repeat.' },
      { q: 'The run passes through an accepting state in the middle but ends in a non-accepting one. What happens?', options: ['Accepted: it reached acceptance', 'Rejected: only the last state counts', 'It depends on the next string', 'The machine is not a DFA'], answer: 1, why: 'Acceptance is decided once, when the input is used up, by the state the run ends in.' },
      { q: 'Why does a DFA always finish its run quickly?', options: ['It has few states', 'It makes exactly one move per symbol and never goes back', 'It skips symbols it does not need', 'It stops at the first accepting state'], answer: 1, why: 'Each symbol is read once and causes exactly one move, so the run takes |w| steps.' },
    ],
  });

  // ---- design ----------------------------------------------------------------------------------------------------
  // Each design is a machine built in a teaching order: its states with what each remembers, then the moves
  // out of each state with the reason, then the start and accepting states, then a test run.
  function designMod(n) {
    const st = Array.from({ length: n }, (_, k) => 'r' + k);
    const pos = R.ring(st, 0, 0, n === 2 ? 100 : 60 + 22 * n, Math.PI);
    const steps = st.map((q, k) => ({ state: q, moves: [0, 1].map((b) => ({ sym: String(b), to: st[(2 * k + b) % n], why: 'reading ' + b + ' after a value ≡ ' + k + ' gives 2·' + k + (b ? ' + 1' : '') + ' = ' + (2 * k + b) + ' ≡ ' + ((2 * k + b) % n) })) }));
    let v = 3 * n; if (n === 2) v = 6;
    const sample = v.toString(2);
    return {
      alphabet: ['0', '1'], states: st, start: 'r0', accept: ['r0'], pos, steps, sample, crossOk: n >= 4,
      goal: 'binary numerals whose value is a multiple of ' + n,
      idea: ['Reading bit b turns the value v into 2v + b.', 'So v mod ' + n + ' after the bit depends only on', 'v mod ' + n + ' before it: ' + n + ' states are enough.'],
      meaning: st.map((q, k) => q + ':  value ≡ ' + k + ' (mod ' + n + ')'),
      startWhy: 'r0 is both the start and the only accepting state: the empty numeral counts as 0, and a value ≡ 0 is a multiple of ' + n + '.',
      member: (w) => w !== '' && parseInt(w, 2) % n === 0 || w === '',
      describe: (w) => w + ' is ' + parseInt(w, 2) + ' in decimal, ' + (parseInt(w, 2) % n === 0 ? 'a multiple of ' + n : 'not a multiple of ' + n),
    };
  }
  function designPattern(p, ends) {
    const k = [...p];
    const name = (j) => (j === 0 ? 'ε' : k.slice(0, j).join(''));
    const st = k.map((_, j) => name(j)).concat([name(k.length)]);
    // the longest end of s that is a beginning of p
    const back = (s) => { for (let l = Math.min(s.length, k.length); l >= 0; l--) if (s.slice(s.length - l) === p.slice(0, l)) return l; return 0; };
    const steps = st.map((q, j) => ({ state: q, moves: ['a', 'b'].map((c) => {
      if (j === k.length && !ends) return { sym: c, to: q, why: 'once ' + p + ' has been seen it stays seen, so the last state keeps every symbol' };
      const s = (j ? q : '') + c, l = j < k.length && k[j] === c ? j + 1 : back(s.slice(1)) ;
      const to = name(Math.min(l, k.length));
      if (j < k.length && k[j] === c) return { sym: c, to, why: (j ? q : 'nothing') + ' then ' + c + ': the match grows to ' + to };
      return { sym: c, to, why: (j ? q : '') + c + ' ' + (l ? 'ends in ' + to + ', the longest end that begins ' + p : 'has no end that begins ' + p + ', so back to ε') };
    }) }));
    return {
      alphabet: ['a', 'b'], states: st, start: 'ε', accept: [name(k.length)], pos: R.row(st, 0, 0, 150), steps,
      sample: ends ? (p[0] === 'a' ? 'b' : 'a') + p[0] + p : (p.length > 1 ? p.slice(0, -1) + (p[p.length - 1] === 'a' ? 'b' : 'a') : 'b') + p,
      goal: ends ? 'strings that end with ' + p : 'strings that contain ' + p,
      idea: ['Remember the longest end of what has been read', 'that is also a beginning of ' + p + '.', 'That is all a later match can use.'],
      meaning: st.map((q, j) => q + ':  ' + (j === 0 ? 'no progress' : j === k.length ? (ends ? 'just read ' + p : p + ' has appeared') : 'the input ends in ' + q)),
      startWhy: 'Start in ε (no progress yet). ' + (ends ? 'Accept in ' + p + ' only: the string must end there.' : 'Accept in ' + p + ', which nothing ever leaves.'),
      member: (w) => (ends ? w.endsWith(p) : w.includes(p)),
      describe: (w) => w + (ends ? (w.endsWith(p) ? ' ends with ' : ' does not end with ') : (w.includes(p) ? ' contains ' : ' does not contain ')) + p,
    };
  }
  function designParity() {
    const st = ['e,e', 'e,o', 'o,e', 'o,o'];
    const pos = { 'e,e': { x: 0, y: 0 }, 'e,o': { x: 200, y: 0 }, 'o,e': { x: 0, y: 170 }, 'o,o': { x: 200, y: 170 } };
    const flipA = { e: 'o', o: 'e' };
    const steps = st.map((q) => ({ state: q, moves: [
      { sym: 'a', to: flipA[q[0]] + ',' + q[2], why: 'a flips the parity of the a\'s (the first letter) and keeps the b\'s' },
      { sym: 'b', to: q[0] + ',' + flipA[q[2]], why: 'b flips the parity of the b\'s (the second letter) and keeps the a\'s' },
    ] }));
    return {
      alphabet: ['a', 'b'], states: st, start: 'e,e', accept: ['e,o'], pos, steps, sample: 'babab', product: true,
      goal: 'strings with an even number of a\'s and an odd number of b\'s',
      idea: ['Two small machines each count one parity.', 'Run them side by side: a state of the product', 'is a pair, (a-parity, b-parity).'],
      meaning: ['e,e:  even a\'s, even b\'s', 'e,o:  even a\'s, odd b\'s', 'o,e:  odd a\'s, even b\'s', 'o,o:  odd a\'s, odd b\'s'],
      startWhy: 'Start in e,e: no a\'s and no b\'s yet, both even. Accept in e,o only: even a\'s and odd b\'s.',
      member: (w) => [...w].filter((c) => c === 'a').length % 2 === 0 && [...w].filter((c) => c === 'b').length % 2 === 1,
      describe: (w) => w + ' has ' + [...w].filter((c) => c === 'a').length + ' a\'s and ' + [...w].filter((c) => c === 'b').length + ' b\'s',
    };
  }

  T.topic({
    id: 'dfa-design', family: 'dfa', order: 20, title: 'Designing a DFA',
    blurb: 'Decide what the machine must remember, give each memory a state, then work out every move. Remainders, the progress of a pattern, and two parities run side by side as a product.',
    inputs: [
      { id: 'task', kind: 'choice', label: 'Language', def: 'mod', options: [{ value: 'mod', label: 'binary multiples of n' }, { value: 'contains', label: 'contains a pattern' }, { value: 'ends', label: 'ends with a pattern' }, { value: 'parity', label: 'even a\'s and odd b\'s' }] },
      { id: 'n', kind: 'number', label: 'n (for multiples)', def: 3, min: 2, max: 6 },
      { id: 'p', kind: 'string', label: 'Pattern (for contains / ends with)', def: 'aba', min: 1, max: 4, alphabet: 'ab' },
    ],
    presets: [
      { label: 'Multiples of 3', values: { task: 'mod', n: 3 } },
      { label: 'Multiples of 4: only the last two bits matter', values: { task: 'mod', n: 4 } },
      { label: 'Multiples of 5', values: { task: 'mod', n: 5 } },
      { label: 'Contains aba', values: { task: 'contains', p: 'aba' } },
      { label: 'Ends with abb', values: { task: 'ends', p: 'abb' } },
      { label: 'Even a\'s, odd b\'s: a product', values: { task: 'parity' } },
    ],
    counters: [{ id: 'states', label: 'states' }, { id: 'moves', label: 'moves decided' }],
    run(inp) {
      const D = inp.task === 'mod' ? designMod(inp.n) : inp.task === 'parity' ? designParity() : designPattern(inp.p, inp.task === 'ends');
      const F = new T.Frames(['states', 'moves']);
      const trans = [];
      const full = { kind: 'dfa', states: D.states, start: D.start, accept: D.accept, trans: [], pos: {} };
      for (const s of D.steps) for (const mv of s.moves) full.trans.push({ from: s.state, to: mv.to, label: mv.sym });
      const fa = R.fa(full);
      const g1 = K.graph.draw(full, { pos: D.pos });
      // the meaning of each state, beside the machine (or below, for a long row)
      const lh = R.note('legend', { x: 0, y: 0, title: 'what each state remembers', lines: D.meaning, mono: true, size: 14 }).box.h;
      const notePos = { x: R.bounds(g1.items).x + R.bounds(g1.items).w + 44, y: g1.box.y + g1.box.h / 2 - lh / 2 };
      const legend = (lit) => R.note('legend', { x: notePos.x, y: notePos.y, title: 'what each state remembers', lines: D.meaning, mono: true, size: 14, lineCls: D.states.map((q) => (lit && lit.includes(q) ? 'hot' : '')) });
      // a ring of remainders cannot always be drawn without crossings: those edges may cross
      const crossing = (items) => (D.crossOk ? items.map((it) => (it.kind === 'edge' && /\btr\b/.test(it.cls || '') ? Object.assign({}, it, { audit: 'edge-x' }) : it)) : items);
      const lg = legend([]);
      // the two factor machines of the product sit on the axes of its grid
      const factors = (act) => {
        if (!D.product) return [];
        const A = { kind: 'dfa', states: ['e', 'o'], start: 'e', accept: [], trans: [{ from: 'e', to: 'o', label: 'a' }, { from: 'o', to: 'e', label: 'a' }, { from: 'e', to: 'e', label: 'b' }, { from: 'o', to: 'o', label: 'b' }], pos: {} };
        const B = { kind: 'dfa', states: ['e', 'o'], start: 'e', accept: [], trans: [{ from: 'e', to: 'o', label: 'b' }, { from: 'o', to: 'e', label: 'b' }, { from: 'e', to: 'e', label: 'a' }, { from: 'o', to: 'o', label: 'a' }], pos: {} };
        const ga = K.graph.draw(A, { prefix: 'fa', pos: { e: { x: -170, y: 0 }, o: { x: -170, y: 170 } }, active: act ? [act[0]] : [], hideStart: true, r: 22 });
        const gb = K.graph.draw(B, { prefix: 'fb', pos: { e: { x: 0, y: -160 }, o: { x: 200, y: -160 } }, active: act ? [act[1]] : [], hideStart: true, r: 22 });
        return ga.items.concat(gb.items, [R.caption('fa:cap', -170, -125, 'parity of a', 'title'), R.caption('fb:cap', 100, -226, 'parity of b', 'title')]);
      };
      const partial = (opts) => {
        const m = { kind: 'dfa', states: D.states, start: D.start, accept: opts.accept ? D.accept : [], trans: trans.slice(), pos: {} };
        return crossing(K.graph.draw(m, Object.assign({ pos: D.pos, hideStart: !opts.start }, opts.g || {})).items);
      };
      // the idea is shown first, where the machine is about to be built
      const n0 = R.note('idea', { x: 0, y: 0, title: 'the idea', lines: D.idea, size: 16 });
      const ideaNote = R.note('idea', { x: g1.box.x + g1.box.w / 2 - n0.box.w / 2, y: g1.box.y + g1.box.h / 2 - n0.box.h / 2, title: 'the idea', lines: D.idea, size: 16 });
      F.add({ items: ideaNote.items.concat(factors()), say: 'Goal: a DFA for ' + D.goal + '. A DFA has no memory except its state, so first decide what it must remember. ' + D.idea.join(' ') });
      F.set('states', D.states.length);
      F.add({ items: factors().concat(partial({ g: { enter: 'grow' } }), lg.items), say: 'One state per thing worth remembering: ' + D.states.join(', ') + '. ' + (D.product ? 'Each is a pair: the first letter is the a-parity, the second the b-parity, so the grid is the two small machines multiplied.' : 'The panel says what each one means.'), hl: {} });
      const dt = R.delta(fa);
      D.steps.forEach((s, k) => {
        for (const mv of s.moves) trans.push({ from: s.state, to: mv.to, label: mv.sym });
        F.count('moves', s.moves.length);
        const taken = s.moves.map((mv) => s.state + '>' + mv.to);
        F.add({ items: factors(D.product ? [s.state[0], s.state[2]] : null).concat(partial({ g: { hot: [s.state], taken } }), legend([s.state]).items), say: 'Moves out of ' + s.state + ': ' + s.moves.map((mv) => 'on ' + mv.sym + ' to ' + mv.to + ' (' + mv.why + ')').join('; ') + '.', hl: { delta: s.moves.map((mv) => dt.rc(s.state, mv.sym)) }, meta: { design: true, k, state: s.state, moves: s.moves } });
      });
      F.add({ items: factors().concat(partial({ start: true, accept: true, g: { good: D.accept, startHot: true } }), lg.items), say: D.startWhy, hl: { tuple: ['2', '3'] } });
      // test it on a sample string
      const w = [...D.sample];
      const run = R.runDFA(fa, D.sample);
      const g2 = K.graph.draw(full, { pos: D.pos });
      const cw = Math.max(46, ...D.states.map((q) => chipW(q) + 8));
      const below = Math.max(R.bounds(g2.items).y + R.bounds(g2.items).h, lg.box.y + lg.box.h) + 50;
      const sx = g2.box.x + g2.box.w / 2 - (w.length * cw) / 2;
      const tscene = (i, gopts) => factors(D.product ? [run.path[i][0], run.path[i][2]] : null).concat(crossing(K.graph.draw(full, Object.assign({ pos: D.pos }, gopts)).items), lg.items, K.string.draw({ text: w, pos: i, x: sx, y: below, cw, label: 'test', headText: i >= w.length ? 'end' : 'next' }).items);
      F.add({ items: tscene(0, { active: [D.start], startHot: true }), say: 'Test the design on ' + D.sample + '. Start in ' + D.start + '.', meta: { test: 0 } });
      for (let i = 0; i < w.length; i++) F.add({ items: tscene(i + 1, { active: [run.path[i + 1]], taken: [run.path[i] + '>' + run.path[i + 1]] }), say: 'Read ' + w[i] + ': ' + run.path[i] + ' → ' + run.path[i + 1] + '.', hl: { delta: [dt.rc(run.path[i], w[i])] }, meta: { test: i + 1, next: run.path[i + 1] } });
      const ok = run.accept;
      F.add({ items: tscene(w.length, ok ? { good: [run.end] } : { bad: [run.end] }), say: 'It ends in ' + run.end + (ok ? ', an accepting state: ' : ', which does not accept: ') + D.describe(D.sample) + ', just as the design intends.', mark: ok ? 'accepted' : 'rejected', meta: { verdict: ok ? 'Accept' : 'Reject' } });
      return { frames: F.list, def: { sections: [R.tuple(fa), dt.section, { id: 'mean', kind: 'text', title: 'The states', text: D.meaning.join('; ') + '.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.design && fr[i + 1].meta.k === 1, once: true, pick: 'item', ask: (fr, i) => 'Where should ' + fr[i + 1].meta.state + ' go on reading ' + fr[i + 1].meta.moves[1].sym + '? Click the state.', answer: (fr, i) => 'g:s:' + fr[i + 1].meta.moves[1].to, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.test === 2, once: true, pick: 'item', ask: 'During the test: which state comes next? Click it.', answer: (fr, i) => 'g:s:' + fr[i + 1].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the design accept the test string?', answer: (fr) => fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A DFA for binary multiples of 7 needs how many states, at least?', options: ['2', '3', '7', '128'], answer: 2, why: 'It must tell apart the seven remainders: two numerals with different remainders behave differently once a suitable tail is added.' },
      { q: 'Why is it enough to remember v mod n rather than v itself?', options: ['Because v is always small', 'Because (2v + b) mod n depends only on v mod n', 'Because DFAs can store numbers', 'Because the last bit decides everything'], answer: 1, why: 'If v ≡ k then 2v + b ≡ 2k + b (mod n), so the remainder after a bit follows from the remainder before it.' },
      { q: 'In the DFA for "contains aba", the machine has read ab and then reads b. Where does it go?', options: ['To ab', 'To a', 'To ε', 'To aba'], answer: 2, why: 'abb has no end that begins aba (b and bb do not start with a), so all progress is lost.' },
      { q: 'What is the difference between the machines for "contains aba" and "ends with aba"?', options: ['None', 'The last state of "contains" keeps every symbol; for "ends with" it can be left again', '"Ends with" needs more states', '"Contains" needs an NFA'], answer: 1, why: 'Once aba has appeared it stays appeared; but a string that ended with aba stops doing so when more symbols come.' },
      { q: 'Two DFAs have 3 and 4 states. How many states can their product have?', options: ['7', '12', '3', '4'], answer: 1, why: 'A product state is a pair, one state from each: 3 × 4 = 12 pairs (fewer if some are unreachable).' },
    ],
  });

  // ---- the dead state --------------------------------------------------------------------------------------------
  const STARTS_AB = 'start p\naccept r\np -a-> q\nq -b-> r\nr -a,b-> r';
  const EXACTLY_ABA = 'start s\naccept t3\ns -a-> t1\nt1 -b-> t2\nt2 -a-> t3';
  const EVEN_A = 'start even\naccept even\neven -a-> odd\nodd -a-> even\neven -b-> even\nodd -b-> odd';
  const NO_B_AFTER = 'start A\naccept A B\nA -a-> A\nA -b-> B\nB -b-> B';
  T.topic({
    id: 'dfa-dead', family: 'dfa', order: 30, title: 'The dead state',
    blurb: 'A DFA drawn with moves missing is shorthand. Every missing move really goes to one more state, the dead state, which never accepts and never lets the run out.',
    inputs: [
      R.machineInput({ id: 'm', label: 'Machine (missing moves allowed)', def: STARTS_AB, kind: 'dfa', max: 7 }),
      { id: 'w', kind: 'string', label: 'Input', def: 'ba', max: 8 },
    ],
    presets: [
      { label: 'Starts with ab: ba dies at once', values: { m: STARTS_AB, w: 'ba' } },
      { label: 'Starts with ab: abba survives', values: { m: STARTS_AB, w: 'abba' } },
      { label: 'Exactly aba: abab dies after accepting', values: { m: EXACTLY_ABA, w: 'abab' } },
      { label: 'No a after b', values: { m: NO_B_AFTER, w: 'abba' } },
      { label: 'Already complete: no dead state needed', values: { m: EVEN_A, w: 'aba' } },
    ],
    check: R.alphaCheck('m', 'w'),
    counters: [{ id: 'missing', label: 'moves missing' }, { id: 'fixed', label: 'sent to dead' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const miss = T.FA.missing(fa);
      const comp = T.FA.complete(fa, 'dead');
      const DEAD = comp.dead;
      const full = R.dia(comp.fa);
      const pos = K.graph.layout(full).pos;
      const F = new T.Frames(['missing', 'fixed']);
      const byState = new Map();
      for (const x of miss) { if (!byState.has(x.state)) byState.set(x.state, []); byState.get(x.state).push(x.sym); }
      // the machine with only some of the moves into dead, and dead itself only once it exists
      const stage = (o) => {
        const sent = o.sent || [];
        const m = { kind: 'dfa', states: fa.states.concat(o.dead ? [DEAD] : []), start: fa.start, accept: fa.accept, trans: R.dia(fa).trans.slice(), pos: {} };
        for (const q of sent) m.trans.push({ from: q, to: DEAD, label: byState.get(q).join(', ') });
        if (o.loop) m.trans.push({ from: DEAD, to: DEAD, label: fa.alphabet.join(', ') });
        return K.graph.draw(m, Object.assign({ pos, dead: o.dead ? [DEAD] : [] }, o.g || {}));
      };
      // dashed stubs for the moves still missing, pointing where there is room, roughly towards dead
      const stubs = (g, left) => {
        const out = [];
        for (const [q, syms] of byState) {
          if (!left.includes(q)) continue;
          const p = pos[q], d = pos[DEAD];
          const toward = Math.atan2(d.y - p.y, d.x - p.x);
          let best = null;
          for (let k = 0; k < 16; k++) {
            const a = toward + (k % 2 ? 1 : -1) * Math.ceil(k / 2) * Math.PI / 8;
            const tip = { x: p.x + Math.cos(a) * 92, y: p.y + Math.sin(a) * 92 };
            const seg = [{ x: p.x + Math.cos(a) * 28, y: p.y + Math.sin(a) * 28 }, tip];
            const tb = { x: tip.x - 26, y: tip.y - 16, w: 52, h: 32 };
            let s = Math.ceil(k / 2);
            for (const r of g.routes) { s += 20 * Geo.polyCross(seg, r.pts); if (Geo.polyBox(r.pts, tb)) s += 20; if (Geo.boxHit(tb, Geo.labelBox(r.label, r.lx, r.ly, 15), 4) || Geo.polyBox(seg, Geo.labelBox(r.label, r.lx, r.ly, 15))) s += 20; }
            for (const r of fa.states.concat([DEAD])) if (r !== q && (Geo.boxHit(tb, { x: pos[r].x - 34, y: pos[r].y - 34, w: 68, h: 68 }, 0) || Geo.polyBox(seg, { x: pos[r].x - 30, y: pos[r].y - 30, w: 60, h: 60 }))) s += 50;
            for (const o of out) if (o.kind === 'cell' && Geo.boxHit(tb, { x: o.x, y: o.y, w: o.w, h: o.h }, 6)) s += 50;
            if (!best || s < best.s) best = { s, tip };
          }
          const txt = syms.join(', ') + ' ?';
          const w = Math.max(44, Geo.textWidth(txt, 14, { bold: true }) + 16);
          out.push({ key: 'stub:c:' + q, kind: 'cell', x: best.tip.x - w / 2, y: best.tip.y - 15, w, h: 30, rx: 15, text: txt, cls: 'bad', size: 14 });
          out.push({ key: 'stub:e:' + q, kind: 'edge', from: 'g:s:' + q, to: 'stub:c:' + q, cls: 'bad dead' });
        }
        return out;
      };
      const g0 = stage({});
      const dt = R.delta(comp.fa);
      F.add({ items: g0.items, say: miss.length ? 'This DFA is drawn with some moves missing. What happens when the input asks for one of them?' : 'Every state of this DFA has a move on every symbol of {' + fa.alphabet.join(', ') + '}: it is complete.', meta: { missing: miss.length } });
      if (!miss.length) {
        F.add({ items: g0.items.concat([R.caption('note', g0.box.x + g0.box.w / 2, g0.box.y + g0.box.h + 40, 'complete: no dead state is needed', 'hot')]), say: 'No move is missing, so there is nothing to add. (If no state here can reach acceptance any more, it already acts as a dead state.)' });
      } else {
        F.set('missing', miss.length);
        const left = [...byState.keys()];
        F.add({ items: g0.items.concat(stubs(g0, left)), say: R.plural(miss.length, 'move is', 'moves are') + ' missing: ' + miss.map((x) => x.state + ' on ' + x.sym).join(', ') + '. A DFA must say what every state does on every symbol, so these are a shorthand for something.' });
        const g1 = stage({ dead: true, g: { enter: 'grow' } });
        F.add({ items: g1.items.concat(stubs(g1, left)), say: 'Add one new state, ' + DEAD + '. It does not accept, and (as we will see) it never lets the run leave.', hl: { delta: [dt.row(DEAD)] } });
        const sent = [];
        for (const q of left) {
          sent.push(q);
          const g = stage({ dead: true, sent: sent.slice(), g: { taken: [q + '>' + DEAD], hot: [q] } });
          F.count('fixed', byState.get(q).length);
          F.add({ items: g.items.concat(stubs(g, left.filter((x) => !sent.includes(x)))), say: q + ' had no move on ' + byState.get(q).join(' or ') + ': send ' + (byState.get(q).length > 1 ? 'them' : 'it') + ' to ' + DEAD + '.', hl: { delta: byState.get(q).map((a) => dt.rc(q, a)) }, meta: { sent: q } });
        }
        F.add({ items: stage({ dead: true, sent, loop: true, g: { taken: [DEAD + '>' + DEAD] } }).items, say: DEAD + ' loops to itself on every symbol (' + fa.alphabet.join(', ') + '): once the run is there it can never reach an accepting state. Now the DFA is complete.', hl: { delta: fa.alphabet.map((a) => dt.rc(DEAD, a)) }, meta: { loop: true } });
      }
      // run the string on the complete machine
      const w = [...inp.w];
      const run = R.runDFA(comp.fa, inp.w);
      const done = (o) => (miss.length ? stage(Object.assign({ dead: true, sent: [...byState.keys()], loop: true }, o)) : stage(o));
      const gb = done({});
      const cw = 46, sx = gb.box.x + gb.box.w / 2 - (Math.max(1, w.length) * cw) / 2, sy = gb.box.y + gb.box.h + 60;
      const scene = (i, g) => done({ g }).items.concat(K.string.draw({ text: w, pos: i, x: sx, y: sy, cw, label: 'input', headText: i >= w.length ? 'end' : 'next' }).items);
      F.add({ items: scene(0, { active: [fa.start], startHot: true }), say: 'Now run ' + R.w(inp.w) + ' on the complete machine, starting in ' + fa.start + '.', meta: { run: 0, next: run.path[1] } });
      const firstDead = run.path.indexOf(DEAD);
      for (let i = 0; i < w.length; i++) {
        const p = run.path[i], q = run.path[i + 1];
        const say = q === DEAD && p !== DEAD ? 'Read ' + w[i] + ' in ' + p + ': this was a missing move, so the run falls into ' + DEAD + '.' : p === DEAD ? 'Read ' + w[i] + ': ' + DEAD + ' loops to itself. The rest of the input changes nothing.' : 'Read ' + w[i] + ': ' + p + ' → ' + q + '.';
        F.add({ items: scene(i + 1, { active: [q], taken: [p + '>' + q], bad: q === DEAD ? [DEAD] : [] }), say, hl: { delta: [dt.rc(p, w[i])] }, meta: { run: i + 1, next: run.path[i + 2], into: q === DEAD && p !== DEAD } });
      }
      const ok = run.accept;
      F.add({ items: scene(w.length, ok ? { good: [run.end] } : { bad: [run.end] }), say: (run.end === DEAD ? R.w(inp.w) + ' ends in ' + DEAD + ' and is rejected, exactly as the missing move meant: the shorthand and the complete machine accept the same strings.' : R.w(inp.w) + ' ends in ' + run.end + (ok ? ', which accepts.' : ', which does not accept.') + (firstDead < 0 ? ' The run never needed the dead state.' : '')), mark: ok ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [R.tuple(comp.fa, 'The completed machine'), dt.section] } };
    },
    predict: [
      { at: (f, i) => i === 0 && f.meta && f.meta.missing > 0, once: true, pick: 'option', options: (fr) => R.numberOptions(fr[0].meta.missing), ask: 'How many moves are missing from this DFA? (Count every state and every symbol.)', answer: (fr) => String(fr[0].meta.missing), explain: (fr) => fr[1].say },
      { at: (f, i, fr) => f.meta && f.meta.run !== undefined && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.into, once: true, pick: 'item', ask: 'Which state is the run in after the next symbol? Click it.', answer: (fr, i) => 'g:s:' + fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A DFA has 5 states and 2 symbols, and 3 moves are missing. How many moves does its completion have?', options: ['10', '12', '13', '15'], answer: 1, why: 'Adding the dead state gives 6 states, each with a move on each of the 2 symbols: 12.' },
      { q: 'Can the dead state be accepting?', options: ['Yes, if we like', 'No: then missing moves would lead to acceptance and the language would change', 'Only in a complete DFA', 'Only when the language is empty'], answer: 1, why: 'A missing move means "reject this string"; a dead state that accepted would accept strings the shorthand rejects.' },
      { q: 'Does adding the dead state change the language?', options: ['Yes, it adds strings', 'Yes, it removes strings', 'No', 'Only for the empty string'], answer: 2, why: 'Strings that used a missing move were rejected before and end in the non-accepting dead state now.' },
      { q: 'Why does the dead state need a loop on every symbol?', options: ['To make the picture look complete', 'So that it too has a move on every symbol, and the run can never get out', 'To accept long strings', 'It does not need one'], answer: 1, why: 'Every state of a complete DFA needs every move; looping keeps the run trapped where nothing accepts.' },
    ],
  });

  // ---- complement -------------------------------------------------------------------------------------------------
  const ENDS_B = 'start x\naccept y\nx -a-> x\nx -b-> y\ny -a-> x\ny -b-> y';
  const HAS_AA = 'start n\naccept aa\nn -a-> a1\nn -b-> n\na1 -a-> aa\na1 -b-> n\naa -a,b-> aa';
  const NOTHING = 'start q\nq -a,b-> q';
  T.topic({
    id: 'dfa-complement', family: 'dfa', order: 40, title: 'The complement: flip the accepting states',
    blurb: 'Make every accepting state rejecting and every rejecting state accepting, and the DFA accepts exactly the strings it used to reject. But only if no move is missing.',
    inputs: [
      R.machineInput({ id: 'm', label: 'DFA', def: STARTS_AB, kind: 'dfa', max: 6 }),
    ],
    presets: [
      { label: 'Ends in b (complete)', values: { m: ENDS_B } },
      { label: 'Contains aa (complete)', values: { m: HAS_AA } },
      { label: 'Starts with ab (missing moves: flipping alone fails)', values: { m: STARTS_AB } },
      { label: 'Exactly aba (missing moves)', values: { m: EXACTLY_ABA } },
      { label: 'The empty language ∅', values: { m: NOTHING } },
    ],
    check: (inp) => { const al = T.Machine.alphabet(T.Machine.parse(inp.m)); return al.length > 3 ? 'DFA: at most 3 symbols, so every short string fits on the picture' : null; },
    counters: [{ id: 'flipped', label: 'states flipped' }, { id: 'inL', label: 'short strings accepted' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const maxLen = fa.alphabet.length >= 3 ? 2 : 3;
      const comp = T.FA.complete(fa, 'dead');
      const full = R.dia(comp.fa);
      const DEAD = comp.dead;
      const pos = K.graph.layout(full).pos;
      const partialDia = R.dia(fa);
      const draw = (m, acc, o) => K.graph.draw(Object.assign({}, m, { accept: acc }), Object.assign({ pos }, o || {}));
      const g0 = draw(full, fa.accept);
      const cx = g0.box.x + g0.box.w / 2, py = g0.box.y + g0.box.h + 64;
      const member = (m) => T.FA.acceptor(m);
      const inL = member(fa);
      const pyr = (fn, extra) => R.pyramid({ alphabet: fa.alphabet, maxLen, member: fn, x: cx, y: py, label: 'every string up to length ' + maxLen + ': lit = accepted', cls: extra });
      const all = R.upTo(fa.alphabet, maxLen);
      const F = new T.Frames(['flipped', 'inL']);
      const nIn = (fn) => all.filter((w) => fn(w)).length;
      F.set('inL', nIn(inL));
      F.add({ items: draw(partialDia, fa.accept).items.concat(pyr(inL).items), say: 'This DFA accepts the lit strings. Its complement should accept exactly the others, ' + (all.length - nIn(inL)) + ' of these ' + all.length + '.', hl: { tuple: ['3'] }, meta: { stage: 'start' } });
      const flipNames = (states, acc) => states.filter((q) => !acc.includes(q));
      const missing = T.FA.missing(fa);
      if (missing.length) {
        // flipping a partial machine: strings that die are rejected both before and after
        const naiveAcc = flipNames(fa.states, fa.accept);
        const naive = T.FA.make(Object.assign({}, fa, { accept: naiveAcc }));
        const inN = member(naive);
        const lost = all.filter((w) => !inL(w) && !inN(w));
        F.set('flipped', fa.states.length);
        F.set('inL', nIn(inN));
        F.add({ items: draw(partialDia, naiveAcc, { hot: fa.states }).items.concat(pyr((w) => (inN(w) ? true : lost.includes(w) ? 'bad' : false)).items), say: 'Flip every ring as drawn: accept ' + R.set(naiveAcc) + '. But ' + lost.slice(0, 4).map(R.w).join(', ') + (lost.length > 4 ? ' and others' : '') + ' (red) are rejected by both machines: their runs hit a missing move and die, and a dead end rejects whether we flip or not.', hl: { tuple: ['3'] }, meta: { stage: 'naive', lost: lost[0] } });
        F.set('flipped', 0);
        F.set('inL', nIn(inL));
        F.add({ items: draw(full, fa.accept, { dead: [DEAD], enter: 'grow' }).items.concat(pyr(inL).items), say: 'Undo that and complete the machine first: the missing ' + (missing.length === 1 ? 'move goes' : 'moves go') + ' to a new state ' + DEAD + '. The language is unchanged.', meta: { stage: 'complete' } });
      }
      const states = comp.fa.states;
      const newAcc = flipNames(states, comp.fa.accept);
      const cm = T.FA.make(Object.assign({}, comp.fa, { accept: newAcc }));
      const inC = member(cm);
      F.add({ items: draw(missing.length ? full : partialDia, comp.fa.accept, { dead: missing.length ? [DEAD] : [] }).items.concat(pyr(inL).items), say: 'Now every state has every move. Which states will accept after the flip?', meta: { stage: 'ask', newAcc } });
      F.set('flipped', states.length);
      F.set('inL', nIn(inC));
      F.add({ items: draw(missing.length ? full : partialDia, newAcc, { good: newAcc }).items.concat(pyr(inC).items), say: 'Flip: accept ' + R.set(newAcc) + (missing.length ? ', and ' + DEAD + ' now accepts too, so the strings that died are accepted' : '') + '. Every string changes side' + (inL('') ? '; ε was accepted, so now it is not.' : '; ε was rejected, so now it is accepted.'), hl: { tuple: ['3'] }, meta: { stage: 'flip' } });
      const agree = all.every((w) => inC(w) !== inL(w));
      F.add({ items: draw(missing.length ? full : partialDia, newAcc).items.concat(pyr(inC).items), say: (agree ? 'Check: each of the ' + all.length + ' short strings is accepted by exactly one of the two machines.' : 'Some string is accepted by both or neither.') + ' The complement of a regular language is regular: the same states, the opposite verdicts.', mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(fa, 'The original machine'), { id: 'flip', kind: 'math', title: 'The complement', text: 'Q, Σ, δ, q₀ the same' + (missing.length ? ' (after adding ' + DEAD + ')' : '') + '\nF′ = Q − F = ' + R.set(newAcc) }, R.delta(comp.fa).section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.stage === 'naive', once: true, pick: 'option', options: ['Yes', 'No'], ask: (fr, i) => 'Flip the rings of the machine exactly as drawn. Will ' + R.w(fr[i + 1].meta.lost) + ' be accepted then?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.stage === 'ask', once: true, pick: 'item', ask: 'Click a state that will accept in the complement.', answer: (fr, i) => (fr[i].meta.newAcc.length ? fr[i].meta.newAcc.map((q) => 'g:s:' + q) : null), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Flipping the accepting states of a DFA with a missing move gives…', options: ['the complement', 'a machine that misses the strings whose runs die', 'the reversal', 'the empty language'], answer: 1, why: 'A string whose run dies is rejected before and after the flip, so it is in neither language.' },
      { q: 'Does flipping the accepting states of an NFA give its complement?', options: ['Yes, always', 'No: an NFA accepts if some run accepts, and flipping does not turn "some" into "none"', 'Only without ε-moves', 'Only for finite languages'], answer: 1, why: 'A string can have one accepting and one rejecting run; after the flip it still has an accepting run. Determinise first.' },
      { q: 'A complete DFA accepts every string. What does its complement accept?', options: ['Every string', 'Only ε', 'Nothing: the empty language', 'Strings of odd length'], answer: 2, why: 'Every reachable state accepts, so after the flip no reachable state does.' },
      { q: 'What does the complement show about regular languages?', options: ['They are closed under complement', 'They are not closed under complement', 'Complements are context-free', 'Nothing'], answer: 0, why: 'For any DFA, flipping the accepting states of its completion gives a DFA for the complement.' },
    ],
  });
})();
