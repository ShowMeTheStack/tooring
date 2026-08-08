// Beyond acceptors: machines that write as they read (Moore machines print in their states, Mealy machines on
// their moves, here as a vending machine), a two-way DFA whose head walks back (with a space-time picture of
// its head), pattern search as a DFA built from the failure function, and a lexer generated from regexes
// that cuts a line of code into tokens by the longest match.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg;

  T.family({ id: 'reg-beyond', part: 'regular', order: 90, title: 'Transducers, two-way machines and applications', blurb: 'Finite machines that print as they read, that move their head both ways, that search text and that cut code into tokens.' });

  /** Merge moves per pair of states into one edge with the labels joined (kind 'x' keeps the labels as given) */
  const crossOk = (items) => items.map((it) => (it.kind === 'edge' && /\btr\b/.test(it.cls || '') ? Object.assign({}, it, { audit: 'edge-x' }) : it));
  const merged = (states, start, accept, moves, join) => {
    const by = new Map();
    for (const m of moves) { const k = m.from + '>' + m.to; if (!by.has(k)) by.set(k, { from: m.from, to: m.to, labels: [] }); if (!by.get(k).labels.includes(m.label)) by.get(k).labels.push(m.label); }
    return { kind: 'x', states: states.slice(), start, accept: accept || [], trans: [...by.values()].map((e) => ({ from: e.from, to: e.to, label: e.labels.join(join || '\n') })), pos: {} };
  };
  /** A list of symbols written compactly: runs of consecutive letters or digits become ranges */
  const ranges = (syms) => {
    const s = [...new Set(syms)].sort((a, b) => a.codePointAt(0) - b.codePointAt(0));
    const out = [];
    for (let i = 0; i < s.length;) {
      let j = i;
      while (j + 1 < s.length && s[j + 1].codePointAt(0) === s[j].codePointAt(0) + 1 && /[a-z0-9]/i.test(s[j + 1])) j++;
      out.push(j - i >= 2 ? s[i] + '–' + s[j] : s.slice(i, j + 1).join(', '));
      i = j + 1;
    }
    return out.join(', ').replace(/ /g, (m, k, str) => m);
  };
  const show = (c) => (c === ' ' ? '␣' : c);

  // ---- Moore and Mealy ----------------------------------------------------------------------------------------
  // a sweet costs 3; coins are 1 and 2. Outputs: · nothing, s a sweet, c a sweet and 1 change
  const MOORE = { states: ['c0', 'c1', 'c2', 'S', 'C'], inputs: ['1', '2'], start: 'c0', out: { c0: '·', c1: '·', c2: '·', S: 's', C: 'c' }, trans: [] };
  const moveMoore = { c0: ['c1', 'c2'], c1: ['c2', 'S'], c2: ['S', 'C'], S: ['c1', 'c2'], C: ['c1', 'c2'] };
  for (const q of MOORE.states) ['1', '2'].forEach((a, k) => MOORE.trans.push({ from: q, sym: a, to: moveMoore[q][k] }));
  const MEALY = { states: ['c0', 'c1', 'c2'], inputs: ['1', '2'], start: 'c0', trans: [
    { from: 'c0', sym: '1', to: 'c1', out: '·' }, { from: 'c0', sym: '2', to: 'c2', out: '·' }, { from: 'c1', sym: '1', to: 'c2', out: '·' },
    { from: 'c1', sym: '2', to: 'c0', out: 's' }, { from: 'c2', sym: '1', to: 'c0', out: 's' }, { from: 'c2', sym: '2', to: 'c0', out: 'c' }] };
  const OUTS = 'outputs:  · nothing,  s a sweet,  c a sweet and 1 change';
  const mooreDia = (m) => merged(m.states, m.start, [], m.trans.map((e) => ({ from: e.from, to: e.to, label: e.sym })), ', ');
  const mooreBoxes = (m) => Object.fromEntries(m.states.map((q) => [q, [q, 'out ' + m.out[q]]]));
  const mealyDia = (m) => merged(m.states, m.start, [], m.trans.map((e) => ({ from: e.from, to: e.to, label: e.sym + ' / ' + e.out })));
  T.topic({
    id: 'moore-mealy', family: 'reg-beyond', order: 10, title: 'Moore and Mealy machines: a vending machine',
    blurb: 'A sweet costs 3; the machine takes coins of 1 and 2. A Moore machine prints with its states, a Mealy machine prints on its moves, and each can be turned into the other.',
    inputs: [
      { id: 'how', kind: 'choice', label: 'Show', def: 'moore', options: [{ value: 'moore', label: 'the Moore machine running' }, { value: 'mealy', label: 'the Mealy machine running' }, { value: 'toMealy', label: 'Moore → Mealy' }, { value: 'toMoore', label: 'Mealy → Moore' }] },
      { id: 'w', kind: 'string', label: 'Coins', def: '1221', max: 8, alphabet: '12' },
    ],
    presets: [
      { label: 'Moore: coins 1 2 2 1', values: { how: 'moore', w: '1221' } },
      { label: 'Mealy: the same coins', values: { how: 'mealy', w: '1221' } },
      { label: 'No coins: Moore still prints once', values: { how: 'moore', w: '' } },
      { label: 'No coins: Mealy prints nothing', values: { how: 'mealy', w: '' } },
      { label: 'Moore → Mealy: move each output onto the arrows in', values: { how: 'toMealy', w: '22' } },
      { label: 'Mealy → Moore: split states by what they just printed', values: { how: 'toMoore', w: '22' } },
    ],
    counters: [{ id: 'coins', label: 'coins read' }, { id: 'printed', label: 'symbols printed' }],
    run(inp) {
      const F = new T.Frames(['coins', 'printed']);
      const w = [...inp.w];
      const legend = (x, y) => R.caption('legend', x, y, OUTS, 'title');
      if (inp.how === 'moore' || inp.how === 'mealy') {
        const moore = inp.how === 'moore';
        const M = moore ? MOORE : MEALY;
        const dia = moore ? mooreDia(M) : mealyDia(M);
        const boxes = moore ? mooreBoxes(M) : null;
        const pos = moore ? { c0: { x: 0, y: 0 }, c1: { x: 210, y: -120 }, c2: { x: 210, y: 120 }, S: { x: 440, y: -120 }, C: { x: 440, y: 120 } } : { c0: { x: 0, y: 0 }, c1: { x: 230, y: -130 }, c2: { x: 230, y: 130 } };
        const g0 = { items: crossOk(K.graph.draw(dia, { pos, boxes }).items) };
        const b = R.bounds(g0.items);
        const res = moore ? T.Transducer.runMoore(M, inp.w) : T.Transducer.runMealy(M, inp.w);
        const cw = 44, sx = b.x + b.w / 2 - Math.max(w.length + (moore ? 1 : 0), 1) * cw / 2 + 30, sy = b.y + b.h + 50;
        const tapes = (i, out) => K.string.draw({ text: w, pos: i, x: sx, y: sy, cw, label: 'coins', headText: i >= w.length ? 'end' : 'next' }).items.concat(K.string.draw({ text: [...out], x: sx, y: sy + 110, cw, label: 'printed', prefix: 'o', head: false, cls: (k) => (k === out.length - 1 ? 'hot' : '') }).items);
        const dt = { id: 'delta', kind: 'table', title: moore ? 'Moves and outputs' : 'Moves / outputs', corner: 'δ', colHead: ['1', '2'].concat(moore ? ['out'] : []), rowHead: M.states, rows: M.states.map((q) => ['1', '2'].map((a) => { const e = M.trans.find((t) => t.from === q && t.sym === a); return moore ? e.to : e.to + ' / ' + e.out; }).concat(moore ? [M.out[q]] : [])) };
        let out = moore ? M.out[M.start] : '';
        F.set('printed', out.length);
        F.add({ items: g0.items.concat(tapes(0, out), [legend(b.x + b.w / 2, b.y - 18)]), say: moore ? 'The Moore machine starts in c0 (no credit) and prints its output · at once, before any coin: a Moore machine prints one symbol more than it reads.' : 'The Mealy machine starts in c0 (no credit) and prints nothing yet: it prints only when it moves.', hl: { delta: ['0'] }, meta: { next: res.trace[1] && res.trace[1].to } });
        res.trace.slice(1).forEach((s, k) => {
          out += moore ? M.out[s.to] : s.out;
          F.count('coins').set('printed', out.length);
          const credit = (q) => ({ c0: 0, c1: 1, c2: 2, S: 0, C: 0 })[q];
          F.add({ items: crossOk(K.graph.draw(dia, { pos, boxes, active: [s.to], taken: [s.from + '>' + s.to] }).items).concat(tapes(k + 1, out), [legend(b.x + b.w / 2, b.y - 18)]), say: 'Coin ' + s.sym + ' in ' + s.from + ': go to ' + s.to + (moore ? ', whose output is ' + M.out[s.to] : ', printing ' + s.out + ' on the way') + ((moore ? M.out[s.to] : s.out) === 's' ? ': 3 is paid, out comes a sweet.' : (moore ? M.out[s.to] : s.out) === 'c' ? ': 4 is paid, a sweet and 1 change.' : ': credit ' + credit(s.to) + '.'), hl: { delta: [M.states.indexOf(s.from) + ',' + (+s.sym - 1)] }, meta: { next: res.trace[k + 2] && res.trace[k + 2].to } });
        });
        F.add({ items: crossOk(K.graph.draw(dia, { pos, boxes, good: [res.trace[res.trace.length - 1].state || res.trace[res.trace.length - 1].to] }).items).concat(tapes(w.length, out), [legend(b.x + b.w / 2, b.y - 18)]), say: 'Read ' + w.length + ' coin' + (w.length === 1 ? '' : 's') + ', printed ' + R.w(out) + ' (' + out.length + ' symbol' + (out.length === 1 ? '' : 's') + '). ' + (moore ? 'A Moore machine needs separate states S and C to print a sweet, so it has 5 states; the Mealy one needs only 3.' : 'The Mealy machine prints on the arrow into c0, so it needs no extra states for "just sold".'), mark: 'done' });
        return { frames: F.list, def: { sections: [{ id: 'kind', kind: 'math', title: moore ? 'A Moore machine' : 'A Mealy machine', text: moore ? '(Q, Σ, Δ, δ, λ, q₀)\nλ : Q → Δ   output of a state\noutput length = input length + 1' : '(Q, Σ, Δ, δ, λ, q₀)\nλ : Q × Σ → Δ   output of a move\noutput length = input length' }, dt] } };
      }
      // conversions, the source machine on the left and the result growing on the right
      if (inp.how === 'toMealy') {
        const conv = T.Transducer.mooreToMealy(MOORE).mealy;
        const pos = { c0: { x: 0, y: 0 }, c1: { x: 210, y: -120 }, c2: { x: 210, y: 120 }, S: { x: 440, y: -120 }, C: { x: 440, y: 120 } };
        const dia = mooreDia(MOORE);
        const done = [];
        const draw = (hot, o) => {
          const m = merged(MOORE.states, MOORE.start, [], MOORE.trans.map((e) => ({ from: e.from, to: e.to, label: done.includes(e.to) ? e.sym + ' / ' + MOORE.out[e.to] : e.sym })));
          return crossOk(K.graph.draw(m, Object.assign({ pos, boxes: Object.fromEntries(MOORE.states.map((q) => [q, done.includes(q) ? [q] : [q, 'out ' + MOORE.out[q]]])), hot: hot ? [hot] : [] }, o || {})).items);
        };
        F.add({ items: crossOk(K.graph.draw(dia, { pos, boxes: mooreBoxes(MOORE) }).items).concat([legend(220, -235)]), say: 'Start from the Moore machine: each state carries its output. To make a Mealy machine, print each state\'s output on the arrows that enter it instead.' });
        for (const q of MOORE.states) {
          done.push(q);
          const ins = MOORE.trans.filter((e) => e.to === q);
          F.add({ items: draw(q, { taken: ins.map((e) => e.from + '>' + q) }).concat([legend(220, -235)]), say: ins.length ? 'Every arrow into ' + q + ' (' + ins.map((e) => e.from + ' on ' + e.sym).join(', ') + ') now prints ' + MOORE.out[q] + ', the output of ' + q + '.' : 'Nothing enters ' + q + ', so its output simply disappears.', meta: { q } });
        }
        F.add({ items: draw(null).concat([legend(220, -235)]), say: 'The Mealy machine prints the same symbols at the same moments, except the very first: the start state\'s output ' + MOORE.out.c0 + ' had no arrow to ride on. (S and C now act exactly like c0 and could be merged, giving ' + conv.states.length + ' − 2 = 3 states.)', mark: 'done' });
        return { frames: F.list, def: { sections: [{ id: 'rule', kind: 'math', title: 'Moore → Mealy', text: 'λ′(q, a) = λ(δ(q, a))\nsame states, same moves' }] } };
      }
      const conv = T.Transducer.mealyToMoore(MEALY, '·');
      const mo = conv.moore;
      const mpos = { c0: { x: -360, y: 0 }, c1: { x: -130, y: -130 }, c2: { x: -130, y: 130 } };
      const left = K.graph.draw(mealyDia(MEALY), { pos: mpos, prefix: 'ml' }).items;
      const rpos = K.graph.layout(Object.assign(mooreDia(mo), { kind: 'x' }), { boxes: mooreBoxes(mo) }).pos;
      const lb = R.bounds(left);
      let minX = Infinity; for (const q in rpos) minX = Math.min(minX, rpos[q].x);
      for (const q in rpos) rpos[q] = { x: rpos[q].x - minX + lb.x + lb.w + 120, y: rpos[q].y };
      const made = [];
      const right = (hot) => {
        const m = merged(made, mo.start, [], mo.trans.filter((e) => made.includes(e.from) && made.includes(e.to)).map((e) => ({ from: e.from, to: e.to, label: e.sym })), ', ');
        return crossOk(K.graph.draw(m, { pos: rpos, boxes: Object.fromEntries(made.map((q) => [q, [q, 'out ' + mo.out[q]]])), hot: hot ? [hot] : [], prefix: 'mo' }).items);
      };
      const cap = [R.caption('capL', lb.x + lb.w / 2, lb.y - 20, 'Mealy', 'title'), R.caption('capR', rpos[mo.start].x + 60, lb.y - 20, 'Moore', 'title')];
      F.add({ items: left.concat(cap), say: 'Start from the Mealy machine: outputs sit on its moves. A Moore state must know what to print, so split each state by the output on the move that entered it.' });
      for (const s of conv.trace) {
        made.push(s.state);
        F.add({ items: left.concat(cap, right(s.state)), say: s.say, meta: { made: s.state } });
      }
      F.add({ items: left.concat(cap, right(null)), say: 'The Moore machine has ' + mo.states.length + ' states for the Mealy machine\'s ' + MEALY.states.length + ': c0 is reached printing ·, s or c, and must remember which. It prints one extra symbol first, its start output ·.', mark: 'done' });
      return { frames: F.list, def: { sections: [{ id: 'rule', kind: 'math', title: 'Mealy → Moore', text: 'states: pairs q/o, "in q, having just printed o"\nδ′(q/o, a) = δ(q, a) / λ(q, a)\nλ′(q/o) = o' }] } };
    },
    predict: [
      { at: (f, i, fr) => i === 1 && f.meta && f.meta.next, once: true, pick: 'item', ask: 'Which state comes after the next coin? Click it.', answer: (fr, i) => 'g:s:' + fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.made === 'c0/s', once: true, pick: 'option', options: ['c0/·', 'c0/s', 'c0/c', 'c1/s'], ask: 'Paying 3 from c1 (coin 2) enters c0 printing s. Which Moore state is that?', answer: () => 'c0/s', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A Moore machine reads 5 symbols. How many does it print?', options: ['4', '5', '6', 'It depends'], answer: 2, why: 'It prints the start state\'s output before reading, then one per state entered.' },
      { q: 'Where does a Mealy machine keep its outputs?', options: ['On its states', 'On its moves', 'On the tape', 'In its accepting states'], answer: 1, why: 'The output depends on the state and the symbol just read: λ(q, a).' },
      { q: 'Why does the Mealy vending machine need fewer states?', options: ['It is nondeterministic', 'The moment of the sale is printed on the move, so no state has to mean "just sold"', 'It accepts fewer coins', 'It has no start state'], answer: 1, why: 'A Moore machine must enter a special state to print a sweet; a Mealy machine prints it while moving back to c0.' },
      { q: 'Turning a Mealy machine into a Moore machine can multiply the states by at most…', options: ['2', 'the number of output symbols', 'the number of input symbols', 'nothing: never more states'], answer: 1, why: 'Each state splits into at most one copy per output it can be entered with.' },
      { q: 'Do these machines accept or reject?', options: ['Accept when the output is non-empty', 'Neither: they compute an output string, they are transducers', 'Reject on an empty input', 'Accept in state c0'], answer: 1, why: 'They have no accepting states; their job is to translate the input into an output.' },
    ],
  });

  // ---- two-way DFA ------------------------------------------------------------------------------------------------
  const TW = () => T.TwoWay;
  const BOUNCE = { name: 'a machine that rocks back and forth for ever', states: ['p', 'q', 'yes'], alphabet: ['a', 'b'], start: 'p', accept: 'yes', reject: 'no',
    delta: [{ from: 'p', sym: '⊢', to: 'p', move: 'R' }, { from: 'p', sym: 'a', to: 'q', move: 'R' }, { from: 'q', sym: 'a', to: 'p', move: 'L' }, { from: 'q', sym: 'b', to: 'yes', move: 'R' }, { from: 'p', sym: 'b', to: 'p', move: 'R' }, { from: 'q', sym: '⊣', to: 'yes', move: 'L' }] };
  const RUNAWAY = { name: 'a machine that forgets to stop at the end marker', states: ['go'], alphabet: ['a', 'b'], start: 'go', accept: 'yes', reject: 'no',
    delta: [{ from: 'go', sym: '⊢', to: 'go', move: 'R' }, { from: 'go', sym: 'a', to: 'go', move: 'R' }, { from: 'go', sym: 'b', to: 'go', move: 'R' }, { from: 'go', sym: '⊣', to: 'go', move: 'R' }] };
  const twoMachines = () => ({ third: TW().examples.thirdFromEnd, twoPass: TW().examples.twoPass, bounce: BOUNCE, runaway: RUNAWAY });
  T.topic({
    id: 'twoway', family: 'reg-beyond', order: 20, title: 'A two-way DFA walks back',
    blurb: 'A DFA whose head may move left as well as right, between end markers ⊢ and ⊣. It can re-read its input, yet it still accepts only regular languages. Watch the head\'s path through time.',
    inputs: [
      { id: 'ex', kind: 'choice', label: 'Machine', def: 'third', options: [{ value: 'third', label: 'third symbol from the end is a' }, { value: 'twoPass', label: 'even a\'s and odd b\'s, in two passes' }, { value: 'bounce', label: 'a machine that can loop' }, { value: 'runaway', label: 'a machine that falls off the end' }] },
      { id: 'w', kind: 'string', label: 'Input', def: 'babba', max: 7, alphabet: 'ab' },
    ],
    presets: [
      { label: 'Third from the end: babba', values: { ex: 'third', w: 'babba' } },
      { label: 'Third from the end: bb is too short', values: { ex: 'third', w: 'bb' } },
      { label: 'Two passes: abab', values: { ex: 'twoPass', w: 'abab' } },
      { label: 'Loops for ever on aa (a repeated configuration)', values: { ex: 'bounce', w: 'aa' } },
      { label: 'Falls off the right end', values: { ex: 'runaway', w: 'ab' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'turns', label: 'turns' }],
    run(inp) {
      const M = twoMachines()[inp.ex];
      const res = TW().run(M, inp.w, 200);
      const states = M.states.concat(M.states.includes(M.reject) || !M.delta.some((e) => e.to === M.reject) ? [] : [M.reject]);
      const dia = merged(states, M.start, [M.accept], [], '\n');
      // one edge per pair, symbols grouped by direction: "a, b →R"
      const groups = new Map();
      for (const e of M.delta) { const k = e.from + '>' + e.to + '>' + e.move; if (!groups.has(k)) groups.set(k, { from: e.from, to: e.to, move: e.move, syms: [] }); groups.get(k).syms.push(e.sym); }
      const lab = new Map();
      for (const g of groups.values()) { const k = g.from + '>' + g.to; lab.set(k, (lab.has(k) ? lab.get(k) + '\n' : '') + g.syms.join(',') + ' ' + (g.move === 'L' ? '←' : '→')); }
      dia.trans = [...lab.entries()].map(([k, label]) => ({ from: k.split('>')[0], to: k.split('>')[1], label }));
      const pos = K.graph.layout(dia).pos;
      const g0 = K.graph.draw(dia, { pos });
      const gb = R.bounds(g0.items);
      const tape = res.tape;
      const cw = 44, tx = gb.x + gb.w / 2 - (tape.length * cw) / 2, ty = gb.y + gb.h + 50;
      const rowH = Math.max(12, Math.min(22, 300 / Math.max(1, res.trace.length)));
      const st0 = ty + 44 + 46;
      const F = new T.Frames(['steps', 'turns']);
      const pts = [];
      let turns = 0, lastDir = null;
      const spacetime = () => {
        const out = [R.caption('time', tx - 14, st0 + 4, 'time ↓', 'title', 'end')];
        pts.forEach((p, k) => {
          out.push({ key: 'st:' + k, kind: 'token', x: tx + p * cw + cw / 2, y: st0 + k * rowH, r: 4.5, cls: k === pts.length - 1 ? '' : 'act', audit: 'ignore' });
          if (k) out.push({ key: 'sl:' + k, kind: 'line', x1: tx + pts[k - 1] * cw + cw / 2, y1: st0 + (k - 1) * rowH, x2: tx + p * cw + cw / 2, y2: st0 + k * rowH, cls: 'hot', audit: 'ignore' });
        });
        return out;
      };
      const scene = (s, g) => K.graph.draw(dia, Object.assign({ pos }, g)).items.concat(K.string.draw({ text: tape, pos: Math.max(0, Math.min(tape.length - 1, s.head)), x: tx, y: ty, cw, consumed: false, headText: s.state || s.to, label: 'tape' }).items, spacetime());
      for (const s of res.trace) {
        if (s.kind === 'start') { pts.push(0); F.add({ items: scene({ head: 0, state: s.state }, { active: [s.state], startHot: true }), say: 'The input ' + R.w(inp.w) + ' sits between the end markers ⊢ and ⊣. The machine starts in ' + s.state + ' with its head on ⊢. Below the tape, time runs downwards: a dot for each step.' }); continue; }
        if (s.kind === 'move') {
          if (lastDir && lastDir !== s.dir) turns++;
          lastDir = s.dir;
          F.count('steps').set('turns', turns);
          if (s.head >= 0 && s.head < tape.length) pts.push(s.head);
          F.add({ items: scene({ head: s.head, state: s.to }, { active: [s.to], taken: [s.from + '>' + s.to] }), say: s.say + (s.dir === 'L' ? ' The head goes back over input it has already read.' : ''), hl: { delta: [String(M.delta.findIndex((e) => e.from === s.from && e.sym === s.sym))] }, meta: { dir: s.dir, next: s.to } });
          continue;
        }
        if (s.kind === 'halt') {
          const st = s.state;
          F.add({ items: scene({ head: s.head, state: st }, s.accepted ? { good: [st] } : { bad: states.includes(st) ? [st] : [] }), say: s.say + (s.loop ? ' Since the machine is deterministic, the same configuration will always lead to the same steps again.' : '') + (s.accepted ? ' ' + R.w(inp.w) + ' is accepted.' : ''), mark: s.accepted ? 'accepted' : 'rejected', meta: { verdict: s.accepted ? 'Accept' : 'Reject' } });
        }
      }
      return { frames: F.list, def: { sections: [{ id: 'm', kind: 'math', title: M.name, text: 'start ' + M.start + ', accept ' + M.accept + ', reject ' + M.reject + '\ntape ⊢ w ⊣, head starts on ⊢' }, { id: 'delta', kind: 'table', title: 'Moves', colHead: ['state', 'reads', 'goes to', 'moves'], rows: M.delta.map((e) => [e.from, e.sym, e.to, e.move]) }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.dir === 'L' && !(f.meta && f.meta.dir === 'L'), once: true, pick: 'option', options: ['Left', 'Right'], ask: 'Which way will the head move next?', answer: () => 'Left', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the machine accept?', answer: (fr) => fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Can a two-way DFA accept a language that no ordinary DFA accepts?', options: ['Yes, aⁿbⁿ', 'No: two-way DFAs accept exactly the regular languages', 'Only with a stack', 'Only on long inputs'], answer: 1, why: 'Moving back adds convenience and can save states, but never power: every two-way DFA has an equivalent one-way DFA.' },
      { q: 'Why are the end markers ⊢ and ⊣ there?', options: ['Decoration', 'So the machine knows where the input starts and ends and can turn round there', 'To mark accepted strings', 'They count symbols'], answer: 1, why: 'Without them the head could not tell it had reached an end of the input.' },
      { q: 'The machine is in state q on cell 3 for the second time. What follows?', options: ['It will accept', 'It loops for ever: being deterministic, it repeats the same steps', 'It moves to the next cell', 'Nothing in particular'], answer: 1, why: 'A configuration (state, head position) determines everything after it, so a repeat means a cycle.' },
      { q: 'How many different configurations has a two-way DFA with k states on an input of length n?', options: ['k', 'k(n + 2)', 'kⁿ', '2ⁿ'], answer: 1, why: 'A state and a head position among the n + 2 cells: so a halting run takes at most k(n + 2) steps.' },
    ],
  });

  // ---- KMP ------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'kmp', family: 'reg-beyond', order: 30, title: 'Searching text with a DFA',
    blurb: 'To find a pattern in a text, a DFA remembers the longest part of the pattern the text has just matched. When a symbol breaks the match, it falls back to the longest border: the failure function.',
    inputs: [
      { id: 'p', kind: 'string', label: 'Pattern', def: 'abab', min: 1, max: 5, alphabet: 'abc' },
      { id: 't', kind: 'string', label: 'Text', def: 'aabababb', min: 1, max: 11, alphabet: 'abc' },
    ],
    presets: [
      { label: 'abab in aabababb: overlapping matches', values: { p: 'abab', t: 'aabababb' } },
      { label: 'aba in ababa', values: { p: 'aba', t: 'ababa' } },
      { label: 'aab: the fall back keeps an a', values: { p: 'aab', t: 'aaab' } },
      { label: 'No match at all', values: { p: 'abc', t: 'abababab' } },
      { label: 'A pattern of one letter', values: { p: 'b', t: 'abba' } },
    ],
    counters: [{ id: 'read', label: 'symbols read' }, { id: 'matches', label: 'matches' }],
    run(inp) {
      const p = [...inp.p], t = [...inp.t];
      const al = [...new Set(p.concat(t))].sort();
      const kd = T.KMP.dfa(inp.p, al);
      const fa = kd.fa;
      const fail = kd.fail;
      const pos = R.row(fa.states, 0, 0, 130);
      const dia = R.dia(fa);
      const F = new T.Frames(['read', 'matches']);
      const g0 = K.graph.draw(dia, { pos });
      const gb = R.bounds(g0.items);
      const tb = (j) => K.table.draw({ rows: [p.map((_, k) => p.slice(0, k + 1).join('')), p.map((_, k) => (j === undefined || k <= j ? String(fail[k]) : ''))], rowHead: ['prefix', 'border'], x: gb.x, y: gb.y - 120, mono: true, size: 15, ch: 36, hot: j !== undefined && j >= 0 ? [[1, j]] : [] });
      const tbBox = R.bounds(tb().items);
      const cw = 44, sy = gb.y + gb.h + 50, sx = gb.x + gb.w / 2 - (t.length * cw) / 2;
      const dt = R.delta(fa);
      const failSec = { id: 'fail', kind: 'table', title: 'The failure function', colHead: p.map((_, k) => p.slice(0, k + 1).join('')), rowHead: ['border'], rows: [fail.map(String)] };
      void tbBox;
      F.add({ items: tb(-1).items, say: 'First the failure function: for each prefix of ' + inp.p + ', the length of its longest border, a proper beginning that is also an ending. It says how much of a match survives a mismatch.' });
      p.forEach((_, j) => { if (j) F.add({ items: tb(j).items, say: 'border(' + p.slice(0, j + 1).join('') + ') = ' + fail[j] + (fail[j] ? ': ' + p.slice(0, fail[j]).join('') + ' both begins and ends it.' : ': no proper beginning is also an ending.'), hl: { fail: ['0,' + j] } }); });
      F.add({ items: tb(p.length - 1).items.concat(K.graph.draw(dia, { pos, enter: 'grow' }).items), say: 'The DFA: state ' + 'ε, ' + fa.states.slice(1).join(', ') + ' means "the text so far ends with this much of the pattern". Forward arrows extend the match; the others fall back, as the border would, to the longest prefix that still fits.' });
      const run = R.runDFA(fa, inp.t);
      const found = [];
      const brs = () => found.map((s, k) => ({ id: 'm' + s, from: s, to: s + p.length, text: 'at ' + (s + 1), cls: k % 2 ? 'z' : 'x', level: k % 2 }));
      for (let i = 0; i <= t.length; i++) {
        const q = run.path[i];
        if (i > 0) { F.count('read'); if (q === fa.accept[0]) { found.push(i - p.length); F.count('matches'); } }
        const hit = i > 0 && q === fa.accept[0];
        const back = i > 0 && [...q].length <= [...run.path[i - 1]].length && run.path[i - 1] !== 'ε' || (i > 0 && q === 'ε' && run.path[i - 1] !== 'ε');
        F.add({ items: tb(p.length - 1).items.concat(K.graph.draw(dia, { pos, active: [q], taken: i ? [run.path[i - 1] + '>' + q] : [], good: hit ? [q] : [] }).items, K.string.draw({ text: t, pos: i, x: sx, y: sy, cw, label: 'text', sub: true, headText: i >= t.length ? 'end' : 'next', brackets: brs(), cls: (k) => (found.some((s) => k >= s && k < s + p.length) ? 'good' : '') }).items), say: i === 0 ? 'Now read the text ' + inp.t + ' from ε, one symbol at a time, never going back.' : 'Read ' + t[i - 1] + ': ' + run.path[i - 1] + ' → ' + q + (hit ? '. The whole pattern has matched, starting at position ' + (i - p.length + 1) + '. The DFA keeps going, so overlapping matches are found too.' : back ? ': the match breaks, and the longest piece still matching is ' + q + '.' : '.'), hl: i ? { delta: [dt.rc(run.path[i - 1], t[i - 1])] } : {}, meta: { next: run.path[i + 1], back: i < t.length && run.path[i + 1] !== undefined && [...run.path[i + 1]].length <= [...q].length && q !== 'ε' } });
      }
      F.add({ items: tb(p.length - 1).items.concat(K.graph.draw(dia, { pos, good: fa.accept }).items, K.string.draw({ text: t, x: sx, y: sy, cw, label: 'text', sub: true, head: false, brackets: brs(), cls: (k) => (found.some((s) => k >= s && k < s + p.length) ? 'good' : '') }).items), say: found.length ? R.plural(found.length, 'match', 'matches') + ', starting at position' + (found.length > 1 ? 's ' : ' ') + found.map((s) => s + 1).join(', ') + ', found with exactly one step per symbol of the text.' : 'No match: ' + inp.p + ' does not occur in ' + inp.t + ', and the DFA read each symbol once to know it.', mark: 'done', meta: { n: found.length } });
      return { frames: F.list, def: { sections: [failSec, dt.section] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.back && f.meta.next !== undefined && i > 2, once: true, pick: 'item', ask: 'The next symbol breaks the match. Which state does the DFA fall back to? Click it.', answer: (fr, i) => 'g:s:' + fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === 1, once: true, pick: 'option', options: (fr) => R.numberOptions(fr[fr.length - 1].meta.n), ask: 'How many times will the pattern be found in the text (overlaps count)?', answer: (fr) => String(fr[fr.length - 1].meta.n), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'How many states has the search DFA for a pattern of length m?', options: ['m', 'm + 1', '2m', '2ᵐ'], answer: 1, why: 'One per prefix, from ε to the whole pattern.' },
      { q: 'What is the border of abab?', options: ['ε', 'a', 'ab', 'aba'], answer: 2, why: 'ab is the longest proper beginning that is also an ending.' },
      { q: 'Why does the search never move back in the text?', options: ['It skips symbols', 'The state already records everything about the text that a future match can use', 'It reads the text twice', 'It only finds the first match'], answer: 1, why: 'The longest matched prefix is all that matters for what comes next, and the DFA carries exactly that.' },
      { q: 'How many steps does the search take on a text of length n?', options: ['n', 'n × m', 'n²', 'm'], answer: 0, why: 'One move per symbol of the text, once the DFA is built.' },
      { q: 'After a full match, why does the DFA not go back to ε?', options: ['It does', 'Matches can overlap: the border of the pattern may start the next one', 'To save a state', 'Because the text ends'], answer: 1, why: 'In ababa, the second aba starts inside the first.' },
    ],
  });

  // ---- lexer ------------------------------------------------------------------------------------------------------
  const RULES = [
    { name: 'IF', regex: 'if' }, { name: 'ID', regex: '[a-z]+' }, { name: 'NUM', regex: '[0-9]+' },
    { name: 'ARROW', regex: '<->' }, { name: 'OP', regex: '<|<=' }, { name: 'WS', regex: '\\ +', skip: true },
  ];
  const RULES_ID_FIRST = [RULES[1], RULES[0]].concat(RULES.slice(2));
  T.topic({
    id: 'lexer', family: 'reg-beyond', order: 40, title: 'A lexer built from regular expressions',
    blurb: 'Each kind of token is a regular expression. Joined into one DFA, they cut a line of code into tokens: take the longest match, and when two rules match equally, the one listed first.',
    inputs: [
      { id: 'line', kind: 'string', spaces: true, label: 'A line of code', def: 'if a<=12', max: 14 },
      { id: 'order', kind: 'choice', label: 'Rule order', def: 'if', options: [{ value: 'if', label: 'IF before ID' }, { value: 'id', label: 'ID before IF' }] },
    ],
    presets: [
      { label: 'if a<=12', values: { line: 'if a<=12', order: 'if' } },
      { label: 'Backing up: x<-y', values: { line: 'x<-y', order: 'if' } },
      { label: 'Longest match: iff is a name', values: { line: 'if iff', order: 'if' } },
      { label: 'Rules in the other order: if becomes a name', values: { line: 'if b', order: 'id' } },
      { label: 'A character no rule allows', values: { line: 'c1 # d', order: 'if' } },
    ],
    check: (inp) => (inp.line.length ? null : 'Line: type a few characters'),
    counters: [{ id: 'tokens', label: 'tokens' }, { id: 'scanned', label: 'characters scanned' }, { id: 'backed', label: 'backed up' }],
    run(inp) {
      const rules = inp.order === 'id' ? RULES_ID_FIRST : RULES;
      const lx = T.Lexer.build(rules);
      const d = lx.dfa;
      const del = T.FA._deltaMap(d);
      // edges labelled with ranges, states tagged with their token
      const moves = [];
      const by = new Map();
      for (const e of d.trans) { const k = e.from + '>' + e.to; if (!by.has(k)) by.set(k, []); by.get(k).push(e.sym); }
      for (const [k, syms] of by) moves.push({ from: k.split('>')[0], to: k.split('>')[1], label: ranges(syms.map(show)) });
      const dia = { kind: 'x', states: d.states.slice(), start: d.start, accept: d.accept.slice(), trans: moves, pos: {} };
      const boxes = Object.fromEntries(d.states.map((q) => [q, lx.token[q] ? [lx.token[q]] : [q === d.start ? 'start' : '·']]));
      const pos = K.graph.layout(dia, { boxes, mode: 'layered', gapX: 150, gapY: 120 }).pos;
      const crossOk = (items) => items.map((it) => (it.kind === 'edge' && /\btr\b/.test(it.cls || '') ? Object.assign({}, it, { audit: 'edge-x' }) : it));
      const G = (o) => crossOk(K.graph.draw(dia, Object.assign({ pos, boxes }, o || {})).items);
      const gb = R.bounds(G());
      const ruleNote = R.note('rules', { x: gb.x - 230, y: gb.y, title: 'rules, in order', lines: rules.map((r) => r.name.padEnd(7, '\u00a0') + RE_show(r.regex) + (r.skip ? '  skip' : '')), mono: true, size: 14 });
      const s = [...inp.line];
      const cw = 38, sx = gb.x + gb.w / 2 - (s.length * cw) / 2, sy = Math.max(gb.y + gb.h, ruleNote.box.y + ruleNote.box.h) + 50;
      const cuts = [];
      const line = (o) => K.string.draw({ text: s.map(show), pos: o.pos, x: sx, y: sy, cw, label: 'line', head: o.pos === null ? false : 'below', headText: o.headText || 'scan', headCls: o.headCls, brackets: cuts.map((c, k) => ({ id: 't' + c.start, from: c.start, to: c.end, text: c.name, cls: c.skip ? 'z' : c.error ? 'y' : 'x', level: k % 2 })), cls: (k) => (o.lit && k >= o.lit[0] && k < o.lit[1] ? 'hot' : cuts.some((c) => k >= c.start && k < c.end) ? 'read' : '') }).items;
      const F = new T.Frames(['tokens', 'scanned', 'backed']);
      const base = () => ruleNote.items;
      F.add({ items: base().concat(G(), line({ pos: 0, headText: 'start' })), say: 'The rules become one DFA: Thompson NFAs joined by ε, determinised, then minimised. Each accepting state is labelled with the token it ends; where two rules end together, the one listed first wins (' + rules.slice(0, 2).map((r) => r.name).join(' before ') + ').' });
      let pos0 = 0;
      while (pos0 < s.length) {
        let q = d.start, i = pos0, last = null;
        F.add({ items: base().concat(G({ active: [q] }), line({ pos: pos0, lit: [pos0, pos0] })), say: 'A new token starts at position ' + (pos0 + 1) + ', with ' + show(s[pos0]) + '. Run the DFA from its start as far as it will go.', meta: { from: pos0 } });
        while (i < s.length) {
          const to = del.get(q) && del.get(q).get(s[i]);
          if (to === undefined) break;
          const p = q;
          q = to; i++;
          F.count('scanned');
          if (lx.token[q]) last = { end: i, name: lx.token[q] };
          F.add({ items: base().concat(G({ active: [q], taken: [p + '>' + q] }), line({ pos: i, lit: [pos0, i] })), say: 'Read ' + show(s[i - 1]) + ': ' + (lx.token[q] ? 'this state ends ' + (/^[AEIOU]/.test(lx.token[q]) ? 'an ' : 'a ') + lx.token[q] + ', so ' + s.slice(pos0, i).join('') + ' would do as a token; remember it and keep going for a longer one.' : 'no token ends here yet; keep going.'), meta: { next: i < s.length ? del.get(q) && del.get(q).get(s[i]) : undefined } });
        }
        const stopWhy = i < s.length ? 'There is no move on ' + show(s[i]) : 'The line is used up';
        if (!last) {
          cuts.push({ start: pos0, end: pos0 + 1, name: '?', error: true });
          F.add({ items: base().concat(G({ bad: [d.start] }), line({ pos: pos0 + 1, lit: [pos0, pos0 + 1], headCls: 'bad', headText: 'error' })), say: stopWhy + ' and no token was ever completed: no rule can start with ' + show(s[pos0]) + '. Report an error and skip that one character.', meta: { error: true } });
          pos0++;
          continue;
        }
        const backed = i - last.end;
        F.count('backed', backed);
        const rule = rules.find((r) => r.name === last.name);
        cuts.push({ start: pos0, end: last.end, name: last.name, skip: !!rule.skip });
        if (!rule.skip) F.count('tokens');
        F.add({ items: base().concat(G({ good: [q].filter((x) => lx.token[x] === last.name) }), line({ pos: last.end, lit: [pos0, last.end] })), say: stopWhy + '. The longest match was ' + JSON.stringify(s.slice(pos0, last.end).join('')) + (backed ? ', ending ' + backed + ' character' + (backed > 1 ? 's' : '') + ' before the scan stopped, so back up' : '') + ': ' + (rule.skip ? 'it is ' + last.name + ', which is skipped.' : 'cut ' + (/^[AEIOU]/.test(last.name) ? 'an ' : 'a ') + last.name + ' token.'), meta: { cut: last.name } });
        pos0 = last.end;
      }
      const toks = cuts.filter((c) => !c.skip && !c.error);
      F.add({ items: base().concat(G(), line({ pos: null })), say: 'Tokens: ' + (toks.length ? toks.map((c) => c.name + ' ' + s.slice(c.start, c.end).join('')).join(', ') : 'none') + (cuts.some((c) => c.error) ? '; with ' + cuts.filter((c) => c.error).length + ' error(s) reported.' : '.') + ' A parser now works on these instead of single characters.', mark: 'done' });
      return { frames: F.list, def: { sections: [{ id: 'rules', kind: 'math', title: 'The rules', text: rules.map((r) => r.name + ' = ' + RE_show(r.regex) + (r.skip ? '   (skipped)' : '')).join('\n') }, { id: 'how', kind: 'text', title: 'Two tie-breaks', text: 'Longest match: keep scanning while the DFA can move, then cut at the last place a token ended. Priority: when one string ends several rules, the rule listed first names the token.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.cut, once: true, pick: 'option', options: ['IF', 'ID', 'NUM', 'OP', 'ARROW', 'WS'], ask: 'The scan has stopped. Which token is cut?', answer: (fr, i) => fr[i + 1].meta.cut, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => f.meta && f.meta.next && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.next !== undefined && i > 2, once: true, pick: 'item', ask: 'Which DFA state comes after the next character? Click it.', answer: (fr, i) => 'g:s:' + fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'The line has iff. Why is it one identifier and not IF followed by f?', options: ['IF is listed first', 'Longest match: the scan prefers the longest token, iff', 'Identifiers always win', 'f is not a token'], answer: 1, why: 'Priority only settles ties between rules matching the same string; length comes first.' },
      { q: 'The string if matches both IF and ID. Which wins?', options: ['ID, it is longer', 'The rule listed first', 'Neither: an error', 'Both tokens are produced'], answer: 1, why: 'Both match exactly if; the tie is broken by the order of the rules.' },
      { q: 'On x<-y the scan reads <- and then fails. What does it do?', options: ['Reports an error at <', 'Backs up to the last place a token ended, cutting <', 'Skips the rest of the line', 'Waits for >'], answer: 1, why: '< alone was a complete OP, so the lexer falls back to it and starts again at -.' },
      { q: 'Why build one DFA for all the rules instead of trying each regex in turn?', options: ['It is the only way', 'One pass of one DFA finds every rule\'s matches at once, in time proportional to the characters read', 'Regexes cannot be tested separately', 'To save memory'], answer: 1, why: 'The combined DFA tracks all rules simultaneously; the subset construction does the bookkeeping once, in advance.' },
    ],
  });
  function RE_show(r) { return r.replace(/\\ /g, '␣'); }
})();
