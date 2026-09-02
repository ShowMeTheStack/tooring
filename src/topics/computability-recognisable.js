// Recognisable versus decidable. Dovetailing: a recogniser for "this program accepts some input" cannot try
// the inputs one at a time (the first endless run would stall it), so it gives every input a turn, one more
// step each, sweeping a diagonal across the grid of inputs × steps. And the two-sided race: a recogniser for
// L and one for its complement, run in turns, one of which must stop, which is why a language is decidable
// exactly when it and its complement are both recognisable, and why the complement of A_TM is not.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom;

  T.family({ id: 'recognisable', part: 'computability', order: 30, title: 'Recognisable and co-recognisable', blurb: 'A recogniser says yes to every member but may run forever on the rest. Dovetailing keeps endless runs from blocking, and running a language and its complement side by side gives a decider.' });

  const wrap = (text, width) => { const words = String(text).split(' '), out = []; let cur = ''; for (const w of words) { const t = cur ? cur + ' ' + w : w; if (cur && Geo.textWidth(t, 15) > width) { out.push(cur); cur = w; } else cur = t; } if (cur) out.push(cur); return out; };
  const card = (key, x, y, w, text, cls, extra) => { const lines = wrap(text, w - 28); return Object.assign({ key, kind: 'cell', x, y, w, h: lines.length * 21 + 18, lines, size: 15, cls: 'card ' + (cls || ''), rx: 12 }, extra || {}); };


  /** Give each run of frames with the same phase one camera, so a new picture is framed for itself */
  const phase = (F, name) => { for (const f of F.list) if (f.phase === undefined) f.phase = name; };
  const phaseViews = (frames) => { const by = new Map(); for (const f of frames) { const b = T.stageBounds(f.items); if (b) by.set(f.phase, by.has(f.phase) ? T.geom.union([by.get(f.phase), b]) : b); } for (const f of frames) if (by.has(f.phase)) f.view = by.get(f.phase); return frames; };

  // ---------------------------------------------------------------------------------------------------
  // Dovetailing
  // ---------------------------------------------------------------------------------------------------
  const INPUTS = ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb'];
  const show = (w) => (w === '' ? 'ε' : w);
  // each program: what it does on w, as [verdict, steps] (Infinity steps for running forever)
  const PROGS = {
    bb: { text: 'loops on inputs starting with a; accepts inputs ending in bb after |w| + 1 steps; rejects the rest after |w| + 2 steps', act: (w) => (w[0] === 'a' ? ['loop', Infinity] : /bb$/.test(w) ? ['accept', w.length + 1] : ['reject', w.length + 2]) },
    slowb: { text: 'accepts b after 6 steps and runs forever on everything else', act: (w) => (w === 'b' ? ['accept', 6] : ['loop', Infinity]) },
    ba: { text: 'rejects ε at once, runs forever on a, b and aa, accepts ba after 2 steps', act: (w) => (w === '' ? ['reject', 1] : w === 'ba' ? ['accept', 2] : w.length <= 2 && w !== 'ab' && w !== 'bb' ? ['loop', Infinity] : ['reject', 3]) },
    eps: { text: 'accepts ε after 2 steps and runs forever on everything else', act: (w) => (w === '' ? ['accept', 2] : ['loop', Infinity]) },
    never: { text: 'runs forever on every input', act: () => ['loop', Infinity] },
  };
  const STAGES = 9;

  T.topic({
    id: 'rec-dovetail', family: 'recognisable', order: 10, title: 'Dovetailing',
    blurb: 'To recognise "P accepts at least one input", trying the inputs one by one gets stuck on the first endless run. Give every input one more step in turn instead, sweeping a diagonal across inputs × steps.',
    inputs: [
      { id: 'p', kind: 'choice', label: 'Program P', def: 'bb', options: Object.keys(PROGS).map((k) => ({ value: k, label: PROGS[k].text.length > 60 ? PROGS[k].text.slice(0, 58) + '…' : PROGS[k].text })) },
    ],
    presets: [
      { label: 'Stuck on a, accepts bb', values: { p: 'bb' } },
      { label: 'Only b, slowly', values: { p: 'slowb' } },
      { label: 'Loops early, accepts ba', values: { p: 'ba' } },
      { label: 'The very first input works', values: { p: 'eps' } },
      { label: 'Accepts nothing: runs forever', values: { p: 'never' } },
    ],
    counters: [{ id: 'stage', label: 'stage' }, { id: 'steps', label: 'steps simulated' }],
    run(inp) {
      const P = PROGS[inp.p];
      const act = INPUTS.map((w) => P.act(w));
      const n = INPUTS.length, S = STAGES;
      const grid = INPUTS.map(() => new Array(S).fill(''));
      const F = new T.Frames(['stage', 'steps']);
      const MB = K.mbox;
      const LINES = ['On input ⟨P⟩:', 'For stage k = 1, 2, 3, …:', '  give each of the first k inputs one more step of P;', '  if any run accepts, accept.'];
      const scene = (o) => {
        o = o || {};
        const mb = MB.draw({ prefix: 'R', title: 'Recogniser for {⟨P⟩ : P accepts some input}', lines: LINES, hot: o.lines || [], cls: 'r0', x: 0, y: 0, input: '⟨P⟩', outs: [{ id: 'a', text: 'accept', cls: 'good', lit: !!o.found }] });
        const y0 = mb.box.h + 50;
        const tb = K.table.draw({ prefix: 'dv', x: 0, y: y0, rows: grid, rowHead: INPUTS.map(show), colHead: Array.from({ length: S }, (_, j) => 'step ' + (j + 1)), corner: 'input', cw: 52, ch: 36,
          cls: (r, c, v) => [v === '✓' ? 'good' : v === '✗' ? 'bad' : v === '·' ? 'mark' : '', o.hot && o.hot.has(r + ',' + c) ? 'act' : '', o.rowHot === r ? 'hot' : ''].filter(Boolean).join(' ') });
        const items = mb.items.concat(tb.items);
        items.push({ key: 'dv:t', kind: 'text', x: 0, y: y0 - 14, text: o.title || 'Runs of P: one cell per step', cls: 'title' });
        if (o.note) items.push(card('note', 0, tb.box.y + tb.box.h + 24, tb.box.w, o.note.text, o.note.cls));
        return items;
      };
      F.add({ items: scene(), say: 'P ' + P.text + '. Does P accept at least one input? A recogniser has to answer yes whenever that is true.', hl: { p: [0] } });
      // the naive way: one input at a time
      let naiveDone = false;
      for (let i = 0; i < n && !naiveDone; i++) {
        const [v, s] = act[i];
        const shown = Math.min(s, S);
        for (let j = 0; j < shown; j++) grid[i][j] = '·';
        if (v === 'accept' && s <= S) { grid[i][s - 1] = '✓'; naiveDone = true; F.add({ items: scene({ rowHot: i, title: 'One input at a time', note: { text: 'One at a time works here, but only because P accepts ' + show(INPUTS[i]) + ' before any endless run is met.', cls: 'good' } }), say: 'Trying the inputs in order: P accepts ' + show(INPUTS[i]) + ' after ' + s + ' steps. Lucky: no endless run came first.', meta: { naive: true } }); break; }
        if (v === 'reject') { grid[i][s - 1] = '✗'; F.add({ items: scene({ rowHot: i, title: 'One input at a time' }), say: 'Trying the inputs in order: P rejects ' + show(INPUTS[i]) + ' after ' + s + ' step' + (s > 1 ? 's' : '') + '. On to the next input.' }); continue; }
        F.add({ items: scene({ rowHot: i, title: 'One input at a time', note: { text: 'Stuck: P runs forever on ' + show(INPUTS[i]) + ', so the inputs after it are never tried.', cls: 'bad' } }), say: 'Trying the inputs in order: P is still running on ' + show(INPUTS[i]) + ' after ' + S + ' steps, and it never stops. One at a time, the recogniser waits here for ever.', mark: 'stuck' });
        naiveDone = true;
      }
      // dovetailing
      for (const r of grid) r.fill('');
      F.add({ items: scene({ lines: [1] }), say: 'Dovetail instead: at stage k, each of the first k inputs gets one more step. No single run can hold up the others.', hl: { p: [1] } });
      const ran = new Array(n).fill(0), over = new Array(n).fill(false);
      let found = -1;
      for (let k = 1; k <= S && found < 0; k++) {
        const hot = new Set();
        F.set('stage', k);
        for (let i = 0; i < Math.min(k, n); i++) {
          if (over[i]) continue;
          const j = ran[i]++;
          F.count('steps');
          hot.add(i + ',' + j);
          const [v, s] = act[i];
          if (j + 1 === s) { grid[i][j] = v === 'accept' ? '✓' : '✗'; over[i] = true; if (v === 'accept' && found < 0) found = i; } else grid[i][j] = '·';
        }
        const parts = [];
        for (let i = 0; i < Math.min(k, n); i++) { const c = [...hot].find((h) => +h.split(',')[0] === i); if (c) { const j = +c.split(',')[1]; parts.push(show(INPUTS[i]) + (grid[i][j] === '✓' ? ' accepts' : grid[i][j] === '✗' ? ' rejects' : ' step ' + (j + 1))); } }
        F.add({ items: scene({ hot, lines: [2, 3], found: found >= 0 }), say: 'Stage ' + k + ': ' + (parts.length ? parts.join(', ') : 'every run so far has already stopped') + '.' + (found >= 0 ? ' P accepts ' + show(INPUTS[found]) + ', so the recogniser accepts ⟨P⟩.' : ''), meta: { stage: k, found: found >= 0 ? found : null }, hl: { p: [2, 3] }, mark: found >= 0 ? 'accept' : undefined });
      }
      if (found < 0) {
        F.add({ items: scene({ note: { text: inp.p === 'never' ? 'P accepts nothing, so ⟨P⟩ is not in the language, and the recogniser keeps sweeping for ever. That is allowed: a recogniser only has to say yes to members.' : 'No acceptance yet; the sweep goes on with more stages and more inputs.', cls: inp.p === 'never' ? 'hot' : '' } }), say: inp.p === 'never' ? 'P accepts nothing: the sweep goes on for ever and the recogniser never answers. Recognising is not deciding.' : 'No acceptance within ' + S + ' stages; the recogniser keeps going.', mark: 'runs on' });
      }
      const firstAcc = act.map((a, i) => [a, i]).filter(([a]) => a[0] === 'accept').sort((x, y) => (x[0][1] + x[1]) - (y[0][1] + y[1]))[0];
      return { frames: F.list, def: { sections: [
        { id: 'p', kind: 'math', title: 'The recogniser', text: LINES.join('\n') },
        { id: 'prog', kind: 'text', title: 'The program P', text: 'P ' + P.text + '.' },
        { id: 'why', kind: 'math', title: 'Why it works', text: 'If P accepts w after s steps, and w is the i-th input,\nthat acceptance shows up at stage i + s − 1.\nAn endless run only ever takes one step per stage.' },
      ] }, result: firstAcc ? firstAcc[1] : null };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.stage === 1 && fr.some((x) => x.meta && x.meta.found !== null && x.meta.found !== undefined), once: true, pick: 'item', ask: 'Click the input whose acceptance the sweep will find first.', answer: (fr) => 'dv:rh:' + fr.find((x) => x.meta && x.meta.found !== null && x.meta.found !== undefined).meta.found, explain: 'An input gets its first step at the stage equal to its place in the list, and then one step per stage.' },
      { at: (f, i, fr) => f.meta && f.meta.stage === 1 && !fr.some((x) => x.meta && x.meta.found !== null && x.meta.found !== undefined), once: true, pick: 'option', options: ['Some stage accepts', 'It never answers'], ask: 'This P runs forever on every input. What will the recogniser do?', answer: () => 'It never answers', explain: 'With nothing to accept, the sweep simply continues; a recogniser may run forever on non-members.' },
    ],
    quiz: [
      { q: 'Why not run P on ε, then on a, then on b, and so on?', options: ['It is too slow', 'If P runs forever on an early input, the later inputs are never tried', 'P might accept twice', 'Inputs must be tried in reverse'], answer: 1, why: 'A run that never ends never hands control back, so an accepted input further down the list is never reached.' },
      { q: 'At stage k of the sweep, which runs get a step?', options: ['Only the k-th input', 'Each of the first k inputs (that has not stopped)', 'All inputs at once', 'Inputs of length k'], answer: 1, why: 'Stage k adds the k-th input and advances every earlier run by one more step.' },
      { q: 'P accepts the 4th input after 3 steps. At which stage is this seen?', options: ['3', '4', '6', '12'], answer: 2, why: 'Input 4 gets its first step at stage 4 and its third at stage 6 (4 + 3 − 1).' },
      { q: 'P accepts nothing. What does the dovetailing recogniser do on ⟨P⟩?', options: ['Rejects after the last input', 'Runs forever', 'Accepts', 'Crashes'], answer: 1, why: 'There is no last input. Never answering is allowed for a recogniser, which is why this language is recognisable but not decidable.' },
      { q: 'Which language does this show to be recognisable?', options: ['{⟨P⟩ : P accepts no input}', '{⟨P⟩ : P accepts some input}', '{⟨P⟩ : P halts on every input}', '{⟨P⟩ : P has 5 states}'], answer: 1, why: 'Whenever P accepts some input, the sweep finds it in finite time.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // A language and its complement, raced
  // ---------------------------------------------------------------------------------------------------
  // L = strings with at least one a. R1 recognises L: scan right, accept at an a, loop at the end.
  // R2 recognises the complement: scan right, loop at an a, accept at the end.
  const CLASSES = [
    { id: 'A_DFA', where: 'dec', why: 'it is decided by simulating the DFA' },
    { id: 'E_CFG', where: 'dec', why: 'marking generating variables decides it' },
    { id: 'A_TM', where: 'rec', why: 'the universal machine recognises it, but it is undecidable' },
    { id: 'HALT', where: 'rec', why: 'simulate and accept when it halts; undecidable' },
    { id: 'co-A_TM', where: 'co', why: 'its complement A_TM is recognisable, and it is not' },
    { id: 'E_TM', where: 'co', why: 'its complement "accepts something" is recognisable by dovetailing' },
    { id: 'EQ_TM', where: 'none', why: 'neither it nor its complement is recognisable' },
  ];
  T.topic({
    id: 'rec-both', family: 'recognisable', order: 20, title: 'Recognise both sides: decide',
    blurb: 'Run a recogniser for L and one for its complement in turns, one step each. Exactly one of them accepts, so together they always answer. That is why the complement of A_TM cannot be recognisable.',
    inputs: [
      { id: 'w', kind: 'string', label: 'Input', def: 'bbab', max: 8, alphabet: 'ab' },
    ],
    presets: [
      { label: 'An a in the middle: bbab', values: { w: 'bbab' } },
      { label: 'No a at all: bbbb', values: { w: 'bbbb' } },
      { label: 'An a at once: abbb', values: { w: 'abbb' } },
      { label: 'The empty string ε', values: { w: '' } },
    ],
    counters: [{ id: 'turns', label: 'turns' }, { id: 'r1', label: 'R₁ steps' }, { id: 'r2', label: 'R₂ steps' }],
    run(inp) {
      const w = [...inp.w], n = w.length;
      const MB = K.mbox;
      const F = new T.Frames(['turns', 'r1', 'r2']);
      // each machine's state: head, verdict ('run' | 'accept' | 'loop')
      const m = [{ head: 0, st: 'run', steps: 0 }, { head: 0, st: 'run', steps: 0 }];
      const step = (k) => {
        const s = m[k];
        if (s.st === 'loop') { s.steps++; return 'still looping'; }
        const c = s.head < n ? w[s.head] : '⊔';
        s.steps++;
        if (k === 0) { if (c === 'a') { s.st = 'accept'; return 'reads a and accepts'; } if (c === '⊔') { s.st = 'loop'; return 'reaches the end without an a and starts looping'; } s.head++; return 'reads b and moves right'; }
        if (c === 'a') { s.st = 'loop'; return 'reads a and starts looping'; }
        if (c === '⊔') { s.st = 'accept'; return 'reaches the end without seeing an a and accepts'; }
        s.head++; return 'reads b and moves right';
      };
      const L1 = ['scan right;', 'see an a → accept;', 'reach the end → loop forever.'];
      const L2 = ['scan right;', 'see an a → loop forever;', 'reach the end → accept.'];
      const scene = (o) => {
        o = o || {};
        const items = [];
        let y = 0;
        [0, 1].forEach((k) => {
          const s = m[k];
          const lit = s.st === 'accept' ? 'accept' : s.st === 'loop' ? 'loop' : null;
          const r = MB.draw({ prefix: 'r' + (k + 1), x: 0, y, w: 420, title: k === 0 ? 'R₁ recognises L: strings with an a' : 'R₂ recognises the complement: no a', lines: k === 0 ? L1 : L2, hot: o.turn === k ? [s.st === 'run' ? 0 : s.st === 'accept' ? 1 + k : 2 - k] : [], cls: (o.turn === k ? 'hot ' : '') + (k === 0 ? 'r0' : 'r3'), outs: [{ id: 'accept', text: 'accept', cls: 'good', lit: lit === 'accept' }, { id: 'loop', text: 'loops ∞', cls: 'hot', lit: lit === 'loop' }] });
          items.push(...r.items);
          const t = K.tape.draw({ prefix: 'tp' + k, tape: w, head: s.head, state: s.st === 'run' ? 'R' + (k + 1) : s.st === 'accept' ? 'accept' : 'loop', cells: Math.max(6, n + 2), origin: 0, x: 60, y: y + r.box.h + 22, cw: 40, ch: 40, headCls: s.st === 'accept' ? 'good' : s.st === 'loop' ? 'hot' : '' });
          items.push(...t.items);
          y += r.box.h + 22 + 40 + 64;
        });
        const res = m[0].st === 'accept' ? 'accept' : m[1].st === 'accept' ? 'reject' : null;
        const d = MB.draw({ prefix: 'dc', x: 0, y, w: 420, title: 'Decider: R₁ and R₂ in turns', lines: ['R₁ accepts → accept;', 'R₂ accepts → reject.'], hot: res ? [res === 'accept' ? 0 : 1] : [], cls: 'r1', outs: K.mbox.answers(res) });
        items.push(...d.items);
        return items;
      };
      F.add({ items: scene(), say: 'L is the set of strings with at least one a. R₁ accepts exactly L but loops on the rest; R₂ accepts exactly the complement but loops on L. Neither alone is a decider. Input: ' + (n ? w.join('') : 'ε, the empty string') + '.', hl: { def: [0, 1] } });
      let turn = 0;
      let guard = 0;
      while (m[0].st !== 'accept' && m[1].st !== 'accept' && guard++ < 40) {
        const k = turn % 2;
        const what = step(k);
        F.count('turns').count(k ? 'r2' : 'r1');
        const done = m[k].st === 'accept';
        F.add({ items: scene({ turn: k }), say: 'R' + (k + 1) + '\'s turn: it ' + what + '.' + (done ? (k === 0 ? ' R₁ accepted, so the input is in L: the decider accepts.' : ' R₂ accepted, so the input is not in L: the decider rejects.') : ''), meta: { turn: k, winner: done ? k : null }, hl: { def: [2] }, mark: done ? (k ? 'reject' : 'accept') : undefined });
        turn++;
      }
      phase(F, 'race');
      // the argument for A_TM, as a chain of cards
      const items = [];
      const steps = [
        ['A_TM is recognisable: the universal machine runs M on w and accepts if M accepts.', ''],
        ['Suppose its complement were recognisable too, by some machine R.', 'hot'],
        ['Run the universal machine and R in turns, exactly as above. One of them must accept.', ''],
        ['That would decide A_TM. But A_TM is undecidable (the diagonal argument).', 'bad'],
        ['So no such R exists: the complement of A_TM is not recognisable.', 'good'],
      ];
      let y = 0;
      steps.forEach(([t, cls], k) => {
        const c = card('arg' + k, 0, y, 480, (k + 1) + '. ' + t, cls, { enter: 'drop' });
        items.push(c);
        if (k) items.push({ key: 'arg-e' + k, kind: 'edge', from: 'arg' + (k - 1), to: 'arg' + k, cls: 'mflow' });
        F.add({ items: items.slice(), say: t, hl: { def: [3] } });
        y += c.h + 30;
      });
      phase(F, 'arg');
      // the class map
      const placed = new Set();
      const map = (hot) => {
        const mem = { RC: [], R: [], C: [], '': [] };
        for (const c of CLASSES) if (placed.has(c.id)) mem[{ dec: 'RC', rec: 'R', co: 'C', none: '' }[c.where]].push(c.id);
        return K.set.venn({ prefix: 'cm', sets: [{ id: 'R', label: 'recognisable' }, { id: 'C', label: 'co-recognisable' }], members: mem, universe: 'all languages', r: 130, hot }).items;
      };
      F.add({ items: map(), say: 'Every language falls in one of four places: decidable (both sides recognisable), recognisable only, co-recognisable only, or neither.', meta: { mapAsk: true } });
      for (const c of CLASSES) {
        placed.add(c.id);
        F.add({ items: map(c.where === 'rec' ? ['R'] : c.where === 'co' ? ['C'] : c.where === 'dec' ? ['R', 'C'] : []), say: c.id + ' goes ' + { dec: 'in the middle, decidable', rec: 'in recognisable only', co: 'in co-recognisable only', none: 'outside both' }[c.where] + ': ' + c.why + '.', meta: { placed: c.id } });
      }
      phase(F, 'map');
      return { frames: phaseViews(F.list), def: { sections: [
        { id: 'def', kind: 'math', title: 'Definitions', text: 'L is recognisable: some machine accepts exactly L\n(it may loop on strings not in L)\nRun both in turns, one step each\nL decidable ⇔ L and its complement both recognisable' },
        { id: 'lang', kind: 'text', title: 'Here', text: 'L = strings over {a, b} with at least one a.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0, once: true, pick: 'item', ask: 'Which machine will accept first? Click its box.', answer: (fr) => { const w = fr.find((x) => x.meta && x.meta.winner !== null && x.meta.winner !== undefined); return 'r' + (w.meta.winner + 1) + ':box'; }, explain: 'If the input has an a, R₁ accepts when it reaches it; if not, R₂ accepts when it reaches the end. Exactly one of them accepts.' },
      { at: (f) => f.meta && f.meta.mapAsk, once: true, pick: 'option', options: ['decidable', 'recognisable only', 'co-recognisable only', 'neither'], ask: 'Where does the complement of A_TM go?', answer: () => 'co-recognisable only', explain: 'Its complement, A_TM, is recognisable, so it is co-recognisable; it is not recognisable itself, by the argument just made.' },
    ],
    quiz: [
      { q: 'Why run R₁ and R₂ in turns rather than R₁ first, then R₂?', options: ['It is faster', 'R₁ may loop forever on its own, and then R₂ would never get to run', 'R₂ must go first', 'To save memory'], answer: 1, why: 'On a string not in L, R₁ may never stop; taking turns guarantees R₂ also makes progress.' },
      { q: 'L is recognisable and so is its complement. What follows?', options: ['L is regular', 'L is decidable', 'L is context-free', 'Nothing'], answer: 1, why: 'Every string is accepted by one of the two recognisers, so running both in turns always stops with the right answer.' },
      { q: 'Why is the complement of A_TM not recognisable?', options: ['It is too big', 'If it were, A_TM would be decidable, and A_TM is not', 'Because A_TM is regular', 'Because machines cannot read descriptions'], answer: 1, why: 'A_TM is recognisable; with a recogniser for its complement too, it would be decidable.' },
      { q: 'E_TM = {⟨M⟩ : L(M) = ∅}. Which class is it in?', options: ['Decidable', 'Recognisable only', 'Co-recognisable only', 'Neither'], answer: 2, why: 'Its complement ("M accepts some string") is recognisable by dovetailing; E_TM itself is not decidable, so not recognisable.' },
      { q: 'A recogniser for L runs forever on some string w. What can you conclude?', options: ['w ∈ L', 'w ∉ L', 'The recogniser is wrong', 'L is finite'], answer: 1, why: 'A recogniser accepts every member of L, so if it never accepts w, w is not in L.' },
    ],
  });
})();
