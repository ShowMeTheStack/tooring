// Turing machines on one tape: a run with the diagram and the tape, configurations as a timeline, deciders
// against recognisers, machines that compute functions, a machine designed by crossing off, and the
// zig-zag of a palindrome checker drawn as a trail through time.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const TK = () => T.TK;
  const lib = (id) => T.tmLib.entry(id).text.trim();

  T.family({ id: 'tm', part: 'turing', order: 10, title: 'Turing machines', blurb: 'A tape that goes on for ever, a head that reads, writes and moves, and a handful of states: enough to compute anything that can be computed.' });

  const INC = 'start: right\naccept: done\nright, 0 -> right, 0, R\nright, 1 -> right, 1, R\nright, _ -> carry, _, L\ncarry, 1 -> carry, 0, L\ncarry, 0 -> done, 1, S\ncarry, _ -> done, 1, S';
  const EVEN = 'start: even\naccept: yes\neven, 1 -> odd, 1, R\nodd, 1 -> even, 1, R\neven, 0 -> even, 0, R\nodd, 0 -> odd, 0, R\neven, _ -> yes, _, S\nodd, _ -> no, _, S';
  const AWAY = 'start: go\naccept: done\ngo, 0 -> go, 0, R\ngo, 1 -> done, 1, S\ngo, _ -> go, _, R';
  const ERASE = 'start: find\naccept: done\nfind, 0 -> find, 0, R\nfind, 1 -> wipe, _, R\nwipe, 0 -> wipe, _, R\nwipe, 1 -> wipe, _, R\nwipe, _ -> done, _, S\nfind, _ -> done, _, S';

  /** A machine-text input for one-tape machines, read by both the diagram editor and the engine */
  const machineInput = (def, max) => ({ id: 'm', kind: 'machine', machine: 'tm', label: 'Machine', def, check: (v) => TK().checkMachine(v, { tapes: 1, deterministic: true, maxStates: max || 8, anyHalt: true }) });

  /** The layout of a machine's diagram, keeping positions the student gave in the editor */
  function diagramOf(M, text) {
    const d = TK().diagram(M);
    let fixed = {};
    try { fixed = T.Machine.parse(text).pos || {}; } catch (e) { fixed = {}; }
    const pos = K.graph.layout(d, { fixed }).pos;
    return { d, pos };
  }

  // ======================================================================================================
  // A run: the diagram above, the tape below, the move just made written between them
  // ======================================================================================================
  T.topic({
    id: 'tm-run', family: 'tm', order: 10, title: 'A Turing machine runs',
    blurb: 'Each step reads the symbol under the head, writes one back, moves one cell and changes state. Follow the head along the tape until the machine halts, or see that it never will.',
    inputs: [machineInput(INC), { id: 'w', kind: 'string', label: 'Tape', def: '1011', max: 10 }],
    presets: [
      { label: 'Add one: 1011', values: { m: INC, w: '1011' } },
      { label: 'Even number of 1s: 1101', values: { m: EVEN, w: '1101' } },
      { label: 'A long carry: 111', values: { m: INC, w: '111' } },
      { label: 'Add one to the empty tape', values: { m: INC, w: '' } },
      { label: 'Erase from the first 1: 0011', values: { m: ERASE, w: '0011' } },
      { label: 'Never halts: looking for a 1 in 00', values: { m: AWAY, w: '00' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'writes', label: 'symbols changed' }, { id: 'cells', label: 'cells visited' }],
    check: (inp) => { const M = TK().compile(inp.m).M; const bad = [...inp.w].find((c) => !M.gamma.includes(c) || c === M.blank); return bad !== undefined ? 'Tape: the machine has no rules that read "' + bad + '"' : null; },
    run(inp) {
      const tk = TK();
      const M = tk.compile(inp.m).M;
      const run = tk.trace(M, inp.w, { max: 40 });
      const { d, pos } = diagramOf(M, inp.m);
      const g0 = K.graph.draw(d, { pos });
      const N = 11, CW = 46;
      const tx = g0.box.x + g0.box.w / 2 - (N * CW) / 2, ty = g0.box.y + g0.box.h + 92;
      const sc = K.tape.scroller({ cells: N, origin: -2, margin: 2 });
      const def = tk.defOf(M);
      const F = new T.Frames(['steps', 'writes', 'cells']);
      const seen = new Set([0]);
      const scene = (cfg, gopts, headCls, rule) => {
        const origin = sc.at(cfg.heads[0].p);
        const items = K.graph.draw(d, Object.assign({ pos }, gopts)).items;
        items.push(...tk.tape(cfg, { state: cfg.state, cells: N, origin, prevOrigin: sc.prev, x: tx, y: ty, headCls: headCls || '', label: 'tape' }).items);
        const txt = rule ? 'δ(' + rule.from + ', ' + tk.sym(rule.read[0]) + ') = (' + rule.to + ', ' + tk.sym(rule.write[0]) + ', ' + rule.move[0] + ')' : 'start in ' + M.start;
        items.push({ key: 'rule', kind: 'text', x: tx + (N * CW) / 2, y: ty - 26, text: txt, anchor: 'middle', cls: 'mono', mono: true });
        return items;
      };
      F.set('cells', 1);
      F.add({ items: scene(run.list[0].cfg, { active: [M.start], startHot: true }), say: 'The input ' + (inp.w || 'ε') + ' is on the tape, every other cell holds the blank ⊔, and the head is on the first cell in state ' + M.start + '.' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        F.count('steps');
        if (rule.write[0] !== rule.read[0]) F.count('writes');
        seen.add(cfg.heads[0].p);
        F.set('cells', seen.size);
        F.add({ items: scene(cfg, { active: [cfg.state], taken: [rule.from + '>' + rule.to] }, '', rule), say: tk.sayRule(rule), hl: def.hl(rule), meta: { move: rule.move[0], to: rule.to, from: rule.from } });
      }
      const last = run.last;
      const out = tk.word(tk.contents(last, 0));
      const end = {
        accept: 'In ' + last.state + ', an accepting state, the machine halts and accepts. The tape now reads ' + out + '.',
        reject: run.how === 'stuck' ? 'In ' + last.state + ' there is no move on ' + tk.sym(tk.reads(last)[0]) + ', so the machine halts' + (T.tm.isAccept(M, last.state) ? '' : ' without accepting') + '. The tape reads ' + out + '.' : 'The machine enters ' + last.state + ', a rejecting state, and halts.',
        loop: 'This configuration is exactly the one of step ' + run.loopAt + ': state, tape and head all repeat, so the machine will go round the same steps for ever.',
        limit: 'After ' + (run.list.length - 1) + ' steps the head is still walking into fresh blanks. Nothing will ever stop it: this machine never halts on ' + (inp.w || 'ε') + '.',
      }[run.verdict];
      const good = run.verdict === 'accept';
      F.add({ items: scene(last, good ? { good: [last.state] } : { bad: [last.state] }, good ? 'good' : 'bad', run.list.length > 1 ? run.list[run.list.length - 1].rule : null), say: end, mark: good ? 'accepted' : run.verdict === 'reject' ? 'rejected' : 'never halts' });
      // predictions: the direction of an early move, and the state a later step goes to
      const fr = F.list;
      if (fr.length > 3 && fr[2].meta) fr[1].predict = { ask: 'Which way will the head move next: left (L), right (R) or stay (S)? Look at the table.', options: ['L', 'R', 'S'], answer: fr[2].meta.move, explain: fr[2].say, pick: 'option' };
      for (let i = 3; i < fr.length - 2; i++) if (fr[i + 1].meta && fr[i].meta && fr[i + 1].meta.to !== fr[i].meta.to) { fr[i].predict = { ask: 'Click the state the machine will be in after the next step.', answer: 'g:s:' + fr[i + 1].meta.to, explain: fr[i + 1].say, pick: 'item' }; break; }
      return { frames: fr, def: { sections: def.sections } };
    },
    quiz: [
      { q: 'What does a Turing machine do in one step?', options: ['Reads a symbol and changes state only', 'Reads, writes, moves one cell and changes state', 'Moves to any cell it likes', 'Reads the whole tape'], answer: 1, why: 'A step looks at one cell, writes a symbol there, moves the head one cell left or right (or stays) and enters a new state.' },
      { q: 'When does a machine with no explicit reject state halt?', options: ['At the end of the input', 'When there is no move for its state and the symbol under the head', 'After as many steps as the input is long', 'Never'], answer: 1, why: 'It halts when δ has no move; whether it accepts depends on the state it halted in.' },
      { q: 'Adding one to 111 gives 1000. Where does the new leading 1 go?', options: ['Over the first 1', 'Into the blank cell left of the input', 'At the right end', 'Nowhere: the tape is full'], answer: 1, why: 'The carry walks left over the 1s, turning them to 0s, and lands in the blank before the input: the tape goes on for ever both ways.' },
      { q: 'The machine that walks right for ever never repeats a configuration. Why not?', options: ['Its state changes', 'Its head is at a new place every step', 'It writes new symbols', 'It does repeat'], answer: 1, why: 'A configuration includes the head position. Here the head moves on each step, so the configurations all differ, and spotting a repeat cannot prove it runs for ever.' },
      { q: 'Why does a simulator need a step limit?', options: ['The tape runs out', 'Some machines never halt, and no program can always tell which', 'The machine forgets its state', 'To save colour'], answer: 1, why: 'A machine may run for ever. Whether it halts is undecidable in general, so a simulator has to stop watching at some point.' },
    ],
  });

  // ======================================================================================================
  // Configurations u q v, one per step, as a timeline that scrolls up
  // ======================================================================================================
  const LOOPY = 'start: q0\naccept: qa\nq0, a -> q1, a, R\nq0, b -> q0, b, R\nq1, a -> qa, a, S\nq1, b -> q0, b, R\nq0, _ -> q0, _, S\nq1, _ -> q1, _, S';
  /** u, q, v of a configuration on tape 0: the written part and the head's cell, blank cells inside shown */
  function uqv(cfg) {
    const t = cfg.tapes[0], h = cfg.heads[0].p, b = t.bounds();
    const lo = Math.min(b.hi < b.lo ? h : b.lo, h), hi = Math.max(b.hi < b.lo ? h : b.hi, h);
    return { u: t.slice(lo, h - 1), q: cfg.state, v: t.slice(h, hi), lo };
  }
  const cfgText = (c) => { const x = uqv(c); return (x.u.length ? TK().word(x.u) + ' ' : '') + x.q + ' ' + TK().word(x.v); };

  T.topic({
    id: 'tm-configs', family: 'tm', order: 20, title: 'Configurations: u q v',
    blurb: 'Everything about a machine at one moment fits in one string: the tape left of the head, the state, and the tape from the head on. A run is a chain of these, each yielding the next.',
    inputs: [machineInput(lib('anbn'), 8), { id: 'w', kind: 'string', label: 'Input', def: 'aabb', max: 8 }],
    presets: [
      { label: 'aⁿbⁿ: aabb', values: { m: lib('anbn'), w: 'aabb' } },
      { label: 'aⁿbⁿ: ab', values: { m: lib('anbn'), w: 'ab' } },
      { label: 'aⁿbⁿ: aab, rejected', values: { m: lib('anbn'), w: 'aab' } },
      { label: 'Even length: the empty string', values: { m: lib('even-length'), w: '' } },
      { label: 'A configuration repeats: b', values: { m: LOOPY, w: 'b' } },
    ],
    counters: [{ id: 'steps', label: 'configurations' }, { id: 'len', label: 'longest u q v' }],
    check: (inp) => { const M = TK().compile(inp.m).M; const bad = [...inp.w].find((c) => !M.input.includes(c)); return bad !== undefined ? 'Input: "' + bad + '" is not an input symbol of the machine' : null; },
    run(inp) {
      const tk = TK();
      const M = tk.compile(inp.m).M;
      const run = tk.trace(M, inp.w, { max: 60 });
      const def = tk.defOf(M);
      const list = run.list;
      const CW = 32, CH = 38, RH = 52, VIS = 6;
      const chipW = (q) => Math.max(40, T.geom.textWidth(q, 14, { bold: true }) + 16);
      const widths = list.map((x) => { const p = uqv(x.cfg); return (p.u.length + p.v.length) * CW + chipW(p.q) + 4; });
      const maxW = Math.max(...widths);
      const noteX = maxW + 70;
      const F = new T.Frames(['steps', 'len']);
      // one row: its cells keyed by the configuration's number, so a row glides as the timeline scrolls
      const row = (i, y, opts) => {
        opts = opts || {};
        const p = uqv(list[i].cfg), items = [];
        let x = 0;
        const r = list[i].rule;
        const wrote = r && r.write[0] !== r.read[0] ? list[i - 1].cfg.heads[0].p : null;
        const P = (opts.prefix || 'r') + i;
        const cell = (s, pos, k) => { items.push({ key: P + ':' + k, kind: 'cell', x, y, w: CW, h: CH, text: tk.sym(s), rx: 4, cls: 'mono' + (tk.sym(s) === tk.BL ? ' blank' : '') + (pos === wrote && opts.last ? ' tu-new' : '') + (opts.cls ? ' ' + opts.cls : ''), enter: opts.enter || 'drop', exit: 'rise', size: 15 }); x += CW; };
        p.u.forEach((s, j) => cell(s, p.lo + j, 'u' + j));
        const qw = chipW(p.q);
        items.push({ key: P + ':q', kind: 'cell', x: x + 2, y, w: qw - 4, h: CH, text: p.q, rx: 10, cls: 'tu-q' + (opts.qcls ? ' ' + opts.qcls : ''), enter: opts.enter || 'drop', exit: 'rise' });
        x += qw;
        p.v.forEach((s, j) => cell(s, cfgPos(list[i].cfg) + j, 'v' + j));
        items.push({ key: P + ':name', kind: 'text', x: -14, y: y + CH / 2 + 5, text: 'C' + i, anchor: 'end', cls: 'title', enter: 'drop', exit: 'rise' });
        if (i > 0 && !opts.noTurn) items.push({ key: P + ':yields', kind: 'text', x: -52, y: y + CH / 2 + 6, text: '⊢', anchor: 'end', cls: 'strong', size: 18, enter: 'drop', exit: 'rise' });
        if (r && !opts.noNote) items.push({ key: P + ':note', kind: 'text', x: noteX, y: y + CH / 2 + 5, text: 'by δ(' + r.from + ', ' + tk.sym(r.read[0]) + ') = (' + r.to + ', ' + tk.sym(r.write[0]) + ', ' + r.move[0] + ')', cls: 'mono', mono: true, size: 13, enter: 'drop', exit: 'rise' });
        return items;
      };
      const cfgPos = (c) => c.heads[0].p;
      const scene = (i, extra) => {
        const first = Math.max(0, i - VIS + 1);
        const items = [];
        for (let k = first; k <= i; k++) items.push(...row(k, (k - first) * RH, { last: k === i, qcls: k === i && extra && extra.qcls ? extra.qcls : '' }));
        items.push({ key: 'head', kind: 'text', x: 0, y: -22, text: 'TAPE LEFT OF THE HEAD · STATE · THE REST', cls: 'title' });
        return items;
      };
      for (let i = 0; i < list.length; i++) {
        F.count('steps');
        F.set('len', Math.max(F.counts.len, uqv(list[i].cfg).u.length + uqv(list[i].cfg).v.length + 1));
        const r = list[i].rule;
        const say = i === 0
          ? 'The start configuration C0 is ' + cfgText(list[0].cfg) + ': nothing left of the head, the state ' + M.start + ', then the input from the head on' + (inp.w ? '' : ' (just a blank, as the input is ε)') + '.'
          : 'C' + (i - 1) + ' ⊢ C' + i + ': ' + tk.sayRule(r) + ' So the state chip ' + (r.move[0] === 'L' ? 'jumps left of the symbol before it' : r.move[0] === 'R' ? 'steps right past the symbol just written' : 'stays where it is') + ': ' + cfgText(list[i].cfg) + '.';
        F.add({ items: scene(i), say, hl: def.hl(r), meta: { text: cfgText(list[i].cfg) } });
      }
      const last = run.last;
      if (run.verdict === 'loop') {
        const j = run.loopAt, i = list.length - 1;
        const items = scene(i, { qcls: 'bad' });
        const first = Math.max(0, i - VIS + 1);
        if (j >= first) {
          // both rows are in view: colour them alike
          for (const it of items) if (it.key.startsWith('r' + j + ':') || it.key.startsWith('r' + i + ':')) { if (it.kind === 'cell' && !/tu-q/.test(it.cls)) it.cls += ' tu-k5'; }
          items.push({ key: 'earlyNote', kind: 'text', x: noteX, y: (i - first) * RH + CH + 26, text: 'C' + i + ' = C' + j, cls: 'bad' });
        } else {
          const y = (i - first + 1) * RH + 20;
          items.push(...row(j, y, { prefix: 'early', cls: 'tu-k5', noTurn: true, noNote: true, enter: 'fade' }));
          items.push({ key: 'earlyNote', kind: 'text', x: noteX, y: y + CH / 2 + 5, text: 'the same as C' + i, cls: 'bad' });
        }
        F.add({ items, say: 'C' + i + ' is the same string as C' + j + '. A configuration fixes everything that happens next, so the machine will pass through the same configurations again and again: it never halts.', mark: 'loops' });
      } else {
        const good = run.verdict === 'accept';
        F.add({ items: scene(list.length - 1, { qcls: good ? 'good' : 'bad' }), say: (good ? cfgText(last) + ' is a halting configuration in the accepting state ' + last.state + ': the run is accepted after ' + (list.length - 1) + ' steps.' : 'No configuration follows ' + cfgText(last) + (run.how === 'stuck' ? ': δ has no move for ' + last.state + ' on ' + tk.sym(tk.reads(last)[0]) : '') + ', so the run halts and rejects.'), mark: good ? 'accepted' : 'rejected' });
      }
      // predict the next configuration among three that look alike
      const fr = F.list;
      const at = Math.min(3, list.length - 2);
      if (at >= 1) {
        const right = fr[at + 1].meta.text;
        const r = list[at + 1].rule;
        const alt = (move, write) => { const c = T.tm.cloneCfg(list[at].cfg); T.tm.apply(c, Object.assign({}, r, { move: [move], write: [write] })); return cfgText(c); };
        const opts = [...new Set([right, alt(r.move[0] === 'L' ? 'R' : 'L', r.write[0]), alt(r.move[0], r.read[0]), alt('S', r.write[0])])].slice(0, 3);
        if (opts.length >= 2) fr[at].predict = { ask: 'Which configuration does C' + at + ' yield?', options: opts.sort(), answer: right, explain: fr[at + 1].say, pick: 'option' };
      }
      return { frames: fr, def: { sections: def.sections.concat([{ id: 'yield', kind: 'math', title: 'One step, on configurations', text: 'u c q a v  ⊢  u q′ c b v    when δ(q, a) = (q′, b, L)\nu q a v  ⊢  u b q′ v    when δ(q, a) = (q′, b, R)\nat the right end, q a stands for q a ⊔' }]) } };
    },
    quiz: [
      { q: 'In the configuration aX q2 bb, which symbol is under the head?', options: ['X', 'the first b', 'the last b', 'none: the head is between cells'], answer: 1, why: 'u q v means: u is left of the head and the head reads the first symbol of v, here b.' },
      { q: 'Why is a configuration enough to know the whole future of a run?', options: ['It records every past step', 'The next move depends only on the state and the symbol under the head, both in the configuration', 'Because the tape is finite', 'It is not enough'], answer: 1, why: 'A deterministic machine\'s next configuration is a function of the current one, so the rest of the run follows.' },
      { q: 'A run reaches a configuration it has had before. What follows?', options: ['It will accept', 'It will reject', 'It runs for ever, round the same cycle', 'Nothing can be said'], answer: 2, why: 'From the same configuration the same steps follow, back to the same configuration, again and again.' },
      { q: 'The input is ε. What is the start configuration?', options: ['ε', 'q0 ⊔', '⊔', 'q0'], answer: 1, why: 'The head is on a blank cell, so v is that one blank: q0 ⊔.' },
    ],
  });

  // ======================================================================================================
  // A decider and a recogniser for the same language, side by side, step for step
  // ======================================================================================================
  const D_AA = 'start: s\naccept: yes\nreject: no\ns, a -> sa, a, R\ns, b -> s, b, R\ns, _ -> no, _, S\nsa, a -> yes, a, S\nsa, b -> s, b, R\nsa, _ -> no, _, S';
  const R_AA = 'start: s\naccept: yes\ns, a -> sa, a, R\ns, b -> s, b, R\ns, _ -> s, _, S\nsa, a -> yes, a, S\nsa, b -> s, b, R\nsa, _ -> sa, _, S';
  const D_EVEN = 'start: e\naccept: yes\nreject: no\ne, a|b -> o, *, R\no, a|b -> e, *, R\ne, _ -> yes, _, S\no, _ -> no, _, S';
  const R_EVEN = 'start: e\naccept: yes\ne, a|b -> o, *, R\no, a|b -> e, *, R\ne, _ -> yes, _, S\no, _ -> o, _, R';
  const PAIRS = { aa: { d: D_AA, r: R_AA, lang: 'strings containing aa' }, even: { d: D_EVEN, r: R_EVEN, lang: 'strings of even length' } };

  T.topic({
    id: 'tm-decide', family: 'tm', order: 30, title: 'Deciders and recognisers',
    blurb: 'A decider halts on every input with yes or no. A recogniser only has to halt with yes on the strings of its language; on the others it may run for ever. Watch both on the same input.',
    inputs: [
      { id: 'pair', kind: 'choice', label: 'Language', def: 'aa', options: [{ value: 'aa', label: 'contains aa' }, { value: 'even', label: 'even length' }] },
      { id: 'w', kind: 'string', label: 'Input', def: 'bab', alphabet: 'ab', max: 7 },
    ],
    presets: [
      { label: 'In the language: baab', values: { pair: 'aa', w: 'baab' } },
      { label: 'Not in it: bab (the recogniser spins)', values: { pair: 'aa', w: 'bab' } },
      { label: 'The empty string', values: { pair: 'aa', w: '' } },
      { label: 'Even length: abab', values: { pair: 'even', w: 'abab' } },
      { label: 'Odd length: aba (the recogniser runs away)', values: { pair: 'even', w: 'aba' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'dsteps', label: 'decider steps' }],
    run(inp) {
      const tk = TK();
      const P = PAIRS[inp.pair];
      const Md = tk.compile(P.d).M, Mr = tk.compile(P.r).M;
      const rd = tk.trace(Md, inp.w, { max: 40 }), rr = tk.trace(Mr, inp.w, { max: 14 });
      const dd = tk.diagram(Md), dr = tk.diagram(Mr);
      const pd = K.graph.layout(dd).pos, pr = K.graph.layout(dr).pos;
      const gd = K.graph.draw(dd, { pos: pd, prefix: 'd' }), gr0 = K.graph.draw(dr, { pos: pr, prefix: 'r' });
      const N = 9, CW = 42;
      // two lanes, the decider above the recogniser: each a diagram with its tape to the right
      const W = Math.max(gd.box.w, gr0.box.w), hD = Math.max(gd.box.h, 110);
      const off = { x: -gd.box.x, y: 30 - gd.box.y }, offR = { x: -gr0.box.x, y: 30 + hD + 80 - gr0.box.y };
      const tx = W + 90;
      const scD = K.tape.scroller({ cells: N, origin: -2 }), scR = K.tape.scroller({ cells: N, origin: -2 });
      const lane = (M, d, pos, run, k, prefix, o, sc, label) => {
        const i = Math.min(k, run.list.length - 1);
        const { cfg, rule } = run.list[i];
        const done = k >= run.list.length - 1;
        const fin = done && run.verdict !== 'loop' && run.verdict !== 'limit';
        const good = fin && run.verdict === 'accept', bad = fin && run.verdict !== 'accept';
        const g = K.graph.draw(d, { pos, prefix, x: o.x, y: o.y, active: fin ? [] : [cfg.state], good: good ? [cfg.state] : [], bad: bad ? [cfg.state] : [], taken: rule && k === i ? [rule.from + '>' + rule.to] : [] });
        const items = g.items;
        const ty = g.box.y + g.box.h / 2 - CW / 2 - 8;
        items.push(...tk.tape(cfg, { state: cfg.state, cells: N, cw: CW, origin: sc.at(cfg.heads[0].p), prevOrigin: sc.prev, x: tx, y: ty, prefix: prefix + 't', headCls: good ? 'good' : bad ? 'bad' : '' }).items);
        items.push({ key: prefix + ':title', kind: 'text', x: 0, y: o.y + (prefix === 'd' ? gd.box.y : gr0.box.y) - 30 + 30 - 34, text: label.toUpperCase(), cls: 'title' });
        const looping = run.verdict === 'loop' && k >= run.list.length - 1;
        const state = fin ? (good ? 'halted: accepts' : 'halted: rejects') : looping ? 'never halts' : run.verdict === 'limit' && done ? 'still running…' : 'running';
        items.push({ key: prefix + ':verdict', kind: 'text', x: tx + N * CW, y: ty - 16, text: state, anchor: 'end', cls: fin ? (good ? 'good' : 'bad') : looping || (run.verdict === 'limit' && done) ? 'hot' : 'strong' });
        return { items };
      };
      const total = Math.max(rd.list.length, rr.list.length + (rr.verdict === 'loop' ? 3 : 0));
      const F = new T.Frames(['steps', 'dsteps']);
      const short = (run, k, name) => {
        if (k >= run.list.length) return run.verdict === 'loop' ? name + ' makes the same move again, getting nowhere' : run.verdict === 'limit' ? name + ' keeps going' : name + ' has halted';
        const r = run.list[k].rule;
        return name + ' reads ' + tk.sym(r.read[0]) + ' in ' + r.from + (r.to === r.from && r.move[0] === 'S' && r.write[0] === r.read[0] ? ' and does nothing but stay there' : ' and goes to ' + r.to + (r.move[0] === 'S' ? '' : ', moving ' + (r.move[0] === 'L' ? 'left' : 'right')));
      };
      for (let k = 0; k < total; k++) {
        const a = lane(Md, dd, pd, rd, k, 'd', off, scD, 'decider D');
        const b = lane(Mr, dr, pr, rr, k, 'r', offR, scR, 'recogniser R');
        if (k) F.count('steps');
        if (k && k < rd.list.length) F.count('dsteps');
        let say;
        if (k === 0) say = 'Both machines are for ' + P.lang + ' and both start on ' + (inp.w || 'ε') + '. D must halt on every input; R only has to halt when the answer is yes.';
        else {
          const parts = [];
          if (k < rd.list.length) parts.push(short(rd, k, 'D') + (k === rd.list.length - 1 ? ', and halts: ' + (rd.verdict === 'accept' ? 'yes' : 'no') : ''));
          parts.push(short(rr, k, 'R') + (k === rr.list.length - 1 && rr.verdict === 'accept' ? ', and halts: yes' : ''));
          say = 'Step ' + k + ': ' + parts.join('; ') + '.';
        }
        F.add({ items: a.items.concat(b.items), say });
      }
      const dv = rd.verdict === 'accept' ? 'accepts' : 'rejects';
      const rv = rr.verdict === 'accept' ? 'accepts too' : rr.verdict === 'loop' ? 'is spinning in place: its configuration repeats, so it will never halt, and never say no' : 'is walking right into blanks for ever: it never halts, and never says no';
      const lastItems = F.last().items;
      F.add({ items: lastItems, say: 'D ' + dv + ' ' + (inp.w || 'ε') + '. R ' + rv + '. ' + (rr.verdict === 'accept' ? 'On strings in the language the two behave alike.' : 'Both are correct: R recognises the language, D decides it. Only D can be used to answer the question in every case.'), mark: rr.verdict === 'accept' ? 'both accept' : 'R never halts' });
      F.list[0].predict = { ask: 'Will the recogniser R halt on ' + (inp.w || 'ε') + '?', options: ['Yes', 'No'], answer: rr.verdict === 'accept' ? 'Yes' : 'No', explain: rr.verdict === 'accept' ? 'The string is in the language, so R must halt and accept.' : 'The string is not in the language. R has no reject state; it ' + (rr.verdict === 'loop' ? 'stays on the blank for ever.' : 'walks off to the right for ever.'), pick: 'option' };
      const defD = tk.defOf(Md, { title: 'Decider D' }), defR = tk.defOf(Mr, { title: 'Recogniser R' });
      return { frames: F.list, def: { sections: [defD.sections[0], Object.assign({}, defD.sections[1], { id: 'dd', title: 'δ of D' }), defR.sections[0], Object.assign({}, defR.sections[1], { id: 'dr', title: 'δ of R' }), { id: 'words', kind: 'text', title: 'The words', text: 'L is decidable when some machine halts on every input and accepts exactly L. L is recognisable (recursively enumerable) when some machine accepts exactly L, halting on every member but maybe running for ever on the rest.' }] } };
    },
    quiz: [
      { q: 'A recogniser for L is run on w and has not halted after a million steps. What do you know?', options: ['w is not in L', 'w is in L', 'Nothing yet: it may halt and accept later', 'The machine is broken'], answer: 2, why: 'A recogniser can take as long as it likes before accepting a member, and may never halt on a non-member. Waiting longer tells you nothing for sure.' },
      { q: 'Every decider is also…', options: ['a recogniser', 'a finite automaton', 'a transducer', 'nondeterministic'], answer: 0, why: 'A decider accepts exactly its language and halts on members, so it meets the definition of a recogniser too.' },
      { q: 'Here both machines recognise the same language. What makes D a decider and R not?', options: ['D has fewer states', 'D halts on every input, R does not', 'D accepts more strings', 'R is nondeterministic'], answer: 1, why: 'They accept the same strings. The difference is only on strings outside the language: D halts in no, R runs for ever.' },
      { q: 'The two ways R fails to halt here are spinning on one cell and walking right for ever. Which one can a simulator detect by spotting a repeated configuration?', options: ['Spinning on one cell', 'Walking right for ever', 'Both', 'Neither'], answer: 0, why: 'Spinning returns to the same configuration. Walking right reaches a new head position each step, so no configuration repeats even though it never halts.' },
      { q: 'If both L and its complement are recognisable, then L is…', options: ['regular', 'decidable', 'not decidable', 'finite'], answer: 1, why: 'Run the two recognisers in alternation, one step each: one of them must accept, and that answers the question. So L is decidable.' },
    ],
  });

  // ======================================================================================================
  // Machines that compute functions: the output is what is on the tape when they halt
  // ======================================================================================================
  const FUNS = {
    add: { id: 'unary-add', name: 'unary addition', alpha: '1+', check: (w) => /^1*\+1*$/.test(w) ? null : 'Input: two unary numbers joined by +, like 11+111', f: (w) => '1'.repeat(w.length - 1), wrong: (w) => ['1'.repeat(w.length), '1'.repeat(Math.max(0, w.length - 2))], show: (w) => { const [a, b] = w.split('+'); return a.length + ' + ' + b.length; }, val: (o) => String(o.length) },
    inc: { id: 'bin-inc', name: 'binary increment', alpha: '01', check: (w) => /^[01]*$/.test(w) ? null : 'Input: a binary number', f: (w) => T.tmLib.entry('bin-inc').oracle(w), wrong: (w) => [w ? w.slice(0, -1) + (w.slice(-1) === '1' ? '0' : '1') : '0', (parseInt(w || '0', 2) + 1).toString(2).slice(-Math.max(1, w.length))], show: (w) => (w || 'ε') + ' (' + parseInt(w || '0', 2) + ')', val: (o) => o + ' (' + parseInt(o || '0', 2) + ')' },
    copy: { id: 'copy', name: 'copy', alpha: 'ab', check: (w) => /^[ab]*$/.test(w) ? null : 'Input: a string of a and b', f: (w) => w + '#' + w, wrong: (w) => [w + '#' + [...w].reverse().join(''), w + w], show: (w) => w || 'ε', val: (o) => o },
  };
  T.topic({
    id: 'tm-transducer', family: 'tm', order: 40, title: 'Machines that compute functions',
    blurb: 'A transducer is a machine whose answer is what it leaves on the tape. Unary addition, binary increment and copying, each with a function box that waits for the result.',
    inputs: [
      { id: 'f', kind: 'choice', label: 'Function', def: 'add', options: [{ value: 'add', label: 'unary addition' }, { value: 'inc', label: 'binary increment' }, { value: 'copy', label: 'copy w to w#w' }] },
      { id: 'w', kind: 'string', label: 'Input', def: '11+1', max: 6, check: (v, inp) => FUNS[inp.f].check(v) },
    ],
    presets: [
      { label: '2 + 1 in unary', values: { f: 'add', w: '11+1' } },
      { label: '0 + 2: nothing before the +', values: { f: 'add', w: '+11' } },
      { label: '1011 + 1 in binary', values: { f: 'inc', w: '1011' } },
      { label: '111 + 1: one digit more', values: { f: 'inc', w: '111' } },
      { label: 'Copy ab', values: { f: 'copy', w: 'ab' } },
      { label: 'Copy ε', values: { f: 'copy', w: '' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'writes', label: 'symbols written' }],
    run(inp) {
      const tk = TK();
      const fn = FUNS[inp.f];
      const M = T.tmLib.get(fn.id);
      const run = tk.trace(M, inp.w, { max: 400 });
      const d = tk.diagram(M), pos = K.graph.layout(d, M.states.length > 4 ? { mode: 'layered', gapX: 130, gapY: 96 } : {}).pos;
      const g0 = K.graph.draw(d, { pos });
      const N = 12, CW = 44;
      const tx = g0.box.x + g0.box.w / 2 - (N * CW) / 2, ty = g0.box.y + g0.box.h + 70;
      const sc = K.tape.scroller({ cells: N, origin: -2 });
      const def = tk.defOf(M);
      const out = T.tm.outputOf(M, run.last);
      const F = new T.Frames(['steps', 'writes']);
      const box = (res, cls) => {
        const y = ty + CW + 70, x = tx;
        return [
          { key: 'fbox', kind: 'region', x, y, w: N * CW, h: 56, rx: 12, text: '', cls: 'tu-box' + (cls ? ' ' + cls : '') },
          { key: 'ftext', kind: 'text', x: x + 18, y: y + 35, text: fn.name + '(' + (inp.w || 'ε') + ') = ' + res, cls: 'mono', mono: true, size: 18 },
        ];
      };
      const scene = (cfg, gopts, res, cls, headCls) => K.graph.draw(d, Object.assign({ pos }, gopts)).items.concat(tk.tape(cfg, { state: cfg.state, cells: N, cw: CW, origin: sc.at(cfg.heads[0].p), prevOrigin: sc.prev, x: tx, y: ty, label: 'tape', headCls }).items, box(res, cls));
      F.add({ items: scene(run.list[0].cfg, { active: [M.start], startHot: true }, '?'), say: 'The function is ' + fn.name + ' and its argument, ' + (inp.w || 'ε') + ', is on the tape. Whatever the tape holds when the machine halts is the value.' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        F.count('steps');
        if (rule.write[0] !== rule.read[0]) F.count('writes');
        F.add({ items: scene(cfg, { active: [cfg.state], taken: [rule.from + '>' + rule.to] }, '?'), say: tk.sayRule(rule), hl: def.hl(rule) });
      }
      const last = run.last;
      F.add({ items: scene(last, { good: [last.state] }, out || 'ε', 'hot', 'good'), say: 'The machine halts in ' + last.state + '. The tape holds ' + (out || 'nothing but blanks, ε') + ', so ' + fn.name + '(' + (inp.w || 'ε') + ') = ' + (out || 'ε') + (inp.f === 'add' ? ': ' + fn.show(inp.w) + ' = ' + out.length + '.' : inp.f === 'inc' ? ', that is ' + fn.val(out) + '.' : '.'), mark: 'output' });
      const right = fn.f(inp.w);
      const opts = [...new Set([right].concat(fn.wrong(inp.w)))].map((x) => x || 'ε');
      if (opts.length >= 2 && F.list.length > 3) F.list[1].predict = { ask: 'What will the tape hold when the machine halts?', options: opts.slice().sort(), answer: right || 'ε', explain: 'The machine computes ' + fn.name + ': the result is ' + (right || 'ε') + '.', pick: 'option' };
      return { frames: F.list, def: { sections: def.sections.concat([{ id: 'fn', kind: 'text', title: 'Computing a function', text: 'M computes f when, started with w on the tape, it halts with f(w) on the tape (blanks at either end ignored). If M never halts on w, f(w) is undefined: the function is partial.' }]) } };
    },
    quiz: [
      { q: 'How does the unary adder turn 11+1 into 111?', options: ['It counts and writes 3', 'It overwrites the + with 1 and erases the last 1', 'It copies both numbers', 'It moves the second number left'], answer: 1, why: 'Filling the gap adds a 1, erasing one at the end takes it away again: 11+1 → 1111 → 111.' },
      { q: 'Incrementing 0111 gives 1000. Which cells does the machine change?', options: ['Only the last', 'The last three 1s and the 0 before them', 'All four, and one more', 'None'], answer: 1, why: 'The carry turns each trailing 1 into 0 and stops at the first 0, which becomes 1.' },
      { q: 'What does the copier use the capital letters A and B for?', options: ['To mark symbols already copied, so it can find the next one', 'For the output', 'They are part of the input', 'To mark the end of the tape'], answer: 0, why: 'Each trip carries one symbol to the end; marking it A or B shows where to pick up next time. At the end they are turned back into a and b.' },
      { q: 'If a transducer never halts on some input, the function it computes is…', options: ['zero there', 'undefined there', 'the input itself', 'not a function at all'], answer: 1, why: 'Machines compute partial functions: no halt, no value.' },
    ],
  });

  // ======================================================================================================
  // Designing a machine for aⁿbⁿcⁿ: cross off one of each per round, coloured by round
  // ======================================================================================================
  const PLAN = [
    'q0: cross off the next a (a → X)',
    'q1: skip a and Y, cross off a b (b → Y)',
    'q2: skip b and Z, cross off a c (c → Z)',
    'q3: walk back left to the last X',
    'q4, q5: no a is left: only Y…Y Z…Z may remain',
  ];
  const planOf = (q, rd) => (q === 'q0' ? (rd === 'a' ? 0 : 4) : q === 'q1' ? 1 : q === 'q2' ? 2 : q === 'q3' ? 3 : 4);
  T.topic({
    id: 'tm-anbncn', family: 'tm', order: 50, title: 'Designing a machine: aⁿbⁿcⁿ',
    blurb: 'No pushdown automaton can check that three counts agree, but a Turing machine can: cross off one a, one b and one c per round, and colour each round so the matching is plain to see.',
    inputs: [{ id: 'w', kind: 'string', label: 'Input', def: 'aabbcc', alphabet: 'abc', max: 9 }],
    presets: [
      { label: 'aabbcc', values: { w: 'aabbcc' } },
      { label: 'abc', values: { w: 'abc' } },
      { label: 'aaabbbccc', values: { w: 'aaabbbccc' } },
      { label: 'aabbc: a c is missing', values: { w: 'aabbc' } },
      { label: 'abcabc: wrong order', values: { w: 'abcabc' } },
      { label: 'ε: zero of each', values: { w: '' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'round', label: 'rounds' }],
    run(inp) {
      const tk = TK();
      const M = T.tmLib.get('anbncn');
      const run = tk.trace(M, inp.w, { max: 400 });
      const n = inp.w.length;
      const N = Math.max(8, n + 3), CW = 48;
      const def = tk.defOf(M);
      const round = new Map();   // place -> round it was crossed off in
      let r = 0;
      const F = new T.Frames(['steps', 'round']);
      const scene = (cfg, k, headCls, planCls) => {
        const items = tk.tape(cfg, { state: cfg.state, cells: N, cw: CW, origin: -1, x: 0, y: 0, label: 'tape', headCls, cls: (i) => (round.has(i) ? 'tu-k' + (((round.get(i) - 1) % 6) + 1) : '') }).items;
        const rd = tk.reads(cfg)[0];
        const lst = tk.listing({ lines: PLAN, x: 0, y: CW + 92, hot: planCls ? null : planOf(cfg.state, rd), done: planCls === 'good' ? 4 : null, bad: planCls === 'bad' ? planOf(cfg.state, rd) : null, prefix: 'plan', num: false, size: 15, lh: 30 });
        items.push(...lst.items);
        items.push({ key: 'planT', kind: 'text', x: 0, y: CW + 68, text: 'the plan', cls: 'title' });
        if (r) items.push({ key: 'roundT', kind: 'text', x: N * CW, y: -26, text: 'round ' + r, anchor: 'end', cls: 'hot' });
        void k;
        return items;
      };
      F.add({ items: scene(run.list[0].cfg, 0), say: (n ? 'The input ' + inp.w + ' is on the tape. ' : 'The tape is empty. ') + 'Each round crosses off one a (as X), one b (as Y) and one c (as Z); the colours show which three went together.' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        const p = run.list[k - 1].cfg.heads[0].p;
        if (rule.write[0] === 'X' && rule.read[0] === 'a') { r++; F.set('round', r); }
        if (rule.write[0] !== rule.read[0] && /[XYZ]/.test(rule.write[0])) round.set(p, r);
        F.count('steps');
        const crossed = rule.write[0] !== rule.read[0];
        F.add({ items: scene(cfg, k), say: crossed ? 'Round ' + r + ': ' + rule.read[0] + ' becomes ' + rule.write[0] + ' (' + PLAN[planOf(rule.from, rule.read[0])].split(': ')[1] + ').' : tk.sayRule(rule), hl: def.hl(rule), meta: { p, crossed } });
      }
      const last = run.last, good = run.verdict === 'accept';
      const why = good ? (n ? 'Every a, b and c was crossed off in ' + r + ' round' + (r === 1 ? '' : 's') + ', so there were ' + r + ' of each, in order: accept.' : 'There is nothing to cross off: zero of each, which is fine. Accept.')
        : 'In ' + last.state + ' the head reads ' + tk.sym(tk.reads(last)[0]) + ' and the plan has no move for it' + (last.state === 'q2' ? ': a b was crossed off but no c was found to go with it' : last.state === 'q1' ? ': an a was crossed off but there is no b for it' : last.state === 'q4' || last.state === 'q5' ? ': after the a\'s ran out, something other than Y…Y Z…Z is left' : '') + '. Reject.';
      F.add({ items: scene(last, 0, good ? 'good' : 'bad', good ? 'good' : 'bad'), say: why, mark: good ? 'accepted' : 'rejected' });
      // predict which cell gets crossed off next, once a round has started
      const fr = F.list;
      for (let i = 2; i < fr.length - 2; i++) {
        if (fr[i].meta && fr[i].meta.crossed) {
          for (let j = i + 1; j < fr.length - 1; j++) if (fr[j].meta && fr[j].meta.crossed) { fr[i].predict = { ask: 'Click the cell the machine will cross off next.', answer: 't:c:' + fr[j].meta.p, explain: fr[j].say, pick: 'item' }; break; }
          break;
        }
      }
      return { frames: fr, def: { sections: def.sections.concat([{ id: 'plan', kind: 'text', title: 'Why it works', text: 'Each round removes exactly one a, one b and one c, and a round can only start while an a is left. When the a\'s run out, accept exactly when nothing but crossed-off symbols remain, in the order Y…Y Z…Z. So the counts agree and the order is a…ab…bc…c.' }]) } };
    },
    quiz: [
      { q: 'Why does the machine cross symbols off instead of erasing them?', options: ['Erasing is not allowed', 'Blanks inside the input would look like its end', 'Crossing off is faster', 'To use fewer states'], answer: 1, why: 'The machine finds the ends of the input by meeting blanks. X, Y and Z keep the cells occupied, so the shape of the input survives.' },
      { q: 'How many rounds does the machine make on aⁿbⁿcⁿ?', options: ['1', 'n', '3n', 'n²'], answer: 1, why: 'One a, one b and one c disappear per round, so n rounds.' },
      { q: 'Roughly how many steps does it take on an input of length 3n?', options: ['about 3n', 'about n²', 'about 2ⁿ', 'about log n'], answer: 1, why: 'Each of the n rounds walks across most of the input and back: a few times 3n steps, n times, which grows like n².' },
      { q: 'On abcabc the machine rejects. Where does it notice?', options: ['At the first a', 'After round one, when it finds an a after the Z', 'At the very end only', 'It accepts'], answer: 1, why: 'After X Y Z, q0 sees Y and goes to the final check, which allows only Y and Z; the next a has no move, so the run halts and rejects.' },
    ],
  });

  // ======================================================================================================
  // A palindrome checker: the head's path through time is a zig-zag
  // ======================================================================================================
  T.topic({
    id: 'tm-palindrome', family: 'tm', order: 60, title: 'Palindromes: the zig-zag',
    blurb: 'Erase the first symbol, remember it in the state, run to the far end and check the last one matches. The head\'s path through time, drawn under the tape, is a zig-zag that shows why this takes about n² steps.',
    inputs: [{ id: 'w', kind: 'string', label: 'Input', def: 'abba', alphabet: 'ab', max: 7 }],
    presets: [
      { label: 'abba', values: { w: 'abba' } },
      { label: 'aba: odd length', values: { w: 'aba' } },
      { label: 'abaaba', values: { w: 'abaaba' } },
      { label: 'ab: caught at the first check', values: { w: 'ab' } },
      { label: 'abab: caught at once', values: { w: 'abab' } },
      { label: 'ε', values: { w: '' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'sweeps', label: 'sweeps' }],
    run(inp) {
      const tk = TK();
      const M = T.tmLib.get('palindrome');
      const run = tk.trace(M, inp.w, { max: 400 });
      const n = inp.w.length, CW = 46, N = Math.max(6, n + 2);
      const total = run.list.length - 1;
      const DY = Math.max(6, Math.min(16, 300 / Math.max(1, total)));
      const y0 = CW + 66;
      const def = tk.defOf(M);
      const cx = (p) => (p + 1) * CW + CW / 2;
      const F = new T.Frames(['steps', 'sweeps']);
      let sweeps = 0;
      const turns = [];
      const scene = (k, headCls) => {
        const { cfg } = run.list[k];
        const gone = new Set();
        for (let j = 1; j <= k; j++) { const r = run.list[j].rule; if (r.write[0] === '_' && r.read[0] !== '_') gone.add(run.list[j - 1].cfg.heads[0].p); }
        const items = tk.tape(cfg, { state: cfg.state, cells: N, cw: CW, origin: -1, x: 0, y: 0, label: 'tape', headCls, cls: (i) => (gone.has(i) ? 'tu-gone' : '') }).items;
        for (let p = -1; p <= n; p++) items.push({ key: 'guide' + p, kind: 'line', x1: cx(p), y1: CW + 46, x2: cx(p), y2: y0 + total * DY + 8, cls: 'dash', audit: 'ignore', opacity: 0.35 });
        items.push({ key: 'axis', kind: 'text', x: -30, y: y0 + 5, text: 'time ↓', anchor: 'end', cls: 'title' });
        for (let j = 1; j <= k; j++) {
          const a = run.list[j - 1].cfg.heads[0].p, b = run.list[j].cfg.heads[0].p;
          items.push({ key: 'tr' + j, kind: 'line', x1: cx(a), y1: y0 + (j - 1) * DY, x2: cx(b), y2: y0 + j * DY, cls: 'tu-trail' + (j < k - 12 ? ' old' : ''), audit: 'ignore', enter: 'grow' });
        }
        items.push({ key: 'dot', kind: 'token', x: cx(cfg.heads[0].p), y: y0 + k * DY, r: 6, cls: 'tu-dot' + (headCls ? ' ' + headCls : ''), audit: 'ignore' });
        for (const t of turns) if (t.k <= k) items.push({ key: 'turn' + t.k, kind: 'text', x: cx(t.p) + (t.side > 0 ? 18 : -18), y: y0 + t.k * DY + 5, text: t.text, anchor: t.side > 0 ? 'start' : 'end', cls: 'tu-num', size: 12 });
        return items;
      };
      // where the head turns round: a sweep ends
      for (let k = 1; k < run.list.length - 1; k++) {
        const a = run.list[k - 1].cfg.heads[0].p, b = run.list[k].cfg.heads[0].p, c = run.list[k + 1].cfg.heads[0].p;
        if ((b - a) * (c - b) < 0 || (b === a && k === 1)) turns.push({ k, p: b, side: c < b ? 1 : -1, text: '' });
      }
      turns.forEach((t, i) => { t.text = 'turn ' + (i + 1); });
      F.add({ items: scene(0), say: (n ? 'The input ' + inp.w + ' is on the tape.' : 'The input is empty, and ε reads the same both ways.') + ' Under the tape, time runs downwards: each step adds a segment from where the head was to where it is.' });
      for (let k = 1; k < run.list.length; k++) {
        const { rule } = run.list[k];
        F.count('steps');
        if (turns.some((t) => t.k === k)) F.count('sweeps');
        let say = tk.sayRule(rule);
        if (rule.from === 'q0' && rule.read[0] !== '_') say = 'Erase the first symbol, ' + rule.read[0] + ', and remember it in the state ' + rule.to + '.';
        else if ((rule.from === 'ta' || rule.from === 'tb') && rule.read[0] !== '_') say = 'The last symbol is ' + rule.read[0] + ', the same as the first one remembered in ' + rule.from + ': erase it and head back.';
        else if (rule.from === 'back' && rule.to === 'q0') say = 'Back at the left end: the outer pair matched, and the inside is what remains to check.';
        F.add({ items: scene(k), say, hl: def.hl(rule) });
      }
      const good = run.verdict === 'accept', last = run.last;
      F.add({ items: scene(run.list.length - 1, good ? 'good' : 'bad'), say: good ? 'Nothing is left to compare: ' + (inp.w || 'ε') + ' is a palindrome. ' + total + ' steps for ' + n + ' symbols; the zig-zag has about n/2 sweeps of about n steps each, so the time grows like n².' : 'In ' + last.state + ' the head reads ' + tk.sym(tk.reads(last)[0]) + ': the last symbol is not the one remembered. Not a palindrome, after ' + total + ' steps.', mark: good ? 'accepted' : 'rejected' });
      // predict where the first long sweep turns round
      const fr = F.list;
      if (turns.length && turns[0].k > 1 && turns[0].k < fr.length - 1) fr[1].predict = { ask: 'The head is carrying the first symbol to the right. Click the cell where it will turn round.', answer: 't:c:' + turns[0].p, explain: 'It runs past the last symbol to the blank and steps back onto the last symbol, cell ' + turns[0].p + '.', pick: 'item' };
      // the cost for growing palindromes, for the definition panel
      const cost = [];
      for (let m = 0; m <= 8; m++) cost.push([String(m), String(T.tm.run(M, 'a'.repeat(m), { trace: false }).steps), String(Math.round((m * m) / 2 + 2 * m))]);
      return { frames: fr, def: { sections: def.sections.concat([{ id: 'cost', kind: 'table', title: 'Steps on aⁿ, against n²/2 + 2n', colHead: ['n', 'steps', 'n²/2 + 2n'], rows: cost }]) } };
    },
    quiz: [
      { q: 'Why must the machine remember the first symbol in its state?', options: ['The tape cannot hold it', 'It erases it and must compare it with the last symbol, far away', 'To save steps', 'It does not need to'], answer: 1, why: 'Only the state travels with the head, and with two letters two states suffice: pa remembers a, pb remembers b.' },
      { q: 'How does the number of steps grow with the length n?', options: ['Like n', 'Like n²', 'Like 2ⁿ', 'Like log n'], answer: 1, why: 'Each pair costs a walk across what remains, so about n + (n − 2) + (n − 4) + … steps, which is about n²/4 each way: quadratic.' },
      { q: 'A two-tape machine can check palindromes in about…', options: ['n steps', 'n² steps', 'n³ steps', '2ⁿ steps'], answer: 0, why: 'Copy the input to the second tape, then read one tape forwards and the other backwards together: a few passes of n steps.' },
      { q: 'On abab the machine rejects quickly. Why?', options: ['The first and last symbols differ', 'It has odd length', 'It contains ab', 'The tape is too short'], answer: 0, why: 'It remembers a, runs to the end and finds b: the very first comparison fails.' },
    ],
  });
})();
