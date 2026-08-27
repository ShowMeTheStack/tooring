// Other models of computation: register machines and RAMs, two-counter machines, linear-bounded automata,
// unrestricted grammars rewriting a string, and the Chomsky hierarchy with a machine for each level.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const TK = () => T.TK;

  T.family({ id: 'models', part: 'turing', order: 40, title: 'Other models', blurb: 'Registers that count, counters that only go up and down, a tape walled in on both sides, grammars with any rules at all: each a model of computation, and how they line up.' });

  // ======================================================================================================
  // Register machines and RAMs
  // ======================================================================================================
  const ramText = (id) => T.ram.lib.find((x) => x.id === id).text.replace(/^\n/, '');
  const SPIN = 'loop: inc r0\n  jmp loop';
  const OPS = [
    ['inc r', 'r := r + 1'], ['dec r', 'r := r − 1, but not below 0'], ['jz r L', 'jump to L if r = 0'], ['jmp L', 'jump to L'], ['halt', 'stop; the answer is r0'],
    ['set r k', 'r := k'], ['copy r s', 'r := s'], ['add r s', 'r := r + s'], ['sub r s', 'r := r − s, not below 0'], ['jnz r L', 'jump if r ≠ 0'], ['load r s', 'r := R[s]: the register whose number is in s'], ['store r s', 'R[r] := s: write into the register whose number is in r'],
  ];
  const opRow = (op) => OPS.findIndex((o) => o[0].split(' ')[0] === op);
  /** "r1=3, r2=2" into {1: 3, 2: 2} */
  const regsOf = (text) => { const o = {}; for (const m of String(text).matchAll(/r(\d+)\s*=\s*(\d+)/gi)) o[+m[1]] = +m[2]; return o; };
  T.topic({
    id: 'ram-run', family: 'models', order: 10, title: 'Register machines and RAMs',
    blurb: 'Registers hold whole numbers of any size; a program adds one, takes one away and jumps when a register is zero. That is already enough for everything a Turing machine can do. A RAM adds arithmetic and registers named by other registers.',
    inputs: [
      { id: 'p', kind: 'program', label: 'Program', def: ramText('mul'), check: (v) => { const r = T.ram.parse(v); if (r.errors.length) return 'Program: line ' + r.errors[0].line + ': ' + r.errors[0].msg; if (String(v).split('\n').length > 16) return 'Program: at most 16 lines'; return null; } },
      { id: 'r', kind: 'text', label: 'Registers at the start', def: 'r1=2, r2=3', check: (v) => (/^\s*(r\d+\s*=\s*\d+\s*,?\s*)*$/i.test(v) ? (Object.values(regsOf(v)).some((x) => x > 12) ? 'Registers: values up to 12, so the picture stays readable' : null) : 'Registers: write them like r1=2, r2=3') },
    ],
    presets: [
      { label: 'Multiply 2 × 3', values: { p: ramText('mul'), r: 'r1=2, r2=3' } },
      { label: 'Add 3 + 2', values: { p: ramText('add'), r: 'r1=3, r2=2' } },
      { label: 'Subtract 2 − 5: stops at 0', values: { p: ramText('monus'), r: 'r1=2, r2=5' } },
      { label: '2 to the power 3', values: { p: ramText('pow2'), r: 'r1=3' } },
      { label: 'RAM: sum of an array', values: { p: ramText('sum-array'), r: 'r1=3, r10=4, r11=1, r12=5' } },
      { label: 'A program that never halts', values: { p: SPIN, r: '' } },
    ],
    counters: [{ id: 'steps', label: 'instructions run' }, { id: 'r0', label: 'r0' }],
    run(inp) {
      const tk = TK();
      const P = T.ram.parse(inp.p);
      const regs0 = regsOf(inp.r);
      const res = T.ram.run(P, regs0, { maxSteps: 90 });
      const lines = String(inp.p).split('\n').map((l) => l.replace(/\s+$/, ''));
      const lst = tk.listing({ lines, x: 0, y: 0 });
      // the registers to show: those the program names, those given, those it writes
      const used = new Set([0]);
      for (const i of P.prog) { if (i.a !== undefined) used.add(i.a); if (i.b !== undefined) used.add(i.b); }
      for (const k in regs0) used.add(+k);
      for (const s of res.trace) for (const k in s.regs || {}) used.add(+k);
      const ids = [...used].sort((a, b) => a - b).slice(0, 9);
      const RX = lst.box.w + 60, RW = 62, RG = 14, BASE = 210, UNIT = 13;
      const rx = (r) => RX + ids.indexOf(r) * (RW + RG);
      const F = new T.Frames(['steps', 'r0']);
      const scene = (regs, pc, changed, ptr, endCls) => {
        const items = tk.listing({ lines, x: 0, y: 0, hot: pc === null ? null : pc, done: endCls === 'good' ? null : null }).items;
        items.push({ key: 'regT', kind: 'text', x: RX, y: -24, text: 'REGISTERS', cls: 'title' });
        for (const r of ids) {
          const v = regs[r] || 0, x = rx(r);
          const hot = changed && r in changed;
          const h = Math.min(12, v) * UNIT;
          if (v) items.push({ key: 'bar' + r, kind: 'cell', x: x + 12, y: BASE - 8 - h, w: RW - 24, h, text: '', rx: 4, cls: 'tu-k' + (r === 0 ? 3 : 1) });
          items.push({ key: 'reg' + r, kind: 'cell', x, y: BASE, w: RW, h: 44, text: String(v), cls: 'mono' + (hot ? ' hot' : r === 0 && endCls ? ' ' + endCls : ''), rx: 6 });
          items.push({ key: 'rn' + r, kind: 'text', x: x + RW / 2, y: BASE + 64, text: 'r' + r, anchor: 'middle', cls: 'strong' });
        }
        if (ptr && ids.includes(ptr[0]) && ids.includes(ptr[1]) && ptr[0] !== ptr[1]) items.push({ key: 'ptr', kind: 'edge', from: 'reg' + ptr[0], to: 'reg' + ptr[1], bend: rx(ptr[0]) < rx(ptr[1]) ? -60 : 60, cls: 'alt', audit: 'ignore', layer: 'top' });
        return items;
      };
      const lineOf = (pc) => (pc < P.prog.length ? P.prog[pc].line - 1 : null);
      F.add({ items: scene(Object.assign({}, regs0), lineOf(0), null, null), say: 'The registers start as given (every other one holds 0) and the program starts at its first instruction. When it halts, the answer is in r0.' });
      let jzFrame = null;
      for (const s of res.trace) {
        if (s.kind !== 'exec') continue;
        F.count('steps').set('r0', s.regs[0] || 0);
        const ins = P.prog[s.pc];
        let ptr = null;
        if (ins.op === 'load') ptr = [ins.b, (res.trace[res.trace.indexOf(s) - 1] || { regs: regs0 }).regs[ins.b] || regs0[ins.b] || 0];
        if (ins.op === 'store') ptr = [ins.a, s.regs[ins.a] || 0];
        const fr = F.add({ items: scene(s.regs, lineOf(s.next), s.changed, ptr), say: ins.text + ': ' + s.say, hl: { ops: [String(opRow(ins.op))] }, meta: { op: ins.op, jumped: s.next !== s.pc + 1, ins: ins.text } });
        if (!jzFrame && ins.op === 'jz' && F.list.length > 2) jzFrame = fr;
      }
      const fin = res.trace[res.trace.length - 1];
      const halted = res.verdict === 'halt';
      F.add({ items: scene(fin.regs, null, null, null, halted ? 'good' : 'bad'), say: halted ? 'Halted after ' + res.steps + ' instructions with r0 = ' + res.output + '.' : 'After ' + res.steps + ' instructions it is still going round its loop, and it always will: there is no way out of it.', mark: halted ? 'halted' : 'never halts' });
      const fr = F.list;
      if (jzFrame) { const i = fr.indexOf(jzFrame); fr[i - 1].predict = { ask: 'Next is ' + jzFrame.meta.ins + '. Will it jump?', options: ['Yes', 'No'], answer: jzFrame.meta.jumped ? 'Yes' : 'No', explain: jzFrame.say, pick: 'option' }; }
      else if (fr.length > 3) fr[1].predict = { ask: 'Which register will change in the next instruction?', options: ids.slice(0, 4).map((r) => 'r' + r), answer: 'r' + (Object.keys(res.trace[1] && res.trace[1].changed || {})[0] || ids[0]), explain: fr[2].say, pick: 'option' };
      if (fr[1].predict && !fr[1].predict.options.includes(fr[1].predict.answer)) delete fr[1].predict;
      return { frames: fr, def: { sections: [
        { id: 'ops', kind: 'table', title: 'Instructions', colHead: ['instruction', 'meaning'], rows: OPS.map((o) => [o[0], o[1]]) },
        { id: 'kind', kind: 'text', title: P.core ? 'A register machine' : 'A random-access machine', text: P.core ? 'This program uses only inc, dec, jz, jmp and halt: a plain register machine. With that alone, every computable function can be computed.' : 'This program uses RAM extras. load and store name a register by the number held in another one, like an array index: the arrow shows which register is meant.' },
      ] } };
    },
    quiz: [
      { q: 'With only inc, dec and jz, how does the program copy r1 to r2 without losing r1?', options: ['It cannot', 'Move r1 into r2 and a spare register at once, then move the spare back into r1', 'With a copy instruction', 'By reading r1 twice'], answer: 1, why: 'Every move destroys the source, so a scratch register holds a second copy. The multiplier restores r2 the same way after each round.' },
      { q: 'Can a register machine simulate a Turing machine?', options: ['No, it has no tape', 'Yes: two registers can hold the tape left and right of the head as numbers', 'Only for finite tapes', 'Only a RAM can'], answer: 1, why: 'Read the tape on each side of the head as a number in base |Γ|; moving the head is multiplying and dividing by |Γ|, which inc, dec and jz can do.' },
      { q: 'What does load r3 r2 do when r2 holds 11?', options: ['r3 := 11', 'r3 := the value of r11', 'r11 := r3', 'r2 := r3'], answer: 1, why: 'Indirect addressing: r2 names which register to read.' },
      { q: 'What does dec do on a register holding 0?', options: ['Makes it −1', 'Leaves it 0', 'Halts the machine', 'Jumps'], answer: 1, why: 'Registers hold natural numbers, so subtraction stops at 0.' },
    ],
  });

  // ======================================================================================================
  // Two-counter machines
  // ======================================================================================================
  const cText = (id) => T.counter.lib.find((x) => x.id === id).text.replace(/^\n/, '');
  T.topic({
    id: 'counter-run', family: 'models', order: 20, title: 'Two-counter machines',
    blurb: 'Two counters, each a pile of pebbles: add one, take one away, or see that a pile is empty. It looks hopelessly weak, yet with numbers like 2ˣ·3ʸ in one counter it can simulate any Turing machine.',
    inputs: [
      { id: 'p', kind: 'choice', label: 'Program', def: 'double', options: T.counter.lib.map((x) => ({ value: x.id, label: x.title })) },
      { id: 'a', kind: 'number', label: 'A at the start', def: 3, min: 0, max: 12 },
    ],
    presets: [
      { label: 'Double 3', values: { p: 'double', a: 3 } },
      { label: 'Halve 5', values: { p: 'half', a: 5 } },
      { label: 'Is 5 even or odd?', values: { p: 'parity', a: 5 } },
      { label: '12 = 2²·3 becomes 2³', values: { p: 'prime-powers', a: 12 } },
      { label: 'Double 0', values: { p: 'double', a: 0 } },
    ],
    check: (inp) => (inp.p === 'prime-powers' && inp.a < 1 ? 'A at the start: at least 1, a product 2ˣ·3ʸ' : null),
    counters: [{ id: 'steps', label: 'steps' }, { id: 'A', label: 'A' }, { id: 'B', label: 'B' }],
    run(inp) {
      const P = T.counter.parse(cText(inp.p));
      const res = T.counter.run(P, { A: inp.a, B: 0 }, { maxSteps: 160 });
      const states = Object.keys(P.prog);
      const trans = [];
      for (const q of states) { const ins = P.prog[q]; if (ins.op === 'inc') trans.push({ from: q, to: ins.next, label: ins.c + '+1' }); if (ins.op === 'dec') { trans.push({ from: q, to: ins.next, label: ins.c + '−1' }); trans.push({ from: q, to: ins.zero, label: ins.c + '=0' }); } }
      const m = { kind: 'tm', states, start: P.start, accept: states.filter((q) => P.prog[q].op === 'halt'), trans, pos: {} };
      const g0 = K.graph.draw(m, {});
      const pos = g0.pos;
      const PX = g0.box.x + g0.box.w + 70, PB = g0.box.y + g0.box.h;
      const pile = (name, v, x, cls) => {
        const items = [{ key: 'pl' + name, kind: 'text', x: x + 20, y: PB + 30, text: name + ' = ' + v, anchor: 'middle', cls: 'strong', size: 16 }];
        const shown = Math.min(v, 14);
        for (let i = 0; i < shown; i++) items.push({ key: 'pb' + name + i, kind: 'token', x: x + 20, y: PB - 4 - i * 19, r: 8, cls: cls, enter: 'drop', exit: 'rise' });
        if (v > 14) items.push({ key: 'pm' + name, kind: 'text', x: x + 20, y: PB - 4 - 14 * 19, text: '+' + (v - 14), anchor: 'middle', cls: 'tu-small' });
        items.push({ key: 'base' + name, kind: 'line', x1: x, y1: PB + 8, x2: x + 40, y2: PB + 8 });
        return items;
      };
      const F = new T.Frames(['steps', 'A', 'B']);
      const scene = (at, C, taken, cls) => K.graph.draw(m, { pos, active: cls ? [] : [at], good: cls === 'good' ? [at] : [], taken: taken ? [taken] : [] }).items.concat(pile('A', C.A || 0, PX, 'tu-pebble'), pile('B', C.B || 0, PX + 80, 'tu-pebble2'));
      F.set('A', inp.a);
      F.add({ items: scene(P.start, { A: inp.a, B: 0 }), say: 'Counter A holds ' + inp.a + ' pebbles and B is empty. The machine is in ' + P.start + '. A dec move takes a pebble if there is one, and otherwise follows its "=0" arrow.' });
      let decZero = null;
      for (const s of res.trace) {
        if (s.kind !== 'exec') continue;
        const ins = P.prog[s.at];
        F.count('steps').set('A', s.counters.A).set('B', s.counters.B || 0);
        const fr = F.add({ items: scene(s.next, s.counters, s.at + '>' + s.next), say: 'In ' + s.at + ': ' + s.say + (/go to/.test(s.say) ? '' : ' Go to ' + s.next + '.'), meta: { next: s.next, zero: ins.op === 'dec' && s.next === ins.zero } });
        if (!decZero && fr.meta.zero) decZero = fr;
      }
      const fin = res.trace[res.trace.length - 1];
      const out = { double: 'A = ' + fin.counters.A + ', twice ' + inp.a, half: 'A = ' + fin.counters.A + ', half of ' + inp.a + ' rounded down', parity: 'it halted in ' + res.state + ': ' + inp.a + ' is ' + res.state, 'prime-powers': 'A = ' + fin.counters.A + ': the exponents of 2 and 3 in ' + inp.a + ' were added' }[inp.p];
      F.add({ items: scene(res.state, fin.counters, null, 'good'), say: 'Halted after ' + res.steps + ' steps: ' + out + '. With only add, take away and test for empty, two counters do all of this.', mark: 'halted' });
      const fr = F.list;
      if (decZero) { const i = fr.indexOf(decZero); if (i > 1) fr[i - 1].predict = { ask: 'The next move is a dec on an empty counter. Click the state it goes to.', answer: 'g:s:' + decZero.meta.next, explain: decZero.say, pick: 'item' }; }
      return { frames: fr, def: { sections: [
        { id: 'prog', kind: 'math', title: 'The program', text: cText(inp.p).trim() },
        { id: 'why', kind: 'text', title: 'Two counters are enough', text: 'A machine with any number of counters can simulate a Turing machine (two stacks, each a number). Those counters c₁, c₂, c₃ fit in one number 2^c₁·3^c₂·5^c₃; adding one to c₂ is multiplying by 3, and testing c₂ = 0 is testing divisibility by 3, each done with the help of a second counter. So two counters compute every computable function, given the input encoded as 2ⁿ.' },
      ] } };
    },
    quiz: [
      { q: 'What can a dec move tell the machine?', options: ['The exact value', 'Whether the counter was zero', 'Nothing', 'Whether it is even'], answer: 1, why: 'Its only test: take one away if possible, otherwise go the other way. Everything else must be built from that.' },
      { q: 'How does the doubling program keep track of what it has done?', options: ['In its states', 'It moves A into B two pebbles at a time, then moves B back', 'It uses a third counter', 'It guesses'], answer: 1, why: 'Each pebble taken from A becomes two in B; then B is poured back into A.' },
      { q: 'How can one counter hold three numbers x, y, z?', options: ['It cannot', 'As 2ˣ·3ʸ·5ᶻ', 'As x + y + z', 'As x·y·z'], answer: 1, why: 'Prime factorisation is unique, so the exponents can be read back by dividing.' },
      { q: 'Is the halting problem for two-counter machines decidable?', options: ['Yes, there are only two counters', 'No, since they simulate Turing machines', 'Only for small inputs', 'Yes, by counting'], answer: 1, why: 'Two counters suffice to simulate any Turing machine, so their halting problem is just as undecidable. (With one counter it is decidable.)' },
    ],
  });

  // ======================================================================================================
  // Linear-bounded automata: the head stays between two walls
  // ======================================================================================================
  const BOUNCE = 'mode: lba\ninput: a b\nq0, a|b -> q0, *, R\nq0, > -> q1, >, L\nq1, a|b -> q1, *, L\nq1, < -> q0, <, R';
  const LBAS = { abc: { text: () => T.tmLib.entry('anbncn-lba').text.trim(), alpha: 'abc', name: 'aⁿbⁿcⁿ' }, bounce: { text: () => BOUNCE, alpha: 'ab', name: 'a machine that bounces for ever' } };
  T.topic({
    id: 'lba-run', family: 'models', order: 30, title: 'Linear-bounded automata',
    blurb: 'A Turing machine whose head may never leave the cells of its input, held between the walls < and >. With finitely many possible configurations, a run either halts or repeats one: so an LBA\'s acceptance is decidable.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'abc', options: Object.entries(LBAS).map(([value, x]) => ({ value, label: x.name })) },
      { id: 'w', kind: 'string', label: 'Input', def: 'aabbcc', max: 9, check: (v, inp) => ([...v].some((c) => !LBAS[inp.m].alpha.includes(c)) ? 'Input: use only ' + [...LBAS[inp.m].alpha].join(' ') : null) },
    ],
    presets: [
      { label: 'aabbcc', values: { m: 'abc', w: 'aabbcc' } },
      { label: 'aabcc: rejected', values: { m: 'abc', w: 'aabcc' } },
      { label: 'ε: just the walls', values: { m: 'abc', w: '' } },
      { label: 'Bouncing on ab', values: { m: 'bounce', w: 'ab' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'seen', label: 'configurations seen' }],
    run(inp) {
      const tk = TK();
      const M = tk.compile(LBAS[inp.m].text()).M;
      const n = inp.w.length;
      const run = tk.trace(M, inp.w, { max: 400 });
      const bound = T.lba.bound(M, n);
      const CW = 50, cells = n + 2;
      const def = tk.defOf(M);
      const F = new T.Frames(['steps', 'seen']);
      const wallX = cells * CW;
      const scene = (cfg, headCls, extra) => {
        const items = tk.tape(cfg, { state: cfg.state, cells, cw: CW, origin: 0, x: 0, y: 0, label: 'tape', headCls, cls: (i) => (i === 0 || i === n + 1 ? 'tu-wall' : '') }).items.filter((it) => !/more-[lr]$/.test(it.key));
        items.push({ key: 'wl', kind: 'line', x1: -6, y1: -22, x2: -6, y2: CW + 22, cls: 'tu-wall' }, { key: 'wr', kind: 'line', x1: wallX + 6, y1: -22, x2: wallX + 6, y2: CW + 22, cls: 'tu-wall' });
        items.push(...tk.dial('db', wallX / 2, CW + 100, 'configurations possible: |Q|·(n+2)·|Γ|ⁿ', bound.toLocaleString('en')));
        if (extra) items.push(...extra);
        return items;
      };
      F.set('seen', 1);
      F.add({ items: scene(run.list[0].cfg), say: 'The input ' + (inp.w || 'ε') + ' sits between the walls < and >. The machine may read the walls but never cross or overwrite them, so it has only these ' + cells + ' cells to work in.' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        F.count('steps').set('seen', k + 1);
        const atWall = rule.read[0] === '<' || rule.read[0] === '>';
        F.add({ items: scene(cfg), say: tk.sayRule(rule) + (atWall ? ' The wall turns it back.' : ''), hl: def.hl(rule) });
      }
      const v = run.verdict;
      const loop = v === 'loop';
      const extra = loop ? [{ key: 'loopT', kind: 'text', x: wallX / 2, y: -40, text: 'the same configuration as at step ' + run.loopAt, anchor: 'middle', cls: 'bad' }] : null;
      F.add({ items: scene(run.last, v === 'accept' ? 'good' : 'bad', extra), say: v === 'accept' ? 'Accepted after ' + (run.list.length - 1) + ' steps, never leaving the walls.' : loop ? 'Step ' + (run.list.length - 1) + ' repeats the configuration of step ' + run.loopAt + ': this run will cycle for ever. A decider simulating the LBA can stop here and say no; it never needs more than ' + bound.toLocaleString('en') + ' steps to be sure.' : 'Rejected after ' + (run.list.length - 1) + ' steps: no move for ' + run.last.state + ' on ' + tk.sym(tk.reads(run.last)[0]) + '.', mark: v === 'accept' ? 'accepted' : loop ? 'repeats' : 'rejected' });
      const fr = F.list;
      if (fr.length > 2) { const opts = [...new Set([bound, cells, M.states.length * cells, Math.pow(M.gamma.length, n)])].map((x) => x.toLocaleString('en')); fr[0].predict = { ask: 'How many different configurations can this machine have on this input? (|Q| = ' + M.states.length + ', |Γ| = ' + M.gamma.length + ', n = ' + n + ')', options: opts.slice(0, 4).sort(), answer: bound.toLocaleString('en'), explain: 'A state (' + M.states.length + '), a head position (' + cells + ' cells) and contents for the ' + n + ' inner cells (' + M.gamma.length + ' choices each): ' + M.states.length + ' · ' + cells + ' · ' + M.gamma.length + '^' + n + '.', pick: 'option' }; }
      return { frames: fr, def: { sections: def.sections.concat([{ id: 'lba', kind: 'text', title: 'Why LBAs are deciders in disguise', text: 'With q states, n + 2 cells and g tape symbols there are at most q·(n+2)·gⁿ configurations. A run longer than that repeats one and so never halts. Simulate for that many steps: accept if it accepts, reject otherwise. LBAs recognise exactly the context-sensitive languages.' }]) } };
    },
    quiz: [
      { q: 'What stops an LBA using more tape?', options: ['Its states', 'The walls: rules may read < and > but not cross or overwrite them', 'A step limit', 'Nothing'], answer: 1, why: 'The input is held between endmarkers that the machine must respect.' },
      { q: 'Why is "does this LBA accept w?" decidable?', options: ['LBAs always halt', 'There are finitely many configurations, so a run that goes on too long must repeat one', 'LBAs are finite automata', 'It is not decidable'], answer: 1, why: 'Simulate for q·(n+2)·gⁿ steps; if it has not halted it is looping.' },
      { q: 'Which languages do LBAs recognise?', options: ['Regular', 'Context-free', 'Context-sensitive', 'All recognisable ones'], answer: 2, why: 'Nondeterministic LBAs match context-sensitive (noncontracting) grammars.' },
      { q: 'An LBA could still use more space by…', options: ['writing past >', 'using a bigger tape alphabet, packing several symbols into one cell', 'moving faster', 'it cannot'], answer: 1, why: 'A cell can hold a tuple of symbols, so k·n cells fit into n: "linear" bounded.' },
    ],
  });

  // ======================================================================================================
  // Unrestricted grammars: the sentential form rewritten, symbols sliding past each other
  // ======================================================================================================
  const G_LIB = (id) => T.ugrammar.lib.find((x) => x.id === id).text;
  T.topic({
    id: 'ugrammar-derive', family: 'models', order: 40, title: 'Unrestricted grammars',
    blurb: 'A rule may replace any string by any string: cB → Bc lets a variable walk past a terminal. With rules like that, aⁿbⁿcⁿ has a grammar; with no restriction at all, grammars generate exactly the recognisable languages.',
    inputs: [
      { id: 'g', kind: 'program', label: 'Grammar (uppercase variables, one rule per line)', def: G_LIB('anbncn'), check: (v) => { const g = T.ugrammar.parse(v); if (g.errors.length) return 'Grammar: line ' + g.errors[0].line + ': ' + g.errors[0].msg; if (g.prods.length > 14) return 'Grammar: at most 14 rules'; return null; } },
      { id: 'w', kind: 'string', label: 'String', def: 'aabbcc', max: 8 },
    ],
    presets: [
      { label: 'aⁿbⁿcⁿ: aabbcc', values: { g: G_LIB('anbncn'), w: 'aabbcc' } },
      { label: 'aⁿbⁿcⁿ: abc', values: { g: G_LIB('anbncn'), w: 'abc' } },
      { label: 'aⁿbⁿcⁿ: aabbc has no derivation', values: { g: G_LIB('anbncn'), w: 'aabbc' } },
      { label: 'Equal numbers, any order: cab', values: { g: G_LIB('equal-abc'), w: 'cab' } },
      { label: 'Doubling: aaaa', values: { g: G_LIB('double-a'), w: 'aaaa' } },
    ],
    counters: [{ id: 'steps', label: 'derivation steps' }, { id: 'len', label: 'form length' }],
    run(inp) {
      const G = T.ugrammar.parse(inp.g);
      const res = T.ugrammar.derive(G, inp.w, { maxNodes: 30000 });
      const CW = 44, F = new T.Frames(['steps', 'len']);
      let next = 0;
      let row = [{ k: next++, s: G.start }];
      const hist = [];
      const ruleIx = (rule) => G.prods.findIndex((p) => p.lhs + ' → ' + (p.rhs || 'ε') === rule);
      const scene = (opts) => {
        opts = opts || {};
        const items = [];
        const W = Math.max(row.length, 1) * CW;
        const x0 = -W / 2;
        if (!row.length) items.push({ key: 'eps', kind: 'cell', x: -CW / 2, y: 0, w: CW, h: CW, text: 'ε', cls: 'mono empty' });
        row.forEach((c, i) => items.push({ key: 'f' + c.k, kind: 'cell', x: x0 + i * CW, y: 0, w: CW, h: CW, text: c.s, rx: 6, cls: 'mono' + (G.isVar(c.s) ? ' tu-k1' : '') + (opts.win && i >= opts.win[0] && i < opts.win[1] ? (opts.after ? ' hot' : ' src-a') : ''), enter: 'grow', exit: 'shrink', size: 18 }));
        if (opts.rule) items.push({ key: 'rule', kind: 'text', x: 0, y: -30, text: opts.rule, anchor: 'middle', cls: 'mono', mono: true, size: 17 });
        const hs = hist.slice(-5);
        hs.forEach((h, i) => items.push({ key: 'h' + (hist.length - hs.length + i), kind: 'text', x: 0, y: CW + 46 + i * 24, text: (hist.length - hs.length + i ? '⇒ ' : '') + (h || 'ε'), anchor: 'middle', cls: 'mono', mono: true, size: 14, enter: 'fade', exit: 'rise' }));
        items.push({ key: 'histT', kind: 'text', x: 0, y: CW + 24, text: 'THE DERIVATION SO FAR', anchor: 'middle', cls: 'title' });
        return items;
      };
      F.set('len', 1);
      hist.push(G.start);
      F.add({ items: scene(), say: 'Start from ' + G.start + '. Variables are coloured; a rule may rewrite any piece of the string that matches its left side, wherever it is.' });
      if (res.found) {
        const D = res.derivation;
        for (let i = 1; i < D.length; i++) {
          const via = D[i].via, p = G.prods[ruleIx(via.rule)] || { lhs: via.rule.split(' → ')[0], rhs: via.rule.split(' → ')[1].replace('ε', '') };
          const at = via.at, L = p.lhs.length;
          F.add({ items: scene({ win: [at, at + L], rule: via.rule }), say: 'The rule ' + via.rule + ' matches ' + p.lhs + ' at position ' + (at + 1) + '.', hl: { rules: [String(ruleIx(via.rule))] }, meta: { rule: via.rule } });
          // reuse the keys of matching symbols so they glide instead of popping
          const old = row.slice(at, at + L), fresh = [];
          for (const ch of p.rhs) { const j = old.findIndex((o) => o && o.s === ch); if (j >= 0) { fresh.push(old[j]); old[j] = null; } else fresh.push({ k: next++, s: ch }); }
          row = row.slice(0, at).concat(fresh, row.slice(at + L));
          hist.push(D[i].form);
          F.count('steps').set('len', row.length);
          const moved = p.lhs.length === p.rhs.length && [...p.lhs].sort().join('') === [...p.rhs].sort().join('') && p.lhs !== p.rhs;
          F.add({ items: scene({ win: [at, at + p.rhs.length], after: true, rule: via.rule }), say: (D[i].form || 'ε') + (moved ? ': the same symbols, in a new order. This is how a variable travels to where it is needed.' : p.rhs.length < p.lhs.length ? ': the string got shorter, something only a contracting rule can do.' : '.'), hl: { rules: [String(ruleIx(via.rule))] } });
        }
        F.add({ items: scene(), say: 'Only terminals are left: ' + (inp.w || 'ε') + ' is derived in ' + (D.length - 1) + ' steps.', mark: 'derived' });
      } else {
        F.add({ items: scene({ rule: res.exact ? 'no derivation' : 'not found in bounds' }), say: res.exact ? 'The grammar is noncontracting: no rule makes the string shorter, so a derivation of ' + (inp.w || 'ε') + ' passes only through forms of length ≤ ' + inp.w.length + '. All ' + res.explored + ' such forms were tried and none is ' + (inp.w || 'ε') + ': it has no derivation.' : 'No derivation turned up among ' + res.explored + ' forms. With contracting rules, forms may grow and shrink without bound, and no search can be sure.', mark: 'no derivation' });
      }
      const fr = F.list;
      const ask = fr.findIndex((f, i) => i > 2 && f.meta && f.meta.rule);
      if (ask > 0) { const right = fr[ask].meta.rule; const opts = [...new Set([right].concat(G.prods.map((p) => p.lhs + ' → ' + (p.rhs || 'ε'))))].slice(0, 4); if (opts.length >= 2) fr[ask - 1].predict = { ask: 'Which rule does the derivation use next?', options: opts.sort(), answer: right, explain: fr[ask].say, pick: 'option' }; }
      const kind = G.contextFree ? 'context-free' : G.noncontracting ? 'noncontracting (context-sensitive)' : 'unrestricted';
      return { frames: fr, def: { sections: [
        { id: 'rules', kind: 'grammar', title: 'Rules (' + kind + ')', rules: G.prods.map((p) => p.lhs + ' → ' + (p.rhs || 'ε')), nonterminals: [...new Set(G.prods.flatMap((p) => [...p.lhs + p.rhs].filter(G.isVar)))] },
        { id: 'types', kind: 'text', title: 'Kinds of grammar', text: 'Unrestricted: α → β with α not empty; these generate exactly the recognisable languages. Noncontracting (|α| ≤ |β|): the context-sensitive languages, decided by linear-bounded automata. Context-free: α is one variable.' },
      ] } };
    },
    quiz: [
      { q: 'What does the rule cB → Bc achieve in the aⁿbⁿcⁿ grammar?', options: ['It deletes a c', 'It lets B move left past c, so the B\'s gather before the c\'s', 'It makes a b', 'Nothing'], answer: 1, why: 'The rule S → aSBc leaves B\'s among the c\'s; swapping sorts them into place.' },
      { q: 'Why is membership decidable for a noncontracting grammar?', options: ['There are few rules', 'Forms never shrink, so only the finitely many forms no longer than w need to be searched', 'Every derivation is short', 'It is not decidable'], answer: 1, why: 'A derivation of w uses only forms of length ≤ |w|, and there are finitely many of them.' },
      { q: 'Unrestricted grammars generate exactly…', options: ['the decidable languages', 'the recognisable languages', 'the context-sensitive languages', 'all languages'], answer: 1, why: 'A machine can search all derivations; a grammar can mimic a machine\'s configurations with rules.' },
      { q: 'The doubling grammar uses L → ε and R → ε. What does that cost?', options: ['Nothing', 'It is contracting, so a search for derivations can no longer be bounded by the length of w', 'It makes the language finite', 'It makes it context-free'], answer: 1, why: 'Forms may grow and shrink again, so "no derivation found yet" never becomes "none exists" in general.' },
    ],
  });

  // ======================================================================================================
  // The Chomsky hierarchy as nested regions, a grammar form and a machine for each level
  // ======================================================================================================
  const LEVELS = [
    { id: 'reg', label: 'Regular', type: '3', rule: 'A → aB, A → a', machine: 'finite automaton' },
    { id: 'cf', label: 'Context-free', type: '2', rule: 'A → γ', machine: 'pushdown automaton' },
    { id: 'cs', label: 'Context-sensitive', type: '1', rule: 'α → β, |α| ≤ |β|', machine: 'linear-bounded automaton' },
    { id: 'dec', label: 'Decidable', type: '', rule: '–', machine: 'TM that always halts' },
    { id: 're', label: 'Recognisable', type: '0', rule: 'α → β', machine: 'Turing machine' },
    { id: 'all', label: 'All languages', type: '', rule: '–', machine: 'none' },
  ];
  const LANGS = [
    { id: 'l1', label: '(ab)*', in: 'reg', why: 'a finite automaton with two states reads it' },
    { id: 'l2', label: 'aⁿbⁿ', in: 'cf', why: 'a stack counts the a\'s, but a finite automaton cannot (pumping)' },
    { id: 'l3', label: 'palindromes', in: 'cf', why: 'a PDA pushes the first half and pops against the second, after guessing the middle' },
    { id: 'l4', label: 'aⁿbⁿcⁿ', in: 'cs', why: 'it fails the context-free pumping lemma, yet a machine crossing off within the input decides it' },
    { id: 'l5', label: 'ww', in: 'cs', why: 'no PDA can compare two copies, but an LBA can' },
    { id: 'l6', label: 'HALT', in: 're', why: 'running the machine recognises it, but no machine decides it' },
    { id: 'l7', label: 'complement of HALT', in: 'all', why: 'if it were recognisable too, HALT would be decidable' },
  ];
  T.topic({
    id: 'chomsky-map', family: 'models', order: 50, title: 'The Chomsky hierarchy',
    blurb: 'Regular inside context-free inside context-sensitive inside decidable inside recognisable: each class with its kind of grammar and its kind of machine, and a language that lives in each ring and no further in.',
    inputs: [{ id: 'focus', kind: 'choice', label: 'Ask about', def: 'l4', options: LANGS.map((l) => ({ value: l.id, label: l.label })) }],
    presets: [
      { label: 'Where does aⁿbⁿcⁿ go?', values: { focus: 'l4' } },
      { label: 'Where does aⁿbⁿ go?', values: { focus: 'l2' } },
      { label: 'Where does HALT go?', values: { focus: 'l6' } },
      { label: 'And its complement?', values: { focus: 'l7' } },
    ],
    counters: [{ id: 'levels', label: 'classes shown' }, { id: 'langs', label: 'languages placed' }],
    run(inp) {
      const nest = (upto) => { let r = null; for (let i = 0; i <= upto; i++) { const L = LEVELS[i]; r = { id: L.id, label: L.label + (L.type ? ' (type ' + L.type + ')' : ''), children: r ? [r] : [] }; } return r; };
      const F = new T.Frames(['levels', 'langs']);
      const legendX = 470;
      const legend = (hot) => K.table.draw({ x: legendX, y: 0, prefix: 'lg', colHead: ['class', 'rules', 'machine'], rows: LEVELS.slice(0, 5).map((L) => [L.label, L.rule, L.machine]), hot: hot >= 0 && hot < 5 ? [[hot, 0], [hot, 1], [hot, 2]] : [], size: 13 }).items;
      const scene = (upto, placed, hot, focus) => {
        const pts = LANGS.filter((l) => placed.includes(l.id) && LEVELS.findIndex((L) => L.id === l.in) <= upto).map((l) => ({ id: l.id, label: l.label, in: l.in, cls: l.id === focus ? 'good' : 'act' }));
        // the whole nesting from the start, outer rings hidden until their turn: the stage paints items in the
        // order they first appear, so the rings must all exist from the first frame, outermost first
        const items = K.set.nested({ regions: [nest(LEVELS.length - 1)], points: pts, x: 0, y: 0, hot: hot ? [hot] : [], prefix: 'ns' }).items;
        for (const it of items) if (it.kind === 'region' && LEVELS.findIndex((L) => 'ns:' + L.id === it.key) > upto) it.opacity = 0;
        const shade = { reg: 'r0', cf: 'r1', cs: 'r2', dec: 'r3', re: 'r4', all: 'frame' };
        for (const it of items) if (it.kind === 'region') { it.pick = true; const id = it.key.slice(3); it.cls = shade[id] + (hot === id ? ' hot' : ''); }
        const L = LEVELS.find((x) => x.id === hot);
        const bottom = Math.max(...items.filter((it) => it.kind === 'region').map((it) => it.y + it.h));
        if (L && L.machine !== 'none') { if (L.rule !== '–') items.push({ key: 'cap1', kind: 'text', x: 0, y: bottom + 30, text: 'rules: ' + L.rule, cls: 'mono', mono: true, size: 15 }); items.push({ key: 'cap2', kind: 'text', x: 0, y: bottom + 56, text: 'machine: ' + L.machine, cls: 'strong', size: 15 }); }
        void legend;
        return items;
      };
      const placed = [];
      const others = LANGS.filter((l) => l.id !== inp.focus);
      LEVELS.forEach((L, i) => {
        F.set('levels', i + 1);
        for (const l of others) if (l.in === L.id) { placed.push(l.id); }
        F.set('langs', placed.length);
        const here = others.filter((l) => l.in === L.id);
        F.add({ items: scene(i, placed, L.id), hl: { tab: L.type ? [String(['3', '2', '1', '0'].indexOf(L.type))] : [] }, say: (i === 0 ? 'Start small: ' : '') + L.label + (L.id === 'all' ? ': the languages no machine recognises lie out here, and most languages do, since there are uncountably many languages and only countably many machines.' : L.id === 'dec' ? ' languages: a Turing machine that halts on every input. Every context-sensitive language is decidable, since an LBA can be simulated with a loop check.' : ' languages: generated by rules ' + L.rule + ', recognised by a ' + L.machine + '.') + (here.length ? ' Here: ' + here.map((l) => l.label + ', since ' + l.why).join('; ') + '.' : '') });
      });
      const f = LANGS.find((l) => l.id === inp.focus);
      const fr0 = F.list[F.list.length - 1];
      placed.push(f.id);
      F.set('langs', placed.length);
      F.add({ items: scene(LEVELS.length - 1, placed, f.in, f.id), say: f.label + ' belongs in ' + LEVELS.find((L) => L.id === f.in).label.toLowerCase() + (f.in === 'all' ? ' languages, outside the recognisable ones' : '') + ': ' + f.why + '.', mark: 'placed' });
      fr0.predict = { ask: 'Click the smallest class that contains ' + f.label + '.', answer: 'ns:' + f.in, explain: f.label + ': ' + f.why + '.', pick: 'item' };
      return { frames: F.list, def: { sections: [
        { id: 'tab', kind: 'table', title: 'Grammars and machines', colHead: ['type', 'class', 'rules', 'machine'], rows: LEVELS.filter((L) => L.type).map((L) => ['type ' + L.type, L.label, L.rule, L.machine]) },
        { id: 'strict', kind: 'text', title: 'Every inclusion is strict', text: '(ab)* is regular; aⁿbⁿ is context-free but not regular; aⁿbⁿcⁿ is context-sensitive but not context-free; some decidable languages are not context-sensitive (by diagonalising over LBAs); HALT is recognisable but not decidable; its complement is not even recognisable.' },
      ] } };
    },
    quiz: [
      { q: 'Which machine goes with context-sensitive grammars?', options: ['Pushdown automaton', 'Linear-bounded automaton', 'Finite automaton', 'Two-stack machine'], answer: 1, why: 'Noncontracting grammars and nondeterministic LBAs describe the same languages.' },
      { q: 'Is every context-sensitive language decidable?', options: ['Yes', 'No', 'Only the context-free ones', 'Only finite ones'], answer: 0, why: 'An LBA has finitely many configurations on each input, so its runs can be checked for loops.' },
      { q: 'Why must some languages lie outside every ring?', options: ['They are too long', 'There are countably many machines but uncountably many languages', 'They have no strings', 'They are ambiguous'], answer: 1, why: 'Each machine is a finite string, so they can be listed; the languages over {a, b} cannot (diagonalisation).' },
      { q: 'A language and its complement are both recognisable. Where is it?', options: ['Outside the recognisable ones', 'In the decidable ring', 'Only in the regular ring', 'Nowhere'], answer: 1, why: 'Run both recognisers in turns: one of them must accept, giving a decider.' },
      { q: 'aⁿbⁿ sits in the context-free ring but not the regular one. What shows it is not regular?', options: ['It is infinite', 'The pumping lemma (or Myhill–Nerode): a finite automaton cannot count the a\'s', 'It has two letters', 'It is ambiguous'], answer: 1, why: 'Strings aⁱ for different i need different states, and there are only finitely many.' },
    ],
  });
})();
