// Variants of the Turing machine and why they add no power: several tapes and their simulation on one tape
// with tracks, the two-way tape folded onto a one-way one, a two-dimensional tape, nondeterminism with its
// computation tree and the address-tape simulation, enumerators, and dovetailing.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const TK = () => T.TK;

  T.family({ id: 'tm-variants', part: 'turing', order: 30, title: 'Variants of the machine', blurb: 'More tapes, a tape infinite in one direction only, a grid, nondeterministic choices, a printer: each variant is simulated by the plain machine, so none of them computes anything new.' });

  const MULTI = {
    pal: { id: 'pal-2tape', one: 'palindrome', alpha: 'ab', name: 'palindromes' },
    abc: { id: 'anbncn-2tape', one: 'anbncn', alpha: 'abc', name: 'aⁿbⁿcⁿ' },
    copy: { id: 'copy-2tape', one: 'copy', alpha: 'ab', name: 'copying' },
    add: { id: 'bin-add-3tape', one: 'bin-add', alpha: '01+', name: 'binary addition' },
  };
  const ruleText = (r) => 'δ(' + r.from + ', ' + r.read.map(TK().sym).join(' ') + ') = (' + r.to + ', ' + r.write.map(TK().sym).join(' ') + ', ' + r.move.join(' ') + ')';
  const ruleTable = (M) => ({ id: 'rules', kind: 'table', title: 'Rules: state, reads → next, writes, moves', colHead: ['state', 'reads', 'next', 'writes', 'moves'], rows: M.rules.map((r) => [r.from, r.read.map(TK().sym).join(' '), r.to, r.write.map(TK().sym).join(' '), r.move.join(' ')]), maxRows: 40 });

  // ======================================================================================================
  // Several tapes, each with its own head
  // ======================================================================================================
  T.topic({
    id: 'tm-multitape', family: 'tm-variants', order: 10, title: 'Machines with several tapes',
    blurb: 'Each tape has its own head; one step reads under all of them, writes under all of them and moves each its own way. Watch how much shorter the runs get than on one tape.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'pal', options: Object.entries(MULTI).map(([value, x]) => ({ value, label: x.name + ' (' + T.tmLib.entry(x.id).text.match(/tapes: (\d)/)[1] + ' tapes)' })) },
      { id: 'w', kind: 'string', label: 'Input', def: 'abba', max: 7, check: (v, inp) => ([...v].some((c) => !MULTI[inp.m].alpha.includes(c)) ? 'Input: use only ' + [...MULTI[inp.m].alpha].join(' ') : inp.m === 'add' && !/^[01]*\+[01]*$/.test(v) ? 'Input: two binary numbers joined by +, like 101+11' : null) },
    ],
    presets: [
      { label: 'Palindrome: abba', values: { m: 'pal', w: 'abba' } },
      { label: 'Not a palindrome: abab', values: { m: 'pal', w: 'abab' } },
      { label: 'aⁿbⁿcⁿ: aabbcc', values: { m: 'abc', w: 'aabbcc' } },
      { label: 'Copy ab to abab', values: { m: 'copy', w: 'ab' } },
      { label: 'Add 101 + 11 on three tapes', values: { m: 'add', w: '101+11' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }],
    run(inp) {
      const tk = TK();
      const X = MULTI[inp.m];
      const M = T.tmLib.get(X.id);
      const run = tk.trace(M, inp.w, { max: 300 });
      const N = 11, CW = 44, GAP = CW + 70;
      const scs = Array.from({ length: M.tapes }, () => K.tape.scroller({ cells: N, origin: -2 }));
      const F = new T.Frames(['steps']);
      const scene = (cfg, rule, headCls) => {
        const items = [];
        for (let t = 0; t < M.tapes; t++) items.push(...tk.tape(cfg, { t, state: t === 0 ? cfg.state : 'head ' + (t + 1), cells: N, cw: CW, origin: scs[t].at(cfg.heads[t].p), prevOrigin: scs[t].prev, x: 0, y: t * GAP, prefix: 'mt' + t, label: 'tape ' + (t + 1), headCls: t === 0 ? headCls : 'read' }).items);
        items.push({ key: 'rule', kind: 'text', x: (N * CW) / 2, y: -26, text: rule ? ruleText(rule) : 'start in ' + M.start, anchor: 'middle', cls: 'mono', mono: true, size: 14 });
        return items;
      };
      F.add({ items: scene(run.list[0].cfg, null), say: 'The input ' + (inp.w || 'ε') + ' is on tape 1; the other ' + (M.tapes - 1) + ' tape' + (M.tapes > 2 ? 's are' : ' is') + ' blank. All heads start on the first cell, and one state controls them all.' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        F.count('steps');
        F.add({ items: scene(cfg, rule), say: tk.sayRule(rule), hl: { rules: [String(M.rules.indexOf(rule))] }, meta: { moves: rule.move.join('') } });
      }
      const ok = run.verdict === 'accept';
      const one = T.tmLib.get(X.one);
      const oneRun = T.tm.run(one, inp.w, { trace: false, maxSteps: 300000, loops: false });
      const steps = run.list.length - 1;
      const last = scene(run.last, null, ok ? 'good' : 'bad');
      // a race: this machine's steps against a one-tape machine for the same job
      const y0 = M.tapes * GAP + 30, W = N * CW, mx = Math.max(steps, oneRun.steps, 1);
      const bar = (key, y, n, label, cls) => [
        { key: key + 'b', kind: 'cell', x: 0, y, w: Math.max(6, (W - 150) * n / mx), h: 26, text: '', cls, rx: 5 },
        { key: key + 't', kind: 'text', x: Math.max(6, (W - 150) * n / mx) + 10, y: y + 18, text: n + ' steps · ' + label, cls: 'strong' },
      ];
      last.push({ key: 'raceT', kind: 'text', x: 0, y: y0, text: 'THE SAME JOB', cls: 'title' }, ...bar('r1', y0 + 12, steps, M.tapes + ' tapes', 'tu-k1'), ...bar('r2', y0 + 48, oneRun.steps, '1 tape', 'tu-k5'));
      const out = M.output ? T.tm.outputOf(M, run.last) : null;
      F.add({ items: last, say: (ok ? (out !== null ? 'Halted with ' + (out || 'ε') + ' on tape ' + (M.outTape + 1) + '.' : 'Accepted.') : 'Rejected: no rule for ' + run.last.state + ' on (' + tk.reads(run.last).map(tk.sym).join(', ') + ').') + ' ' + steps + ' steps here; the one-tape machine for ' + X.name + ' needs ' + oneRun.steps + ' on the same input.', mark: ok ? 'accepted' : 'rejected' });
      const fr = F.list;
      if (fr.length > 4 && fr[3].meta) fr[2].predict = { ask: 'How will the heads move in the next step? (one letter per tape)', options: [...new Set([fr[3].meta.moves, ...['RR', 'RS', 'SL', 'LL', 'RL', 'SR'].filter((x) => x.length === M.tapes)])].slice(0, 4).sort(), answer: fr[3].meta.moves, explain: fr[3].say, pick: 'option' };
      return { frames: fr, def: { sections: [{ id: 'tuple', kind: 'math', title: 'A ' + M.tapes + '-tape machine', text: 'δ : Q × Γ^' + M.tapes + ' → Q × Γ^' + M.tapes + ' × {L, R, S}^' + M.tapes + '\nQ = {' + M.states.join(', ') + '}\nstart ' + M.start + ', accept {' + M.accept.concat(M.halt).join(', ') + '}' }, ruleTable(M)] } };
    },
    quiz: [
      { q: 'What does one step of a 3-tape machine read?', options: ['One symbol', 'Three symbols, one under each head', 'A whole tape', 'Only tape 1'], answer: 1, why: 'δ takes the state and the three symbols under the heads, and gives three writes and three moves.' },
      { q: 'Why is the two-tape palindrome checker so much faster?', options: ['It has more states', 'It can read the string forwards and backwards at the same time', 'It skips symbols', 'It is nondeterministic'], answer: 1, why: 'After copying, one head walks forwards on tape 1 while the other walks backwards on tape 2: no shuttling back and forth.' },
      { q: 'Can a k-tape machine decide a language no one-tape machine can decide?', options: ['Yes', 'No: one tape can simulate k tapes', 'Only for k > 2', 'Only nondeterministic ones'], answer: 1, why: 'Keep the k tapes on k tracks of one tape with a mark for each head. It is slower (about the square of the time) but decides the same languages.' },
      { q: 'A k-tape machine takes t(n) steps. Roughly how long does the one-tape simulation take?', options: ['t(n)', 'about t(n)²', '2^t(n)', 'k·t(n)'], answer: 1, why: 'Each simulated step sweeps over the used part of the tape, which is at most about t(n) cells long: t(n) sweeps of length t(n).' },
    ],
  });

  // ======================================================================================================
  // k tapes on one tape: tracks, head marks, two sweeps per step, two clocks
  // ======================================================================================================
  T.topic({
    id: 'tm-ksim', family: 'tm-variants', order: 20, title: 'One tape simulates two',
    blurb: 'Put the tapes on tracks of a single tape and mark where each head is. For every step of the two-tape machine the single head sweeps right to read under the marks, then left to write and move them. Two clocks show the price.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'pal', options: [{ value: 'pal', label: 'palindromes (2 tapes)' }, { value: 'copy', label: 'copy w to ww (2 tapes)' }] },
      { id: 'w', kind: 'string', label: 'Input', def: 'aba', alphabet: 'ab', max: 4 },
    ],
    presets: [
      { label: 'Palindrome: aba', values: { m: 'pal', w: 'aba' } },
      { label: 'Palindrome: ab (rejected)', values: { m: 'pal', w: 'ab' } },
      { label: 'Copy ab', values: { m: 'copy', w: 'ab' } },
      { label: 'The empty string', values: { m: 'pal', w: '' } },
    ],
    counters: [{ id: 'sim', label: 'two-tape steps' }, { id: 'one', label: 'one-tape steps' }],
    run(inp) {
      const tk = TK();
      const M = T.tmLib.get(inp.m === 'pal' ? 'pal-2tape' : 'copy-2tape');
      const sim = T.tm.simulateKTape(M, inp.w, { maxSteps: 200 });
      const direct = tk.trace(M, inp.w, { max: 200 });
      const k = M.tapes;
      // the cells the simulation ever uses: a fixed window
      let lo = 0, hi = Math.max(0, inp.w.length - 1);
      for (const n of sim.trace) { if (n.pos !== undefined) { lo = Math.min(lo, n.pos); hi = Math.max(hi, n.pos); } if (n.from !== undefined) { lo = Math.min(lo, n.from); hi = Math.max(hi, n.from + n.tracks[0].symbols.length - 1); } }
      const origin = lo - 1, cells = Math.min(12, hi - lo + 3);
      const CW = 46;
      // the single tape's contents, kept up to date note by note
      let cellsNow = new Map(), head = 0, clock = 0, simN = 0, state = M.start;
      const sync = (n) => { cellsNow = new Map(); n.tracks[0].symbols.forEach((_, j) => { const p = n.from + j; cellsNow.set(p, { sym: n.tracks.map((t) => t.symbols[j]), mark: n.tracks.map((t) => t.marks[j]) }); }); };
      const get = (p) => cellsNow.get(p) || { sym: new Array(k).fill(M.blank), mark: new Array(k).fill(false) };
      const yOne = k * (CW + 64) + 110;
      const scene = (opts) => {
        opts = opts || {};
        const items = [];
        const cfg = direct.list[Math.min(simN, direct.list.length - 1)].cfg;
        items.push({ key: 'tA', kind: 'text', x: 0, y: -24, text: 'THE TWO-TAPE MACHINE, STEP ' + simN, cls: 'title' });
        for (let t = 0; t < k; t++) items.push(...tk.tape(cfg, { t, state: t === 0 ? cfg.state : 'head 2', cells, cw: CW, origin, x: 0, y: t * (CW + 64), prefix: 'kt' + t, label: 'tape ' + (t + 1), headCls: t ? 'read' : '' }).items);
        items.push({ key: 'tB', kind: 'text', x: 0, y: yOne - 24, text: 'ONE TAPE, ' + 2 * k + ' TRACKS: SYMBOL AND MARK FOR EACH TAPE', cls: 'title' });
        const tape = [];
        for (let p = origin; p < origin + cells; p++) { const c = get(p); const lines = []; for (let t = 0; t < k; t++) { lines.push(tk.sym(c.sym[t])); lines.push(c.mark[t] ? '▲' + (t + 1) : '·'); } tape.push(lines); }
        items.push(...K.tape.draw({ tape, offset: origin, tracks: 2 * k, head, state: opts.headText || state, cells, cw: CW, origin, x: 0, y: yOne, prefix: 'one', label: '', headCls: opts.headCls || 'hot', cls: (p) => (opts.lit === p ? 'tu-new' : '') }).items);
        const dx = cells * CW + 70;
        items.push(...tk.dial('c1', dx + 40, 40, 'two-tape clock', simN), ...tk.dial('c2', dx + 40, yOne + 30, 'one-tape clock', clock, 'hot'));
        return items;
      };
      const F = new T.Frames(['sim', 'one']);
      for (const n of sim.trace) {
        let say = n.say, lit;
        if (n.kind === 'sim-start') { sync(n); head = n.head; say = 'The two tapes become ' + 2 * k + ' tracks of one tape: a symbol track and a mark track for each. Both marks start on the first cell, like the two heads.'; }
        else if (n.kind === 'gather') { head = n.pos; lit = n.pos; say = 'Sweeping right to read: at cell ' + n.pos + ' ' + n.say.replace(/^At cell \d+ the marks show /, 'the marks show ') ; }
        else if (n.kind === 'decide') { clock = n.steps; say = 'At the right end the state knows what both heads read, (' + n.seen.map(tk.sym).join(', ') + '), so it knows the move: ' + ruleText(n.rule) + '.'; }
        else if (n.kind === 'update') {
          head = n.pos; lit = n.pos;
          const c = get(n.pos); const c2 = { sym: c.sym.slice(), mark: c.mark.slice() }; c2.sym[n.head] = n.write;
          const d = T.tm.MOVES[n.move];
          if (d) { c2.mark[n.head] = false; const o = get(n.pos + d); const o2 = { sym: o.sym.slice(), mark: o.mark.slice() }; o2.mark[n.head] = true; cellsNow.set(n.pos + d, o2); }
          cellsNow.set(n.pos, c2);
          say = 'Sweeping back: at cell ' + n.pos + ' write ' + tk.sym(n.write) + ' on track ' + (2 * n.head + 1) + (d ? ' and move mark ' + (n.head + 1) + ' one cell ' + (d < 0 ? 'left' : 'right') : ', mark ' + (n.head + 1) + ' stays') + '.';
        } else if (n.kind === 'sim-step') { sync(n); head = n.head; simN = n.sim; clock = n.steps; state = n.state; F.set('sim', simN); say = 'One step of the two-tape machine is done: now in ' + n.state + '. The one-tape clock reads ' + n.steps + '.'; }
        else if (n.kind === 'accept' || n.kind === 'reject' || n.kind === 'limit') { clock = n.steps; say = (n.kind === 'accept' ? 'Accepted' : 'Rejected') + ' after ' + n.sim + ' two-tape steps, which cost ' + n.steps + ' steps on one tape: about ' + (n.sim ? Math.round(n.steps / n.sim) : 0) + ' for each, and the cost per step grows with the part of the tape in use.'; }
        else if (n.kind === 'stuck') say = 'No rule applies to (' + n.seen.map(tk.sym).join(', ') + ') in ' + n.state + ': the simulated machine halts and rejects, and so does the simulation.';
        F.set('one', clock);
        const fin = n.kind === 'accept' || n.kind === 'reject';
        F.add({ items: scene({ lit, headCls: fin ? (n.kind === 'accept' ? 'good' : 'bad') : 'hot' }), say, mark: fin ? n.kind + 'ed' : undefined, meta: { kind: n.kind, steps: clock } });
      }
      // the price, for growing inputs
      const rows = [];
      for (let n = 1; n <= 7; n++) { const w = 'ab'.repeat(4).slice(0, Math.ceil(n / 2)); const x = inp.m === 'pal' ? w + [...w].reverse().join('').slice(n % 2) : 'a'.repeat(n); const s = T.tm.simulateKTape(M, x, { trace: false, maxSteps: 400 }); rows.push([String(n), x, String(s.simulated), String(s.steps)]); }
      const fr = F.list;
      const d = fr.findIndex((f) => f.meta && f.meta.kind === 'sim-step');
      if (d > 1) fr[d - 1].predict = { ask: 'The first simulated step is about to finish. How many one-tape steps has it cost?', options: [...new Set([String(fr[d].meta.steps), '1', String(fr[d].meta.steps * 2), String(Math.max(2, fr[d].meta.steps - 3))])].sort((a, b) => a - b), answer: String(fr[d].meta.steps), explain: 'A sweep right to read under the marks and a sweep back to write and move them: ' + fr[d].meta.steps + ' steps for one step of the two-tape machine.', pick: 'option' };
      return { frames: fr, def: { sections: [
        { id: 'how', kind: 'text', title: 'The simulation', text: 'Track 2i − 1 holds tape i; track 2i holds a mark under the cell where head i is. For each step: sweep right over the used cells, remembering in the state the symbols under the marks; choose the rule; sweep left writing those symbols and moving the marks. A step of the k-tape machine costs O(t) steps when t cells are in use, so t steps cost O(t²).' },
        { id: 'cost', kind: 'table', title: 'The two clocks on longer inputs', colHead: ['n', 'input', 'two-tape', 'one-tape'], rows },
        ruleTable(M),
      ] } };
    },
    quiz: [
      { q: 'How does the single head know what the two simulated heads are reading?', options: ['It has two heads', 'It sweeps across the tape and remembers, in its state, the symbols at the marks', 'It guesses', 'It reads track 1 only'], answer: 1, why: 'The finite control can remember a symbol per track, since there are finitely many symbols.' },
      { q: 'Why does each simulated step cost more as the run goes on?', options: ['The state set grows', 'The used part of the tape grows, and each step sweeps over it', 'Marks get heavier', 'It does not'], answer: 1, why: 'The marks can drift apart, so every step has to sweep over everything in use.' },
      { q: 'How many tape symbols does the one-tape machine need for 2 tapes over Γ?', options: ['|Γ|', '2|Γ|', '(2|Γ|)², one per combination of symbols and marks, plus its own', '2'], answer: 2, why: 'A cell holds a symbol and a mark bit for each tape: (|Γ| · 2)² combinations. Finite, which is all that matters.' },
      { q: 'What does this show?', options: ['Two tapes are strictly more powerful', 'Two tapes decide the same languages as one, with at most a quadratic slowdown', 'One tape is faster', 'Nothing about power'], answer: 1, why: 'The simulation is exact; only time changes, by about squaring.' },
    ],
  });

  // ======================================================================================================
  // A tape infinite both ways folded onto a tape with a left end
  // ======================================================================================================
  const ONEWAY = { inc: { id: 'bin-inc', alpha: '01' }, u2b: { id: 'unary-to-bin', alpha: '1' } };
  T.topic({
    id: 'tm-oneway', family: 'tm-variants', order: 30, title: 'Two-way tape on a one-way tape',
    blurb: 'A tape that ends on the left can still hold a tape infinite both ways: fold it at cell 0, so the right half lies on an upper track and the left half, reversed, on a lower one.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'inc', options: [{ value: 'inc', label: 'binary increment' }, { value: 'u2b', label: 'unary to binary' }] },
      { id: 'w', kind: 'string', label: 'Input', def: '111', max: 5, check: (v, inp) => ([...v].some((c) => !ONEWAY[inp.m].alpha.includes(c)) ? 'Input: use only ' + [...ONEWAY[inp.m].alpha].join(' and ') : null) },
    ],
    presets: [
      { label: 'Increment 111: the carry goes left of cell 0', values: { m: 'inc', w: '111' } },
      { label: 'Increment 1010: never left of cell 0', values: { m: 'inc', w: '1010' } },
      { label: 'Unary to binary: 11', values: { m: 'u2b', w: '11' } },
      { label: 'Unary to binary: 111', values: { m: 'u2b', w: '111' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'left', label: 'steps left of cell 0' }],
    run(inp) {
      const tk = TK();
      const M = T.tmLib.get(ONEWAY[inp.m].id);
      const run = tk.trace(M, inp.w, { max: 150 });
      let lo = 0, hi = Math.max(inp.w.length, 1);
      for (const { cfg } of run.list) { const b = cfg.tapes[0].bounds(); lo = Math.min(lo, cfg.heads[0].p, b.hi >= b.lo ? b.lo : 0); hi = Math.max(hi, cfg.heads[0].p, b.hi); }
      const L = Math.max(2, -lo + 1), R = Math.max(3, hi + 2);   // cells -L .. R-1 on the straight tape
      const J = Math.max(L, R);                                  // folded cells 1 .. J
      const CW = 46, CH = 40;
      const xS = 0, yS = 0, yF = 170;
      const xF = xS + (L - 1) * CW;                              // the folded tape starts under cell -1
      const fold = (p) => (p >= 0 ? { j: p + 1, up: true } : { j: -p, up: false });
      const sym = (cfg, p) => tk.sym(cfg.tapes[0].get(p));
      const straight = (cfg, P, opts) => {
        const items = [];
        for (let p = -L; p < R; p++) items.push({ key: P + p, kind: 'cell', x: xS + (p + L) * CW, y: yS, w: CW, h: CH, text: sym(cfg, p), cls: 'mono' + (sym(cfg, p) === tk.BL ? ' blank' : '') + (p === cfg.heads[0].p ? ' act' : '') + (p < 0 ? ' tu-k2' : ''), rx: 4 });
        for (let p = -L; p < R; p++) items.push({ key: P + 'n' + p, kind: 'text', x: xS + (p + L) * CW + CW / 2, y: yS - 10, text: String(p), anchor: 'middle', cls: 'tu-num', size: 12 });
        if (!opts || !opts.noHead) items.push({ key: P + 'head', kind: 'head', x: xS + (cfg.heads[0].p + L) * CW + CW / 2, y: yS + CH + 2, text: cfg.state, side: 'below' });
        items.push({ key: P + 'lab', kind: 'text', x: xS - 14, y: yS + CH / 2 + 5, text: 'TWO-WAY', anchor: 'end', cls: 'title' });
        return items;
      };
      const folded = (cfg, headCls) => {
        const items = [{ key: 'fend', kind: 'cell', x: xF, y: yF, w: CW, h: 2 * CH, text: '>', cls: 'mono tu-wall', rx: 4 }];
        for (let j = 1; j <= J; j++) for (const up of [true, false]) {
          const p = up ? j - 1 : -j;
          if (p < -L || p >= R) { items.push({ key: 'w' + (up ? 'u' : 'd') + j, kind: 'cell', x: xF + j * CW, y: yF + (up ? 0 : CH), w: CW, h: CH, text: tk.BL, cls: 'mono blank', rx: 4 }); continue; }
          items.push({ key: 'w' + p, kind: 'cell', x: xF + j * CW, y: yF + (up ? 0 : CH), w: CW, h: CH, text: sym(cfg, p), cls: 'mono' + (sym(cfg, p) === tk.BL ? ' blank' : '') + (p === cfg.heads[0].p ? ' act' : '') + (p < 0 ? ' tu-k2' : ''), rx: 4 });
        }
        const f = fold(cfg.heads[0].p);
        items.push({ key: 'fhead', kind: 'head', x: xF + f.j * CW + CW / 2, y: yF + 2 * CH + 2, text: cfg.state + (f.up ? ' ↑' : ' ↓'), side: 'below', cls: headCls || '' });
        items.push({ key: 'flab', kind: 'text', x: xF - 14, y: yF + CH + 5, text: 'ONE-WAY', anchor: 'end', cls: 'title' });
        items.push({ key: 'fu', kind: 'text', x: xF + (J + 1) * CW + 12, y: yF + CH / 2 + 5, text: 'cells 0, 1, 2, … →', cls: 'tu-small' });
        items.push({ key: 'fd', kind: 'text', x: xF + (J + 1) * CW + 12, y: yF + CH + CH / 2 + 5, text: 'cells −1, −2, … →', cls: 'tu-small' });
        return items;
      };
      const F = new T.Frames(['steps', 'left']);
      const c0 = run.list[0].cfg;
      // first the tape straight, then folded: the same cells glide to their new places
      const flat = [];
      for (let p = -L; p < R; p++) flat.push({ key: 'w' + p, kind: 'cell', x: xS + (p + L) * CW, y: yF, w: CW, h: CH, text: sym(c0, p), cls: 'mono' + (sym(c0, p) === tk.BL ? ' blank' : '') + (p < 0 ? ' tu-k2' : ''), rx: 4 });
      flat.push({ key: 'flab', kind: 'text', x: xS - 14, y: yF + CH / 2 + 5, text: 'TWO-WAY', anchor: 'end', cls: 'title' });
      for (let p = -L; p < R; p++) flat.push({ key: 'fn' + p, kind: 'text', x: xS + (p + L) * CW + CW / 2, y: yF - 10, text: String(p), anchor: 'middle', cls: 'tu-num', size: 12 });
      F.add({ items: flat, say: 'A tape infinite in both directions, cells numbered …, −2, −1, 0, 1, 2, …, with the input from cell 0. The cells left of 0 are tinted.' });
      F.add({ items: straight(c0, 's', { noHead: true }).concat(folded(c0)), say: 'Fold it at cell 0: cells 0, 1, 2, … go on an upper track, cells −1, −2, … on a lower track, and a marker > fills the first cell. Every cell of the two-way tape now has a place on a tape with a left end.' });
      let left = 0;
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        const before = run.list[k - 1].cfg.heads[0].p, p = cfg.heads[0].p;
        F.count('steps');
        if (before < 0) { left++; F.count('left'); }
        let note = '';
        if (before === 0 && p === -1) note = ' Crossing from cell 0 to −1: the folded head bounces off the marker > and drops to the lower track.';
        else if (before === -1 && p === 0) note = ' Back from −1 to 0: the folded head climbs to the upper track.';
        else if (p < 0 && before < 0 && p !== before) note = ' On the lower track directions flip: ' + (p < before ? 'left' : 'right') + ' on the two-way tape is ' + (p < before ? 'right' : 'left') + ' on the folded one.';
        F.add({ items: straight(cfg, 's').concat(folded(cfg)), say: tk.sayRule(rule) + note, meta: { p } });
      }
      const out = T.tm.outputOf(M, run.last);
      F.add({ items: straight(run.last, 's').concat(folded(run.last, 'good')), say: 'Halted with ' + (out || 'ε') + '. The one-way machine did the same with states that also remember the track (upper or lower): ' + left + ' of the ' + (run.list.length - 1) + ' steps were on the lower track.', mark: 'halted' });
      const fr = F.list;
      const cross = fr.findIndex((f, i) => i > 2 && f.meta && f.meta.p < 0);
      if (cross > 2) fr[cross - 1].predict = { ask: 'The head is about to step left of cell 0. Click the folded cell it will be on.', answer: 'w' + fr[cross].meta.p, explain: 'Cell ' + fr[cross].meta.p + ' of the two-way tape lies on the lower track, under cell ' + (-fr[cross].meta.p - 1) + '.', pick: 'item' };
      else fr[1].predict = { ask: 'Where does cell −2 of the two-way tape sit on the folded tape?', options: ['Upper track, under nothing', 'Lower track, second cell after >', 'Lower track, first cell', 'It is lost'], answer: 'Lower track, second cell after >', explain: 'Cell −j sits on the lower track of folded cell j: −1 in the first, −2 in the second.', pick: 'option' };
      const def = tk.defOf(M);
      return { frames: fr, def: { sections: def.sections.concat([{ id: 'fold', kind: 'math', title: 'The fold', text: 'cell p ≥ 0  ↦  folded cell p + 1, upper track\ncell p < 0  ↦  folded cell −p, lower track\nfolded cell 0 holds the marker >\nstates (q, up) and (q, down): on the lower track L and R swap' }]) } };
    },
    quiz: [
      { q: 'Where does cell −3 go on the folded tape?', options: ['Upper track, cell 3', 'Lower track, cell 3', 'Lower track, cell 4', 'Upper track, cell 4'], answer: 1, why: 'Cell −j sits on the lower track of folded cell j.' },
      { q: 'What does the one-way machine do when the two-way head moves left on the lower track?', options: ['Moves left', 'Moves right', 'Stays', 'Halts'], answer: 1, why: 'The lower track holds the left half in reverse order, so leftwards on the original tape is rightwards on the folded one.' },
      { q: 'How does the one-way machine know which track it is on?', options: ['From the tape', 'Its states come in pairs, (q, upper) and (q, lower)', 'It guesses', 'It does not need to'], answer: 1, why: 'Doubling the states records the track; the marker > tells it when to switch tracks.' },
      { q: 'How much slower is the one-way simulation?', options: ['Not at all, step for step (plus the turn at >)', 'Quadratically', 'Exponentially', 'It cannot simulate it'], answer: 0, why: 'Each two-way step is one folded step; crossing cell 0 costs one extra step at the marker. So the two models are equivalent with almost no slowdown.' },
    ],
  });

  // ======================================================================================================
  // A two-dimensional tape: a drawing machine
  // ======================================================================================================
  const SHADOW = 'mode: 2d\ninput: a b\nq0, a|b -> s, *, D\ns, _|# -> t, *, R\nt, _|# -> q0, #, U\nq0, _ -> halt, _, S';
  const STAIRS = 'mode: 2d\ninput: 1\nr, 1 -> d, #, D\nd, _ -> u, #, R\nu, _ -> r2, _, U\nr2, 1 -> d, #, D\nr2, _ -> halt, _, S\nr, _ -> halt, _, S';
  T.topic({
    id: 'tm-2d', family: 'tm-variants', order: 40, title: 'A two-dimensional tape',
    blurb: 'Give the head four directions on a grid and the machine can draw. A grid is no stronger than a tape, though: number the cells along diagonals and one tape holds them all.',
    inputs: [
      { id: 'p', kind: 'program', label: 'Machine (moves L, R, U, D, S)', def: SHADOW, check: (v) => TK().checkMachine(v, { mode: '2d', deterministic: true, maxStates: 10, anyHalt: true }) },
      { id: 'w', kind: 'string', label: 'Row 0', def: 'abba', max: 6 },
    ],
    presets: [
      { label: 'Drop a shadow under abba', values: { p: SHADOW, w: 'abba' } },
      { label: 'Stairs from 1111', values: { p: STAIRS, w: '1111' } },
      { label: 'Copy row 0 into row 1', values: { p: T.tmLib.entry('copy-down-2d').text.trim(), w: 'abab' } },
      { label: 'An ant that never stops', values: { p: T.tmLib.entry('ant-2d').text.trim(), w: '' } },
    ],
    check: (inp) => { const M = TK().compile(inp.p).M; const bad = [...inp.w].find((c) => !M.gamma.includes(c)); return bad !== undefined ? 'Row 0: the machine has no rules for "' + bad + '"' : null; },
    counters: [{ id: 'steps', label: 'steps' }, { id: 'ink', label: 'cells written' }],
    run(inp) {
      const tk = TK();
      const M = tk.compile(inp.p).M;
      const r = T.tm.run2d(M, inp.w, { maxSteps: 70 });
      const tr = r.trace;
      let x0 = 0, x1 = 3, y0 = 0, y1 = 2;
      for (const s of tr) if (s.rows) { x0 = Math.min(x0, s.x0, s.head[0]); y0 = Math.min(y0, s.y0, s.head[1]); x1 = Math.max(x1, s.x0 + s.rows[0].length - 1, s.head[0]); y1 = Math.max(y1, s.y0 + s.rows.length - 1, s.head[1]); }
      x0 = Math.max(x0 - 1, -6); y0 = Math.max(y0 - 1, -5); x1 = Math.min(x1 + 1, x0 + 13); y1 = Math.min(y1 + 1, y0 + 9);
      const S = 42;
      const cellsOf = (s) => { const o = {}; s.rows.forEach((row, j) => row.forEach((v, i) => { if (v !== M.blank) o[(s.x0 + i) + ',' + (s.y0 + j)] = v; })); return o; };
      const ctr = (x, y) => ({ x: (x - x0) * S + S / 2, y: 40 + (y - y0) * S + S / 2 });
      const F = new T.Frames(['steps', 'ink']);
      const heads = [];
      const scene = (s, k, cls) => {
        const g = K.tape.grid({ cells: cellsOf(s), head: { x: s.head[0], y: s.head[1] }, state: s.state, window: { x0, y0, w: x1 - x0 + 1, h: y1 - y0 + 1 }, x: 0, y: 40, cs: S, prefix: 'g2' });
        const items = g.items;
        for (const it of items) if (it.kind === 'head' && cls) it.cls = cls;
        items.push({ key: 'rowmark', kind: 'text', x: -12, y: ctr(0, s.head[1]).y + 6, text: '▶', anchor: 'end', cls: 'hot' });
        for (let j = Math.max(1, k - 40); j <= k; j++) { const a = ctr(heads[j - 1][0], heads[j - 1][1]), b = ctr(heads[j][0], heads[j][1]); if (a.x !== b.x || a.y !== b.y) items.push({ key: 'tr' + j, kind: 'edge', from: { x: a.x, y: a.y }, to: { x: b.x, y: b.y }, head: false, gapB: 0, cls: 'tu-trail' + (j < k - 8 ? ' old' : ''), audit: 'ignore', layer: 'top' }); }
        for (let y = y0; y <= y1; y++) items.push({ key: 'ry' + y, kind: 'text', x: (x1 - x0 + 1) * S + 12, y: ctr(0, y).y + 5, text: 'row ' + y, cls: 'tu-num', size: 12 });
        return items;
      };
      let ink = 0;
      tr.forEach((s, k) => {
        if (!s.rows) return;
        heads.push(s.head);
        const h = heads.length - 1;
        if (s.kind === 'start') { F.add({ items: scene(s, 0), say: 'The input ' + (inp.w || 'ε') + ' is on row 0 of a grid that goes on for ever in all four directions. The head starts at (0, 0) in ' + s.state + '.' }); return; }
        if (s.kind === 'move') {
          F.count('steps');
          if (s.rule.write[0] !== s.rule.read[0]) { ink++; F.set('ink', ink); }
          F.add({ items: scene(s, h), say: tk.sayRule(s.rule), meta: { move: s.rule.move[0] } });
          return;
        }
        const ok = s.kind === 'accept';
        F.add({ items: scene(s, h, ok ? 'good' : s.kind === 'limit' ? 'hot' : 'bad'), say: ok ? 'Halted after ' + r.steps + ' steps: the drawing is done.' : s.kind === 'limit' ? 'Still going after ' + r.steps + ' steps. This machine has no halting state at all; it just keeps drawing.' : s.kind === 'loop' ? 'The grid, head and state repeat an earlier moment: it will cycle for ever.' : 'No rule applies: the machine halts without accepting.', mark: ok ? 'halted' : 'stopped' });
        void k;
      });
      const fr = F.list;
      if (fr.length > 4 && fr[2].meta) fr[1].predict = { ask: 'Which way will the head go next: left, right, up or down?', options: ['L', 'R', 'U', 'D'], answer: fr[2].meta.move === 'S' ? 'L' : fr[2].meta.move, explain: fr[2].say, pick: 'option' };
      if (fr[1].predict && fr[2].meta.move === 'S') delete fr[1].predict;
      const def = tk.defOf(M);
      return { frames: fr, def: { sections: def.sections.concat([{ id: 'grid', kind: 'text', title: 'Why a grid adds no power', text: 'Number the cells of the grid along diagonals (a pairing function) and keep them on one tape. Moving up, down, left or right becomes a walk to another number, found by arithmetic on the tape: slow, but always possible.' }]) } };
    },
    quiz: [
      { q: 'What does a move U do on a 2-D tape?', options: ['Writes a U', 'Moves the head one cell up', 'Undoes the last step', 'Moves to row 0'], answer: 1, why: 'There are four directions: L, R, U, D (and S to stay).' },
      { q: 'Can a one-tape machine simulate a 2-D one?', options: ['No', 'Yes, by laying the grid out on one tape', 'Only for finite grids', 'Only nondeterministically'], answer: 1, why: 'Lay the grid out (row by row of the used rectangle, or along diagonals) and translate each move into a walk on the tape.' },
      { q: 'The ant never halts. What kind of machine is it?', options: ['A decider', 'A machine that computes nothing, but still a perfectly legal Turing machine', 'Not a Turing machine', 'An enumerator'], answer: 1, why: 'Nothing obliges a machine to halt; this one just never does, on any input.' },
      { q: 'How many cells can the head have visited after t steps?', options: ['t + 1 at most', 't²', '4t', 'Unlimited'], answer: 0, why: 'Each step moves to at most one new cell, in a grid just as on a line.' },
    ],
  });

  // ======================================================================================================
  // Nondeterminism: the computation tree, explored level by level
  // ======================================================================================================
  const NTM_AB = 'nondet: yes\ninput: a b\nq0, a|b -> q0, *, R\nq0, a -> q1, a, R\nq1, b -> qa, b, S\nq0, _ -> q0, _, R';
  const NTMS = { rep: { text: () => T.tmLib.entry('ntm-repeat').text.trim(), alpha: 'abc', name: 'some letter occurs twice' }, ab: { text: () => NTM_AB, alpha: 'ab', name: 'contains ab (one branch never stops)' } };
  /** The computation tree of a nondeterministic machine as nested nodes for the tree kit */
  function treeOf(res, upto, cls) {
    const nodes = res.nodes;
    const shown = new Set([0]);
    for (const n of nodes) if (n.id && upto(n)) shown.add(n.id);
    const build = (id) => ({ id: 'n' + id, label: nodes[id].state, cls: cls(nodes[id]), children: nodes.filter((c) => c.parent === id && shown.has(c.id)).map((c) => build(c.id)) });
    return build(0);
  }
  T.topic({
    id: 'tm-ntm-tree', family: 'tm-variants', order: 50, title: 'Nondeterminism: the computation tree',
    blurb: 'Where a nondeterministic machine has several moves, its run splits. It accepts if any branch accepts. A deterministic machine can search the tree level by level, breadth first, and an endless branch cannot trap it.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'rep', options: Object.entries(NTMS).map(([value, x]) => ({ value, label: x.name })) },
      { id: 'w', kind: 'string', label: 'Input', def: 'abca', max: 5, check: (v, inp) => ([...v].some((c) => !NTMS[inp.m].alpha.includes(c)) ? 'Input: use only ' + [...NTMS[inp.m].alpha].join(' ') : null) },
    ],
    presets: [
      { label: 'abca: a repeats', values: { m: 'rep', w: 'abca' } },
      { label: 'abc: no branch accepts', values: { m: 'rep', w: 'abc' } },
      { label: 'bab: an endless branch, and ab found anyway', values: { m: 'ab', w: 'bab' } },
      { label: 'bba: no ab, and the search never ends', values: { m: 'ab', w: 'bba' } },
    ],
    counters: [{ id: 'nodes', label: 'configurations' }, { id: 'level', label: 'level' }],
    run(inp) {
      const tk = TK();
      const M = tk.compile(NTMS[inp.m].text()).M;
      const res = T.tm.ntmTree(M, inp.w, { maxDepth: 6, maxNodes: 60 });
      const seen = new Set([0]);
      let cur = -1;
      const done = new Set();
      const cls = (n) => (n.id === cur ? 'hot' : n.status === 'accept' && done.has(n.id) ? 'good' : n.status === 'reject' && done.has(n.id) ? 'reject' : n.status === 'cut' && done.has(n.id) ? 'pruned' : '');
      const F = new T.Frames(['nodes', 'level']);
      const scene = (opts) => {
        opts = opts || {};
        const t = treeOf(res, (n) => seen.has(n.id), cls);
        const d = K.tree.draw(t, { path: opts.path, gapY: 74, gapX: 18 });
        const items = d.items;
        const maxD = Math.max(...[...seen].map((i) => res.nodes[i].depth));
        for (let k = 0; k <= maxD; k++) items.push({ key: 'lv' + k, kind: 'text', x: d.box.x - 30, y: k * 74 + 5, text: 'level ' + k, anchor: 'end', cls: 'tu-num', size: 12 });
        items.push({ key: 'cfg', kind: 'text', x: d.box.x - 90, y: -50, text: opts.top || '', cls: 'mono', mono: true, size: 15 });
        return items;
      };
      for (const s of res.trace) {
        if (s.kind === 'root') { F.set('nodes', 1); F.add({ items: scene({ top: 'root: ' + res.nodes[0].config }), say: 'The root of the tree is the start configuration ' + res.nodes[0].config + '. A node\'s children are the configurations its moves lead to.' }); continue; }
        if (s.kind === 'expand') {
          cur = s.node;
          for (const c of s.children) seen.add(c);
          done.add(s.node);
          F.set('nodes', seen.size).set('level', s.depth + 1);
          const n = res.nodes[s.node];
          const say = n.config + (s.children.length > 1 ? ' has ' + s.children.length + ' moves, so the run splits: ' : ' has one move: ') + s.children.map((c) => res.nodes[c].config).join('; ') + '.';
          F.add({ items: scene({ top: 'expanding: ' + n.config }), say, meta: { kids: s.children.length } });
          continue;
        }
        if (s.kind === 'level') {
          cur = -1;
          for (const id of seen) { const n = res.nodes[id]; if (n.status === 'reject' || n.status === 'cut' || n.status === 'accept') done.add(id); }
          F.add({ items: scene({ top: 'level ' + s.depth + ' complete' }), say: 'Level ' + s.depth + ' is complete with ' + s.nodes.length + ' configuration' + (s.nodes.length === 1 ? '' : 's') + '. Breadth first: every configuration of this level is looked at before any of the next.' });
          continue;
        }
        cur = -1;
        for (const id of seen) done.add(id);
        const path = (s.path || []).map((i) => 'n' + i);
        F.add({ items: scene({ path, top: s.kind === 'accept' ? 'accepting: ' + res.nodes[s.path[s.path.length - 1]].config : s.kind === 'reject' ? 'every branch halted' : 'still branching at level 6' }), say: s.kind === 'accept' ? 'An accepting configuration on level ' + (s.path.length - 1) + '. One accepting branch is enough: the machine accepts ' + inp.w + ', and the path to it is lit.' : s.kind === 'reject' ? 'Every branch has died without accepting: no move left, no accepting state. With all branches finite, the machine rejects.' : 'Some branch is still running at level 6 and none has accepted. Here one branch runs right for ever, so the search would never end: this nondeterministic machine only recognises its language.', mark: s.kind });
      }
      const fr = F.list;
      const split = fr.findIndex((f) => f.meta && f.meta.kids > 1);
      if (split > 0) fr[split - 1].predict = { ask: 'How many children will the next configuration have?', options: ['0', '1', '2', '3'], answer: String(fr[split].meta.kids), explain: fr[split].say, pick: 'option' };
      const def = tk.defOf(M);
      return { frames: fr, def: { sections: [def.sections[0], Object.assign({}, def.sections[1], { title: 'δ(state, read) = set of moves' }), { id: 'bfs', kind: 'text', title: 'Accepting, nondeterministically', text: 'N accepts w if some branch of the tree reaches an accepting state. Search the tree breadth first: if an accepting node exists at depth d, it is found after finitely many nodes, even when other branches are infinite. Depth first could follow an infinite branch for ever.' }] } };
    },
    quiz: [
      { q: 'When does a nondeterministic machine accept?', options: ['When every branch accepts', 'When some branch accepts', 'When most branches accept', 'When the first branch accepts'], answer: 1, why: 'One accepting computation is enough.' },
      { q: 'Why search breadth first rather than depth first?', options: ['It uses less memory', 'A depth-first search can follow an infinite branch for ever and miss an accepting one', 'It is faster', 'Depth first does not work on trees'], answer: 1, why: 'Breadth first reaches every node of depth d after finitely many steps, whatever the other branches do.' },
      { q: 'When does the breadth-first simulation reject?', options: ['Never', 'When every branch has halted without accepting', 'After a fixed number of steps', 'When one branch rejects'], answer: 1, why: 'If the tree is finite and has no accepting node, the search runs out of nodes and rejects. If the tree is infinite with no accepting node, the search runs for ever.' },
      { q: 'With at most b choices per step, how many nodes can level d have?', options: ['d', 'b·d', 'bᵈ', 'd^b'], answer: 2, why: 'Each level multiplies by at most b. That is why the deterministic simulation can take exponentially longer.' },
    ],
  });

  // ======================================================================================================
  // The address tape: try every choice sequence in shortlex order, replaying from the start each time
  // ======================================================================================================
  T.topic({
    id: 'tm-ntm-address', family: 'tm-variants', order: 60, title: 'Simulating nondeterminism with an address tape',
    blurb: 'Three tapes: the input, kept clean; a work tape where one branch is replayed from the start; and an address tape counting 1, 2, 11, 12, 21, … that says which choice to take at each step.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'rep', options: Object.entries(NTMS).map(([value, x]) => ({ value, label: x.name })) },
      { id: 'w', kind: 'string', label: 'Input', def: 'aba', max: 4, check: (v, inp) => ([...v].some((c) => !NTMS[inp.m].alpha.includes(c)) ? 'Input: use only ' + [...NTMS[inp.m].alpha].join(' ') : null) },
    ],
    presets: [
      { label: 'aba: found along an address', values: { m: 'rep', w: 'aba' } },
      { label: 'ab: every address dies', values: { m: 'rep', w: 'ab' } },
      { label: 'bab: contains ab', values: { m: 'ab', w: 'bab' } },
    ],
    counters: [{ id: 'tried', label: 'addresses tried' }, { id: 'replay', label: 'steps replayed' }],
    run(inp) {
      const tk = TK();
      const M = tk.compile(NTMS[inp.m].text()).M;
      const res = T.tm.ntmAddress(M, inp.w, { maxLen: 5 });
      const tree = T.tm.ntmTree(M, inp.w, { maxDepth: 5, maxNodes: 80 });
      const nodes = tree.nodes;
      const kids = (id) => nodes.filter((n) => n.parent === id);
      const follow = (addr) => { const ids = [0]; for (const a of addr) { const ch = kids(ids[ids.length - 1]); if (a > ch.length) return { ids, bad: true }; ids.push(ch[a - 1].id); } return { ids, bad: false }; };
      // replay a branch for the work tape
      const replay = (addr) => { let c = T.tm.initial(M, inp.w); for (const a of addr) { const rs = T.tm.rulesFor(M, c); if (!rs.length || T.tm.isHalting(M, c.state) || a > rs.length) break; c = T.tm.apply(c, rs[a - 1]); } return c; };
      const N = 9, CW = 40;
      const F = new T.Frames(['tried', 'replay']);
      const notes = res.trace.filter((s) => s.kind === 'address');
      const shown = notes.slice(0, 36);
      const scene = (addr, outcome) => {
        const f = follow(addr);
        const path = new Set(f.ids);
        const t = (function build(id) { return { id: 'n' + id, label: nodes[id].state, cls: path.has(id) && id === f.ids[f.ids.length - 1] ? (outcome === 'accept' ? 'good' : outcome === 'reject' || outcome === 'invalid' ? 'reject' : 'hot') : '', children: kids(id).map((c) => build(c.id)) }; })(0);
        const d = K.tree.draw(t, { path: [...path].map((i) => 'n' + i), gapY: 64, gapX: 16, grow: false });
        const items = d.items;
        // the choice numbers on the edges
        for (const n of nodes) if (n.parent >= 0 && d.pos.has('n' + n.id)) {
          const a = d.pos.get('n' + n.parent), b = d.pos.get('n' + n.id), i = kids(n.parent).findIndex((x) => x.id === n.id) + 1;
          items.push({ key: 'ch' + n.id, kind: 'token', x: (a.x + b.x) / 2, y: (a.y + b.y) / 2, r: 9, text: String(i), cls: 'tu-choice' + (path.has(n.id) && path.has(n.parent) ? ' hot' : ''), audit: 'ignore' });
        }
        const ty = d.box.y + d.box.h + 50, tx = d.box.x + d.box.w / 2 - (N * CW) / 2;
        const c0 = T.tm.initial(M, inp.w), c = replay(addr);
        items.push(...tk.tape(c0, { cells: N, cw: CW, origin: -1, x: tx, y: ty, prefix: 'in', label: 'input', noHead: true }).items);
        items.push(...tk.tape(c, { state: c.state, cells: N, cw: CW, origin: -1, x: tx, y: ty + 80, prefix: 'wk', label: 'work', headCls: outcome === 'accept' ? 'good' : outcome === 'running' ? '' : 'bad' }).items);
        items.push(...K.tape.draw({ tape: addr.map(String), head: Math.max(0, addr.length - 1), state: 'choice', cells: N, cw: CW, origin: -1, x: tx, y: ty + 186, prefix: 'ad', label: 'address', headCls: 'read' }).items);
        return items;
      };
      F.add({ items: scene([], 'running'), say: 'The tree of ' + inp.w + ', with each edge numbered by its choice. At most ' + res.branching + ' choices at any step, so addresses are strings over 1…' + res.branching + '. The address ε replays nothing: the start configuration.' });
      let replayed = 0;
      shown.forEach((s) => {
        F.count('tried');
        replayed += s.path.length - 1;
        F.set('replay', replayed);
        const what = { accept: 'reaches an accepting configuration', reject: 'reaches a configuration with no move: that branch is dead', invalid: 'names a choice that does not exist there, so it is skipped', running: 'ends while the branch is still running: try the next address' }[s.outcome];
        F.add({ items: scene(s.address, s.outcome), say: 'Address ' + (s.address.join('') || 'ε') + ': copy the input to the work tape and replay ' + (s.address.length ? 'choices ' + s.address.join(', ') : 'nothing') + '. It ' + what + '.', meta: { addr: s.address.join('') || 'ε' }, mark: s.outcome === 'accept' ? 'accepted' : undefined });
      });
      const v = res.verdict;
      const lastAddr = shown.length ? shown[shown.length - 1] : { address: [], outcome: 'running' };
      F.add({ items: scene(lastAddr.address, lastAddr.outcome), say: (notes.length > shown.length ? '(' + (notes.length - shown.length) + ' more addresses were tried.) ' : '') + (v === 'accept' ? 'An address led to acceptance, so the deterministic machine accepts. It replayed ' + replayed + ' steps in all: wasteful, but it needs only three tapes and no memory of the tree.' : v === 'reject' ? 'Every address of length ' + (lastAddr.address.length) + ' ends in a dead or invalid branch: the whole tree is finite and has no accepting node, so the machine rejects.' : 'No acceptance up to length 5, and branches are still running.'), mark: v });
      const fr = F.list;
      for (let i = 2; i < fr.length - 2; i++) if (fr[i].meta && fr[i + 1].meta) {
        const nx = fr[i + 1].meta.addr, cands = [...new Set([nx, fr[i].meta.addr + '1', nx.split('').reverse().join(''), String(Number(fr[i].meta.addr) + 10)])].filter((x) => /^[0-9ε]+$/.test(x)).slice(0, 4);
        if (cands.length >= 2) { fr[i].predict = { ask: 'Which address is tried after ' + fr[i].meta.addr + '?', options: cands.sort(), answer: nx, explain: 'Addresses go in shortlex order: all of one length, counting up, before any longer one.', pick: 'option' }; break; }
      }
      return { frames: fr, def: { sections: [{ id: 'how', kind: 'text', title: 'The three tapes', text: 'Tape 1 keeps the input and is never written. Tape 3 holds an address: a string over 1…b, where b is the most choices any configuration has. For each address in shortlex order: copy tape 1 to tape 2 and run, taking choice d at the i-th step when the i-th digit is d. Accept if an accepting state is reached.' }, tk.defOf(M).sections[1]] } };
    },
    quiz: [
      { q: 'Why is tape 1 never written?', options: ['It is read-only by definition', 'Each address replays from the start, so the original input must survive', 'To save time', 'It holds the address'], answer: 1, why: 'Every branch is tried from scratch; tape 2 is wiped and refilled from tape 1 each time.' },
      { q: 'Why shortlex order, shortest addresses first?', options: ['It is alphabetical', 'So every branch prefix of length d is tried after finitely many addresses: a breadth-first search', 'To find the longest branch', 'It does not matter'], answer: 1, why: 'Trying all addresses of length 1, then 2, … visits the tree level by level, so an infinite branch cannot trap the search.' },
      { q: 'The address names choice 3 where only 2 moves exist. What happens?', options: ['The machine crashes', 'That address is skipped and the next one tried', 'It takes choice 1', 'It accepts'], answer: 1, why: 'An invalid address just leads nowhere; the counter moves on.' },
      { q: 'What does the deterministic simulation cost?', options: ['The same number of steps', 'Exponentially many steps in the worst case', 'Twice as many', 'Infinitely many always'], answer: 1, why: 'There can be bᵈ addresses of length d, and each replays up to d steps.' },
    ],
  });

  // ======================================================================================================
  // Enumerators: a machine with a printer
  // ======================================================================================================
  const ENUM_ANBN = 'print: pr\nstart: pr\ninput: a b\npr, a|b|_ -> w1, *, L\nw1, _ -> r, a, R\nr, a|b -> r, *, R\nr, _ -> bk, b, L\nbk, a|b -> bk, *, L\nbk, _ -> pr, _, R';
  const ENUMS = { bin: { text: () => T.tmLib.entry('enum-binary').text.trim(), name: 'every binary string' }, anbn: { text: () => ENUM_ANBN, name: 'aⁿbⁿ' }, even: { text: () => T.tmLib.entry('enum-even-a').text.trim(), name: 'even numbers of a' } };
  T.topic({
    id: 'tm-enumerator', family: 'tm-variants', order: 70, title: 'Enumerators: machines that print a language',
    blurb: 'An enumerator starts on a blank tape and never reads input. Each time it enters its print state, what is on the tape goes to the printer. The language is everything it ever prints.',
    inputs: [{ id: 'm', kind: 'choice', label: 'Enumerator', def: 'anbn', options: Object.entries(ENUMS).map(([value, x]) => ({ value, label: x.name })) }, { id: 'n', kind: 'number', label: 'Strings to print', def: 4, min: 2, max: 6 }],
    presets: [
      { label: 'aⁿbⁿ, starting with ε', values: { m: 'anbn', n: 4 } },
      { label: 'Binary strings in shortlex order', values: { m: 'bin', n: 6 } },
      { label: 'Even numbers of a', values: { m: 'even', n: 5 } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'printed', label: 'printed' }],
    run(inp) {
      const tk = TK();
      const M = tk.compile(ENUMS[inp.m].text()).M;
      const c = T.tm.initial(M, '');
      const N = 11, CW = 44;
      const sc = K.tape.scroller({ cells: N, origin: -3 });
      const printed = [];
      const F = new T.Frames(['steps', 'printed']);
      const PX = N * CW + 80;
      const scene = (headCls, fresh) => {
        const items = tk.tape(c, { state: c.state, cells: N, cw: CW, origin: sc.at(c.heads[0].p), prevOrigin: sc.prev, x: 0, y: 40, label: 'work', headCls }).items;
        items.push({ key: 'pT', kind: 'text', x: PX, y: 0, text: 'PRINTER', cls: 'title' });
        const vis = printed.slice(-6);
        const off = printed.length - vis.length;
        vis.forEach((s, i) => items.push({ key: 'pr' + (off + i), kind: 'cell', x: PX, y: 14 + i * 40, w: 150, h: 34, text: (off + i + 1) + '.  ' + (s || 'ε'), cls: 'mono' + (fresh && off + i === printed.length - 1 ? ' hot' : ''), enter: 'drop', exit: 'rise', rx: 6 }));
        if (!printed.length) items.push({ key: 'pE', kind: 'text', x: PX, y: 36, text: 'nothing yet', cls: 'tu-small' });
        return items;
      };
      const doPrint = () => { const s = tk.contents(c, 0).join(''); printed.push(s); return s; };
      let say0 = 'The tape starts blank and there is no input. The print state is ' + M.print + '.';
      if (c.state === M.print) { const s = doPrint(); F.set('printed', 1); say0 += ' The machine starts in it, so it prints ' + (s || 'ε') + ' straight away.'; }
      F.add({ items: scene('', true), say: say0 });
      let steps = 0;
      while (printed.length < inp.n && steps < 160) {
        const rs = T.tm.rulesFor(M, c);
        if (!rs.length) break;
        const r = rs[0], was = c.state;
        T.tm.apply(c, r);
        steps++;
        F.count('steps');
        let say = tk.sayRule(r), fresh = false, meta = null;
        if (c.state === M.print && was !== M.print) { const s = doPrint(); F.set('printed', printed.length); fresh = true; say += ' Entering ' + M.print + ' prints the tape: ' + (s || 'ε') + '.'; meta = { printed: s }; }
        F.add({ items: scene(fresh ? 'hot' : '', fresh), say, meta });
      }
      F.add({ items: scene('good'), say: 'Printed so far: ' + printed.map((s) => s || 'ε').join(', ') + ', and it would go on for ever. A string is in the language exactly when it is printed at some point, so a recogniser can run the enumerator and wait for its input to appear.', mark: 'printing' });
      const fr = F.list;
      const pi = fr.map((f, i) => (f.meta && f.meta.printed !== undefined ? i : -1)).filter((i) => i > 0);
      if (pi.length >= 2) {
        const at = pi[1], prev = printed[pi.length > 1 ? printed.indexOf(fr[at].meta.printed) - 1 : 0] || '';
        const right = fr[at].meta.printed || 'ε';
        const opts = [...new Set([right, (prev + prev) || 'ε', (prev + 'a') || 'a', (prev.slice(1)) || 'ε'])].slice(0, 4);
        if (opts.length >= 2 && at - 3 > 0) fr[at - 3].predict = { ask: 'What will the printer print next?', options: opts.sort(), answer: right, explain: fr[at].say, pick: 'option' };
      }
      const def = tk.defOf(M);
      return { frames: fr, def: { sections: [def.sections[1], { id: 'enum', kind: 'text', title: 'Enumerators and recognisers', text: 'L is recognisable exactly when some enumerator prints L. From an enumerator: on input w, run it and accept when w is printed. From a recogniser R: in round i, run R for i steps on each of the first i strings, and print the ones accepted (dovetailing). Strings may be printed in any order and more than once.' }] } };
    },
    quiz: [
      { q: 'An enumerator for L has printed a million strings and not w. What follows?', options: ['w is not in L', 'Nothing yet: w may come later', 'L is finite', 'The enumerator is wrong'], answer: 1, why: 'The order is up to the enumerator; w may simply not have come up yet.' },
      { q: 'If an enumerator prints the strings of L in shortlex order, L is…', options: ['regular', 'decidable', 'undecidable', 'finite'], answer: 1, why: 'To decide w, run the enumerator until it prints w (yes) or something after w in shortlex order (no). (For finite L the printing stops, but finite languages are decidable anyway.)' },
      { q: 'Why can a recogniser not just run R on the strings one after another?', options: ['It can', 'R may run for ever on one string and never reach the next', 'There are too many strings', 'Strings repeat'], answer: 1, why: 'Hence dovetailing: a little time on many strings at once.' },
      { q: 'May an enumerator print a string twice?', options: ['No', 'Yes; the language is the set of strings printed', 'Only ε', 'Only if L is infinite'], answer: 1, why: 'Repeats do no harm: the language is the set of everything printed.' },
    ],
  });

  // ======================================================================================================
  // Dovetailing: a zig-zag through (string, steps) so no single string can stall the search
  // ======================================================================================================
  const RECS = {
    aa: { text: () => T.tmLib.entry('aa-recogniser').text.trim(), name: 'contains aa (spins on the rest)' },
    even: { text: () => 'start: e\naccept: yes\ne, a|b -> o, *, R\no, a|b -> e, *, R\ne, _ -> yes, _, S\no, _ -> o, _, R', name: 'even length (runs away on the rest)' },
  };
  T.topic({
    id: 'tm-dovetail', family: 'tm-variants', order: 80, title: 'Dovetailing',
    blurb: 'To list everything a recogniser accepts, never wait for one string. Run string j for s steps for every pair (j, s), going along the diagonals: every pair is reached, so every accepted string gets printed.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Recogniser', def: 'aa', options: Object.entries(RECS).map(([value, x]) => ({ value, label: x.name })) },
      { id: 'order', kind: 'choice', label: 'Schedule', def: 'zig', options: [{ value: 'zig', label: 'zig-zag along the diagonals' }, { value: 'one', label: 'one string at a time' }] },
    ],
    presets: [
      { label: 'Zig-zag: contains aa', values: { m: 'aa', order: 'zig' } },
      { label: 'One at a time gets stuck on ε', values: { m: 'aa', order: 'one' } },
      { label: 'Zig-zag: even length', values: { m: 'even', order: 'zig' } },
      { label: 'One at a time: even length', values: { m: 'even', order: 'one' } },
    ],
    counters: [{ id: 'runs', label: 'runs started' }, { id: 'printed', label: 'printed' }],
    run(inp) {
      const tk = TK();
      const M = tk.compile(RECS[inp.m].text()).M;
      const ROWS = 7, COLS = 7, S = 44, X0 = 60, Y0 = 40;
      const words = T.tm.strings(['a', 'b'], 3).slice(0, ROWS);
      const status = (j, s) => T.tm.run(M, words[j], { maxSteps: s, loops: false, trace: false });
      const halt = words.map((w) => { const r = T.tm.run(M, w, { maxSteps: 200, loops: false, trace: false }); return r.verdict === 'limit' ? null : { at: r.steps, v: r.verdict }; });
      const order = [];
      if (inp.order === 'zig') {
        for (let d = 0; d < ROWS + COLS - 1; d++) { const cells = []; for (let j = 0; j <= d; j++) { const s = d - j + 1; if (j < ROWS && s <= COLS) cells.push([j, s]); } if (d % 2) cells.reverse(); order.push(...cells); }
      } else { for (let s = 1; s <= COLS; s++) order.push([0, s]); }
      const visited = new Map(), printed = [];
      const F = new T.Frames(['runs', 'printed']);
      const ctr = (j, s) => ({ x: X0 + (s - 1) * S + S / 2, y: Y0 + j * S + S / 2 });
      const scene = (k) => {
        const items = [];
        items.push({ key: 'colT', kind: 'text', x: X0, y: Y0 - 22, text: 'STEPS RUN →', cls: 'title' });
        for (let s = 1; s <= COLS; s++) items.push({ key: 'cn' + s, kind: 'text', x: ctr(0, s).x, y: Y0 - 6, text: String(s), anchor: 'middle', cls: 'tu-num', size: 12 });
        for (let j = 0; j < ROWS; j++) {
          items.push({ key: 'rw' + j, kind: 'text', x: X0 - 12, y: ctr(j, 1).y + 5, text: words[j] || 'ε', anchor: 'end', cls: 'mono', mono: true });
          for (let s = 1; s <= COLS; s++) {
            const v = visited.get(j + ',' + s);
            const here = k >= 0 && order[k][0] === j && order[k][1] === s;
            items.push({ key: 'c' + j + ',' + s, kind: 'cell', x: X0 + (s - 1) * S, y: Y0 + j * S, w: S, h: S, rx: 3, text: v === undefined ? '' : v === 'accept' ? '✓' : v === 'reject' ? '✗' : '…', cls: (here ? 'hot' : v === 'accept' ? 'good' : v === 'reject' ? 'bad' : v ? 'read' : '') });
          }
        }
        for (let i = 1; i <= k; i++) { const a = ctr(order[i - 1][0], order[i - 1][1]), b = ctr(order[i][0], order[i][1]); items.push({ key: 'zz' + i, kind: 'edge', from: { x: a.x, y: a.y }, to: { x: b.x, y: b.y }, head: false, gapB: 0, cls: 'tu-trail' + (i < k - 6 ? ' old' : ''), audit: 'ignore', layer: 'top' }); }
        const PX = X0 + COLS * S + 50;
        items.push({ key: 'pT', kind: 'text', x: PX, y: Y0 - 22, text: 'PRINTED', cls: 'title' });
        printed.forEach((w, i) => items.push({ key: 'p' + w, kind: 'cell', x: PX, y: Y0 + i * 40, w: 90, h: 34, text: w || 'ε', cls: 'mono good', enter: 'drop', rx: 6 }));
        return items;
      };
      F.add({ items: scene(-1), say: 'Rows are the strings in shortlex order, columns the number of steps to run. A cell will show … for still running, ✓ for accepted, ✗ for rejected. The recogniser accepts ' + RECS[inp.m].name.split(' (')[0] + '.' });
      order.forEach(([j, s], k) => {
        const r = status(j, s);
        visited.set(j + ',' + s, r.verdict === 'limit' ? 'run' : r.verdict);
        F.count('runs');
        let say = 'Run ' + (words[j] || 'ε') + ' for ' + s + ' step' + (s === 1 ? '' : 's') + ': ' + (r.verdict === 'limit' ? 'still running.' : r.verdict === 'accept' ? 'accepted.' : 'rejected.');
        if (r.verdict === 'accept' && !printed.includes(words[j])) { printed.push(words[j]); F.set('printed', printed.length); say += ' Print ' + (words[j] || 'ε') + '.'; }
        F.add({ items: scene(k), say, meta: { j, s } });
      });
      const stuck = inp.order === 'one';
      F.add({ items: scene(order.length - 1), say: stuck ? (halt[0] ? 'ε halted, so this time the next string would get its turn; but with another recogniser one looping string blocks everything after it.' : 'ε never halts: this recogniser runs for ever on it. One string at a time, nothing after ε ever gets a turn, and aa is never printed.') : 'Every cell on these diagonals has been visited. Going on along longer diagonals reaches every (string, steps) pair, so every accepted string is printed eventually, and the strings that loop cost only a little time each.', mark: stuck && !halt[0] ? 'stuck' : 'dovetailed' });
      const fr = F.list;
      if (inp.order === 'zig' && fr.length > 6) fr[4].predict = { ask: 'Click the cell the zig-zag visits next.', answer: 'c' + fr[5].meta.j + ',' + fr[5].meta.s, explain: 'Each diagonal holds the pairs with the same total; the path runs along it and turns back on the next.', pick: 'item' };
      else if (fr.length > 3) fr[1].predict = { ask: 'Will ε ever halt, so that the next string gets its turn?', options: ['Yes', 'No'], answer: halt[0] ? 'Yes' : 'No', explain: halt[0] ? 'It halts after ' + halt[0].at + ' steps.' : 'On ε the recogniser never halts.', pick: 'option' };
      return { frames: fr, def: { sections: [tk.defOf(M).sections[1], { id: 'dt', kind: 'text', title: 'The schedule', text: 'Pairs (j, s): string number j, run for s steps. Along the diagonals j + s = 1, 2, 3, …, each finite, so every pair comes up after finitely many others. Rerunning from the start each time wastes steps but needs no memory of earlier runs.' }] } };
    },
    quiz: [
      { q: 'Why does running one string at a time fail?', options: ['It is too slow', 'If the recogniser loops on one string, no later string is ever tried', 'Strings get printed twice', 'It prints rejected strings'], answer: 1, why: 'A recogniser need not halt on non-members, so waiting for an answer may mean waiting for ever.' },
      { q: 'Does the zig-zag reach the pair (string 100, 50 steps)?', options: ['No, it is too far', 'Yes, after finitely many other pairs', 'Only if the string is accepted', 'Only on even diagonals'], answer: 1, why: 'It lies on diagonal 150, and every diagonal is finite.' },
      { q: 'Dovetailing shows that from a recogniser one can build…', options: ['a decider', 'an enumerator for the same language', 'a finite automaton', 'a faster recogniser'], answer: 1, why: 'Print each string the first time some (string, steps) pair accepts it.' },
      { q: 'An accepted string appears in many cells of its row (✓ from some step on). How often is it printed?', options: ['Once, the first time', 'Every time', 'Never', 'Twice'], answer: 0, why: 'The schedule remembers what it printed; printing it again would not be wrong, just untidy.' },
    ],
  });
})();
