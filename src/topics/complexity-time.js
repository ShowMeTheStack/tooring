// Measuring time: a machine's steps counted as its inputs grow, growth rates racing, big-O read off real step
// counts, what a second tape is worth, and why the way a number is written changes how fast an algorithm is.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CX = K.cx;

  T.family({ id: 'cx-time', part: 'complexity', order: 10, title: 'Measuring time', blurb: 'Time is the number of steps a machine takes, as a function of the length of its input: count them, watch them grow, and say how fast with big-O.' });

  // ---- small helpers shared by the topics of this family ------------------------------------------------
  /** Tick marks for an axis from 0 to about max: steps of 1, 2 or 5 times a power of ten */
  const ticks = (max, count) => {
    const raw = Math.max(1, max) / (count || 4);
    const p = Math.pow(10, Math.floor(Math.log10(raw)));
    const step = [1, 2, 5, 10].map((m) => m * p).find((s) => s >= raw);
    const out = [];
    for (let v = 0; v <= max + step * 0.001; v += step) out.push(Math.round(v * 1e6) / 1e6);
    if (out[out.length - 1] < max) out.push(Math.round((out[out.length - 1] + step) * 1e6) / 1e6);
    return out;
  };
  /** How long a number of steps takes at a billion steps a second */
  const howLong = (steps) => {
    const s = steps / 1e9;
    if (!Number.isFinite(s)) return 'for ever';
    if (s < 1e-6) return Math.max(1, Math.round(s * 1e9)) + ' ns';
    if (s < 1e-3) return Math.round(s * 1e6) + ' µs';
    if (s < 1) return Math.round(s * 1e3) + ' ms';
    if (s < 60) return Math.round(s) + ' s';
    if (s < 3600) return Math.round(s / 60) + ' min';
    if (s < 86400) return Math.round(s / 3600) + ' hours';
    if (s < 3.15e7) return Math.round(s / 86400) + ' days';
    if (s < 4.35e17) return CX.num(Math.round(s / 3.15e7)) + ' years';
    return 'older than the universe';
  };
  /** Series labels of a chart kept inside [top, bottom]: the kit pushes a crowd of labels below the axis, so
   *  pull them back up, keeping them 20 apart and in order (a local fix; the kit's own pass only pushes down) */
  const keepLabels = (items, P, top, bottom) => {
    const ls = items.filter((it) => it.key.startsWith(P + ':sl:')).sort((a, b) => a.y - b.y);
    for (let i = ls.length - 1; i >= 0; i--) ls[i].y = Math.min(ls[i].y, i === ls.length - 1 ? bottom : ls[i + 1].y - 20);
    for (let i = 0; i < ls.length; i++) ls[i].y = Math.max(ls[i].y, i ? ls[i - 1].y + 20 : top);
    return items;
  };
  const libChoices = (ids) => ids.map((id) => ({ value: id, label: T.tmLib.entry(id).title }));
  const alphaCheck = (id, w, L) => { const e = T.tmLib.entry(id); const bad = [...w].find((c) => !e.alphabet.includes(c)); return bad === undefined ? null : (L || 'Input') + ': "' + bad + '" is not in this machine\'s alphabet {' + e.alphabet.join(', ') + '}'; };
  const showW = (w) => (w === '' ? 'ε' : w);
  /** One tape from a snapshot of T.tm.run's trace */
  const tapeOf = (snap, k) => { const t = snap.tapes[k || 0]; const h = t.heads.find((x) => x.head === (k || 0)) || t.heads[0]; return { tape: t.cells, offset: t.from, head: h ? h.at : 0 }; };
  /** Every string of length n over an alphabet */
  const ofLength = (alpha, n) => T.tm.strings(alpha, n).filter((w) => w.length === n);

  // =========================================================================================================
  // 1. Counting steps
  // =========================================================================================================
  const STEP_MACHINES = ['anbn', 'palindrome', 'even-length', 'contains-11'];
  T.topic({
    id: 'cx-steps', family: 'cx-time', order: 10, title: 'Counting a machine\'s steps',
    blurb: 'Run a Turing machine and count its moves. Then run it on every input of each length: the worst count for length n is the machine\'s running time t(n).',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'anbn', options: libChoices(STEP_MACHINES) },
      { id: 'w', kind: 'string', label: 'Input to watch', def: 'aabb', max: 8 },
      { id: 'n', kind: 'number', label: 'Lengths up to', def: 6, min: 3, max: 8 },
    ],
    check: (inp) => alphaCheck(inp.m, inp.w, 'Input to watch'),
    presets: [
      { label: 'aⁿbⁿ on aabb', values: { m: 'anbn', w: 'aabb', n: 6 } },
      { label: 'Rejected early: ba', values: { m: 'anbn', w: 'ba', n: 6 } },
      { label: 'The empty input', values: { m: 'anbn', w: '', n: 5 } },
      { label: 'Palindromes: abba', values: { m: 'palindrome', w: 'abba', n: 7 } },
      { label: 'A linear machine: even length', values: { m: 'even-length', w: 'abab', n: 8 } },
    ],
    counters: [{ id: 'steps', label: 'steps of this run' }, { id: 'inputs', label: 'inputs measured' }],
    run(inp) {
      const M = T.tmLib.get(inp.m), e = T.tmLib.entry(inp.m);
      const r = T.tm.run(M, inp.w, { maxSteps: 3000 });
      // every input of every length up to n, with its step count
      const table = [];
      for (let n = 0; n <= inp.n; n++) {
        const all = ofLength(e.alphabet, n).map((w) => ({ w, steps: T.tm.run(M, w, { trace: false, maxSteps: 3000 }).steps }));
        let worst = all[0];
        for (const x of all) if (x.steps > worst.steps) worst = x;
        table.push({ n, all, worst, avg: all.reduce((s, x) => s + x.steps, 0) / all.length });
      }
      const xmax = Math.max(inp.n, inp.w.length);
      const ymax = Math.max(r.steps, ...table.map((t) => t.worst.steps));
      const yt = ticks(ymax, 4);
      const PX = 30, PY = 190, PW = 440, PH = 230;
      const chart = (upto, mine, opts) => {
        opts = opts || {};
        const series = [];
        if (upto >= 0) {
          series.push({ id: 'worst', label: 'worst t(n)', cls: 's4', pts: table.slice(0, upto + 1).map((t) => [t.n, t.worst.steps]) });
          series.push({ id: 'avg', label: 'average', cls: 's0', dash: true, pts: table.slice(0, upto + 1).map((t) => [t.n, t.avg]) });
        }
        if (mine !== null) series.push({ id: 'mine', label: showW(inp.w) + ': ' + mine, cls: 's3', hot: true, pts: [[inp.w.length, mine]] });
        return CX.plot({ prefix: 'pl', x: PX, y: PY, w: PW, h: PH, xs: [0, xmax], ys: [0, yt[yt.length - 1]], yTicks: yt, xTicks: [...Array(xmax + 1).keys()], xLabel: 'input length n', yLabel: 'steps', series, marks: opts.mark !== undefined ? [{ id: 'n', x: opts.mark, text: opts.mark ? 'n = ' + opts.mark : '' }] : [] }).items;
      };
      const sc = K.tape.scroller({ cells: 11, origin: -2, margin: 2 });
      const tape = (snap, label, cls) => {
        const t = tapeOf(snap);
        const origin = sc.at(t.head);
        return K.tape.draw({ prefix: 'tp', tape: t.tape, offset: t.offset, head: t.head, state: snap.state, cells: 11, origin, prevOrigin: sc.prev, x: 0, y: 30, label, headCls: cls || '' }).items;
      };
      const F = new T.Frames(['steps', 'inputs']);
      const moves = r.trace.filter((s) => s.kind === 'move');
      const every = Math.max(1, Math.ceil(moves.length / 22));
      const start = r.trace[0];
      F.add({ items: tape(start, 'tape').concat(chart(-1, 0)), say: 'Watch ' + e.title + ' on ' + showW(inp.w) + ' (length ' + inp.w.length + '). Each move of the head is one step; the amber point on the chart climbs with the count.', hl: { tm: [] } });
      moves.forEach((s, k) => {
        if ((k + 1) % every && k !== moves.length - 1) return;
        F.set('steps', s.step);
        F.add({ items: tape(s, 'tape').concat(chart(-1, s.step)), say: 'Step ' + s.step + ': ' + s.say + (every > 1 ? ' (showing every ' + every + ' steps)' : '') });
      });
      const end = r.trace[r.trace.length - 1];
      F.set('steps', r.steps);
      const early = r.verdict === 'reject' && r.steps <= Math.max(2, inp.w.length / 2);
      F.add({ items: tape(end, 'tape', r.accepted ? 'good' : 'bad').concat(chart(-1, r.steps)), mark: r.accepted ? 'accepted' : 'rejected', say: (r.accepted ? 'Accepted' : 'Rejected') + ' after ' + r.steps + ' step' + (r.steps === 1 ? '' : 's') + '. ' + (inp.w === '' ? 'On the empty input the machine sees a blank at once: one step is all it needs. Even ε has a running time.' : early ? 'It gave up almost at once: ' + r.reason + '. Rejecting early is cheap; running time is about the worst case, not this one.' : 'That is one input. The running time of a machine is not one number but a function of the length n.') });
      // every input of each length
      table.forEach((t, k) => {
        F.count('inputs', t.all.length);
        const wsnap = { tapes: [{ from: -1, cells: ['⊔'].concat([...t.worst.w], ['⊔']), heads: [{ head: 0, at: 0 }] }], state: M.start };
        F.add({ items: tape(wsnap, 'worst').concat(chart(k, r.steps, { mark: t.n })), say: 'Length ' + t.n + ': all ' + t.all.length + ' input' + (t.all.length === 1 ? '' : 's') + ' run. The slowest is ' + showW(t.worst.w) + ' with ' + t.worst.steps + ' steps' + (t.all.length > 1 ? '; the average is ' + (Math.round(t.avg * 10) / 10) : '') + '. So t(' + t.n + ') = ' + t.worst.steps + '.', hl: { tab: [String(k)] }, meta: { n: t.n } });
      });
      const last = table[table.length - 1];
      F.add({ items: tape({ tapes: [{ from: -1, cells: ['⊔'].concat([...last.worst.w], ['⊔']), heads: [{ head: 0, at: 0 }] }], state: M.start }, 'worst').concat(chart(table.length - 1, r.steps)), say: 'The red points are t(n), the worst case for each length; the dashed blue line, the average, sits below it. ' + (inp.w.length <= inp.n ? 'Your input ' + showW(inp.w) + ' took ' + r.steps + ' of the at most ' + table[inp.w.length].worst.steps + ' steps for its length.' : ''), mark: 't(n)' });
      return { frames: F.list, def: { sections: [
        { id: 'tm', kind: 'math', title: 'The machine', text: e.title + '\n' + e.blurb + '\nstates ' + M.states.join(', ') },
        { id: 'def', kind: 'text', title: 'Running time', text: 't(n) = the largest number of steps M takes on any input of length n. Worst case, so that t(n) is a promise for every input.' },
        { id: 'tab', kind: 'table', title: 'Measured', colHead: ['n', 'inputs', 'worst', 'worst input', 'average'], rows: table.map((t) => [t.n, t.all.length, t.worst.steps, showW(t.worst.w), Math.round(t.avg * 10) / 10]) },
      ] }, meta: { table } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.n >= 2 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.n === f.meta.n + 1 && f.meta.n % 2 === 0, pick: 'option',
        ask: (fr, i) => 'Next come all inputs of length ' + (fr[i].meta.n + 1) + '. Which will be the slowest?',
        options: (fr, i, inp) => { const M = T.tmLib.get(inp.m), e = T.tmLib.entry(inp.m), n = fr[i].meta.n + 1; const all = ofLength(e.alphabet, n).map((w) => ({ w, s: T.tm.run(M, w, { trace: false }).steps })).sort((a, b) => b.s - a.s || (a.w < b.w ? -1 : 1)); const pick = [all[0]]; for (const x of all) if (pick.length < 3 && x.s < pick[pick.length - 1].s) pick.push(x); return pick.map((x) => x.w).sort(); },
        answer: (fr, i, inp) => { const M = T.tmLib.get(inp.m), e = T.tmLib.entry(inp.m), n = fr[i].meta.n + 1; let b = null; for (const w of ofLength(e.alphabet, n)) { const s = T.tm.run(M, w, { trace: false }).steps; if (!b || s > b.s) b = { w, s }; } return b.w; },
        explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why is running time defined by the worst input of each length, not the average?', options: ['Averages are hard to compute', 'So that t(n) bounds the steps on every input of length n', 'Because the worst input is always the longest', 'Because machines never finish early'], answer: 1, why: 'A worst-case bound is a guarantee: whatever input of length n arrives, the machine halts within t(n) steps.' },
      { q: 'The machine rejects ba after 1 step. What does that say about t(2)?', options: ['t(2) = 1', 't(2) ≥ 1, and some other input of length 2 may take longer', 't(2) is undefined', 'Nothing: rejections do not count'], answer: 1, why: 't(2) is the maximum over all four inputs of length 2; one quick rejection only shows the maximum is at least 1.' },
      { q: 'What is the running time on the empty input ε?', options: ['0 by definition', 'Whatever the machine takes on ε: t(0) is a real value', 'Undefined', 'Always 1'], answer: 1, why: 'ε is an input like any other; the machine still has to look at the blank and decide.' },
      { q: 'Why does a time count run over inputs of each length rather than each input separately?', options: ['To compare machines by how the work grows with the size of the problem', 'Because the tape is finite', 'Because inputs of the same length take the same time', 'To make the numbers smaller'], answer: 0, why: 'Grouping by length turns a pile of numbers into one function of n, whose growth we can compare.' },
      { q: 'A machine reads its input once from left to right and halts. Its t(n) is about', options: ['1', 'n', 'n²', '2ⁿ'], answer: 1, why: 'One move per symbol plus one for the blank at the end: n + 1 steps.' },
    ],
  });

  // =========================================================================================================
  // 2. The growth-rate race
  // =========================================================================================================
  const G = Object.fromEntries(T.cx.GROWTH.map((g) => [g.id, g]));
  const RACES = {
    race: { label: 'The full field', ids: ['n', 'nlog', 'n2', 'n3', '2n', 'fact'], ns: [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 25, 30, 40, 50, 60], log: true, max: 1e24, ys: [1, 1e24], yTicks: [1, 1e6, 1e12, 1e18, 1e24] },
    polyexp: { label: 'n³ against 2ⁿ', ids: ['n3', '2n'], ns: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], log: false, max: 4000, ys: [1, 1e5], yTicks: [1, 10, 100, 1000, 1e4, 1e5] },
    consts: { label: '100·n against n²', ids: ['100n', 'n2'], ns: [10, 20, 40, 60, 80, 100, 120, 140, 160], log: false, max: 26000, ys: [100, 1e5], yTicks: [100, 1000, 1e4, 1e5] },
    factexp: { label: '2ⁿ against n!', ids: ['2n', 'fact'], ns: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], log: false, max: 5000, ys: [1, 1e7], yTicks: [1, 100, 1e4, 1e6] },
    slow: { label: 'log n against n', ids: ['log', 'n'], ns: [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024], log: false, max: 1100, ys: [1, 1e4], yTicks: [1, 10, 100, 1000, 1e4] },
  };
  const fnOf = (id) => (id === '100n' ? { id, name: '100·n', f: (n) => 100 * n } : G[id]);

  T.topic({
    id: 'cx-growth', family: 'cx-time', order: 20, title: 'The growth-rate race',
    blurb: 'n, n log n, n², n³, 2ⁿ and n! start out close together. Make n bigger and watch them separate, with the time each would take at a billion steps a second.',
    inputs: [{ id: 'race', kind: 'choice', label: 'Race', def: 'race', options: Object.entries(RACES).map(([k, v]) => ({ value: k, label: v.label })) }],
    presets: Object.entries(RACES).map(([k, v]) => ({ label: v.label, values: { race: k } })),
    counters: [{ id: 'n', label: 'n' }],
    run(inp) {
      const R = RACES[inp.race];
      const fs = R.ids.map(fnOf);
      const F = new T.Frames(['n']);
      const leaderAt = (n) => { let b = fs[0]; for (const g of fs) if (g.f(n) > b.f(n)) b = g; return b; };
      const BX = 0, BW = 250;
      const scene = (k) => {
        const n = R.ns[k];
        const rows = fs.map((g, i) => ({ id: g.id, label: g.name, value: g.f(n), cls: 's' + (i % 8), text: CX.num(g.f(n)) + '  ·  ' + howLong(g.f(n)) }));
        const bars = CX.bars({ prefix: 'br', rows, x: BX + 70, y: 30, w: BW, barH: 32, gap: 12, log: R.log, max: R.max, title: 'n = ' + n + (R.log ? '   (bars on a log scale)' : '') });
        for (const it of bars.items) if (it.kind === 'cell') it.pick = true;
        const top = 30 + fs.length * 44 + 40;
        const plot = CX.plot({ prefix: 'pl', x: 50, y: top + 30, w: 400, h: 230, xs: [R.ns[0] > 2 ? 0 : 0, R.ns[R.ns.length - 1]], ys: R.ys, logY: true, yTicks: R.yTicks, xTicks: ticks(R.ns[R.ns.length - 1], 4).filter((v) => v <= R.ns[R.ns.length - 1]), xLabel: 'n', yLabel: 'steps (log scale)', marks: [{ id: 'n', x: n }],
          series: fs.map((g, i) => ({ id: g.id, label: g.name, cls: 's' + (i % 8), pts: R.ns.slice(0, k + 1).map((x) => [x, Math.max(R.ys[0], g.f(x))]) })) });
        return bars.items.concat(keepLabels(plot.items, 'pl', top + 30, top + 30 + 230 + 9));
      };
      R.ns.forEach((n, k) => {
        F.set('n', n);
        const lead = leaderAt(n);
        const prev = k ? leaderAt(R.ns[k - 1]) : null;
        let say;
        if (!k) say = 'At n = ' + n + ' the field is close: ' + fs.map((g) => g.name + ' = ' + CX.num(g.f(n))).join(', ') + '. Each bar is a count of steps; at a billion steps a second none of them takes any time worth mentioning.';
        else if (prev && prev.id !== lead.id) {
          const a = lead, b = prev;
          say = 'Overtaken! At n = ' + n + ', ' + a.name + ' = ' + CX.num(a.f(n)) + ' passes ' + b.name + ' = ' + CX.num(b.f(n)) + '. ' + (a.id === '2n' || a.id === 'fact' ? 'From here on it never looks back: an exponential beats every polynomial in the end.' : a.id === 'n2' && b.id === '100n' ? 'The constant 100 only delayed it: for n > 100, n² is bigger and stays bigger.' : 'The faster-growing function always wins in the end.');
        } else {
          const top = lead;
          const slow = fs.reduce((a, g) => (g.f(n) < a.f(n) ? g : a), fs[0]);
          say = 'n = ' + n + ': ' + top.name + ' leads with ' + CX.num(top.f(n)) + ' steps (' + howLong(top.f(n)) + '), while ' + slow.name + ' needs only ' + CX.num(slow.f(n)) + '.' + (top.f(n) > R.max ? ' Its bar has run off the scale.' : '');
        }
        F.add({ items: scene(k), say, meta: { lead: lead.id, k } });
      });
      const nl = R.ns[R.ns.length - 1];
      const lead = leaderAt(nl);
      F.add({ items: scene(R.ns.length - 1), mark: 'finish', say: 'At n = ' + nl + ' ' + lead.name + ' would take ' + howLong(lead.f(nl)) + '. On the log chart a polynomial bends over and flattens, while 2ⁿ climbs in a straight line and n! curves upward: no faster computer rescues an exponential algorithm.' });
      return { frames: F.list, def: { sections: [
        { id: 'fs', kind: 'table', title: 'The runners', colHead: ['f(n)', 'at n = 10', 'at n = ' + nl], rows: fs.map((g) => [g.name, CX.num(g.f(10)), CX.num(g.f(nl))]) },
        { id: 'o', kind: 'text', title: 'Faster growth', text: 'f grows faster than g when f(n) / g(n) → ∞. Then f passes g at some n and stays ahead for ever, whatever constants are in front.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && f.meta && fr[i + 1].meta.lead !== f.meta.lead, pick: 'item', once: true,
        ask: (fr, i) => 'Make n bigger. Which bar will be the longest at the next step? Click it.',
        answer: (fr, i) => 'br:b:' + fr[i + 1].meta.lead, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: '2ⁿ is smaller than n³ for n = 2 … 9. Which is faster for large n?', options: ['n³', '2ⁿ', 'Neither: they swap for ever', 'It depends on the computer'], answer: 1, why: '2ⁿ / n³ → ∞: from n = 10 on, 2ⁿ is the bigger one and the gap keeps growing.' },
      { q: 'An algorithm takes 100·n steps and another n². Which is better for big inputs?', options: ['100·n', 'n²', 'They are the same', 'n² because it has no constant'], answer: 0, why: 'For n > 100 the quadratic one is slower, and the gap widens without bound; constants only move the crossover.' },
      { q: 'At a billion steps a second, roughly how long do 2⁶⁰ steps take?', options: ['A second', 'An hour', 'About 36 years', 'Longer than the universe has existed'], answer: 2, why: '2⁶⁰ ≈ 1.15 × 10¹⁸ steps, that is 1.15 × 10⁹ seconds, about 36 years.' },
      { q: 'On a log scale, which curve is a straight line?', options: ['n²', '2ⁿ', 'n log n', 'n!'], answer: 1, why: 'log(2ⁿ) = n · log 2 is linear in n; polynomials have log of order log n, so they flatten.' },
      { q: 'A computer 1000 times faster runs a 2ⁿ algorithm. How much bigger an n can it handle in the same time?', options: ['1000 times bigger', 'About 10 more', 'Twice as big', 'No bigger at all'], answer: 1, why: '2¹⁰ ≈ 1000, so a thousandfold speed-up buys only about ten more.' },
    ],
  });

  // =========================================================================================================
  // 3. Big-O from real step counts
  // =========================================================================================================
  const FAMILIES = {
    palindrome: { truth: 'n2', worst: (n) => 'a'.repeat(n), worstText: 'aⁿ (a palindrome: nothing ends the run early)' },
    anbn: { truth: 'n2', worst: (n) => 'a'.repeat(Math.ceil(n / 2)) + 'b'.repeat(Math.floor(n / 2)), worstText: 'a⌈n/2⌉ b⌊n/2⌋' },
    'pal-2tape': { truth: 'n', worst: (n) => 'a'.repeat(n), worstText: 'aⁿ' },
    'even-length': { truth: 'n', worst: (n) => 'a'.repeat(n), worstText: 'any string of length n' },
  };
  const CANDS = ['n', 'nlog', 'n2', '2n'];
  T.topic({
    id: 'cx-bigo', family: 'cx-time', order: 30, title: 'Big-O from real step counts',
    blurb: 'Measure a machine\'s worst-case steps, then try candidate shapes c · f(n). Divide the steps by f(n): when the ratio settles to a constant, you have found the order of growth.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'palindrome', options: libChoices(Object.keys(FAMILIES)) },
      { id: 'n', kind: 'choice', label: 'Measure up to', def: '16', options: [{ value: '5', label: 'n = 5' }, { value: '10', label: 'n = 10' }, { value: '16', label: 'n = 16' }, { value: '24', label: 'n = 24' }] },
    ],
    presets: [
      { label: 'Palindromes up to 16', values: { m: 'palindrome', n: '16' } },
      { label: 'aⁿbⁿ up to 24', values: { m: 'anbn', n: '24' } },
      { label: 'Two tapes: palindromes', values: { m: 'pal-2tape', n: '16' } },
      { label: 'Too few points: n ≤ 5', values: { m: 'palindrome', n: '5' } },
    ],
    counters: [{ id: 'pts', label: 'points measured' }],
    run(inp) {
      const M = T.tmLib.get(inp.m), e = T.tmLib.entry(inp.m), fam = FAMILIES[inp.m], N = +inp.n;
      const pts = [];
      for (let n = 1; n <= N; n++) pts.push({ n, value: T.tm.run(M, fam.worst(n), { trace: false, maxSteps: 20000 }).steps });
      // up to length 7 every string was tried as well: the family really is the worst
      let checked = 0;
      for (let n = 1; n <= Math.min(7, N); n++) { const all = ofLength(e.alphabet, n).map((w) => T.tm.run(M, w, { trace: false }).steps); checked += all.length; if (Math.max(...all) !== pts[n - 1].value) checked = -1e9; }
      const fit = T.cx.fitGrowth(pts);
      const last = pts[pts.length - 1];
      const ratio = (g, p) => p.value / g.f(p.n);
      const norm = (g) => pts.map((p) => [p.n, ratio(g, p) / ratio(g, last)]);
      const yt = ticks(last.value, 4);
      const LW = 400;
      const top = (k, curves) => CX.plot({ prefix: 'st', x: 50, y: 30, w: LW, h: 200, xs: [0, N], ys: [0, yt[yt.length - 1]], yTicks: yt, xTicks: ticks(N, 4).filter((v) => v <= N), xLabel: 'n', yLabel: 'worst-case steps',
        series: [{ id: 'm', label: 'measured', cls: 's4', pts: pts.slice(0, k).map((p) => [p.n, p.value]) }].concat(curves.map((c) => ({ id: 'c' + c.id, label: (Math.round(ratio(G[c.id], last) * 100) / 100) + "·" + c.name, cls: c.cls, dash: !c.solid, dots: false, pts: Array.from({ length: 4 * N + 1 }, (_, j) => j / 4).filter((x) => x >= 1).map((x) => [x, ratio(G[c.id], last) * G[c.id].f(x)]) }))) }).items;
      const bottom = (shown, hot) => CX.plot({ prefix: 'rt', x: 50, y: 350, w: LW, h: 150, xs: [0, N], ys: [0.1, 10], logY: true, yTicks: [0.1, 1, 10], yTickText: (t) => '×' + t, xTicks: ticks(N, 4).filter((v) => v <= N), xLabel: 'n', yLabel: 'steps ÷ f(n), scaled to end at 1',
        series: shown.map((id) => { const g = G[id]; return { id, label: '÷ ' + g.name, cls: 's' + CANDS.indexOf(id), hot: id === hot, pts: norm(g).map(([x, y]) => [x, Math.min(Math.max(y, 0.1), 1e3)]) }; }) }).items;
      const F = new T.Frames(['pts']);
      F.add({ items: top(0, []).concat(bottom([])), say: e.title + ': we run it on its hardest input of each length, ' + fam.worstText + ', and plot the steps.' + (checked > 0 ? ' For lengths up to 7 all ' + checked + ' strings were run too, and none was slower.' : '') });
      const every = N > 12 ? 2 : 1;
      for (let k = 1; k <= N; k++) {
        if (k % every && k !== N) continue;
        F.set('pts', k);
        F.add({ items: top(k, []).concat(bottom([])), say: 'n = ' + pts[k - 1].n + ': ' + pts[k - 1].value + ' steps' + (k > 1 ? ' (up ' + (pts[k - 1].value - pts[k - 2].value) + ' from n = ' + pts[k - 2].n + ')' : '') + '.' });
      }
      const shown = [];
      CANDS.forEach((id, ci) => {
        const g = G[id];
        shown.push(id);
        const rs = pts.map((p) => ratio(g, p));
        const half = rs.slice(Math.floor(rs.length / 2));
        const spread = Math.max(...half) / Math.min(...half);
        const trend = rs[rs.length - 1] > rs[Math.floor(rs.length / 2)] * 1.1 ? 'up' : rs[rs.length - 1] < rs[Math.floor(rs.length / 2)] / 1.1 ? 'down' : 'flat';
        const words = trend === 'up' ? 'keeps growing: ' + g.name + ' is too slow a shape, the steps outgrow it.' : trend === 'down' ? 'keeps falling towards 0: ' + g.name + ' grows too fast, the steps cannot keep up.' : 'levels off (the second half varies by only ' + Math.round((spread - 1) * 100) + '%): steps ≈ ' + (Math.round(rs[rs.length - 1] * 100) / 100) + ' · ' + g.name + '.';
        F.add({ items: top(N, [{ id, name: g.name, cls: 's' + ci }]).concat(bottom(shown.slice(), id)), say: 'Try f(n) = ' + g.name + ': steps ÷ ' + g.name + ' goes ' + rs.filter((_, j) => j % Math.max(1, Math.floor(rs.length / 4)) === 0).map((x) => Math.round(x * 100) / 100).join(', ') + ' … and ' + words, meta: { cand: id } });
      });
      const ok = fit.id === fam.truth;
      F.add({ items: top(N, [{ id: fit.id, name: fit.name, cls: 's' + Math.max(0, CANDS.indexOf(fit.id)), solid: true }]).concat(bottom(shown, fit.id)), mark: 'O(' + fit.name + ')', say: 'The ratio that stays flattest is the one for ' + fit.name + ', with constant ' + (Math.round(fit.constant * 100) / 100) + ': the machine runs in time O(' + fit.name + ').' + (ok ? '' : ' But careful: the machine is really O(' + G[fam.truth].name + '). With points only up to n = ' + N + ' the shapes are too close to tell apart; measure further before you trust a fit.'), meta: { fit: fit.id } });
      return { frames: F.list, def: { sections: [
        { id: 'big', kind: 'text', title: 'Big-O', text: 't(n) = O(f(n)) when some constant c and some n₀ give t(n) ≤ c · f(n) for every n ≥ n₀. Read it from data: if t(n) / f(n) settles to a constant, t = Θ(f).' },
        { id: 'tab', kind: 'table', title: 'Steps ÷ f(n)', colHead: ['n', 'steps', '÷ n', '÷ n²'], rows: pts.filter((p, j) => j % Math.max(1, Math.floor(N / 6)) === 0 || j === N - 1).map((p) => [p.n, p.value, Math.round((p.value / p.n) * 100) / 100, Math.round((p.value / (p.n * p.n)) * 100) / 100]) },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.fit, pick: 'item', once: true,
        ask: 'All four ratio lines are drawn. Click the label of the one that levels off.',
        answer: (fr, i) => 'rt:sl:' + fr[i + 1].meta.fit, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.cand === 'n', pick: 'option', once: true, options: ['It keeps growing', 'It levels off', 'It falls to 0'],
        ask: 'We will divide the steps by n. As n grows, what will that ratio do?',
        answer: (fr, i) => (/keeps growing/.test(fr[i + 1].say) ? 'It keeps growing' : /falling/.test(fr[i + 1].say) ? 'It falls to 0' : 'It levels off'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Steps ÷ n² settles near 0.5 as n grows. What is the running time?', options: ['O(n)', 'Θ(n²)', 'O(0.5)', 'O(2ⁿ)'], answer: 1, why: 'A ratio that tends to a positive constant means the steps grow like n², up to that constant.' },
      { q: 'Steps ÷ n keeps growing without levelling. What does that tell you?', options: ['The steps grow faster than n', 'The steps grow slower than n', 'The machine loops', 'Nothing'], answer: 0, why: 'If t(n)/n → ∞ then t is not O(n): n is too small a shape.' },
      { q: 'Why can a fit over n ≤ 5 be wrong?', options: ['Small n is dominated by constant and lower-order terms', 'Machines run differently on short inputs', 'Big-O only applies to n > 1000', 'Because 5 is odd'], answer: 0, why: 'n² and n log n look alike for small n when constants are present; big-O is about the trend for large n.' },
      { q: 'If t(n) = 3n² + 40n + 7, then t(n) is', options: ['O(n)', 'O(n²)', 'O(n³) only', 'O(40n)'], answer: 1, why: 'The n² term dominates: for n ≥ 41, t(n) ≤ 4n². (It is also O(n³), but O(n²) is the tight answer.)' },
      { q: 'Is a machine with t(n) = 2n also O(n²)?', options: ['Yes: big-O is an upper bound', 'No: it is only O(n)', 'Only for even n', 'Only if it has two tapes'], answer: 0, why: 'O gives an upper bound, so anything O(n) is also O(n²); Θ is the tight statement.' },
    ],
  });

  // =========================================================================================================
  // 4. Two tapes against one
  // =========================================================================================================
  T.topic({
    id: 'cx-multitape', family: 'cx-time', order: 40, title: 'Two tapes against one',
    blurb: 'A two-tape machine checks palindromes in linear time; one tape needs about n² steps. Simulating any k-tape machine on one tape costs at most the square of its time, never more.',
    inputs: [{ id: 'w', kind: 'string', label: 'Input', def: 'abba', alphabet: 'ab', max: 8 }],
    presets: [
      { label: 'abba', values: { w: 'abba' } },
      { label: 'Not a palindrome: abb', values: { w: 'abb' } },
      { label: 'Longer: abaaba', values: { w: 'abaaba' } },
      { label: 'The empty input', values: { w: '' } },
    ],
    counters: [{ id: 't1', label: 'one-tape steps' }, { id: 't2', label: 'two-tape steps' }, { id: 'sim', label: 'simulation steps' }],
    run(inp) {
      const M1 = T.tmLib.get('palindrome'), M2 = T.tmLib.get('pal-2tape');
      const r1 = T.tm.run(M1, inp.w, { maxSteps: 5000 }), r2 = T.tm.run(M2, inp.w, { maxSteps: 5000 });
      const s1 = [r1.trace[0]].concat(r1.trace.filter((s) => s.kind === 'move')), s2 = [r2.trace[0]].concat(r2.trace.filter((s) => s.kind === 'move'));
      const F = new T.Frames(['t1', 't2', 'sim']);
      const CELLS = 10;
      const scA = K.tape.scroller({ cells: CELLS, origin: -1, margin: 1 }), scB = [K.tape.scroller({ cells: CELLS, origin: -1, margin: 1 }), K.tape.scroller({ cells: CELLS, origin: -1, margin: 1 })];
      const race = (t) => {
        const a = s1[Math.min(t, s1.length - 1)], b = s2[Math.min(t, s2.length - 1)];
        const ta = tapeOf(a);
        const oA = scA.at(ta.head);
        const doneA = t >= s1.length - 1, doneB = t >= s2.length - 1;
        const items = [{ key: 'h1', kind: 'text', x: 0, y: 0, text: 'one tape: ' + Math.min(t, s1.length - 1) + ' steps' + (doneA ? ', halted' : ''), cls: doneA ? 'good' : 'strong', size: 15 }];
        items.push(...K.tape.draw({ prefix: 'A', tape: ta.tape, offset: ta.offset, head: ta.head, state: a.state, cells: CELLS, origin: oA, prevOrigin: scA.prev, x: 60, y: 20, label: 'tape', headCls: doneA ? (r1.accepted ? 'good' : 'bad') : '' }).items);
        items.push({ key: 'h2', kind: 'text', x: 0, y: 160, text: 'two tapes: ' + Math.min(t, s2.length - 1) + ' steps' + (doneB ? ', halted' : ''), cls: doneB ? 'good' : 'strong', size: 15 });
        [0, 1].forEach((k) => {
          const tb = tapeOf(b, k);
          const o = scB[k].at(tb.head);
          items.push(...K.tape.draw({ prefix: 'B' + k, tape: tb.tape, offset: tb.offset, head: tb.head, state: k ? '2' : b.state, cells: CELLS, origin: o, prevOrigin: scB[k].prev, x: 60, y: 180 + k * 112, label: 'tape ' + (k + 1), headCls: k ? 'read' : doneB ? (r2.accepted ? 'good' : 'bad') : '' }).items);
        });
        return items;
      };
      const T1 = s1.length - 1, T2 = s2.length - 1, Tm = Math.max(T1, T2);
      const every = Math.max(1, Math.ceil(Tm / 16));
      F.add({ items: race(0), say: 'Both machines decide whether ' + showW(inp.w) + ' is a palindrome. The one-tape machine must shuttle back and forth; the two-tape machine copies the input once and then compares forwards against backwards.' });
      for (let t = every; t < Tm + every; t += every) {
        const tt = Math.min(t, Tm);
        F.set('t1', Math.min(tt, T1)).set('t2', Math.min(tt, T2));
        const justB = tt >= T2 && tt - every < T2, justA = tt >= T1 && tt - every < T1;
        F.add({ items: race(tt), say: 'Time ' + tt + '. ' + (justB ? 'The two-tape machine has halted after ' + T2 + ' steps (' + (r2.accepted ? 'accept' : 'reject') + '). ' : '') + (justA ? 'The one-tape machine halts after ' + T1 + ' steps (' + (r1.accepted ? 'accept' : 'reject') + ').' : tt < T1 ? 'The one-tape head is in ' + s1[tt].state + ', still walking.' : ''), meta: { race: true } });
        if (tt === Tm) break;
      }
      // the one-tape simulation of the two-tape machine
      const sim = T.tm.simulateKTape(M2, inp.w, { maxSteps: 400 });
      const trackItems = (snap, head, extra) => {
        const L = snap.from, cells = [];
        const n = snap.tracks[0].symbols.length;
        for (let i = 0; i < n; i++) cells.push(snap.tracks.flatMap((tr) => [tr.symbols[i] === '_' ? '⊔' : tr.symbols[i], tr.marks[i] ? '▲' : ' ']));
        const origin = Math.min(L - 1, head - 1);
        const items = K.tape.draw({ prefix: 'S', tape: cells, offset: L, tracks: 4, head, state: extra.state, cells: Math.max(8, n + 2), origin, x: 60, y: 60, label: 'one tape', headCls: extra.cls || '', cw: 46 }).items;
        items.push({ key: 'simT', kind: 'text', x: 0, y: 0, text: 'two tapes on one: 4 tracks', cls: 'strong', size: 15 });
        ['tape 1', 'head 1', 'tape 2', 'head 2'].forEach((l, k) => items.push({ key: 'trk' + k, kind: 'text', x: 60 + (Math.max(8, n + 2)) * 46 + 16, y: 60 + 4 + 30 * k + 20, text: l, size: 12, cls: 'tick' }));
        return items.filter((it) => it.key !== 'S:label' && it.key !== 'S:more-r');
      };
      let lastSnap = sim.trace[0];
      let shown = 0;
      for (const s of sim.trace) {
        if (s.tracks) lastSnap = s;
        if (s.kind === 'sim-start') { F.add({ items: trackItems(lastSnap, lastSnap.from, { state: s.state }), say: 'Now run the two-tape machine on one tape. ' + s.say + ' Tracks 1 and 3 hold the two tapes; the ▲ on tracks 2 and 4 mark where each head is.' }); continue; }
        if (shown > 9) continue;
        if (s.kind === 'decide') { F.set('sim', s.steps); F.add({ items: trackItems(lastSnap, lastSnap.from + lastSnap.tracks[0].symbols.length - 1, { state: s.state, cls: 'hot' }), say: 'A sweep to the right has collected what both marks sit on. ' + s.say }); shown++; continue; }
        if (s.kind === 'sim-step') { F.set('sim', s.steps); F.add({ items: trackItems(lastSnap, lastSnap.from, { state: s.state }), say: 'A sweep back to the left wrote both symbols and moved both marks. ' + s.say }); shown++; }
      }
      F.set('sim', sim.steps);
      F.add({ items: trackItems(lastSnap, lastSnap.from, { state: sim.state, cls: sim.verdict === 'accept' ? 'good' : 'bad' }), say: 'The simulation needed ' + sim.steps + ' one-tape steps for ' + sim.simulated + ' two-tape steps: every simulated step sweeps the whole used part of the tape, which can be as long as the time so far.', mark: 'simulated' });
      // the chart: three costs as n grows, on palindromes aⁿ
      const NS = [...Array(11).keys()];
      const c1 = NS.map((n) => [n, T.tm.run(M1, 'a'.repeat(n), { trace: false }).steps]), c2 = NS.map((n) => [n, T.tm.run(M2, 'a'.repeat(n), { trace: false }).steps]), c3 = NS.map((n) => [n, T.tm.simulateKTape(M2, 'a'.repeat(n), { trace: false }).steps]);
      const ymax = ticks(c3[c3.length - 1][1], 4);
      const chart = (k) => CX.plot({ prefix: 'pl', x: 60, y: 40, w: 420, h: 260, xs: [0, 10], ys: [0, ymax[ymax.length - 1]], yTicks: ymax, xTicks: [0, 2, 4, 6, 8, 10], xLabel: 'n (input aⁿ)', yLabel: 'steps',
        series: [{ id: 'two', label: 'two tapes', cls: 's1', pts: c2 }, { id: 'one', label: 'one tape', cls: 's0', pts: k > 0 ? c1 : [] }, { id: 'sim', label: 'simulated', cls: 's4', pts: k > 1 ? c3 : [] }] }).items;
      F.add({ items: chart(0), say: 'On aⁿ, the two-tape machine takes ' + c2.map((p) => p[1]).slice(0, 4).join(', ') + ' … steps: 3n + 3, a straight line.', meta: { chart: 0 } });
      F.add({ items: chart(1), say: 'The one-tape palindrome machine takes ' + c1.map((p) => p[1]).slice(0, 5).join(', ') + ' … steps: about n²/2. Some languages really are slower on one tape: for palindromes, n² is the best one tape can do.', meta: { chart: 1 } });
      F.add({ items: chart(2), say: 'The general simulation of the two-tape machine costs ' + c3[10][1] + ' steps at n = 10: bigger constants, but still O(t(n)²). Any k-tape machine running in time t(n) has a one-tape twin running in O(t(n)²): polynomial stays polynomial.', mark: 'O(t²)' });
      return { frames: F.list, def: { sections: [
        { id: 'thm', kind: 'text', title: 'The simulation', text: 'Put the k tapes on 2k tracks of one tape, marking each head. For each step: sweep right to read the marked symbols, then sweep left to write and move the marks. After t steps the used tape is O(t) long, so each step costs O(t), and t steps cost O(t²).' },
        { id: 'tab', kind: 'table', title: 'Steps on aⁿ', colHead: ['n', 'two tapes', 'one tape', 'simulated'], rows: NS.filter((n) => n % 2 === 0).map((n) => [n, c2[n][1], c1[n][1], c3[n][1]]) },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0, pick: 'option', options: ['The one-tape machine', 'The two-tape machine', 'They tie'], ask: 'Which machine will halt first?', answer: (fr, i, inp) => { const a = T.tm.run(T.tmLib.get('palindrome'), inp.w, { trace: false }).steps, b = T.tm.run(T.tmLib.get('pal-2tape'), inp.w, { trace: false }).steps; return a < b ? 'The one-tape machine' : a > b ? 'The two-tape machine' : 'They tie'; }, explain: 'Copying once and comparing in one pass beats shuttling back and forth, once the input is longer than a few symbols.' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.chart === 2, pick: 'option', options: ['Linear, like the two-tape machine', 'About quadratic', 'Exponential'], ask: 'How will the one-tape simulation\'s cost grow with n?', answer: () => 'About quadratic', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A 3-tape machine runs in time n². A one-tape simulation of it runs in', options: ['O(n²)', 'O(n⁴)', 'O(2ⁿ)', 'O(3n²)'], answer: 1, why: 'The simulation squares the time: O((n²)²) = O(n⁴), still polynomial.' },
      { q: 'Why does each simulated step cost O(t) single-tape moves?', options: ['The head sweeps across the used part of the tape, which is at most O(t) long', 'Each tape needs its own state', 'Because of the blank symbol', 'It does not: it costs O(1)'], answer: 0, why: 'In t steps no head gets more than t cells away, so the tracks span O(t) cells and one sweep costs O(t).' },
      { q: 'Does the class P change if we allow multi-tape machines?', options: ['Yes, it gets bigger', 'No: polynomial time on k tapes is polynomial on one', 'Yes, it gets smaller', 'Only for palindromes'], answer: 1, why: 'Squaring a polynomial gives a polynomial, so P is the same for every reasonable deterministic model.' },
      { q: 'For palindromes, the two-tape machine takes about 3n steps and the one-tape about n²/2. Is the gap real or an artefact of a clumsy machine?', options: ['Real: every one-tape machine for palindromes needs on the order of n² steps', 'An artefact: a cleverer one-tape machine runs in O(n)', 'Neither machine is correct', 'They are the same up to constants'], answer: 0, why: 'A crossing-sequence argument shows one-tape machines need Ω(n²) for palindromes: the simulation\'s square is sometimes necessary.' },
    ],
  });

  // =========================================================================================================
  // 5. Encodings: why unary is cheating
  // =========================================================================================================
  const divisors = (N) => { const tried = []; if (N < 2) return { tried, prime: false, found: null }; for (let d = 2; d * d <= N; d++) { tried.push(d); if (N % d === 0) return { tried, prime: false, found: d }; } return { tried, prime: true, found: null }; };
  T.topic({
    id: 'cx-encoding', family: 'cx-time', order: 50, title: 'Encodings: why unary is cheating',
    blurb: 'Trial division tests whether N is prime with about √N divisions. Is that fast? It depends on how N is written: in unary the input is N symbols long, in binary only about log₂ N.',
    inputs: [{ id: 'N', kind: 'number', label: 'N', def: 91, min: 1, max: 99999 }],
    presets: [
      { label: '91 = 7 · 13', values: { N: 91 } },
      { label: 'A prime: 97', values: { N: 97 } },
      { label: 'Even: 4096 (found at once)', values: { N: 4096 } },
      { label: 'The smallest prime, 2', values: { N: 2 } },
      { label: '1, which is not prime', values: { N: 1 } },
      { label: 'A big prime: 65521', values: { N: 65521 } },
    ],
    counters: [{ id: 'div', label: 'divisions' }, { id: 'unary', label: 'unary length' }, { id: 'binary', label: 'binary length' }],
    run(inp) {
      const N = inp.N;
      const D = divisors(N);
      const bin = N.toString(2), u = N;
      const F = new T.Frames(['div', 'unary', 'binary']);
      F.set('unary', u).set('binary', bin.length);
      const enc = (hot) => {
        const items = [];
        // unary: N ones, the middle elided when there are many
        const showU = Math.min(N, 14);
        const ucells = N <= 14 ? '1'.repeat(N).split('') : '1111111'.split('').concat(['⋯']).concat('111111'.split(''));
        items.push({ key: 'ul', kind: 'text', x: 0, y: 26, text: 'unary', cls: 'title' + (hot === 'u' ? '' : ''), anchor: 'start' });
        ucells.forEach((c, i) => items.push({ key: 'u' + i, kind: 'cell', x: 90 + i * 30, y: 6, w: 30, h: 34, text: c, cls: 'mono' + (c === '⋯' ? ' elide' : '') + (hot === 'u' ? ' act' : ''), rx: 3, pick: true }));
        items.push({ key: 'un', kind: 'text', x: 90 + ucells.length * 30 + 12, y: 28, text: CX.num(N) + ' symbol' + (N === 1 ? '' : 's'), cls: 'strong', anchor: 'start' });
        items.push({ key: 'bl', kind: 'text', x: 0, y: 86, text: 'binary', cls: 'title', anchor: 'start' });
        bin.split('').forEach((c, i) => items.push({ key: 'b' + i, kind: 'cell', x: 90 + i * 30, y: 66, w: 30, h: 34, text: c, cls: 'mono' + (hot === 'b' ? ' act' : ''), rx: 3, pick: true }));
        items.push({ key: 'bn', kind: 'text', x: 90 + bin.length * 30 + 12, y: 88, text: bin.length + ' symbols', cls: 'strong', anchor: 'start' });
        void showU;
        return items;
      };
      // trial division: the candidates so far, as a strip of cells
      const strip = (k, opts) => {
        opts = opts || {};
        const items = [{ key: 'tl', kind: 'text', x: 0, y: 156, text: 'try d = 2, 3, … up to √' + N + (N >= 2 ? ' ≈ ' + Math.floor(Math.sqrt(N)) : ''), cls: 'title', anchor: 'start' }];
        const ds = D.tried.slice(0, k);
        const showN = 12;
        const cut = ds.length > showN;
        const vis = cut ? ds.slice(0, 4).concat(['⋯']).concat(ds.slice(ds.length - 7)) : ds;
        vis.forEach((d, i) => {
          const isF = d === D.found;
          items.push({ key: 'd' + (d === '⋯' ? 'el' : d), kind: 'cell', x: i * 50, y: 172, w: 46, h: 40, text: String(d), cls: 'mono' + (d === '⋯' ? ' elide' : isF ? ' bad' : opts.hot && d === ds[ds.length - 1] ? ' hot' : ' read'), rx: 6, sub: d === '⋯' ? '' : isF ? 'divides' : 'no' });
        });
        return items;
      };
      // the same work, √N divisions, drawn twice: against the unary length m = N and against the binary length b
      const bN = bin.length, mMax = Math.max(4096, N), bMax = Math.max(12, bN), wMax = Math.ceil(Math.sqrt(mMax));
      const yt = ticks(wMax, 3);
      const chart = (k) => {
        const bs = [...Array(bMax + 1).keys()].filter((b) => b >= 1);
        const left = CX.plot({ prefix: 'pu', x: 50, y: 312, w: 230, h: 170, xs: [0, mMax], ys: [0, yt[yt.length - 1]], yTicks: yt, xTicks: ticks(mMax, 2).filter((v) => v <= mMax), xLabel: 'unary length m', yLabel: 'divisions',
          series: [{ id: 'w', label: '√m', cls: 's1', dots: false, pts: Array.from({ length: 41 }, (_, j) => (j / 40) * mMax).map((m) => [m, Math.sqrt(m)]) }, { id: 'me', label: 'N = ' + N, cls: 's3', hot: true, pts: [[N, Math.sqrt(N)]] }] });
        const right = CX.plot({ prefix: 'pb', x: 420, y: 312, w: 230, h: 170, xs: [0, bMax], ys: [0, yt[yt.length - 1]], yTicks: yt, xTicks: ticks(bMax, 3).filter((v) => v <= bMax), xLabel: 'binary length b', yLabel: 'divisions',
          series: k > 0 ? [{ id: 'w', label: '2^(b/2)', cls: 's4', pts: bs.map((b) => [b, Math.pow(2, b / 2)]) }, { id: 'me', label: 'N = ' + N, cls: 's3', hot: true, pts: [[bN, Math.sqrt(N)]] }] : [] });
        const items = left.items.concat(right.items);
        items.push({ key: 'cmpU', kind: 'text', x: 50, y: 266, text: 'gentle: polynomial in m', cls: 'good', anchor: 'start', size: 15 });
        if (k > 0) items.push({ key: 'cmpB', kind: 'text', x: 420, y: 266, text: 'steep: exponential in b', cls: 'bad', anchor: 'start', size: 15 });
        return items;
      };
      F.add({ items: enc().concat(strip(0)), say: 'N = ' + N + ' can be written in unary as ' + CX.num(N) + ' ones, or in binary as ' + bin + ', just ' + bin.length + ' symbols. The same number, two inputs of very different lengths.' });
      if (N < 2) {
        F.add({ items: enc().concat(strip(0)), say: (N === 1 ? '1 has no divisor to try and is not prime by definition: a prime has exactly two divisors.' : '') + ' Trial division does no work at all here; the interesting cases are big N.', mark: 'not prime' });
      } else {
        const ks = D.tried.length;
        const show = ks <= 12 ? [...Array(ks).keys()].map((i) => i + 1) : [1, 2, 3, Math.floor(ks / 2), ks - 1, ks];
        if (!ks) F.add({ items: enc().concat(strip(0)), say: 'For N = ' + N + ' there is no d with d² ≤ N, so there is nothing to try: ' + N + ' is prime.', mark: 'prime' });
        for (const k of show) {
          F.set('div', k);
          const d = D.tried[k - 1];
          F.add({ items: enc().concat(strip(k, { hot: true })), say: 'Try d = ' + d + ': ' + N + ' ÷ ' + d + (N % d === 0 ? ' = ' + N / d + ' exactly, so ' + N + ' is not prime.' : ' leaves remainder ' + (N % d) + '.'), mark: N % d === 0 ? 'not prime' : undefined, meta: { k } });
        }
        if (D.prime && ks) F.add({ items: enc().concat(strip(ks)), say: 'No d up to √' + N + ' divides it, so ' + N + ' is prime, after ' + ks + ' division' + (ks === 1 ? '' : 's') + '.', mark: 'prime' });
      }
      const w = Math.ceil(Math.sqrt(Math.max(N, 1)));
      F.add({ items: enc('u').concat(strip(D.tried.length), chart(0)), say: 'About √N = ' + w + ' divisions. Measured against the unary input of length m = ' + CX.num(N) + ', that is √m: less than linear. Unary makes trial division look fast.', meta: { enc: 1 } });
      F.add({ items: enc('b').concat(strip(D.tried.length), chart(1)), say: 'But measured against the binary input of length b = ' + bin.length + ', √N = 2^(b/2): each extra bit multiplies the work by √2. Exponential. Unary pads the input so much that slow algorithms look fast; reasonable encodings (binary, decimal) are within a polynomial of each other.', mark: 'encodings' });
      return { frames: F.list, def: { sections: [
        { id: 'len', kind: 'math', title: 'The same number, two lengths', text: 'N = ' + N + '\nunary: ' + CX.num(N) + ' symbols\nbinary: ' + bin + ' (' + bin.length + ' symbols)\ndecimal: ' + String(N).length + ' digits' },
        { id: 'rule', kind: 'text', title: 'Reasonable encodings', text: 'Time is measured in the length of the input. Numbers must be written in a base of at least 2; then binary, decimal and hex lengths differ only by constant factors, and polynomial time means the same thing for all of them.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.enc === 1, pick: 'option', options: ['About +1 division', 'About ×1.4 (√2)', 'About ×2', 'It stays the same'], ask: 'If N gets one more binary digit (N doubles), how does the number of divisions change?', answer: () => 'About ×1.4 (√2)', explain: 'Divisions ≈ √N, and √(2N) = √2 · √N: one more bit multiplies the work by √2, so b bits cost about 2^(b/2).' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].mark === 'encodings', pick: 'item', ask: 'Click the encoding in which trial division counts as polynomial time.', answer: () => ['ul', 'u0', 'u1', 'u2', 'u3', 'u4'], explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'An algorithm takes N steps on a number N written in binary. Its running time in the input length b is', options: ['O(b)', 'O(b²)', 'About 2ᵇ: exponential', 'O(log b)'], answer: 2, why: 'N ≈ 2ᵇ, so N steps is exponential in the length b of the input.' },
      { q: 'The same algorithm with N written in unary runs in', options: ['Linear time in the input length', 'Exponential time', 'Logarithmic time', 'It cannot run on unary'], answer: 0, why: 'The unary input has length N, so N steps is linear in it: the encoding hides the cost.' },
      { q: 'Why do binary and decimal encodings give the same notion of polynomial time?', options: ['Their lengths differ by a constant factor (log₂ 10 ≈ 3.3)', 'They are the same string', 'Decimal is always shorter', 'Because computers use binary'], answer: 0, why: 'A polynomial in 3.3·d is still a polynomial in d.' },
      { q: 'Subset sum with numbers in unary can be solved in polynomial time. Does that put subset sum in P?', options: ['Yes', 'No: with numbers in binary it is NP-complete, and the unary version is a different, padded problem', 'Only for small sums', 'Yes, because unary is reasonable'], answer: 1, why: 'The dynamic programme takes time polynomial in the target value, which is exponential in its binary length.' },
    ],
  });
})();
