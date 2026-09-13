// Cook–Levin, acted out: a small nondeterministic machine's accepting run written as a tableau row by row,
// the 2 × 3 windows that check every step, the clause groups of the formula counted as t grows, and the
// two directions of the proof: an accepting tableau gives a satisfying assignment, and a satisfying
// assignment read back is an accepting tableau (none at all when no branch accepts).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'cx-cook', part: 'complexity', order: 60, title: 'Cook–Levin', blurb: 'Why SAT is NP-complete: any polynomial-time nondeterministic computation can be written as a table of symbols, and checking that table is a formula.' });

  // Our own small machines. GUESS guesses a bit, writes it over the first cell and accepts when the second
  // cell holds the same bit. TWICE guesses where a letter occurs and then looks for that letter again.
  const GUESS = 'start: g\naccept: yes\ng, 0 -> c0, 0, R\ng, 0 -> c1, 1, R\ng, 1 -> c0, 0, R\ng, 1 -> c1, 1, R\nc0, 0 -> yes, 0, S\nc1, 1 -> yes, 1, S';
  const TWICE = 'start: s\naccept: yes\ns, a -> s, a, R\ns, b -> s, b, R\ns, a -> fa, a, R\ns, b -> fb, b, R\nfa, b -> fa, b, R\nfa, a -> yes, a, S\nfb, a -> fb, a, R\nfb, b -> yes, b, S';
  const SEP = '\u0001';

  /** The machine text (diagram form, as the editor keeps it) as a T.tm machine; nondeterminism is kept */
  function ntmOf(text) {
    const m = T.Machine.parse(text);
    if (m.kind !== 'tm') throw new Error('Machine: a Turing machine, with rules like g, 0 -> c1, 1, R');
    const bl = (s) => (s === '⊔' || s === '_' ? '_' : s);
    const rules = m.trans.map((t) => { const l = T.Machine.tmLabel(t.label); return { from: t.from, read: [bl(l.read)], to: t.to, write: [bl(l.write)], move: [l.move] }; });
    const input = [...new Set(rules.flatMap((r) => [r.read[0], r.write[0]]))].filter((s) => s !== '_');
    const M = T.tm.fromRules({ start: m.start, accept: m.accept, reject: [], halt: [], input, name: 'N' }, rules);
    return { M, m, rules };
  }
  const isAcc = (M, row) => row.some((x) => x.startsWith('q:') && T.tm.isAccept(M, x.slice(2)));
  const dsym = (s) => (s === '_' ? '⊔' : s.startsWith('q:') ? s.slice(2) : s);
  const rowText = (row) => row.map(dsym).join(' ');
  const statePos = (row) => row.findIndex((x) => x.startsWith('q:'));

  /** Friendly limits shared by the topics: small machines, short inputs, a handful of steps */
  function checkAll(inp, opts) {
    let N;
    try { N = ntmOf(inp.m); } catch (e) { return e.message.startsWith('Machine') ? e.message : 'Machine: ' + e.message; }
    const { M } = N;
    if (M.states.length > 5) return 'Machine: at most 5 states, so the tableau stays readable';
    const long = M.states.find((q) => q.length > 4);
    if (long) return 'Machine: state names of at most 4 letters (' + long + ' is longer), so they fit in a tableau cell';
    if (!M.accept.length) return 'Machine: say which state accepts, with a line like accept: yes';
    if (M.gamma.length > 4) return 'Machine: at most 3 tape symbols besides the blank';
    const bad = [...(inp.w || '')].find((c) => !M.input.includes(c));
    if (bad !== undefined) return 'Input: "' + bad + '" is not a symbol the machine reads (' + M.input.join(', ') + ')';
    if (opts && opts.windows) {
      const C = Math.max([...inp.w].length, inp.t + 1);
      if (Math.pow(M.gamma.length, C) * C * M.states.length > 120000) return 'Too many possible rows to list every legal window: use a smaller t or fewer symbols';
    }
    if (opts && opts.accepts) {
      const r = T.cook.acceptingRun(M, inp.w, inp.t);
      if (!r.accepts) return 'The machine does not accept ' + (inp.w || 'ε') + ' within t = ' + inp.t + ' steps, so there is no accepting tableau to look at: try a larger t';
    }
    return null;
  }

  /**
   * A tableau: rows (null for a row not written yet, drawn as dashed empty cells), cells cw × ch.
   * o: {x, y, prefix, cw, ch, cls(i, j, s), fly: {i: [{x, y}]}, colNums, qrows: [rows of ?], badCells: Set 'i,j'}
   */
  function drawTab(M, rows, o) {
    o = o || {};
    const P = o.prefix || 'tab', CW = o.cw || 46, CH = o.ch || 40, x0 = o.x || 0, y0 = o.y || 0;
    const W = Math.max(...rows.filter(Boolean).map((r) => r.length), o.width || 0);
    const items = [];
    rows.forEach((row, i) => {
      items.push({ key: P + ':r:' + i, kind: 'text', x: x0 - 12, y: y0 + i * CH + CH / 2 + 5, text: 'time ' + i, anchor: 'end', size: 13, cls: 'tick' });
      for (let j = 0; j < W; j++) {
        const x = x0 + j * CW, y = y0 + i * CH;
        if (!row) {
          const q = o.qrows && o.qrows.includes(i);
          items.push({ key: P + ':e:' + i + ':' + j, kind: 'cell', x, y, w: CW, h: CH, rx: 0, text: q ? '?' : '', cls: 'gone' + (q && o.qbad ? ' bad' : '') });
          continue;
        }
        const s = row[j];
        const base = s === '#' ? 'mark' : s.startsWith('q:') ? (T.tm.isAccept(M, s.slice(2)) ? 'good' : 'act') : s === '_' ? 'blank' : '';
        const it = { key: P + ':c:' + i + ':' + j, kind: 'cell', x, y, w: CW, h: CH, rx: 0, text: dsym(s), cls: ['mono', base, o.badCells && o.badCells.has(i + ',' + j) ? 'bad' : '', o.cls ? o.cls(i, j, s) || '' : ''].filter(Boolean).join(' '), pick: true };
        if (o.fly && o.fly[i]) { it.enter = 'fly'; it.from = o.fly[i][j]; }
        items.push(it);
      }
    });
    if (o.colNums) for (let j = 0; j < W; j++) items.push({ key: P + ':n:' + j, kind: 'text', x: x0 + j * CW + CW / 2, y: y0 - 9, text: String(j), anchor: 'middle', size: 12, cls: 'tick' });
    return { items, box: { x: x0 - 70, y: y0 - 24, w: W * CW + 70, h: rows.length * CH + 24 }, cellAt: (i, j) => ({ x: x0 + j * CW, y: y0 + i * CH }), CW, CH, W };
  }
  const ruleText = (r) => 'write ' + dsym(r.write[0]) + ', move ' + r.move[0] + ', enter ' + r.to;
  const ruleSays = (r) => 'writes ' + dsym(r.write[0]) + ', moves ' + r.move[0] + ' and enters ' + r.to;
  const rulesTable = (rules) => ({ id: 'rules', kind: 'table', title: 'The machine N', colHead: ['state', 'read', 'next', 'write', 'move'], rows: rules.map((r) => [r.from, dsym(r.read[0]), r.to, dsym(r.write[0]), r.move[0]]) });
  const ruleIx = (rules, r) => rules.findIndex((x) => x.from === r.from && x.read[0] === r.read[0] && x.to === r.to && x.write[0] === r.write[0] && x.move[0] === r.move[0]);

  const baseInputs = (def) => [
    { id: 'm', kind: 'machine', machine: 'tm', label: 'Nondeterministic machine N', def: def.m },
    { id: 'w', kind: 'string', label: 'Input w', def: def.w, max: 4 },
    { id: 't', kind: 'number', label: 'Time bound t', def: def.t, min: 1, max: def.tmax || 4 },
  ];

  // ---------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cx-cook-tableau', family: 'cx-cook', order: 10, title: 'A computation becomes a tableau',
    blurb: 'Write each configuration of a nondeterministic run as a row # u q v #, one row per time step. Where the machine has a choice, the tableau records the guess the accepting branch makes.',
    inputs: baseInputs({ m: GUESS, w: '01', t: 3 }),
    presets: [
      { label: 'Guess a bit: 01', values: { m: GUESS, w: '01', t: 3 } },
      { label: 'A letter twice: aba', values: { m: TWICE, w: 'aba', t: 3 } },
      { label: 'Accepts early: rows repeat', values: { m: GUESS, w: '11', t: 4 } },
      { label: 'No accepting branch: 0', values: { m: GUESS, w: '0', t: 3 } },
      { label: 'Time bound too short', values: { m: TWICE, w: 'aba', t: 2 } },
    ],
    check: (inp) => checkAll(inp),
    counters: [{ id: 'time', label: 'rows written' }, { id: 'choices', label: 'moves to choose from' }, { id: 'dead', label: 'branches that die' }],
    run(inp) {
      const { M, rules } = ntmOf(inp.m);
      const t = inp.t, S = T.cook.setup(M, inp.w, t), R = t + 1;
      const succ = (row) => T.cook.successors(M, S, row);
      const memo = new Map();
      const canAcc = (row, k) => {
        if (isAcc(M, row)) return true;
        if (k <= 0) return false;
        const key = row.join(SEP) + '|' + k;
        if (!memo.has(key)) memo.set(key, succ(row).some((s) => canAcc(s.row, k - 1)));
        return memo.get(key);
      };
      const life = (row, k) => { if (k <= 0 || isAcc(M, row)) return 0; const ss = succ(row); return ss.length ? 1 + Math.max(...ss.map((s) => life(s.row, k - 1))) : 0; };
      const willAccept = canAcc(S.start, t);
      const rows = new Array(R).fill(null);
      const CW = 46, CH = 40;
      const candY = R * CH + 44;
      const F = new T.Frames(['time', 'choices', 'dead']);
      const scene = (extra, o) => drawTab(M, rows, Object.assign({ colNums: true }, o || {})).items.concat(extra || []);
      const candItems = (i, ss, mark) => {
        const out = [];
        ss.forEach((s, k) => {
          const y = candY + k * (CH + 14);
          const st = mark ? (mark[k] ? 'good' : 'bad') : '';
          s.row.forEach((sym, j) => out.push({ key: 'cd:' + i + ':' + k + ':' + j, kind: 'cell', x: j * CW, y, w: CW, h: CH, rx: 0, text: dsym(sym), cls: ['mono', sym === '#' ? 'mark' : sym.startsWith('q:') ? 'act' : sym === '_' ? 'blank' : '', st].filter(Boolean).join(' '), pick: true }));
          out.push({ key: 'cdl:' + i + ':' + k, kind: 'text', x: s.row.length * CW + 14, y: y + CH / 2 + 5, text: (k + 1) + '. ' + (s.rule ? ruleText(s.rule) : 'stay halted'), size: 14, cls: mark ? (mark[k] ? 'good' : 'bad') : 'strong' });
        });
        out.push({ key: 'cdh:' + i, kind: 'text', x: 0, y: candY - 14, text: 'possible rows for time ' + (i + 1), cls: 'title' });
        return out;
      };
      F.add({ items: scene(), say: 'N gets ' + (inp.w || 'ε') + ' and a time bound of t = ' + t + ' steps, so the tableau has t + 1 = ' + R + ' rows. Each row has ' + S.W + ' columns: # at both ends and ' + S.C + ' tape cells, as far as the head can get in ' + t + ' steps.', meta: { R } });
      rows[0] = S.start;
      F.count('time');
      F.add({ items: scene([], { fly: {} }), say: 'Row 0 is the start configuration ' + rowText(S.start) + ': the state ' + M.start + ' is written just left of the cell the head reads, and the rest of the tape is blank ⊔.' });
      let cur = S.start, accepted = isAcc(M, cur);
      for (let i = 0; i < t; i++) {
        if (isAcc(M, cur)) {
          for (let k = i + 1; k < R; k++) rows[k] = cur;
          F.set('time', R);
          F.add({ items: scene(), say: 'N is in its accepting state at time ' + i + '. A tableau always has t + 1 rows, so rows ' + (i + 1) + (R - 1 > i + 1 ? ' to ' + (R - 1) : '') + ' simply repeat it: a halted machine stays as it is.' });
          accepted = true;
          break;
        }
        const p = statePos(cur), q = cur[p].slice(2), a = cur[p + 1];
        const ss = succ(cur);
        const hl = { rules: ss.map((s) => String(ruleIx(rules, s.rule))) };
        if (!ss.length) {
          F.count('dead');
          F.add({ items: scene(), say: 'In ' + q + ' reading ' + dsym(a) + ' N has no move: this branch halts without accepting at time ' + i + ', and no computation can fill rows ' + (i + 1) + ' to ' + t + '.', hl });
          break;
        }
        F.count('choices', ss.length);
        const good = ss.map((s) => canAcc(s.row, t - i - 1));
        let idx = good.indexOf(true);
        if (idx < 0) { const ls = ss.map((s) => life(s.row, t - i - 1)); idx = ls.indexOf(Math.max(...ls)); }
        if (ss.length > 1) {
          const ng = good.filter(Boolean).length;
          F.add({ items: scene(candItems(i, ss)), say: 'In ' + q + ' reading ' + dsym(a) + ' N has ' + ss.length + ' moves, so row ' + (i + 1) + ' could be any of these ' + ss.length + ' rows. The tableau must commit to one of them: this is the guess.', hl, meta: ng === 1 ? { choose: ss[idx].row.map((_, j) => 'cd:' + i + ':' + idx + ':' + j) } : {} });
          F.count('dead', good.filter((g) => !g).length);
          F.add({ items: scene(candItems(i, ss, good)), say: ng ? (ng === 1 ? 'Only move ' + (idx + 1) + ' can still reach an accepting state within the ' + (t - i - 1) + ' step' + (t - i - 1 === 1 ? '' : 's') + ' left; the other branch' + (ss.length > 2 ? 'es die' : ' dies') + ' or runs out of time.' : ng + ' moves can still lead to acceptance; the tableau may follow any of them, and takes move ' + (idx + 1) + '.') : 'None of these moves can reach an accepting state within the ' + (t - i - 1) + ' step' + (t - i - 1 === 1 ? '' : 's') + ' left. We follow the branch that lives longest, move ' + (idx + 1) + ', to see where it ends.', hl });
        }
        const from = ss[idx].row.map((_, j) => ({ x: j * CW, y: candY + idx * (CH + 14) }));
        rows[i + 1] = ss[idx].row;
        F.count('time');
        F.add({ items: scene([], { fly: { [i + 1]: from } }), say: 'Row ' + (i + 1) + ' is ' + rowText(ss[idx].row) + ': ' + (ss[idx].rule ? 'N ' + ruleSays(ss[idx].rule) + (ss[idx].rule.move[0] === 'R' ? ', so the state symbol moves one place right.' : ss[idx].rule.move[0] === 'L' ? ', so the state symbol moves one place left.' : ', and the head stays put.') : 'it repeats.'), hl });
        cur = rows[i + 1];
        if (i === t - 1 && isAcc(M, cur)) accepted = true;
      }
      if (rows.every(Boolean) && (accepted || isAcc(M, cur))) F.add({ items: scene([], { cls: (i, j, s) => (s.startsWith('q:') && T.tm.isAccept(M, s.slice(2)) ? 'good' : '') }), say: 'Every row is written and an accepting state appears: this ' + R + ' × ' + S.W + ' table is an accepting tableau, a certificate that N accepts ' + (inp.w || 'ε') + ' within ' + t + ' steps.', mark: 'accepting tableau' });
      else F.add({ items: scene([], { qrows: rows.map((r, i) => (r ? -1 : i)).filter((i) => i >= 0), qbad: true }), say: willAccept ? 'Stopped.' : 'No branch of N accepts ' + (inp.w || 'ε') + ' within ' + t + ' steps' + (canAcc(S.start, t + 4) ? ' (it would, given a few more steps)' : '') + ', so no accepting tableau of this size exists. Cook–Levin turns exactly this into an unsatisfiable formula.', mark: 'no tableau' });
      return { frames: F.list, def: { sections: [
        rulesTable(rules),
        { id: 'shape', kind: 'math', title: 'The tableau', text: 'rows: t + 1 = ' + R + '\ncolumns: C + 3 = ' + S.W + ', where C = max(|w|, t + 1) = ' + S.C + '\nrow i: # u q v #, the configuration at time i\nq is written just left of the head\'s cell' },
      ] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', ask: 'How many rows will the tableau have?', options: (fr) => { const R = fr[0].meta.R; return [String(R - 1), String(R), String(2 * R)]; }, answer: (fr) => String(fr[0].meta.R), explain: 'One row for each moment from time 0 to time t: t + 1 rows.' },
      { at: (f) => f.meta && f.meta.choose, once: true, pick: 'item', ask: 'Only one of these rows can still lead to acceptance in time. Click the row the accepting branch takes.', answer: (fr, i) => fr[i].meta.choose, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does one row of the tableau hold?', options: ['One step\'s rule', 'One whole configuration: tape, state and head position', 'One tape cell over time', 'The input only'], answer: 1, why: 'Row i is the configuration at time i, written # u q v #: the tape with the state symbol placed just left of the head\'s cell.' },
      { q: 'Why does a tableau for a time bound t need only about t + 1 tape cells?', options: ['The machine never writes', 'In t steps the head can visit at most t + 1 cells', 'The input is short', 'Blanks are not stored'], answer: 1, why: 'Each step moves the head at most one cell, so after t steps it cannot be further than t cells from where it started.' },
      { q: 'The machine has two moves at some step. What does the tableau do?', options: ['Writes both rows', 'Commits to one of them, the one its branch takes', 'Leaves the row empty', 'Stops'], answer: 1, why: 'A tableau is one branch of the computation. The nondeterministic guesses are exactly what a satisfying assignment will have to choose.' },
      { q: 'The machine accepts at time 2 but t = 4. What are rows 3 and 4?', options: ['Empty', 'Copies of row 2', 'Anything at all', 'The start row again'], answer: 1, why: 'A halted machine stays as it is, so the accepting row repeats until the table has t + 1 rows.' },
      { q: 'No branch accepts w within t steps. What follows?', options: ['There is still an accepting tableau', 'No accepting tableau exists, so the Cook–Levin formula is unsatisfiable', 'The machine is deterministic', 'The tableau is wider'], answer: 1, why: 'Accepting tableaux and accepting branches within t steps are the same thing; with none, the formula has no satisfying assignment.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // The windows: legal ones are read off every pair (row, next row) of this width, as the core does.
  const FAULTS = [
    { value: 'none', label: 'none: an honest tableau' },
    { value: 'far', label: 'a symbol changes far from the head' },
    { value: 'jump', label: 'the head jumps two cells' },
    { value: 'two', label: 'a second state appears' },
  ];
  /** Change one row of an honest tableau; returns {rows, cells: ['i,j'], say} */
  function corrupt(M, rows, fault) {
    const out = rows.map((r) => r.slice());
    if (fault === 'none') return { rows: out, cells: [] };
    const syms = M.gamma;
    if (fault === 'far') {
      const i = out.length - 1, p = statePos(out[i]), pp = statePos(out[i - 1]);
      let j = -1;
      for (let k = out[i].length - 2; k >= 1; k--) if (Math.abs(k - p) > 2 && Math.abs(k - pp) > 2 && !out[i][k].startsWith('q:')) { j = k; break; }
      if (j < 0) for (let k = out[i].length - 2; k >= 1; k--) if (Math.abs(k - p) > 1 && !out[i][k].startsWith('q:')) { j = k; break; }
      const old = out[i][j];
      out[i][j] = syms.find((s) => s !== old && s !== '_') || syms.find((s) => s !== old);
      return { rows: out, cells: [i + ',' + j], say: 'cell ' + j + ' of row ' + i + ' was changed from ' + dsym(old) + ' to ' + dsym(out[i][j]) };
    }
    const i = 1, p = statePos(out[i]);
    if (fault === 'jump') {
      const to = Math.min(p + 2, out[i].length - 2);
      const s = out[i][p];
      out[i].splice(p, 1); out[i].splice(to, 0, s);
      return { rows: out, cells: [i + ',' + to], say: 'the state in row ' + i + ' was moved from column ' + p + ' to column ' + to };
    }
    let j = -1;
    for (let k = out[i].length - 2; k >= 1; k--) if (Math.abs(k - p) > 2) { j = k; break; }
    if (j < 0) j = p > 2 ? 1 : out[i].length - 2;
    const old = out[i][j];
    out[i][j] = 'q:' + M.start;
    return { rows: out, cells: [i + ',' + j], say: 'a second state ' + M.start + ' was written into column ' + j + ' of row ' + i + ' over ' + dsym(old) };
  }

  T.topic({
    id: 'cx-cook-windows', family: 'cx-cook', order: 20, title: 'Checking the tableau window by window',
    blurb: 'A 2 × 3 window slides over the tableau. Each window must be one that some move of the machine can produce. If every window is legal, every row follows from the one above.',
    inputs: baseInputs({ m: GUESS, w: '01', t: 3, tmax: 3 }).concat([{ id: 'fault', kind: 'choice', label: 'Tamper with the tableau', def: 'none', options: FAULTS }]),
    presets: [
      { label: 'An honest tableau', values: { m: GUESS, w: '01', t: 3, fault: 'none' } },
      { label: 'A symbol changes far from the head', values: { m: GUESS, w: '01', t: 3, fault: 'far' } },
      { label: 'The head jumps', values: { m: TWICE, w: 'aba', t: 3, fault: 'jump' } },
      { label: 'Two heads at once', values: { m: GUESS, w: '11', t: 2, fault: 'two' } },
    ],
    check: (inp) => checkAll(inp, { windows: true, accepts: true }),
    counters: [{ id: 'checked', label: 'windows checked' }, { id: 'legal', label: 'legal' }, { id: 'illegal', label: 'illegal' }],
    run(inp) {
      const { M, rules } = ntmOf(inp.m);
      const t = inp.t, S = T.cook.setup(M, inp.w, t);
      const run = T.cook.acceptingRun(M, inp.w, t);
      const L = T.cook.legalWindows(M, S);
      const legal = L.per.map((list) => new Set(list.map((w) => w.join(SEP))));
      const C = corrupt(M, run.rows, inp.fault);
      const rows = C.rows, W = S.W, CW = 46, CH = 40;
      const F = new T.Frames(['checked', 'legal', 'illegal']);
      const bad = new Set();
      const badWins = [];
      // the zoomed window, to the right of the tableau
      const ZX = W * CW + 70, ZC = 56;
      const zoom = (i, j, verdict) => {
        const out = [{ key: 'zt', kind: 'text', x: ZX, y: -6, text: 'time ' + i + ', columns ' + j + '–' + (j + 2), size: 14, cls: 'strong' }];
        for (let r = 0; r < 2; r++) for (let c = 0; c < 3; c++) {
          const s = rows[i + r][j + c];
          out.push({ key: 'z:' + r + ':' + c, kind: 'cell', x: ZX + c * ZC, y: 10 + r * ZC, w: ZC, h: ZC, rx: 0, size: 20, text: dsym(s), cls: ['mono', s === '#' ? 'mark' : s.startsWith('q:') ? 'act' : s === '_' ? 'blank' : '', verdict === false && bad.has((i + r) + ',' + (j + c)) ? 'bad' : ''].filter(Boolean).join(' ') });
        }
        if (verdict !== undefined) out.push({ key: 'zv', kind: 'text', x: ZX + 1.5 * ZC, y: 10 + 2 * ZC + 30, text: verdict ? '✓ legal' : '✗ illegal', anchor: 'middle', size: 18, cls: verdict ? 'good' : 'bad' });
        return out;
      };
      const scene = (win, verdict, extra) => {
        const inWin = (i, j) => win && i >= win[0] && i <= win[0] + 1 && j >= win[1] && j <= win[1] + 2;
        const items = drawTab(M, rows, { colNums: true, badCells: bad, cls: (i, j) => (inWin(i, j) && !bad.has(i + ',' + j) ? (verdict === undefined ? 'hot' : verdict ? 'src-a' : 'bad') : '') }).items;
        if (win) items.push({ key: 'win', kind: 'region', x: win[1] * CW - 6, y: win[0] * CH - 6, w: 3 * CW + 12, h: 2 * CH + 12, rx: 6, text: '', cls: verdict === undefined ? 'hotfill' : verdict ? 'good' : 'bad' });
        for (const [wi, wj] of extra || []) items.push({ key: 'bw:' + wi + ':' + wj, kind: 'region', x: wj * CW - 6, y: wi * CH - 6, w: 3 * CW + 12, h: 2 * CH + 12, rx: 6, text: '', cls: 'bad' });
        if (win) items.push(...zoom(win[0], win[1], verdict));
        return items;
      };
      const tamper = C.cells.length ? C.cells : null;
      F.add({ items: scene(null), say: 'A tableau for N on ' + (inp.w || 'ε') + ' with t = ' + t + '. ' + (tamper ? 'One cell has been tampered with. Can the windows find it?' : 'It was copied from an accepting run. Each window covers 3 cells of one row and the 3 below them.'), meta: tamper ? { tamper: tamper.map((c) => 'tab:c:' + c.replace(',', ':')) } : {} });
      const why = (i, j, ok) => {
        const top = rows[i].slice(j, j + 3), bot = rows[i + 1].slice(j, j + 3);
        const txt = (a) => a.map(dsym).join(' ');
        if (!ok) return 'Window at time ' + i + ', columns ' + j + '–' + (j + 2) + ': no move of N turns ' + txt(top) + ' into ' + txt(bot) + '. This window is illegal, so row ' + (i + 1) + ' does not follow from row ' + i + '.';
        const hasQ = top.concat(bot).some((s) => s.startsWith('q:'));
        const p = statePos(rows[i]);
        if (!hasQ && top.join(SEP) === bot.join(SEP)) return 'Time ' + i + ', columns ' + j + '–' + (j + 2) + ': ' + txt(top) + ' over ' + txt(bot) + '. The head is not here, so nothing changes: legal.';
        if (!hasQ) return 'Time ' + i + ', columns ' + j + '–' + (j + 2) + ': the head just outside this window wrote here, and some move does exactly that: legal.';
        const q = rows[i][p].slice(2);
        if (T.tm.isAccept(M, q)) return 'Time ' + i + ', columns ' + j + '–' + (j + 2) + ': N has accepted, so the row repeats unchanged: legal.';
        const s = T.cook.successors(M, S, rows[i]).find((x) => x.row.join(SEP) === rows[i + 1].join(SEP));
        return 'Time ' + i + ', columns ' + j + '–' + (j + 2) + ': the head is here. ' + (s ? 'In ' + q + ' reading ' + dsym(rows[i][p + 1]) + ', N may ' + ruleText(s.rule) + ', which makes exactly these cells: legal.' : 'Some move of N makes exactly these six cells: legal.');
      };
      let asked = false;
      for (let i = 0; i + 1 < rows.length; i++) for (let j = 0; j + 2 < W; j++) {
        const key = [0, 1, 2].map((c) => rows[i][j + c]).concat([0, 1, 2].map((c) => rows[i + 1][j + c])).join(SEP);
        const ok = legal[j].has(key);
        const hasQ = rows[i].slice(j, j + 3).some((s) => s.startsWith('q:'));
        const p = statePos(rows[i]);
        const rIx = (() => { const s = T.cook.successors(M, S, rows[i]).find((x) => x.row.join(SEP) === rows[i + 1].join(SEP)); return s && s.rule ? [String(ruleIx(rules, s.rule))] : []; })();
        // ask once: about the first illegal window when tampered, else the first window the head moves in
        if (!asked && ((tamper && !ok) || (!tamper && hasQ && p === j + 1 && !T.tm.isAccept(M, rows[i][p].slice(2))))) {
          asked = true;
          F.add({ items: scene([i, j]), say: 'Next: the window at time ' + i + ', columns ' + j + '–' + (j + 2) + '. Is it one some move of N could make?', meta: { legalQ: ok ? 'Legal' : 'Illegal' }, hl: { rules: rIx } });
        }
        F.count('checked');
        if (ok) F.count('legal'); else { F.count('illegal'); badWins.push([i, j]); for (let r = 0; r < 2; r++) for (let c = 0; c < 3; c++) if (C.cells.includes((i + r) + ',' + (j + c))) bad.add((i + r) + ',' + (j + c)); }
        if (!ok && !C.cells.some((c) => { const [a, b] = c.split(',').map(Number); return a >= i && a <= i + 1 && b >= j && b <= j + 2; })) for (let r = 0; r < 2; r++) for (let c = 0; c < 3; c++) if (rows[i + r][j + c].startsWith('q:')) bad.add((i + r) + ',' + (j + c));
        F.add({ items: scene([i, j], ok), say: why(i, j, ok), hl: { rules: rIx } });
      }
      const nb = badWins.length;
      F.add({ items: scene(null, undefined, badWins), say: nb ? nb + ' window' + (nb === 1 ? ' is' : 's are') + ' illegal: ' + C.say + '. The move clauses of the formula say every window is legal, so no assignment can describe this table.' : 'All ' + F.counts.checked + ' windows are legal. With row 0 the start and an accepting state present, the table is an accepting computation: legal windows are all it takes to check every step.', mark: nb ? 'illegal' : 'all legal' });
      return { frames: F.list, def: { sections: [
        rulesTable(rules),
        { id: 'legal', kind: 'table', title: 'Legal windows at each column', colHead: L.per.map((_, j) => 'col ' + j), rows: [L.per.map((l) => String(l.length))] },
        { id: 'idea', kind: 'math', title: 'Why windows are enough', text: 'A move changes only the cells around the head.\nEvery 2 × 3 window legal ⇔ each row follows\nfrom the one above by some move of N.\nLegal windows listed from every row pair: ' + L.rows + ' rows tried' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.tamper, once: true, pick: 'item', ask: 'One cell of this tableau has been changed. Click the cell you think breaks the rules.', answer: (fr, i) => fr[i].meta.tamper, explain: 'The windows will find it: a window holding that cell matches no move of N.' },
      { at: (f) => f.meta && f.meta.legalQ, once: true, pick: 'option', options: ['Legal', 'Illegal'], ask: 'Is this window legal?', answer: (fr, i) => fr[i].meta.legalQ, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does a 2 × 3 window suffice to check a step?', options: ['The tape is short', 'A move changes only the state and the cells next to the head, so every change is seen inside some window', 'Windows are random', 'The machine is deterministic'], answer: 1, why: 'A move writes one cell and moves the state one place, so all the change happens within three adjacent columns.' },
      { q: 'A window has no state symbol and its two rows differ. Can it be legal?', options: ['Never', 'Yes, if the head just outside the window wrote into its edge cell', 'Always', 'Only at time 0'], answer: 1, why: 'A head just left of the window that moves left, for example, can change the window\'s edge cell without its state appearing inside.' },
      { q: 'How many window positions does a tableau with t + 1 rows and W columns have?', options: ['t · W', 't · (W − 2)', '(t + 1) · W', 'W − 2'], answer: 1, why: 'There are t pairs of neighbouring rows and W − 2 starting columns for three adjacent cells.' },
      { q: 'Why is the list of legal windows the same size for every input?', options: ['It depends only on N, not on w', 'It grows with w', 'It is always 6', 'It depends on t only'], answer: 0, why: 'Legal windows are a property of the machine\'s rules, a constant for a fixed N; only the number of window positions grows with the input.' },
      { q: 'One tape cell far from the head changes between two rows. What catches it?', options: ['Nothing', 'The window around that cell: no move changes a cell with no head nearby', 'The start clauses', 'The accept clause'], answer: 1, why: 'Every window over that cell lacks a nearby state, yet its rows differ, which no move allows.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cx-cook-count', family: 'cx-cook', order: 30, title: 'Counting the clauses',
    blurb: 'The formula has four groups of clauses: each cell holds one symbol, row 0 is the start, some cell accepts, every window is legal. Count them as the time bound grows: polynomial, not exponential.',
    inputs: [
      { id: 'mc', kind: 'choice', label: 'Machine', def: 'guess', options: [{ value: 'guess', label: 'guess a bit and match it' }, { value: 'twice', label: 'a letter occurs twice' }] },
      { id: 'w', kind: 'string', label: 'Input w', def: '01', max: 3 },
      { id: 'tmax', kind: 'number', label: 'Largest time bound', def: 5, min: 2, max: 6 },
    ],
    presets: [
      { label: 'Guess a bit, t up to 5', values: { mc: 'guess', w: '01', tmax: 5 } },
      { label: 'A letter twice, t up to 5', values: { mc: 'twice', w: 'ab', tmax: 5 } },
      { label: 'The empty input', values: { mc: 'guess', w: '', tmax: 4 } },
      { label: 'Only up to t = 2', values: { mc: 'twice', w: 'aba', tmax: 2 } },
    ],
    check: (inp) => { const m = inp.mc === 'twice' ? TWICE : GUESS; return checkAll({ m, w: inp.w, t: inp.tmax }, { windows: true }); },
    counters: [{ id: 't', label: 'time bound t' }, { id: 'vars', label: 'variables' }, { id: 'clauses', label: 'clauses' }],
    run(inp) {
      const text = inp.mc === 'twice' ? TWICE : GUESS;
      const { M } = ntmOf(text);
      const t0 = Math.min(inp.tmax, 2);
      const builds = [];
      for (let t = 1; t <= inp.tmax; t++) builds[t] = T.cook.build(M, inp.w, t);
      const K0 = builds[1].symbols.length;
      const F = new T.Frames(['t', 'vars', 'clauses']);
      const GROUPS = [{ id: 'cell', label: 'cell' }, { id: 'start', label: 'start' }, { id: 'accept', label: 'accept' }, { id: 'move', label: 'move' }];
      const S = 18; // mini-tableau cell size
      const mini = (t, hi) => {
        const B = builds[t], items = [];
        for (let i = 0; i < B.rows; i++) for (let j = 0; j < B.cols; j++) {
          const lit = hi === 'cell' ? i === 0 && j === 1 : hi === 'start' ? i === 0 : hi === 'accept' ? true : hi === 'move' ? i <= 1 && j >= 2 && j <= 4 : false;
          items.push({ key: 'mg:' + i + ':' + j, kind: 'cell', x: j * S, y: 30 + i * S, w: S, h: S, rx: 0, text: '', cls: lit ? (hi === 'accept' ? 'good' : hi === 'move' ? 'hot' : 'act') : '', enter: 'grow' });
        }
        items.push({ key: 'mg:t', kind: 'text', x: 0, y: 14, text: B.rows + ' × ' + B.cols + ' tableau', cls: 'title' });
        return items;
      };
      const BX = 300;
      const bars = (t, upto) => K.cx.bars({ rows: GROUPS.slice(0, upto).map((g, k) => ({ id: g.id, label: g.label, value: builds[t].counts[g.id], cls: 's' + k })), x: BX + 70, y: 30, w: 250, barH: 24, gap: 10, log: true, max: Math.max(...GROUPS.map((g) => builds[inp.tmax].counts[g.id])), title: 'clauses by group (log scale)', prefix: 'bars' }).items;
      const total = (t) => builds[t].formula.clauses.length;
      const PY = 230, PW = 430, PH = 170;
      const ymax = Math.ceil(total(inp.tmax) * 1.1);
      const plot = (upto) => {
        const pts = [];
        for (let t = 1; t <= upto; t++) pts.push([t, total(t)]);
        const c = total(inp.tmax) / (inp.tmax * inp.tmax);
        const sq = []; for (let t = 1; t <= inp.tmax; t++) sq.push([t, c * t * t]);
        const yT = [0, Math.round(ymax / 2 / 1000) * 1000 || Math.round(ymax / 2), ymax].filter((v, i, a) => a.indexOf(v) === i);
        return K.cx.plot({ x: 70, y: PY, w: PW, h: PH, xs: [1, inp.tmax], ys: [0, ymax], xTicks: Array.from({ length: inp.tmax }, (_, k) => k + 1), yTicks: yT, xLabel: 'time bound t', yLabel: 'clauses', prefix: 'pl',
          series: [{ id: 'tot', label: 'clauses', pts, cls: 's0', hot: true }, { id: 'sq', label: 'c · t²', pts: sq, cls: 'sm', dash: true, dots: false }] }).items;
      };
      const B0 = builds[t0];
      const setT = (t) => F.set('t', t).set('vars', builds[t].formula.n).set('clauses', total(t));
      setT(t0);
      F.add({ items: mini(t0), say: 'With t = ' + t0 + ', N\'s tableau has ' + B0.rows + ' rows and ' + B0.cols + ' columns. For every cell and each of its ' + K0 + ' possible symbols there is a variable x(i, j, s): ' + B0.rows * B0.cols * K0 + ' of them, plus one selector per legal window at each position.' });
      const says = {
        cell: 'Cell clauses: each cell holds at least one symbol (one clause of ' + K0 + ' literals) and no two (' + (K0 * (K0 - 1) / 2) + ' clauses ¬x ∨ ¬y). That is ' + (1 + K0 * (K0 - 1) / 2) + ' per cell, ' + B0.counts.cell + ' in all.',
        start: 'Start clauses: row 0 must be the start configuration, one single-literal clause per column: ' + B0.counts.start + '.',
        accept: 'Accept clause: just one, a long OR saying the accepting state appears in some cell.',
        move: 'Move clauses: at each of the ' + t0 * (B0.cols - 2) + ' window positions, one of the legal windows must be chosen, and a chosen window fixes its six cells: ' + B0.counts.move + ' clauses, the biggest group.',
      };
      GROUPS.forEach((g, k) => F.add({ items: mini(t0, g.id).concat(bars(t0, k + 1)), say: says[g.id], meta: k === 2 ? { biggest: GROUPS.slice().sort((a, b) => B0.counts[b.id] - B0.counts[a.id])[0].label } : {} }));
      for (let t = t0; t <= inp.tmax; t++) {
        setT(t);
        const B = builds[t];
        F.add({ items: mini(t).concat(bars(t, 4)).concat(plot(t)), say: 't = ' + t + ': ' + B.rows + ' × ' + B.cols + ' cells, ' + B.formula.n + ' variables and ' + total(t) + ' clauses (cell ' + B.counts.cell + ', move ' + B.counts.move + ').', meta: t === Math.min(t0 + 1, inp.tmax) ? { growth: 'polynomial, like t²' } : {} });
      }
      F.add({ items: mini(inp.tmax).concat(bars(inp.tmax, 4)).concat(plot(inp.tmax)), say: 'The count follows c · t²: rows and columns each grow with t, and the number of legal windows depends only on N. For a machine running in time n^k, t = n^k, so the formula has polynomially many clauses in n: it can be written down in polynomial time. (The table in the panel divides by t²: the ratio settles.)', mark: 'polynomial' });
      const tb = []; for (let t = 1; t <= inp.tmax; t++) { const B = builds[t]; tb.push([String(t), B.rows + ' × ' + B.cols, String(B.formula.n), String(B.counts.cell), String(B.counts.move), String(total(t)), String(Math.round(total(t) / (t * t)))]); }
      return { frames: F.list, def: { sections: [
        { id: 'groups', kind: 'math', title: 'The four groups (K = ' + K0 + ' symbols)', text: 'cell: R·W·(1 + K(K−1)/2)\nstart: W\naccept: 1\nmove: Σ over t·(W−2) positions of (1 + 6·legal windows)\nR = t + 1, W = max(|w|, t + 1) + 3' },
        { id: 'tab', kind: 'table', title: 'Size as t grows', colHead: ['t', 'cells', 'variables', 'cell', 'move', 'clauses', 'clauses / t²'], rows: tb },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.biggest, once: true, pick: 'option', options: ['cell', 'start', 'accept', 'move'], ask: 'Which group will turn out to have the most clauses?', answer: (fr, i) => fr[i].meta.biggest, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.growth, once: true, pick: 'option', options: ['polynomial, like t²', 'exponential, like 2ᵗ'], ask: 'As t grows, how will the number of clauses grow?', answer: () => 'polynomial, like t²', explain: 'The tableau has about t² cells and a constant number of clauses per cell and per window: polynomial.' },
    ],
    quiz: [
      { q: 'Why is the number of legal windows a constant?', options: ['It depends only on N\'s states and symbols', 'It is always 6', 'It grows with t', 'It depends on w'], answer: 0, why: 'A window is 6 symbols from N\'s fixed alphabet of symbols and states, so there are boundedly many, whatever the input.' },
      { q: 'For a machine running in time n², about how many cells does the tableau have?', options: ['n', 'n²', 'n⁴', '2ⁿ'], answer: 2, why: 'About t rows by t columns with t = n²: about n⁴ cells, still a polynomial.' },
      { q: 'Which part of the proof needs the time bound to be polynomial?', options: ['That the formula is satisfiable', 'That the formula can be written in polynomial time', 'That windows are legal', 'That the machine halts'], answer: 1, why: 'The reduction must run in polynomial time; with an exponential bound the tableau, and the formula, would be exponentially big.' },
      { q: 'How many accept clauses are there?', options: ['One per cell', 'One per row', 'Exactly one', 'None'], answer: 2, why: 'A single clause OR-ing every variable "cell (i, j) holds an accepting state".' },
      { q: 'What do the cell clauses guarantee?', options: ['The tableau is accepting', 'Each cell holds exactly one symbol, so an assignment describes a table', 'The start row is right', 'Windows are legal'], answer: 1, why: 'At least one symbol and no two: the true variables pick out one symbol per cell.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'cx-cook-assign', family: 'cx-cook', order: 40, title: 'Tableau ↔ satisfying assignment',
    blurb: 'An accepting tableau is a satisfying assignment: x(i, j, s) is true exactly when cell (i, j) holds s. And any satisfying assignment, read back cell by cell, is an accepting tableau. No accepting branch, no satisfying assignment.',
    inputs: baseInputs({ m: GUESS, w: '01', t: 3, tmax: 3 }),
    presets: [
      { label: 'Guess a bit: 01', values: { m: GUESS, w: '01', t: 3 } },
      { label: 'Two accepting branches: aaa', values: { m: TWICE, w: 'aaa', t: 3 } },
      { label: 'No accepting branch: 1', values: { m: GUESS, w: '1', t: 2 } },
      { label: 'Too little time: aba, t = 2', values: { m: TWICE, w: 'aba', t: 2 } },
    ],
    check: (inp) => checkAll(inp, { windows: true }),
    counters: [{ id: 'vars', label: 'variables' }, { id: 'clauses', label: 'clauses' }, { id: 'sat', label: 'clauses satisfied' }],
    run(inp) {
      const { M } = ntmOf(inp.m);
      const t = inp.t, S = T.cook.setup(M, inp.w, t), R = t + 1;
      const B = T.cook.build(M, inp.w, t);
      const run = T.cook.acceptingRun(M, inp.w, t);
      const F = new T.Frames(['vars', 'clauses', 'sat']);
      F.set('vars', B.formula.n).set('clauses', B.formula.clauses.length);
      const CW = 46, CH = 40;
      const syms = B.symbols;
      const CY = R * CH + 60;
      const chips = (i, j, a, reveal) => {
        const out = [{ key: 'ch:h', kind: 'text', x: 0, y: CY - 30, text: 'the variables x(' + i + ', ' + j + ', s) of cell (' + i + ', ' + j + ')', cls: 'title' }];
        syms.forEach((s, k) => {
          const v = a ? a[B.varOf(i, j, s)] : null;
          out.push({ key: 'ch:s:' + k, kind: 'text', x: k * 52 + 23, y: CY - 6, text: dsym(s), anchor: 'middle', size: 14, cls: 'mono' });
          out.push({ key: 'ch:v:' + k, kind: 'cell', x: k * 52, y: CY + 2, w: 46, h: 36, rx: 8, text: reveal ? (v ? '1' : '0') : '?', cls: 'mono chip ' + (reveal ? (v ? 'lit-t' : 'lit-f') : 'lit-u'), pick: true });
        });
        return out;
      };
      const tab = (rows, o) => drawTab(M, rows, Object.assign({ colNums: true }, o || {}));
      const ring = (i, j) => ({ key: 'ring', kind: 'region', x: j * CW - 5, y: i * CH - 5, w: CW + 10, h: CH + 10, rx: 6, text: '', cls: 'hotfill' });
      const groupBars = (a) => {
        const sat = { cell: 0, start: 0, accept: 0, move: 0 };
        let k = 0;
        for (const g of ['cell', 'start', 'accept', 'move']) for (let c = 0; c < B.counts[g]; c++, k++) if (a && T.sat.evalClause(B.formula.clauses[k], a)) sat[g]++;
        return { sat, items: K.cx.bars({ rows: ['cell', 'start', 'accept', 'move'].map((g, x) => ({ id: g, label: g, value: sat[g], text: sat[g] + ' of ' + B.counts[g], cls: sat[g] === B.counts[g] ? 's1' : 's4' })), x: S.W * CW + 140, y: 20, w: 150, barH: 26, gap: 10, log: true, max: Math.max(...Object.values(B.counts)), title: 'clauses satisfied', prefix: 'gb' }).items };
      };
      const empty = new Array(R).fill(null);
      if (run.accepts) {
        const a = B.fromRun(run.rows);
        const rows = run.rows;
        F.add({ items: tab(rows).items, say: 'An accepting tableau of N on ' + (inp.w || 'ε') + '. Read it as an assignment to the ' + B.formula.n + ' variables: x(i, j, s) = 1 exactly when cell (i, j) holds s.' });
        const accCell = (() => { for (let i = 0; i < R; i++) { const j = rows[i].findIndex((s) => s.startsWith('q:') && T.tm.isAccept(M, s.slice(2))); if (j >= 0) return [i, j]; } return [0, 1]; })();
        const blankCell = (() => { const j = rows[0].lastIndexOf('_'); return [0, j > 0 ? j : 2]; })();
        const picks = [[0, 1], blankCell, accCell];
        picks.forEach(([i, j], k) => {
          const s = rows[i][j];
          if (k === 2) F.add({ items: tab(rows).items.concat([ring(i, j)], chips(i, j, a, false)), say: 'Cell (' + i + ', ' + j + ') holds ' + dsym(s) + '. Which of its ' + syms.length + ' variables is 1?', meta: { chip: 'ch:v:' + syms.indexOf(s) } });
          F.add({ items: tab(rows).items.concat([ring(i, j)], chips(i, j, a, true)), say: 'Cell (' + i + ', ' + j + ') holds ' + dsym(s) + ', so x(' + i + ', ' + j + ', ' + dsym(s) + ') = 1 and its other ' + (syms.length - 1) + ' variables are 0: its cell clauses are satisfied.' });
        });
        const g = groupBars(a);
        F.set('sat', Object.values(g.sat).reduce((x, y) => x + y, 0));
        F.add({ items: tab(rows).items.concat(g.items), say: 'Each window position also gets its selector: the legal window this tableau shows there is set to 1. Now every clause is satisfied: ' + F.counts.sat + ' of ' + B.formula.clauses.length + '. Accepting tableau ⇒ satisfying assignment.' });
        const t1 = Date.now();
        const sol = T.sat.solve(B.formula);
        const ms = Date.now() - t1;
        F.set('sat', 0);
        F.add({ items: tab(empty, { qrows: empty.map((_, i) => i), width: S.W }).items.concat(groupBars(null).items), say: 'Now the other way. Forget the machine and hand the ' + B.formula.clauses.length + ' clauses to a SAT solver, which knows nothing about tableaux.' });
        const dec = B.decode(sol.assignment);
        const same = dec.every((r, i) => r.join(SEP) === rows[i].join(SEP));
        const fly = {};
        F.set('sat', B.formula.clauses.length);
        F.add({ items: tab(dec).items.concat(groupBars(sol.assignment).items), say: 'The solver finds a satisfying assignment in ' + sol.decisions + ' decisions (' + ms + ' ms). Reading each cell\'s one true variable gives back a tableau: ' + (same ? 'the same accepting computation as ours.' : 'a different accepting computation, another branch of N that also accepts. Any satisfying assignment is some accepting branch.'), mark: 'decoded' });
        void fly;
        F.add({ items: tab(dec, { cls: (i, j, s) => (s.startsWith('q:') && T.tm.isAccept(M, s.slice(2)) ? 'good' : '') }).items.concat(groupBars(sol.assignment).items), say: 'Row 0 is the start (start clauses), every step is a legal move (move clauses) and an accepting state appears (accept clause): satisfying assignment ⇒ accepting tableau. So the formula is satisfiable exactly when N accepts ' + (inp.w || 'ε') + ' within ' + t + ' steps.' });
      } else {
        // follow the longest-living branch to show where it gets stuck
        const life = (row, k) => { if (k <= 0) return [row]; const ss = T.cook.successors(M, S, row); if (!ss.length) return [row]; let best = null; for (const s of ss) { const p = life(s.row, k - 1); if (!best || p.length > best.length) best = p; } return [row].concat(best); };
        const br = life(S.start, t);
        const rows = empty.map((_, i) => br[i] || null);
        F.add({ items: tab(empty, { width: S.W }).items, say: 'No branch of N accepts ' + (inp.w || 'ε') + ' within ' + t + ' steps, so there is no accepting tableau to read as an assignment. What does the formula make of that?' });
        const stuck = br.length - 1;
        F.add({ items: tab(rows, { qrows: rows.map((r, i) => (r ? -1 : i)).filter((i) => i >= 0), qbad: true }).items, say: br.length < R ? 'The longest branch gets stuck at time ' + stuck + ': no row can follow ' + rowText(br[stuck]) + ' through legal windows, so the move clauses cannot all hold.' : 'The branch runs for all ' + t + ' steps but never enters an accepting state, so the accept clause, one OR over every cell, stays false.' });
        const t1 = Date.now();
        const sol = T.sat.solve(B.formula);
        const ms = Date.now() - t1;
        F.add({ items: tab(rows, { qrows: rows.map((r, i) => (r ? -1 : i)).filter((i) => i >= 0), qbad: true }).items.concat(K.cx.note({ x: 0, y: R * 40 + 40, lines: ['SAT solver: unsatisfiable', B.formula.n + ' variables, ' + B.formula.clauses.length + ' clauses, ' + sol.decisions + ' decisions'], cls: 'bad', prefix: 'nt' }).items), say: 'The SAT solver searches and reports the formula unsatisfiable (' + sol.decisions + ' decisions, ' + ms + ' ms). No accepting branch, no satisfying assignment: the formula answers exactly the question "does N accept w in t steps?".', mark: 'unsatisfiable', meta: { unsat: true } });
        F.add({ items: tab(rows, { qrows: rows.map((r, i) => (r ? -1 : i)).filter((i) => i >= 0), qbad: true }).items.concat(K.cx.note({ x: 0, y: R * 40 + 40, lines: ['N rejects within t ⇔ formula unsatisfiable', 'so SAT decides every problem in NP, given the reduction'], prefix: 'nt' }).items), say: 'This is why SAT is NP-hard: the question for any language in NP becomes a formula of polynomial size, satisfiable exactly when the answer is yes.' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'vars', kind: 'math', title: 'Variables', text: 'x(i, j, s): cell (i, j) holds s\n' + R + ' rows × ' + S.W + ' columns × ' + syms.length + ' symbols = ' + R * S.W * syms.length + '\nplus ' + (B.formula.n - R * S.W * syms.length) + ' window selectors\nsymbols: ' + syms.map(dsym).join(' ') },
        { id: 'groups', kind: 'table', title: 'Clause groups', colHead: ['cell', 'start', 'accept', 'move'], rows: [['cell', 'start', 'accept', 'move'].map((g) => String(B.counts[g]))] },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.chip, once: true, pick: 'item', ask: 'Click the variable of this cell that the tableau makes true.', answer: (fr, i) => fr[i].meta.chip, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.unsat, once: true, pick: 'option', options: ['Satisfiable', 'Unsatisfiable'], ask: 'The formula for this machine and input goes to a SAT solver. What will it say?', answer: () => 'Unsatisfiable', explain: 'A satisfying assignment would be an accepting tableau, and there is none.' },
    ],
    quiz: [
      { q: 'How does a satisfying assignment give a tableau?', options: ['Each true variable is a row', 'In each cell exactly one x(i, j, s) is true; write that s in the cell', 'Count the true variables', 'It cannot'], answer: 1, why: 'The cell clauses force exactly one true variable per cell, which names the symbol there.' },
      { q: 'A solver returns an assignment whose tableau differs from the run you traced. Is something wrong?', options: ['Yes, the formula is wrong', 'No: it describes another accepting branch of N', 'Yes, the solver is wrong', 'Only if t is large'], answer: 1, why: 'A nondeterministic machine may accept along several branches; the formula is satisfied by any of them.' },
      { q: 'N has no accepting branch within t steps. The formula is…', options: ['satisfiable', 'unsatisfiable', 'empty', 'not defined'], answer: 1, why: 'A satisfying assignment would read back as an accepting tableau, which does not exist.' },
      { q: 'What makes this a reduction from any NP language to SAT?', options: ['The formula is short', 'w is in the language ⇔ the formula is satisfiable, and the formula is built in polynomial time', 'SAT is easy', 'The machine is deterministic'], answer: 1, why: 'A polynomial-time map that preserves yes and no answers is exactly a polynomial-time reduction.' },
    ],
  });
})();
