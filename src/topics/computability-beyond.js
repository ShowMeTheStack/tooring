// Beyond decidability: busy beavers (a function that outgrows every computable one), Kolmogorov complexity
// (how short a description can be, and why nobody can compute it) and an intuition card for incompleteness
// (a proof search that cannot settle every true statement about machines).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'comp-beyond', part: 'computability', order: 90, title: 'Beyond: growth, randomness, incompleteness', blurb: 'Busy beavers outgrow every computable function, most strings have no short description, and no proof search can settle every true statement about machines.' });

  // ---------- shared drawing helpers ----------
  /** Split text into lines no wider than w at the given size */
  function wrap(text, w, size) {
    const out = [];
    for (const para of String(text).split('\n')) {
      let cur = '';
      for (const word of para.split(' ')) {
        const t = cur ? cur + ' ' + word : word;
        if (cur && Geo.textWidth(t, size || 15) > w) { out.push(cur); cur = word; } else cur = t;
      }
      out.push(cur);
    }
    return out;
  }
  /** A card of text on the stage: a cell with wrapped lines. Returns the item; its height is it.h */
  function card(key, x, y, w, text, cls, extra) {
    const lines = wrap(text, w - 28, 15);
    return Object.assign({ key, kind: 'cell', x, y, w, h: lines.length * 22 + 22, lines, size: 15, cls: 'card ' + (cls || ''), rx: 12 }, extra || {});
  }
  /** One camera per phase: frames of a phase share the box around all of them */
  function viewPhases(frames) {
    const groups = new Map();
    for (const f of frames) { const p = f.phase || 'main'; if (!groups.has(p)) groups.set(p, []); groups.get(p).push(f); }
    for (const fs of groups.values()) {
      let box = null;
      for (const f of fs) { const b = T.stageBounds(f.items, { minW: 360, minH: 260, margin: 44 }); if (b) box = box ? Geo.union([box, b]) : b; }
      if (box) for (const f of fs) f.view = box;
    }
    return frames;
  }
  const fmt = (n) => (typeof n === 'number' ? n.toLocaleString('en-GB') : String(n));

  // =====================================================================================================
  // Busy beavers
  // =====================================================================================================
  // Machines on the two symbols 0 (the blank) and 1. A state with no rule for what it reads halts the
  // machine; the halting state H has no rules at all.
  const BB = {
    bb2: 'start A\nA, 0 -> B, 1, R\nA, 1 -> B, 1, L\nB, 0 -> A, 1, L\nB, 1 -> H, 1, R',
    bb3: 'start A\nA, 0 -> B, 1, R\nA, 1 -> H, 1, L\nB, 0 -> B, 1, L\nB, 1 -> C, 0, R\nC, 0 -> C, 1, L\nC, 1 -> A, 1, L',
    bb3ones: 'start A\nA, 0 -> B, 1, R\nA, 1 -> C, 1, L\nB, 0 -> A, 1, L\nB, 1 -> B, 1, R\nC, 0 -> B, 1, L\nC, 1 -> H, 1, L',
    bb4: 'start A\nA, 0 -> B, 1, R\nA, 1 -> B, 1, L\nB, 0 -> A, 1, L\nB, 1 -> C, 0, L\nC, 0 -> H, 1, R\nC, 1 -> D, 1, L\nD, 0 -> D, 1, R\nD, 1 -> A, 0, R',
    mine3: 'start A\nA, 0 -> C, 1, L\nA, 1 -> H, 1, R\nB, 0 -> A, 1, R\nB, 1 -> B, 1, L\nC, 0 -> B, 0, L\nC, 1 -> C, 1, R',
    bounce: 'start A\nA, 0 -> B, 1, R\nA, 1 -> B, 1, R\nB, 0 -> A, 0, L\nB, 1 -> H, 1, R',
    runaway: 'start A\nA, 0 -> B, 1, R\nA, 1 -> H, 1, R\nB, 0 -> A, 1, R\nB, 1 -> H, 1, R',
  };
  // the proved records: most steps S(n) and most ones Σ(n) for n working states (and the halting state)
  const RECORD = { 1: { steps: 1, ones: 1 }, 2: { steps: 6, ones: 4 }, 3: { steps: 21, ones: 6 }, 4: { steps: 107, ones: 13 }, 5: { steps: 47176870, ones: 4098 } };
  const LIMIT = 150;
  const sym = (s) => (s === '⊔' || s === '_' ? '0' : s);

  function beaverMachine(text) {
    const m = T.Machine.parse(text);
    const rules = new Map();
    for (const t of m.trans) { const l = T.Machine.tmLabel(t.label); rules.set(t.from + '\u0000' + sym(l.read), { to: t.to, write: sym(l.write), move: l.move, label: t.label, from: t.from, read: sym(l.read) }); }
    const halting = m.states.filter((q) => !m.trans.some((t) => t.from === q));
    m.accept = halting;
    return { m, rules, working: m.states.filter((q) => !halting.includes(q)), halting };
  }

  /**
   * Run from the blank tape. verdict: halt | loop (a configuration repeats) | runaway (the machine meets
   * fresh blanks at its right or left edge in the same state twice, never going back past the first
   * meeting: everything after repeats shifted, for ever) | limit.
   */
  function runBeaver(B, limit) {
    const tape = new Map();
    let q = B.m.start, head = 0;
    const steps = [], seen = new Map();
    const get = (p) => tape.get(p) || '0';
    const snap = () => q + '|' + head + '|' + [...tape].filter(([, v]) => v === '1').map(([k]) => k).sort((a, b) => a - b).join(',');
    const edges = []; // {q, head, side, min, max}
    let lo = 0, hi = 0;
    seen.set(snap(), 0);
    for (let n = 0; n < limit; n++) {
      const s = get(head);
      const r = B.rules.get(q + '\u0000' + s);
      if (!r) return { steps, verdict: 'halt', q, head, tape, sym: s };
      const before = { q, head, sym: s };
      tape.set(head, r.write);
      q = r.to;
      head += r.move === 'L' ? -1 : r.move === 'R' ? 1 : 0;
      steps.push({ before, r, after: { tape: new Map(tape), head, q } });
      const k = snap();
      if (seen.has(k)) return { steps, verdict: 'loop', q, head, tape, first: seen.get(k), again: n + 1 };
      seen.set(k, n + 1);
      for (const e of edges) { e.min = Math.min(e.min, head); e.max = Math.max(e.max, head); }
      const ones = [...tape].filter(([, v]) => v === '1').map(([p]) => p);
      const freshR = ones.every((p) => p < head), freshL = ones.every((p) => p > head);
      for (const side of [freshR ? 'R' : null, freshL ? 'L' : null].filter(Boolean)) {
        const e = edges.find((x) => x.q === q && x.side === side && (side === 'R' ? x.min >= x.head : x.max <= x.head) && x.head !== head);
        if (e) return { steps, verdict: 'runaway', q, head, tape, first: e.n, again: n + 1, side };
        edges.push({ q, head, side, min: head, max: head, n: n + 1 });
      }
      lo = Math.min(lo, head); hi = Math.max(hi, head);
    }
    return { steps, verdict: 'limit', q, head, tape };
  }
  const onesOf = (tape) => [...tape.values()].filter((v) => v === '1').length;
  const tapeArr = (tape, head) => {
    const ks = [...tape.keys(), head];
    const lo = Math.min(...ks), hi = Math.max(...ks);
    const list = [];
    for (let i = lo; i <= hi; i++) list.push(tape.get(i) || '0');
    return { list, offset: lo };
  };

  T.topic({
    id: 'bb-hunt', family: 'comp-beyond', order: 10, title: 'Busy beavers: the hunt for the longest run',
    blurb: 'Among all machines with n states that halt on the blank tape, which runs longest? The answers grow faster than any function a program can compute, and that is exactly why no program can find them.',
    inputs: [
      { id: 'm', kind: 'machine', machine: 'tm', label: 'Machine (symbols 0 and 1, 0 is the blank)', def: BB.bb2, check: (v) => {
        let B;
        try { B = beaverMachine(v); } catch (e) { return 'Machine: ' + e.message; }
        if (B.m.kind !== 'tm') return 'Machine: a Turing machine, with rules like A, 0 -> B, 1, R';
        if (B.working.length < 1 || B.working.length > 4) return 'Machine: 1 to 4 working states (plus a halting state with no rules), so the run stays watchable';
        for (const r of B.rules.values()) if (!['0', '1'].includes(r.read) || !['0', '1'].includes(r.write)) return 'Machine: only the symbols 0 and 1 (0 is the blank), but a rule uses ' + (['0', '1'].includes(r.read) ? r.write : r.read);
        for (const r of B.rules.values()) if (r.move === 'S') return 'Machine: a busy beaver moves left or right on every step (no S)';
        return null;
      } },
    ],
    presets: [
      { label: 'Champion, 2 states: 6 steps', values: { m: BB.bb2 } },
      { label: 'Champion, 3 states: 21 steps', values: { m: BB.bb3 } },
      { label: 'Most ones, 3 states: 6 ones', values: { m: BB.bb3ones } },
      { label: 'Champion, 4 states: 107 steps', values: { m: BB.bb4 } },
      { label: 'A candidate of our own: 3 states', values: { m: BB.mine3 } },
      { label: 'Never halts: it bounces', values: { m: BB.bounce } },
      { label: 'Never halts: it runs away', values: { m: BB.runaway } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'ones', label: 'ones on the tape' }, { id: 'cells', label: 'cells visited' }],
    run(inp) {
      const B = beaverMachine(inp.m);
      const m = B.m, n = B.working.length;
      const run = runBeaver(B, LIMIT);
      const pos = K.graph.layout(m).pos;
      const g0 = K.graph.draw(m, { pos });
      const N = 11, CW = 46;
      const tx = g0.box.x + g0.box.w / 2 - (N * CW) / 2, ty = g0.box.y + g0.box.h + 70;
      const sc = K.tape.scroller({ cells: N, origin: -5, margin: 2 });
      const F = new T.Frames(['steps', 'ones', 'cells']);
      const seen = new Set([0]);
      const syms = ['0', '1'];
      const rowOf = (q) => m.states.indexOf(q);
      const scene = (tape, head, q, opts) => {
        const a = tapeArr(tape, head);
        const origin = sc.at(head);
        const t = K.tape.draw({ tape: a.list, offset: a.offset, head, state: q, cells: N, origin, prevOrigin: sc.prev, x: tx, y: ty, headCls: opts.headCls || '', blank: '0', cls: (i, v) => (v === '1' ? 'one' : '') });
        return K.graph.draw(m, Object.assign({ pos }, opts)).items.concat(t.items);
      };
      F.add({ items: scene(new Map(), 0, m.start, { active: [m.start], startHot: true }), say: 'The tape is blank: every cell holds 0. The machine starts in ' + m.start + ' and may use ' + n + ' working state' + (n > 1 ? 's' : '') + '. The goal of a busy beaver: halt, but only after as many steps as possible.', phase: 'run', meta: { next: run.steps[0] ? run.steps[0].after.q : null } });
      const show = Math.min(run.steps.length, LIMIT);
      for (let k = 0; k < show; k++) {
        const s = run.steps[k];
        F.count('steps');
        seen.add(s.after.head);
        F.set('ones', onesOf(s.after.tape)).set('cells', seen.size);
        const how = s.r.move === 'L' ? 'left' : 'right';
        const nx = run.steps[k + 1];
        F.add({ items: scene(s.after.tape, s.after.head, s.after.q, { active: [s.after.q], taken: [s.before.q + '>' + s.r.to] }), say: 'Step ' + (k + 1) + ': in ' + s.before.q + ' reading ' + s.before.sym + ', write ' + s.r.write + ', move ' + how + ', go to ' + s.r.to + '.' + (B.halting.includes(s.r.to) ? ' ' + s.r.to + ' has no rules: the machine halts.' : ''), hl: { delta: [rowOf(s.before.q) + ',' + syms.indexOf(s.before.sym)] }, phase: 'run', meta: { next: nx ? nx.after.q : null } });
      }
      const last = run.steps.length ? run.steps[run.steps.length - 1].after : { tape: new Map(), head: 0, q: m.start };
      const steps = run.steps.length, ones = onesOf(last.tape);
      const rec = RECORD[n];
      let verdict;
      if (run.verdict === 'halt') {
        const champ = (steps === rec.steps ? 'That equals the record S(' + n + ') = ' + rec.steps + ': no halting ' + n + '-state machine runs longer.' : 'The record for ' + n + ' state' + (n > 1 ? 's' : '') + ' is ' + rec.steps + ' steps, so this one is not the champion.') + (ones === rec.ones ? ' Its ' + ones + ' ones do match the other record, Σ(' + n + ') = ' + rec.ones + ': the most ones any halting ' + n + '-state machine leaves.' : '');
        verdict = 'It halted after ' + steps + ' step' + (steps === 1 ? '' : 's') + ', leaving ' + ones + ' one' + (ones === 1 ? '' : 's') + '. ' + champ;
        F.add({ items: scene(last.tape, last.head, last.q, { good: [last.q], headCls: 'good' }), say: B.halting.includes(last.q) ? verdict : 'In ' + last.q + ' there is no rule for ' + run.sym + ', so the machine halts there. ' + verdict, phase: 'run', mark: 'halted', meta: { halts: true } });
      } else if (run.verdict === 'loop') {
        F.add({ items: scene(last.tape, last.head, last.q, { bad: [last.q], headCls: 'bad' }), say: 'After step ' + run.again + ' the whole configuration (state, head and tape) is exactly what it was after step ' + run.first + '. From here it repeats for ever: this machine never halts, so it is out of the contest.', phase: 'run', mark: 'loops', meta: { halts: false } });
      } else if (run.verdict === 'runaway') {
        F.add({ items: scene(last.tape, last.head, last.q, { bad: [last.q], headCls: 'bad' }), say: 'In ' + run.q + ' at the ' + (run.side === 'R' ? 'right' : 'left') + ' edge of what it has written, with only blanks beyond, after step ' + run.again + ' — just as after step ' + run.first + ', and it never went back past that earlier edge. So the same thing happens again and again, shifted along: it never halts.', phase: 'run', mark: 'loops', meta: { halts: false } });
      } else {
        F.add({ items: scene(last.tape, last.head, last.q, { active: [last.q] }), say: 'After ' + LIMIT + ' steps it is still running. It might halt later or never; watching longer cannot tell us which in general.', phase: 'run', mark: 'limit', meta: { halts: null } });
      }

      // ---- the growth chart: known records against fast computable functions ----
      const fns = [
        { id: 'pow', name: '2ⁿ', v: [2, 4, 8, 16, 32] },
        { id: 'fac', name: 'n!', v: [1, 2, 6, 24, 120] },
        { id: 'tow', name: '2↑↑n (tower)', v: [2, 4, 16, 65536, '2⁶⁵⁵³⁶'] },
        { id: 'S', name: 'S(n): busy beaver', v: [1, 6, 21, 107, 47176870] },
      ];
      const chart = (upto, lit, extra) => {
        const rows = fns.map((f) => f.v.map((x, i) => (i < upto ? fmt(x) : '')));
        const tb = K.table.draw({ prefix: 'gr', rows, rowHead: fns.map((f) => f.name), colHead: ['n = 1', 'n = 2', 'n = 3', 'n = 4', 'n = 5'], corner: 'grows', x: 0, y: 0, cw: 112, mono: true, size: 14, cls: (r, c) => (r === 3 && c < upto ? (c === n - 1 && c < 4 ? 'hot' : 'good') : lit && lit[0] === r && lit[1] === c ? 'hot' : '') });
        return tb.items.concat(extra || []);
      };
      F.add({ items: chart(4, null, [card('gr:note', 0, 260, 700, 'For 1 to 4 states the busy beaver numbers S(n) are 1, 6, 21 and 107. So far they look tame next to a tower of powers of 2.', '')]), say: 'Line the records up against fast functions a program can compute: 2ⁿ, n! and a tower of 2s. Up to 4 states the beavers look harmless.', phase: 'chart', hl: { rec: [0, 1, 2, 3] } });
      F.add({ items: chart(5, null, [card('gr:note', 0, 260, 700, 'S(5) = 47,176,870 steps, proved after decades of searching through every 5-state machine. It has passed 2ⁿ and n! by far; the tower is still ahead at n = 5.', 'hot')]), say: 'With 5 states the champion runs 47,176,870 steps before halting, a value that took decades of work to prove. 2⁵ and 5! are left far behind; the tower is still ahead, for now.', phase: 'chart', hl: { rec: [4] } });
      F.add({ items: chart(5, null, [card('gr:note', 0, 260, 700, 'Nobody knows S(6): machines with 6 states have been found that run so long the step count needs a tower of powers to write. And it never slows down: for every function f a program can compute, S(n) > f(n) for all large enough n.', 'act')]), say: 'S(6) is unknown. Whatever computable function you pick, even a tower of towers, S eventually overtakes it for good.', phase: 'chart' });

      // ---- why no program computes S ----
      const lines = ['1. Count the states of M: n.', '2. Compute S(n), the busy beaver number.', '3. Run M on the blank tape for S(n) steps.', '4. Halted? Accept. Still running? Reject: it never will.'];
      const box = (hot, done, bad, ans, cls) => K.mbox.draw({ prefix: 'arg', x: 0, y: 0, title: 'Does M halt on the blank tape?', tag: 'if S were computable', tagCls: bad.length ? 'bad' : '', input: '⟨M⟩', lines, hot, done, bad, cls: cls || 'r0', outs: K.mbox.answers(ans) });
      const b0 = box([], [], [], undefined);
      const cy = b0.all.y + b0.all.h + 26;
      F.add({ items: box([0], [], [], undefined).items, say: 'Suppose some program computed S. Then this machine could answer whether any machine M halts on the blank tape. First it counts M\'s states.', phase: 'arg', hl: { arg: [0] } });
      F.add({ items: box([1, 2], [0], [], undefined).items, say: 'It computes S(n) and runs M for that many steps. No halting n-state machine runs longer than S(n), by the very definition of S.', phase: 'arg', hl: { arg: [1] } });
      F.add({ items: box([3], [0, 1, 2], [], 'accept').items.concat([card('arg:c1', 0, cy, b0.box.w, 'If M has not halted within S(n) steps, it never will. So the answer is always right, and the machine always stops: a decider for halting on the blank tape.', '')]), say: 'If M halted within S(n) steps it accepts; if not, M never halts and it rejects. It always stops with the right answer.', phase: 'arg', hl: { arg: [2] } });
      F.add({ items: box([], [0, 2, 3], [1], undefined, 'bad').items.concat([card('arg:c1', 0, cy, b0.box.w, 'But halting on the blank tape is undecidable. The only step that is not plainly a program is line 2, so it cannot be one: S is not computable. Its growth is the shadow of the halting problem.', 'bad')]), say: 'Halting on the blank tape is undecidable, so no such decider exists. Line 2 is the culprit: no program computes S(n).', phase: 'arg', mark: 'contradiction', hl: { arg: [3] } });

      const rows = m.states.map((q) => syms.map((a) => { const r = B.rules.get(q + '\u0000' + a); return r ? r.write + ', ' + r.move + ', ' + r.to : (B.halting.includes(q) ? 'halt' : '—'); }));
      return { frames: viewPhases(F.list), def: { sections: [
        { id: 'delta', kind: 'table', title: 'δ(state, read) = write, move, next', corner: 'δ', colHead: syms, rowHead: m.states, rows },
        { id: 'rec', kind: 'table', title: 'Proved records (n working states)', colHead: ['most steps S(n)', 'most ones Σ(n)'], rowHead: ['n = 1', 'n = 2', 'n = 3', 'n = 4', 'n = 5'], rows: [1, 2, 3, 4, 5].map((k) => [fmt(RECORD[k].steps), fmt(RECORD[k].ones)]) },
        { id: 'arg', kind: 'math', title: 'Why S is not computable', text: 'S(n) = the most steps of any n-state machine\nthat halts when started on the blank tape.\nIf S were computable, run M for S(n) steps:\nthat would decide halting. It is undecidable.' },
      ] } };
    },
    predict: [
      { at: (f, i) => i === 1 && f.meta && f.meta.next, once: true, pick: 'item', ask: 'Read the rule for the current state and the symbol under the head. Click the state the machine will be in after the next step.', answer: (fr, i) => 'g:s:' + fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.halts !== undefined && fr[i + 1].meta.halts !== null, once: true, pick: 'option', options: ['It halts', 'It never halts'], ask: 'Next we learn this machine\'s fate. Will it halt?', answer: (fr, i) => (fr[i + 1].meta.halts ? 'It halts' : 'It never halts'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'S(n) is the most steps taken by a halting n-state machine on the blank tape. Why must it exist for each n?', options: ['Because every machine halts', 'There are finitely many n-state machines, so among those that halt one runs longest', 'Because a program computes it', 'It only exists for n ≤ 5'], answer: 1, why: 'With two symbols there are finitely many n-state machines. Some halt; a finite set of numbers has a maximum. Existing is not the same as being computable.' },
      { q: 'Why can\'t we just run every n-state machine and take the longest run?', options: ['There are too many machines to try', 'We cannot tell which of the still-running ones will halt later', 'The machines need input', 'The tape is too short'], answer: 1, why: 'Trying them all is finite work, except that some never halt, and we cannot always tell a never-halter from a slow one. That is the halting problem in disguise.' },
      { q: 'If a program computed S, what could we do with it?', options: ['Nothing new', 'Decide whether any machine halts on the blank tape, by running it for S(n) steps', 'Compute every function', 'Speed machines up'], answer: 1, why: 'A machine with n states that has not halted after S(n) steps never will. That decides blank-tape halting, which is undecidable, so S is not computable.' },
      { q: 'Which is true about the growth of S?', options: ['S(n) < 2ⁿ for every n', 'For every computable f, S(n) > f(n) once n is large enough', 'S grows exactly like a tower of 2s', 'S(6) is 47,176,870'], answer: 1, why: 'S eventually beats every computable function; for small n a tower can still be ahead. S(5) = 47,176,870 and S(6) is unknown.' },
      { q: 'A machine reaches the same state, head position and tape twice. What follows?', options: ['It will halt soon', 'It repeats for ever and never halts', 'It is a busy beaver', 'Nothing can be said'], answer: 1, why: 'The machine is deterministic: the same configuration leads to the same future, so it cycles for ever. Many never-halters can be caught like this, but not all.' },
    ],
  });

  // =====================================================================================================
  // Kolmogorov complexity
  // =====================================================================================================
  /** If s is 1, 10, 11, 100, … (the binary numbers from 1 to k written one after another), that k */
  function counterOf(s) {
    let t = '';
    for (let k = 1; t.length < s.length; k++) { t += k.toString(2); if (t === s && k >= 3) return k; }
    return null;
  }
  const lg = (x) => Math.max(1, Math.ceil(Math.log2(x + 1)));

  /** The descriptions we know how to find, each with its cost in bits (an upper bound on K(s) up to a constant) */
  function descriptions(s) {
    const n = s.length;
    const out = [{ id: 'lit', name: 'write it out', text: 'print "' + (n > 14 ? s.slice(0, 12) + '…' : s || 'ε') + '"', bits: n }];
    const rep = T.kolmo.repeatDescription(s);
    if (rep) out.push({ id: 'rep', name: 'repeat a piece', text: 'repeat "' + rep.unit + '" ' + rep.times + ' times', bits: rep.unit.length + 2 * lg(rep.times), rep });
    else out.push({ id: 'rep', name: 'repeat a piece', text: n ? 'no piece repeats to make it' : 'nothing to repeat', bits: null });
    const lz = T.kolmo.lz78(s, ['0', '1']);
    out.push({ id: 'lz', name: 'LZ78 phrases', text: n ? lz.pairs.length + ' phrases, each an earlier phrase plus one bit' : 'no phrases at all', bits: n ? lz.bits : 0, lz });
    const k = counterOf(s);
    out.push({ id: 'cnt', name: 'count in binary', text: k ? 'write 1, 2, …, ' + k + ' in binary, one after another' : 'not the numbers 1, 2, 3, … in a row', bits: k ? 2 * lg(k) : null, k });
    return out;
  }

  const STR = { periodic: '011011011011011011011011', random: '1101000110111001011010', counter: '11011100101110111', zeros: '00000000000000000000' };

  T.topic({
    id: 'kolmo', family: 'comp-beyond', order: 20, title: 'Kolmogorov complexity: how short can a description be?',
    blurb: 'A string is simple when a short program prints it. Try several ways of describing a string, see why most strings have no short description at all, and why no program can find the shortest one.',
    inputs: [{ id: 's', kind: 'string', label: 'Binary string', def: STR.periodic, alphabet: '01', max: 24 }],
    presets: [
      { label: 'Periodic: 011 again and again', values: { s: STR.periodic } },
      { label: 'Random-looking coin flips', values: { s: STR.random } },
      { label: 'Looks random, but is a counter', values: { s: STR.counter } },
      { label: 'All zeros', values: { s: STR.zeros } },
      { label: 'The empty string ε', values: { s: '' } },
    ],
    counters: [{ id: 'len', label: 'length n' }, { id: 'best', label: 'shortest found (bits)' }],
    run(inp) {
      const s = inp.s, n = s.length;
      const D = descriptions(s);
      const found = D.filter((d) => d.bits !== null);
      const best = Math.min(...found.map((d) => d.bits));
      const winners = found.filter((d) => d.bits === best).map((d) => d.id);
      const F = new T.Frames(['len', 'best']);
      F.set('len', n);
      const CW = 30, W = Math.max(n * CW, 520);
      const unit = Math.min(26, (W - 120) / Math.max(1, n, ...found.map((d) => d.bits)));
      const top = 170, RH = 76;
      const scene = (shown, focus, brackets) => {
        const items = K.string.draw({ text: [...s], x: 0, y: 0, cw: CW, label: 's', brackets: brackets || [] }).items;
        items.push({ key: 'k:hd', kind: 'text', x: 0, y: top - 26, text: 'descriptions (shorter is better)', cls: 'title' });
        D.forEach((d, i) => {
          const y = top + i * RH;
          const on = shown.includes(d.id);
          items.push({ key: 'k:name:' + d.id, kind: 'text', x: 0, y: y + 4, text: d.name + (on ? ':  ' + d.text : ''), cls: on ? 'strong' : '' });
          const w = on ? (d.bits === null ? 120 : Math.max(46, d.bits * unit)) : 70;
          const cls = 'bar ' + (!on ? '' : d.bits === null ? 'bad' : winners.includes(d.id) && shown.length === D.length ? 'good' : d.id === focus ? 'hot' : '');
          items.push({ key: 'k:bar:' + d.id, kind: 'cell', x: 0, y: y + 16, w, h: 34, text: on ? (d.bits === null ? 'does not apply' : d.bits + ' bits') : '?', cls, rx: 6, pick: true });
        });
        if (n) {
          const lx = n * unit;
          items.push({ key: 'k:nline', kind: 'line', x1: lx, y1: top - 4, x2: lx, y2: top + D.length * RH - 12, cls: 'dash hot', audit: 'ignore' });
          items.push({ key: 'k:nlab', kind: 'text', x: lx + 6, y: top + D.length * RH + 4, text: 'n = ' + n + ' bits', cls: 'hot' });
        }
        return items;
      };
      F.add({ items: scene([]), say: n ? 'The string s has ' + n + ' bits. Its Kolmogorov complexity K(s) is the length of the shortest program that prints it. We try four kinds of description and keep the shortest.' : 'The empty string ε: there is nothing to print. Any description of it is just "print nothing", so K(ε) is only the fixed cost of the decoder.', phase: 'desc', meta: { winners: winners.map((w) => 'k:bar:' + w) }, hl: { def: [0] } });
      F.set('best', n);
      F.add({ items: scene(['lit'], 'lit'), say: 'Writing s out costs ' + n + ' bits, one per symbol (plus a constant for "print"). So K(s) is never much more than n.', phase: 'desc', hl: { m: [0], def: [1] } });
      const rep = D[1];
      F.set('best', Math.min(n, rep.bits === null ? n : rep.bits));
      const repBr = rep.rep ? Array.from({ length: rep.rep.times }, (_, i) => ({ id: 'r' + i, from: i * rep.rep.unit.length, to: (i + 1) * rep.rep.unit.length, text: rep.rep.unit.length * CW >= 26 || i % 2 === 0 ? String(i + 1) : '', cls: 'y', level: rep.rep.unit.length === 1 ? i % 2 : 0 })) : [];
      F.add({ items: scene(['lit', 'rep'], 'rep', repBr), say: rep.rep ? 's is the piece ' + rep.rep.unit + ' written ' + rep.rep.times + ' times: say the piece (' + rep.rep.unit.length + ' bits) and the count (about ' + 2 * lg(rep.rep.times) + ' bits, written so the decoder knows where it ends): ' + rep.bits + ' bits.' : (n ? 'No piece repeated whole makes s, so this kind of description does not apply.' : 'There is nothing to repeat.'), phase: 'desc', hl: { m: [1] } });
      const lz = D[2];
      let p = 0;
      const lzBr = [];
      // phrase boundaries: rebuild the phrases from the pairs
      const dict = [''];
      lz.lz.pairs.forEach(([i, c], k) => { const ph = dict[i] + c; dict.push(ph); lzBr.push({ id: 'z' + k, from: p, to: p + ph.length, text: ph.length * CW >= 26 ? String(k + 1) : '', cls: k % 2 ? 'x' : 'z', level: 0 }); p += ph.length; });
      F.set('best', Math.min(...[n, rep.bits, lz.bits].filter((x) => x !== null)));
      F.add({ items: scene(['lit', 'rep', 'lz'], 'lz', lzBr), say: n ? 'LZ78 cuts s into ' + lz.lz.pairs.length + ' phrases, each a phrase seen before plus one new bit, and names each by the earlier phrase\'s number: ' + lz.bits + ' bits. On a string this short the numbers cost more than they save.' : 'LZ78 has no phrases to write: 0 bits.', phase: 'desc', hl: { m: [2] } });
      const cnt = D[3];
      const cntBr = cnt.k ? (() => { const out = []; let q = 0; for (let j = 1; j <= cnt.k; j++) { const b = j.toString(2); out.push({ id: 'c' + j, from: q, to: q + b.length, text: b.length * CW >= 26 ? String(j) : '', cls: j % 2 ? 'y' : 'x', level: 0 }); q += b.length; } return out; })() : [];
      F.set('best', best);
      F.add({ items: scene(['lit', 'rep', 'lz', 'cnt'], 'cnt', cntBr), say: cnt.k ? 'It looked random, but s is 1, 10, 11, … up to ' + cnt.k + ' in binary, one after another. "Count to ' + cnt.k + '" needs only about ' + cnt.bits + ' bits. A string can look random and still be simple.' : (n ? 's is not the numbers 1, 2, 3, … written in a row, so this description does not apply.' : 'There are no numbers to count.'), phase: 'desc', hl: { m: [3] } });
      const bestD = found.filter((d) => winners.includes(d.id)).map((d) => d.name).join(' and ');
      F.add({ items: scene(['lit', 'rep', 'lz', 'cnt']), say: n === 0 ? 'Every description of ε is tiny: K(ε) is the constant every program pays. Every bound we found is 0 bits plus that constant.' : best < n ? 'The best we found is "' + bestD + '" at ' + best + ' bits, under the ' + n + ' it takes to write s out: s is compressible. That is an upper bound; something shorter might still exist.' : 'Nothing we tried beats writing s out (' + n + ' bits). It may be incompressible, or a cleverer description may exist; no program can always tell which.', phase: 'desc', mark: best < n ? 'compressible' : 'no shortcut found', hl: { def: [2] } });

      // ---- counting: most strings have no short description ----
      const L = 4, all = T.tm.strings(['0', '1'], L).filter((x) => x.length === L), short = T.tm.strings(['0', '1'], L - 1);
      const PW = 54, PH = 36, GX = 64, cols = 8;
      const pig = (upto, lit) => {
        const items = [{ key: 'pg:t1', kind: 'text', x: 0, y: -16, text: 'the 16 strings of length 4', cls: 'title' }];
        all.forEach((x, i) => {
          const r = Math.floor(i / cols), c = i % cols;
          const X = c * GX, Y = r * 150;
          items.push({ key: 'pg:s:' + x, kind: 'cell', x: X, y: Y, w: PW, h: PH, text: x, cls: 'mono' + (i < upto ? ' good' : i === 15 && lit ? ' bad' : ''), rx: 6, pick: true });
          if (i < short.length) {
            items.push({ key: 'pg:h:' + i, kind: 'cell', x: X, y: Y + 80, w: PW, h: PH, text: short[i] === '' ? 'ε' : short[i], cls: 'mono' + (i < upto ? ' act' : ''), rx: 6 });
            if (i < upto) items.push({ key: 'pg:e:' + i, kind: 'edge', from: 'pg:h:' + i, to: 'pg:s:' + x, cls: 'good' });
          } else items.push({ key: 'pg:none', kind: 'cell', x: X, y: Y + 80, w: PW, h: PH, text: '—', cls: 'gone', rx: 6 });
        });
        items.push({ key: 'pg:t2', kind: 'text', x: 0, y: 150 + 80 + PH + 30, text: 'below each: a description shorter than 4 bits (only 15 exist)', cls: 'title' });
        return items;
      };
      F.add({ items: pig(0), say: 'Why are most strings incompressible? Count. There are 16 strings of length 4, but only 1 + 2 + 4 + 8 = 15 binary descriptions shorter than 4 bits: ε, 0, 1, 00, …, 111.', phase: 'pig', hl: { def: [3] }, meta: { pig: true } });
      F.add({ items: pig(15, true), say: 'Even if every short description printed a different string, only 15 strings get one. At least one string of length 4, here 1111 in this pairing, has no description shorter than itself.', phase: 'pig', meta: { pig: true } });
      const nn = n || 16, r1 = T.kolmo.incompressible(nn, 1), r8 = T.kolmo.incompressible(nn, Math.min(8, nn));
      const pct = (x) => (x * 100).toFixed(x > 0.999 ? 2 : 1) + '%';
      F.add({ items: pig(15, true).concat([card('pg:c', 0, 150 + 80 + PH + 56, 7 * GX + PW, 'The same count for length ' + nn + ': at least ' + fmt(r1.atLeast) + ' of the ' + fmt(r1.total) + ' strings (' + pct(r1.fraction) + ') cannot be shortened by more than 1 bit, and ' + pct(r8.fraction) + ' not by more than ' + Math.min(8, nn) + ' bits. Random-looking is the normal case.', 'act')]), say: 'For length ' + nn + ' the same pigeonhole count says at least ' + pct(r1.fraction) + ' of the strings cannot be shortened by more than one bit. Strings that compress well are rare.', phase: 'pig', hl: { def: [3] } });

      // ---- why no program computes K ----
      const pl = ['1. For x = ε, 0, 1, 00, 01, … in order:', '2.     compute K(x);', '3.     if K(x) > N, print x and stop.'];
      const pbox = (hot, done, bad, cls) => K.mbox.draw({ prefix: 'pk', x: 0, y: 0, title: 'Program P_N', tag: 'if K were computable', tagCls: bad.length ? 'bad' : '', lines: pl, hot, done, bad, cls: cls || 'r3', outs: [{ id: 'out', text: 'prints x', cls: 'hot', lit: hot.includes(2) }] });
      const pb = pbox([], [], []);
      const py = pb.all.y + pb.all.h + 24;
      F.add({ items: pbox([0, 1], [], []).items.concat([card('pk:c', 0, py, pb.box.w, 'Some string has K(x) > N (most do), so P_N stops and prints the first such x in order.', '')]), say: 'Suppose a program computed K. Then P_N would search the strings in order and print the first one whose shortest description is longer than N bits.', phase: 'paradox', hl: { def: [4] } });
      F.add({ items: pbox([2], [0, 1], []).items.concat([card('pk:c', 0, py, pb.box.w, 'But P_N itself describes that x, and P_N is short: a fixed program plus the number N, about log₂ N + c bits.', 'hot')]), say: 'P_N is a description of the x it prints, and it is only about log₂ N plus a constant bits long, since it just needs N.', phase: 'paradox' });
      F.add({ items: pbox([], [0, 2], [1], 'bad').items.concat([card('pk:c', 0, py, pb.box.w, 'For large N, log₂ N + c < N: a description shorter than N bits of a string with no description shorter than N bits. Impossible, so line 2 is not a program: K is not computable. Compressors only ever give upper bounds.', 'bad')]), say: 'For large N that is a short description of a string that has none: a contradiction. So K is not computable; we can only bound it from above, as the bars did.', phase: 'paradox', mark: 'contradiction', hl: { def: [4] } });

      return { frames: viewPhases(F.list), def: { sections: [
        { id: 'def', kind: 'math', title: 'Kolmogorov complexity', text: 'K(s) = length of the shortest program printing s\nK(s) ≤ |s| + c (just print it)\nany found description is an upper bound\nfewer than 2ⁿ⁻ᶜ programs are shorter than n − c bits\nno program computes K(s)' },
        { id: 'm', kind: 'table', title: 'Descriptions of s', colHead: ['bits', 'how'], rowHead: D.map((d) => d.name), rows: D.map((d) => [d.bits === null ? '—' : String(d.bits), d.text]) },
      ] } };
    },
    predict: [
      { at: (f, i) => i === 0 && f.meta && f.meta.winners, once: true, pick: 'item', ask: 'Four ways to describe s. Before the costs appear: click the bar you think will turn out shortest.', answer: (fr, i) => fr[i].meta.winners, explain: 'The costs: writing it out costs n bits, a repeat costs the piece plus the count, LZ78 pays for phrase numbers, and a counter only needs its last number.' },
      { at: (f, i, fr) => f.meta && f.meta.pig && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.pig, once: true, pick: 'option', options: ['Yes, with care', 'No, at least one is left over'], ask: 'Can all 16 strings of length 4 get their own description shorter than 4 bits?', answer: () => 'No, at least one is left over', explain: 'Only 15 descriptions are shorter than 4 bits, and each describes one string: pigeonhole.' },
    ],
    quiz: [
      { q: 'What is K(s)?', options: ['The number of 1s in s', 'The length of the shortest program that prints s', 'The size s has after zip', 'The time a program needs to print s'], answer: 1, why: 'K(s) measures description length, not time: the shortest program (for a fixed universal machine) whose output is s.' },
      { q: 'A compressor squeezes s to 40 bits. What do we know?', options: ['K(s) = 40', 'K(s) ≤ 40 plus a constant', 'K(s) ≥ 40', 'Nothing'], answer: 1, why: 'Compressed text plus the decompressor is a program printing s: an upper bound. Showing nothing shorter exists is the part no program can do.' },
      { q: 'Why are most strings of length n incompressible?', options: ['Because they contain both 0 and 1', 'There are 2ⁿ strings but fewer than 2ⁿ programs shorter than n bits', 'Because compressors are slow', 'Because n is large'], answer: 1, why: 'Programs shorter than n bits number 2ⁿ − 1 at most, and each prints one string: pigeonhole leaves at least one string out, and most strings save very little.' },
      { q: '11011100101110111 looks random but has low complexity. Why?', options: ['It has many 1s', 'It is 1, 2, …, 7 in binary written in a row: "count to 7" is a short program', 'It is a palindrome', 'Its length is prime'], answer: 1, why: 'Looking random is not being random: a short rule generates it. K catches every such rule, which is exactly why it cannot be computed.' },
      { q: 'If K were computable, what goes wrong?', options: ['Compression would be too good', 'A short program could print the first string with no description shorter than N bits, a contradiction for large N', 'Every string would be random', 'Nothing'], answer: 1, why: 'That program is about log N + c bits long, yet prints a string whose shortest description exceeds N bits. For large N that is impossible.' },
    ],
  });

  // =====================================================================================================
  // An incompleteness intuition card
  // =====================================================================================================
  // A cartoon of a formal system: proofs are strings a checker accepts or rejects, numbered in order. We
  // list which candidate proves what; everything else is not a proof. (A story, not a real proof system.)
  const THEOREMS = [
    { at: 2, text: '0 = 0' }, { at: 4, text: '1 + 1 = 2' }, { at: 7, text: '2 + 3 = 5' }, { at: 9, text: 'machine B halts on the blank tape' },
    { at: 12, text: 'machine L never halts' }, { at: 15, text: 'every number is even or odd' },
  ];
  const TARGETS = {
    sum: { text: '2 + 3 = 5', at: 7, kind: 'true' },
    halts: { text: 'machine B halts on the blank tape', at: 9, kind: 'halts' },
    loops: { text: 'machine L never halts', at: 12, kind: 'loops' },
    self: { text: 'G: "the search for a proof of G never succeeds"', at: null, kind: 'self' },
  };

  T.topic({
    id: 'godel', family: 'comp-beyond', order: 30, title: 'Incompleteness, as an intuition',
    blurb: 'Proofs can be checked by a machine, so theorems can be listed one by one. If that list held every true statement about machines halting, it would decide the halting problem. A picture of why some truths have no proof (an intuition, not the proof).',
    inputs: [{ id: 'target', kind: 'choice', label: 'Search for a proof of', def: 'sum', options: [
      { value: 'sum', label: '2 + 3 = 5' }, { value: 'halts', label: 'machine B halts' }, { value: 'loops', label: 'machine L never halts' }, { value: 'self', label: 'G, the sentence about itself' },
    ] }],
    presets: [
      { label: 'An everyday theorem', values: { target: 'sum' } },
      { label: 'A machine that halts', values: { target: 'halts' } },
      { label: 'A machine that never halts', values: { target: 'loops' } },
      { label: 'The sentence about its own proofs', values: { target: 'self' } },
    ],
    counters: [{ id: 'checked', label: 'candidates checked' }, { id: 'thm', label: 'theorems listed' }],
    run(inp) {
      const tg = TARGETS[inp.target];
      const F = new T.Frames(['checked', 'thm']);
      const W = 440;
      const lines = ['1. For p = 1, 2, 3, … (every string):', '2.     check p: is it a valid proof?', '3.     if it proves the target, stop.'];
      const listed = [];
      const scene = (k, hot, opts) => {
        opts = opts || {};
        const items = [card('g:target', 0, 0, W, 'Target: ' + tg.text, opts.targetCls || 'act')];
        const b = K.mbox.draw({ prefix: 'g', x: 0, y: 70, w: W, title: 'Proof search', tag: 'a machine', lines, hot, outs: opts.noOut ? [] : [{ id: 'found', text: 'found ✓', cls: 'good', lit: !!opts.found }] });
        items.push(...b.items);
        const y0 = b.all.y + b.all.h + 40;
        items.push({ key: 'g:lt', kind: 'text', x: 0, y: y0 - 14, text: 'candidates, in order', cls: 'title' });
        const from = Math.max(1, k - 4);
        for (let p = from; p <= k; p++) {
          const th = THEOREMS.find((t) => t.at === p);
          const isT = tg.at === p;
          items.push({ key: 'g:p' + p, kind: 'cell', x: 0, y: y0 + (p - from) * 44, w: W, h: 38, text: '#' + p + (th ? '   proves: ' + th.text : '   not a valid proof'), cls: (th ? (isT ? 'good' : 'act') : 'gone'), rx: 6, enter: 'drop' });
        }
        return { items, bottom: y0 + 5 * 44 };
      };
      F.add({ items: scene(0, [], {}).items, say: 'A formal system has axioms and rules, and whether a string is a valid proof can be checked by a machine. So a machine can try every string in turn and list every theorem.', phase: 'search', hl: { sys: [0, 1] } });
      const stop = tg.at || 16;
      for (let p = 1; p <= stop; p++) {
        const th = THEOREMS.find((t) => t.at === p);
        F.count('checked');
        if (th) { F.count('thm'); listed.push(th.text); }
        const hit = tg.at === p;
        if (!hit && !th && p % 3 !== 0 && p !== stop) continue; // skip some dull candidates to keep the pace
        F.add({ items: scene(p, hit ? [2] : [1], { found: hit, targetCls: hit ? 'good' : 'act' }).items, say: hit ? 'Candidate #' + p + ' is a valid proof of the target, "' + tg.text + '". The search stops: found.' : th ? 'Candidate #' + p + ' checks out: it proves "' + th.text + '", not the target. Keep going.' : 'Candidate #' + p + ' is not a valid proof. Keep going.', phase: 'search', hl: { sys: [1] }, mark: hit ? 'found' : undefined });
      }
      if (tg.kind === 'true') {
        F.add({ items: scene(stop, [], { found: true, targetCls: 'good' }).items.concat([card('g:end', 0, scene(stop, []).bottom + 10, W, 'If a statement has a proof, this search finds it, eventually. The set of theorems is recognisable: listable by a machine. The question is whether every true statement is among them.', '')]), say: 'Every provable statement turns up sooner or later. Theorems form a recognisable set. Are all true statements theorems?', phase: 'search', hl: { sys: [2] } });
      }
      // ---- the link to halting: run M and search for a proof that M never halts, side by side ----
      if (tg.kind === 'halts' || tg.kind === 'loops') {
        const loops = tg.kind === 'loops';
        const Mn = loops ? 'L' : 'B';
        const two = (step, done) => {
          const a = K.mbox.draw({ prefix: 'r', x: 0, y: 0, w: 210, title: 'Run ' + Mn + ' on the blank tape', lines: ['one step at a time…'], hot: done === 'run' ? [0] : [], cls: done === 'run' ? 'good' : 'r0', outs: [] });
          const b = K.mbox.draw({ prefix: 's', x: a.box.w + 20, y: 0, w: 210, title: 'Prove "' + Mn + ' never halts"', lines: ['try proof #1, #2, …'], hot: done === 'proof' ? [0] : [], cls: done === 'proof' ? 'good' : 'r3', outs: [] });
          a.items[0].pick = true; b.items[0].pick = true;
          const y = Math.max(a.all.h, b.all.h) + 26;
          const items = a.items.concat(b.items, [card('h:step', 0, y, 440, step, done ? 'good' : '')]);
          return items;
        };
        F.add({ items: two('Alternate: one step of the run, one proof candidate, one step, one candidate, …', null), say: 'Now a thought experiment. To decide whether ' + Mn + ' halts, run two searches side by side: run ' + Mn + ' itself, and look for a proof that ' + Mn + ' never halts.', phase: 'pair', hl: { link: [0] }, meta: { finisher: loops ? 's:box' : 'r:box' } });
        F.add({ items: two(loops ? 'The run of L never ends, but the proof search reaches #12: "machine L never halts". Answer: L does not halt.' : 'The run of B halts after a few steps. Answer: B halts. (A halting run can always be written down as a proof.)', loops ? 'proof' : 'run'), say: loops ? 'L never halts, so the left side runs for ever, but here a proof exists and the right side finds it.' : 'B halts, so the left side finishes. A halting machine always finishes this way.', phase: 'pair', hl: { link: [1] } });
        F.add({ items: two('If every true "M never halts" had a proof, one side would always finish, for every M: a decider for halting. The halting problem is undecidable, so some machine never halts with no proof of that fact: a true statement the system cannot prove.', 'x').map((it) => (it.key === 'h:step' ? Object.assign(it, { cls: 'card bad' }) : it)), say: 'If every true "M never halts" were provable, the pair would decide halting for every machine. It cannot, so for some machine that truly never halts, no proof exists. If the system is sound, it is incomplete.', phase: 'pair', mark: 'incomplete', hl: { link: [2, 3] } });
      }
      // ---- the sentence about itself ----
      if (tg.kind === 'self') {
        const y = 0, w = 210;
        const branch = (lit) => [
          card('b:intro', 0, y, 440, 'G says: "the search for a proof of G never succeeds". Two cases.', 'act'),
          card('b:yes', 0, y + 80, w, 'Case 1: the search finds a proof of G. Then G is false (its search succeeded), yet proved: the system proves something false.', lit === 'yes' ? 'bad' : '', { pick: true, dim: lit === 'no' }),
          card('b:no', 230, y + 80, w, 'Case 2: the search never succeeds. Then what G says is true, and G has no proof: a true, unprovable sentence.', lit === 'no' ? 'good' : '', { pick: true, dim: lit === 'yes' }),
        ];
        F.add({ items: branch(null), say: 'The search for a proof of G has run past every theorem shown and found nothing. It may never stop. Look at what G says about itself.', phase: 'self', hl: { self: [0] } });
        F.add({ items: branch('yes'), say: 'If a proof of G turned up, G would be false, since it claims no proof turns up. A system that only proves true statements cannot do that.', phase: 'self', hl: { self: [1] } });
        F.add({ items: branch('no'), say: 'So, for a system that proves only true things, the search never succeeds: G is true, and has no proof. The system is incomplete.', phase: 'self', mark: 'true but unprovable', hl: { self: [2] } });
      }
      const fine = card('fine', 0, 0, 440, 'An intuition, not the proof. The hard part of the real theorem is building a sentence that really does talk about its own proofs, using arithmetic alone; and the full result needs only consistency, not soundness. What it does not say: that truth is unknowable, or that any particular question is out of reach of every system — a stronger system can prove G, and then has its own G.', 'act');
      F.add({ items: [fine], say: 'A word of care: this is the idea, not the proof. The real construction makes arithmetic talk about its own proofs, and it needs fewer assumptions than we used. Any stronger system has its own unprovable sentence.', phase: 'fine', hl: { sys: [3] } });
      return { frames: viewPhases(F.list), def: { sections: [
        { id: 'sys', kind: 'math', title: 'Assumptions', text: 'proofs are checked by a machine\nso theorems can be listed by a machine\nsound: only true statements are provable\n(the full theorem needs only consistency)' },
        { id: 'link', kind: 'math', title: 'The link to halting', text: 'if M halts, its run is a proof that it halts\nif every true "M never halts" were provable,\nrunning M beside the proof search decides halting\nhalting is undecidable: some truths have no proof' },
        { id: 'self', kind: 'math', title: 'The sentence G', text: 'G ⇔ "the search for a proof of G never succeeds"\nproved ⇒ false ⇒ the system is unsound\nsound ⇒ never proved ⇒ G is true and unprovable' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && fr.some((x) => x.mark === 'found'), once: true, pick: 'option', options: ['Yes, eventually', 'Only if it is short', 'No, never'], ask: 'The target has a proof somewhere. Will this blind search, which tries every string in order, find it?', answer: () => 'Yes, eventually', explain: 'Every proof is some finite string, and the search tries every string in order, so it gets there eventually.' },
      { at: (f) => f.meta && f.meta.finisher, once: true, pick: 'item', ask: 'One step of each, in turn. Click the side that will finish.', answer: (fr, i) => fr[i].meta.finisher, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => f.phase === 'self' && i === fr.findIndex((x) => x.phase === 'self'), once: true, pick: 'item', ask: 'Assume the system only ever proves true statements. Click the case that is what really happens.', answer: () => 'b:no', explain: 'Case 1 would make the system prove a false sentence, so with a sound system only case 2 is left: G is true and unprovable.' },
    ],
    quiz: [
      { q: 'Why can a machine list all the theorems of a formal system?', options: ['Because theorems are short', 'Because whether a string is a valid proof can be checked mechanically, so it can try every string', 'Because every statement is a theorem', 'It cannot'], answer: 1, why: 'Try every string in order and check it; print what it proves. The theorems form a recognisable set.' },
      { q: 'If every true statement "M never halts" were provable, what would follow?', options: ['Nothing', 'Running M and the proof search side by side would decide halting', 'Every machine would halt', 'The system would be inconsistent'], answer: 1, why: 'If M halts, the run ends; if it never halts, a proof turns up. One always finishes, giving a decider, which cannot exist.' },
      { q: 'G says the search for a proof of G never succeeds. In a sound system, what is G?', options: ['False and provable', 'True and unprovable', 'False and unprovable', 'Neither true nor false'], answer: 1, why: 'A proof would make G false, and a sound system proves nothing false; so no proof exists, which is exactly what G says: true.' },
      { q: 'Which is NOT a fair conclusion from this card?', options: ['A sound system that can talk about machines leaves some truths unproved', 'Adding G as an axiom gives a stronger system with its own unprovable sentence', 'Some mathematical truths can never be known by any means', 'Provability is recognisable but not decidable'], answer: 2, why: 'Incompleteness is about one fixed system at a time; a stronger system can prove G. It does not say some truths are unknowable outright.' },
      { q: 'Machine B halts. Can the system always prove "B halts"?', options: ['Yes: the halting run itself can be written down as a proof', 'No, never', 'Only if B has few states', 'Only by luck'], answer: 0, why: 'A finished run is finite evidence that can be checked step by step. It is the never-halting side where proofs can be missing.' },
    ],
  });
})();
