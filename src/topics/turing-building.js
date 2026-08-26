// Building machines from parts: a small macro language whose every line becomes states and rules, and
// machines run one after the other by wiring the halting state of the first to the start of the second.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const TK = () => T.TK;

  T.family({ id: 'tm-build', part: 'turing', order: 20, title: 'Building machines', blurb: 'Nobody writes big transition tables by hand. Write statements that expand into states, and glue whole machines together, one after the other.' });

  // ======================================================================================================
  // The macro language: each line of the program becomes states, born next to it; then the result runs
  // ======================================================================================================
  const ENDS_B = 'alphabet: a b\n  seek R _\n  left\n  if b accept\n  reject';
  const SWAP = 'alphabet: a b\nnext:\n  if _ goto home\n  map a:b b:a\n  right\n  goto next\nhome:\n  left\n  seek L _\n  right\n  accept';
  const COPY = 'alphabet: a b\n  call copy\n  accept';
  const TWICE = 'alphabet: 0 1\n  call tm:bin-inc\n  call tm:bin-inc\n  accept';

  /** Which program line made each state of the compiled machine */
  function sources(res) {
    const M = res.machine;
    const own = new Map(), calls = [];
    for (const t of res.trace) {
      if (t.kind === 'stmt' && t.block === 'main') own.set(t.state, t.line);
      if (t.kind === 'inline' && t.block === 'main') calls.push(t);
    }
    const line = new Map();
    for (const q of M.states) {
      if (own.has(q)) { line.set(q, own.get(q)); continue; }
      const c = calls.find((x) => q.startsWith(x.prefix));
      if (c) { line.set(q, c.line); continue; }
      // a move of n cells makes states q~2 … q~n
      const base = q.replace(/~\d+$/, '');
      if (own.has(base)) line.set(q, own.get(base));
    }
    return line;
  }

  T.topic({
    id: 'tm-macro', family: 'tm-build', order: 10, title: 'A macro language for machines',
    blurb: 'Write seek R _, if b accept, call copy: each statement turns into a state with one rule per tape symbol, and a call pastes in a fresh copy of a whole machine. Then the result runs like any other.',
    inputs: [
      { id: 'p', kind: 'program', label: 'Program', def: ENDS_B, check: (v) => {
        const r = T.tmMacro.compile(v);
        if (r.errors.length) return 'Program: ' + (r.errors[0].line ? 'line ' + r.errors[0].line + ': ' : '') + r.errors[0].msg;
        if (r.machine.states.length > 40) return 'Program: it compiles to ' + r.machine.states.length + ' states; at most 40 fit the picture';
        if (String(v).split('\n').length > 16) return 'Program: at most 16 lines';
        return null;
      } },
      { id: 'w', kind: 'string', label: 'Input', def: 'aab', max: 6 },
    ],
    presets: [
      { label: 'Does it end in b? aab', values: { p: ENDS_B, w: 'aab' } },
      { label: 'Swap a and b, then go home', values: { p: SWAP, w: 'abba' } },
      { label: 'Call a subroutine: copy', values: { p: COPY, w: 'ab' } },
      { label: 'Call a machine twice: add 2', values: { p: TWICE, w: '101' } },
      { label: 'Ends in b? the empty string', values: { p: ENDS_B, w: '' } },
    ],
    check: (inp) => { const r = T.tmMacro.compile(inp.p); if (!r.machine) return null; const bad = [...inp.w].find((c) => !r.machine.input.includes(c)); return bad !== undefined ? 'Input: "' + bad + '" is not in the alphabet of the program' : null; },
    counters: [{ id: 'states', label: 'states' }, { id: 'rules', label: 'plain rules' }, { id: 'steps', label: 'steps run' }],
    run(inp) {
      const tk = TK();
      const res = T.tmMacro.compile(inp.p);
      const M = res.machine;
      const src = sources(res);
      const lines = String(inp.p).split('\n').map((l) => l.replace(/\s+$/, ''));
      const lst0 = tk.listing({ lines, x: 0, y: 0 });
      // the states as chips in a grid, in the order the lines make them
      const order = M.states.filter((q) => src.has(q)).sort((a, b) => src.get(a) - src.get(b));
      for (const q of M.states) if (!order.includes(q)) order.push(q);
      const COLS = 4, CWc = 112, CHc = 32, GX = lst0.box.w + 60, GY = 6;
      const groupOf = new Map();
      let gi = 0;
      for (const q of order) { const l = src.get(q); if (l !== undefined && !groupOf.has(l)) groupOf.set(l, ++gi); }
      const chipPos = (k) => ({ x: GX + (k % COLS) * (CWc + 10) + CWc / 2, y: GY + Math.floor(k / COLS) * (CHc + 10) + CHc / 2 });
      const short = (q) => (q.length > 12 ? '…' + q.slice(-11) : q);
      const rulesOf = (q) => M.rules.filter((r) => r.from === q).length;
      const chips = (born, hot, fromLine) => order.filter((q) => born.has(q)).map((q) => {
        const k = order.indexOf(q), p = chipPos(k), l = src.get(q);
        const halting = T.tm.isHalting(M, q);
        return { key: 'chip:' + q, kind: 'state', x: p.x, y: p.y, w: CWc, h: CHc, rx: 8, text: short(q), title: q + ': ' + rulesOf(q) + ' rules', cls: 'tu-chip ' + (hot === q ? 'hot' : halting ? (T.tm.isAccept(M, q) ? 'good' : 'bad') : 'tu-k' + (((groupOf.get(l) || 1) - 1) % 6 + 1)), size: 13, enter: fromLine ? 'fly' : 'fade', from: fromLine ? { x: lst0.box.x + lst0.box.w, y: lst0.lineY(fromLine - 1) } : undefined, pick: true };
      });
      const rows = Math.ceil(order.length / COLS);
      const tapeY = Math.max(lst0.box.y + lst0.box.h, GY + rows * (CHc + 10)) + 60;
      const F = new T.Frames(['states', 'rules', 'steps']);
      const born = new Set();
      const head = [{ key: 'h1', kind: 'text', x: 0, y: -24, text: 'PROGRAM', cls: 'title' }, { key: 'h2', kind: 'text', x: GX, y: -24, text: 'STATES IT BECOMES', cls: 'title' }];
      F.add({ items: tk.listing({ lines, x: 0, y: 0 }).items.concat(head), say: 'A program of ' + lines.filter((l) => l.trim()).length + ' lines. Each statement will turn into states and plain rules of an ordinary Turing machine, one line at a time.' });
      // the halting states exist from the start: accept and reject are where every program ends
      const byLine = new Map();
      for (const q of order) { const l = src.get(q); if (l === undefined) continue; if (!byLine.has(l)) byLine.set(l, []); byLine.get(l).push(q); }
      const stmtAt = new Map(res.trace.filter((t) => t.kind === 'stmt' && t.block === 'main').map((t) => [t.line, t]));
      const callAt = new Map(res.trace.filter((t) => t.kind === 'inline' && t.block === 'main').map((t) => [t.line, t]));
      let firstSeek = null;
      for (let ln = 1; ln <= lines.length; ln++) {
        const text = lines[ln - 1].trim();
        if (!text || /^(alphabet|tape|blank|name|start)\s*:/.test(text) || /^[A-Za-z_][\w.]*\s*:\s*$/.test(text)) continue;
        const qs = byLine.get(ln) || [];
        qs.forEach((q) => born.add(q));
        const nRules = qs.reduce((a, q) => a + rulesOf(q), 0);
        F.set('states', born.size).count('rules', nRules);
        let say;
        const st = stmtAt.get(ln), call = callAt.get(ln);
        if (call) say = 'Line ' + ln + ', ' + text + ': a call is not a jump to shared code. A fresh copy of ' + call.name.replace(/^tm:/, 'the machine ') + ' is pasted in, ' + qs.length + ' states named ' + call.prefix + '…, whose halting state leads on to the next line.';
        else if (st) say = 'Line ' + ln + ', ' + text + ' becomes state ' + st.state + ' with ' + st.rules.length + ' rules, one for each of the ' + M.gamma.length + ' tape symbols' + (/^seek/.test(text) ? ': on the symbols sought it moves on, on every other one it steps and stays in ' + st.state : /^if/.test(text) ? ': the symbols named jump, every other one falls through' : '') + '.';
        else if (/^(goto|accept|reject|halt)/.test(text)) say = 'Line ' + ln + ', ' + text + ', makes no state: the rules of the line before it lead straight to ' + (/^goto/.test(text) ? 'the label' : /^accept/.test(text) ? 'qa' : /^reject/.test(text) ? 'qr' : 'the end') + '.';
        else say = 'Line ' + ln + ': ' + text + '.';
        const fr = F.add({ items: tk.listing({ lines, x: 0, y: 0, hot: ln - 1 }).items.concat(head, chips(born, null, ln)), say, meta: { st } });
        if (st && !firstSeek && /^(seek|write|map|left|right|move)/.test(text)) firstSeek = { fr, n: st.rules.length, text };
      }
      for (const q of order) born.add(q);
      F.set('states', M.states.length).set('rules', M.rules.length);
      F.add({ items: tk.listing({ lines, x: 0, y: 0 }).items.concat(head, chips(born, null, null)), say: 'With the halting states qa and qr, the program is a machine of ' + M.states.length + ' states and ' + M.rules.length + ' plain rules over ' + M.gamma.length + ' tape symbols. Now run it on ' + (inp.w || 'ε') + '.' });
      // the run: the state's chip and the line that made it light up together
      const run = tk.trace(M, inp.w, { max: 60 });
      const N = 11, CW = 42;
      const sc = K.tape.scroller({ cells: N, origin: -2 });
      const runScene = (cfg, headCls) => {
        const l = src.get(cfg.state);
        return tk.listing({ lines, x: 0, y: 0, hot: l ? l - 1 : null }).items.concat(head, chips(born, cfg.state, null), tk.tape(cfg, { state: cfg.state.length > 9 ? '…' + cfg.state.slice(-8) : cfg.state, cells: N, cw: CW, origin: sc.at(cfg.heads[0].p), prevOrigin: sc.prev, x: 0, y: tapeY, label: '', headCls }).items);
      };
      F.add({ items: runScene(run.list[0].cfg), say: 'Start in ' + M.start + ', the state of the first statement, with ' + (inp.w || 'ε') + ' on the tape.' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        F.count('steps');
        const l = src.get(rule.from);
        F.add({ items: runScene(cfg), say: tk.sayRule(rule) + (l ? ' (That state came from line ' + l + ', ' + lines[l - 1].trim() + '.)' : '') });
      }
      const ok = run.verdict === 'accept';
      F.add({ items: runScene(run.last, ok ? 'good' : 'bad'), say: run.verdict === 'limit' ? 'Still running after 60 steps; the picture stops here.' : 'The machine halts in ' + run.last.state + ': ' + (ok ? 'accept' : 'reject') + (ok && M.output ? '' : '') + '. The tape reads ' + tk.word(tk.contents(run.last, 0)) + '.', mark: ok ? 'accepted' : 'rejected' });
      if (firstSeek) {
        const opts = [...new Set([firstSeek.n, 1, 2, firstSeek.n * 2])].map(String);
        const i = F.list.indexOf(firstSeek.fr) - 1;
        if (i >= 0) F.list[i].predict = { ask: 'The next line is ' + firstSeek.text + '. How many plain rules will it become?', options: opts.sort((a, b) => a - b), answer: String(firstSeek.n), explain: 'A state needs a rule for every symbol it might read, and there are ' + M.gamma.length + ' tape symbols: ' + M.gamma.map(tk.sym).join(' ') + '.', pick: 'option' };
      }
      const stmtRows = res.trace.filter((t) => t.kind === 'stmt' && t.block === 'main').map((t) => [String(t.line), t.text, t.state, String(t.rules.length)]);
      return { frames: F.list, def: { sections: [
        { id: 'lang', kind: 'text', title: 'The statements', text: 'left, right, write s, map a:b, seek L|R s1|s2, if s goto label (or accept, reject), goto, accept, reject, call name. Inside a subroutine, halt returns to the caller. Subroutines are pasted in, so recursion is not allowed.' },
        { id: 'stmts', kind: 'table', title: 'Lines of the main program', colHead: ['line', 'statement', 'state', 'rules'], rows: stmtRows.length ? stmtRows : [['–', '–', '–', '–']] },
        { id: 'sum', kind: 'math', title: 'The machine', text: M.states.length + ' states, ' + M.rules.length + ' rules\nΓ = {' + M.gamma.map(tk.sym).join(', ') + '}' },
      ] } };
    },
    quiz: [
      { q: 'Why does seek R _ become a state with one rule per tape symbol?', options: ['To make the machine faster', 'The machine must say what to do on every symbol it could read: step on, or stop seeking', 'Because seek is recursive', 'It does not; it is one rule'], answer: 1, why: 'On _ it moves on to the next statement; on every other symbol it moves right and stays in the same state.' },
      { q: 'A subroutine is called from two places. How many copies of its states end up in the machine?', options: ['One, shared', 'Two', 'It depends on the input', 'None: calls are free'], answer: 1, why: 'A Turing machine has no return stack, so each call site gets its own copy whose halting state leads back to the right place.' },
      { q: 'Why can a subroutine in this language not call itself?', options: ['It would be too slow', 'Pasting copies of itself into itself would never finish', 'Recursion is uncomputable', 'It can'], answer: 1, why: 'Calls are expanded by copying. A recursive call would need infinitely many copies. (A machine can still compute recursive functions, with a stack kept on the tape.)' },
      { q: 'What does goto label turn into?', options: ['A state that moves', 'Nothing of its own: rules that would go to it go straight to the label\'s state', 'A new tape symbol', 'An accept state'], answer: 1, why: 'A jump only changes where arrows point, so it costs no state and no step.' },
    ],
  });

  // ======================================================================================================
  // Two machines in a row: the first one's halting state becomes the second one's start
  // ======================================================================================================
  const PAIRS = {
    neg: { a: 'complement', b: 'bin-inc', title: 'flip every bit, then add one', alpha: '01', what: 'the two\'s-complement negation' },
    two: { a: 'bin-inc', b: 'bin-inc', title: 'add one, then add one again', alpha: '01', what: 'adding two' },
    odd: { a: 'unary-double', b: 'unary-inc', title: 'double, then add one', alpha: '1', what: 'n ↦ 2n + 1 in unary' },
  };
  function rename(M, pre) {
    return M.rules.map((r) => ({ from: pre + r.from, read: r.read.slice(), to: pre + r.to, write: r.write.slice(), move: r.move.slice() }));
  }
  T.topic({
    id: 'tm-combine', family: 'tm-build', order: 20, title: 'Running machines one after another',
    blurb: 'To run M₁ and then M₂, rename their states apart and send every move into M₁\'s halting state to M₂\'s start instead. The combined machine is an ordinary machine.',
    inputs: [
      { id: 'pair', kind: 'choice', label: 'Machines', def: 'neg', options: Object.entries(PAIRS).map(([value, p]) => ({ value, label: p.title })) },
      { id: 'w', kind: 'string', label: 'Input', def: '0110', max: 6, check: (v, inp) => ([...v].some((c) => !PAIRS[inp.pair].alpha.includes(c)) ? 'Input: use only ' + [...PAIRS[inp.pair].alpha].join(' and ') : null) },
    ],
    presets: [
      { label: 'Negate 0110 (6 becomes −6)', values: { pair: 'neg', w: '0110' } },
      { label: 'Negate 0000: the carry falls off', values: { pair: 'neg', w: '0000' } },
      { label: 'Add two to 1011', values: { pair: 'two', w: '1011' } },
      { label: 'Add two to 111', values: { pair: 'two', w: '111' } },
      { label: '2n + 1 with n = 2', values: { pair: 'odd', w: '11' } },
      { label: '2n + 1 with n = 0', values: { pair: 'odd', w: '' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 's1', label: 'steps in M₁' }, { id: 's2', label: 'steps in M₂' }],
    run(inp) {
      const tk = TK();
      const P = PAIRS[inp.pair];
      const A = T.tmLib.get(P.a), B = T.tmLib.get(P.b);
      const hA = A.accept.concat(A.halt), hB = B.accept.concat(B.halt);
      // the glued machine: A's halting state is replaced by B's start
      const glue = (q) => (hA.includes(q.slice(2)) && q.startsWith('A.') ? 'B.' + B.start : q);
      const rules = rename(A, 'A.').map((r) => Object.assign(r, { to: glue(r.to) })).concat(rename(B, 'B.'));
      const C = T.tm.fromRules({ name: 'combined', start: 'A.' + A.start, accept: hB.map((q) => 'B.' + q), input: [...P.alpha], output: 'tape' }, rules);
      // positions: A on the left, B on the right
      const dA = tk.diagram(A), dB = tk.diagram(B);
      const ren = (d, pre) => ({ kind: 'tm', states: d.states.map((q) => pre + q), start: pre + d.start, accept: d.accept.map((q) => pre + q), trans: d.trans.map((t) => ({ from: pre + t.from, to: pre + t.to, label: t.label })), pos: {} });
      const rA = ren(dA, 'A.'), rB = ren(dB, 'B.');
      const pA = K.graph.layout(rA, { gapX: 140 }).pos, pB = K.graph.layout(rB, { gapX: 140 }).pos;
      const bx = (pos) => { const xs = Object.values(pos).map((p) => p.x), ys = Object.values(pos).map((p) => p.y); return { x0: Math.min(...xs), x1: Math.max(...xs), y0: Math.min(...ys), y1: Math.max(...ys) }; };
      const ba = bx(pA), bb = bx(pB);
      const dx = ba.x1 - bb.x0 + 220, dy = (ba.y0 + ba.y1) / 2 - (bb.y0 + bb.y1) / 2;
      const pos = Object.assign({}, pA);
      for (const q in pB) pos[q] = { x: pB[q].x + dx, y: pB[q].y + dy };
      const pad = 62;
      const boxA = { x: ba.x0 - pad, y: Math.min(ba.y0, bb.y0 + dy) - pad - 62, w: ba.x1 - ba.x0 + 2 * pad, h: 0 };
      const boxB = { x: bb.x0 + dx - pad, y: boxA.y, w: bb.x1 - bb.x0 + 2 * pad, h: 0 };
      boxA.h = boxB.h = Math.max(ba.y1, bb.y1 + dy) - boxA.y + pad + 20;
      const short = (q) => q.slice(2);
      const regions = (hot) => [
        { key: 'boxA', kind: 'region', x: boxA.x, y: boxA.y, w: boxA.w, h: boxA.h, text: 'M₁: ' + P.a, cls: 'tu-box' + (hot === 'A' ? ' hot' : '') },
        { key: 'boxB', kind: 'region', x: boxB.x, y: boxB.y, w: boxB.w, h: boxB.h, text: 'M₂: ' + P.b, cls: 'tu-box2' + (hot === 'B' ? ' hot' : '') },
      ];
      const apart = (named) => K.graph.draw(rA, { pos, prefix: 'c', labelOf: named ? null : short }).items.concat(K.graph.draw(rB, { pos, prefix: 'c', hideStart: true, labelOf: named ? null : short }).items);
      const dC = tk.diagram(C);
      const ty = boxA.y + boxA.h + 60, N = 11, CW = 44;
      const tx = (boxA.x + boxB.x + boxB.w) / 2 - (N * CW) / 2;
      const sc = K.tape.scroller({ cells: N, origin: -2 });
      const F = new T.Frames(['steps', 's1', 's2']);
      const run = tk.trace(C, inp.w, { max: 200 });
      const tapeItems = (cfg, headCls) => tk.tape(cfg, { state: cfg.state, cells: N, cw: CW, origin: sc.at(cfg.heads[0].p), prevOrigin: sc.prev, x: tx, y: ty, label: 'tape', headCls }).items;
      F.add({ items: regions().concat(apart(false), tapeItems(run.list[0].cfg)), say: 'Two machines: M₁ (' + P.a + ') and M₂ (' + P.b + '). Run on their own, M₁ halts in ' + hA.join(', ') + ' and M₂ starts in ' + B.start + '. The plan: ' + P.title + '.' });
      F.add({ items: regions().concat(apart(true), tapeItems(run.list[0].cfg)), say: 'First rename every state apart, A. for M₁ and B. for M₂' + (P.a === P.b ? ': the same machine used twice needs two copies, or the second run would wander back into the first' : '') + '.' });
      const exits = {};
      for (const q of hA) exits['c:s:A.' + q] = { exit: 'into', into: 'c:s:B.' + B.start };
      const glued = K.graph.draw(dC, { pos, prefix: 'c', hot: ['B.' + B.start] });
      F.add({ items: regions().concat(glued.items, tapeItems(run.list[0].cfg)), exits, say: 'Now the glue: ' + hA.map((q) => 'A.' + q).join(', ') + ' disappears, and every move that went into it goes to B.' + B.start + ' instead. When M₁ would halt, M₂ starts, on the tape M₁ left behind.' });
      let s1 = 0;
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        const inA = rule.from.startsWith('A.');
        F.count('steps').count(inA ? 's1' : 's2');
        if (inA) s1++;
        const handover = inA && cfg.state.startsWith('B.');
        F.add({ items: regions(inA ? 'A' : 'B').concat(K.graph.draw(dC, { pos, prefix: 'c', active: [cfg.state], taken: [rule.from + '>' + rule.to] }).items, tapeItems(cfg)), say: (handover ? 'Hand-over: ' : '') + tk.sayRule(rule) + (handover ? ' M₁ is done and M₂ takes the tape from here, head and all.' : ''), meta: { handover } });
      }
      const out = T.tm.outputOf(C, run.last);
      F.add({ items: regions().concat(K.graph.draw(dC, { pos, prefix: 'c', good: [run.last.state] }).items, tapeItems(run.last, 'good')), say: 'M₂ halts with ' + (out || 'ε') + ' on the tape after ' + (run.list.length - 1) + ' steps, ' + s1 + ' of them in M₁. That is ' + P.what + ' of ' + (inp.w || 'ε') + (inp.pair === 'neg' && /^0+$/.test(inp.w) ? ': the carry ran past the left end, a digit the fixed width would drop' : '') + '.', mark: 'halted' });
      const hand = F.list.findIndex((f) => f.meta && f.meta.handover);
      if (hand > 3) F.list[hand - 1].predict = { ask: 'M₁ is about to finish. Click the state the machine will be in after this step.', answer: 'c:s:B.' + B.start, explain: 'Moves that went to M₁\'s halting state now go to M₂\'s start, B.' + B.start + '.', pick: 'item' };
      const def = tk.defOf(C, { title: 'The combined machine' });
      return { frames: F.list, def: { sections: def.sections.concat([{ id: 'how', kind: 'text', title: 'The construction', text: 'States of M₁ get the prefix A., states of M₂ the prefix B. Every rule of M₁ that enters a halting state enters B.start instead; M₂\'s rules are kept. The start is A.start and the halting states are M₂\'s. The machine has |Q₁| + |Q₂| − 1 states.' }]) } };
    },
    quiz: [
      { q: 'Why must the states of the two machines be renamed apart?', options: ['For neatness', 'If both have a state q0, the combined machine could not tell which machine\'s q0 is meant', 'To make it faster', 'They need not be'], answer: 1, why: 'A shared name would merge two different states and mix up the two machines\' rules.' },
      { q: 'Where is the head when M₂ starts?', options: ['On the first cell', 'Wherever M₁ left it', 'At the right end', 'On a fresh tape'], answer: 1, why: 'Nothing is reset: M₂ starts on M₁\'s tape, with the head where M₁ halted. M₂ must be written to cope with that (bin-inc first walks to the right end anyway).' },
      { q: 'Flip every bit, then add one: what does this do to a number in two\'s complement?', options: ['Doubles it', 'Negates it', 'Adds one', 'Nothing'], answer: 1, why: 'In two\'s complement −x is the bitwise complement of x plus one.' },
      { q: 'If M₁ never halts on some input, what does the combined machine do?', options: ['Runs M₂ anyway', 'Never halts either', 'Rejects', 'Accepts'], answer: 1, why: 'M₂ only starts when M₁ reaches its halting state; if that never happens, neither does M₂.' },
    ],
  });
})();
