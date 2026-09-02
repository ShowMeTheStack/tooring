// Reductions: a mapping reduction as a machine that writes machines (the transformer f taking ⟨M, w⟩ to
// a new machine with M built into it, then a test bench showing the "exactly when"), the direction of a
// reduction and what flows along it, and Turing reductions, where a decider may ask an oracle questions.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'reductions', part: 'computability', order: 40, title: 'Reductions', blurb: 'Turn questions about one problem into questions about another: a reduction is a machine that writes machines, and it carries undecidability forwards and decidability backwards.' });

  // ---------- small drawing helpers shared by this file ----------
  const eps = (s) => (s === '' ? 'ε' : s);
  /** A card of text: one or more lines centred in a rounded box */
  function card(key, x, y, lines, opts) {
    opts = opts || {};
    lines = [].concat(lines);
    const w = opts.w || Math.ceil(Math.max(...lines.map((l) => Geo.textWidth(l, 15, { bold: true }))) + 34);
    const h = opts.h || lines.length * 22 + 22;
    const it = { key, kind: 'cell', x, y, w, h, size: 15, rx: 12, cls: 'card ' + (opts.cls || ''), pick: !!opts.pick };
    if (lines.length > 1) it.lines = lines; else it.text = lines[0];
    if (opts.enter) it.enter = opts.enter;
    return it;
  }
  /** All strings over an alphabet by length: the rows of a language picture */
  const byLength = (al, n) => { const rows = [['']]; for (let l = 1; l <= n; l++) rows.push(rows[l - 1].flatMap((s) => al.map((a) => s + a))); return rows; };
  /**
   * A language picture: every string up to length n, one row per length, each cell lit by clsOf(s).
   * Returns {items, box}.
   */
  function strip(P, x, y, al, n, clsOf, title, mark) {
    const rows = byLength(al, n);
    const CW = n >= 4 ? 40 : 46, GAP = 4, CH = 34;
    const widest = rows[rows.length - 1].length * (CW + GAP) - GAP;
    const items = [];
    if (title) items.push({ key: P + ':title', kind: 'text', x: x + widest / 2, y: y - 12, text: title, anchor: 'middle', cls: 'title' });
    rows.forEach((r, l) => {
      const rw = r.length * (CW + GAP) - GAP, x0 = x + (widest - rw) / 2;
      r.forEach((s, k) => {
        items.push({ key: P + ':s:' + (s || 'ε'), kind: 'cell', x: x0 + k * (CW + GAP), y: y + l * (CH + GAP), w: CW, h: CH, text: eps(s), size: n >= 4 ? 12 : 14, cls: 'mono ' + (clsOf(s) || '') + (mark !== undefined && mark === s ? ' ring' : ''), rx: 5, pick: true });
      });
    });
    return { items, box: { x, y: y - 24, w: widest, h: rows.length * (CH + GAP) + 24 } };
  }
  /** Give each phase of a run one camera: the box around all the frames of that phase */
  function phaseViews(frames) {
    const boxes = new Map();
    for (const f of frames) { const b = T.stageBounds(f.items); if (!b) continue; const p = f.phase || 0; boxes.set(p, boxes.has(p) ? Geo.union([boxes.get(p), b]) : b); }
    for (const f of frames) if (boxes.has(f.phase || 0)) f.view = boxes.get(f.phase || 0);
  }
  T.compDraw = Object.assign(T.compDraw || {}, { card, strip, byLength, phaseViews });

  // ---------- the machines M may be ----------
  const MACHINES = [
    { value: 'contains-11', label: 'M: contains 11 (always halts)' },
    { value: 'anbn', label: 'M: aⁿbⁿ (always halts)' },
    { value: 'aa-recogniser', label: 'M: contains aa (loops otherwise)' },
    { value: 'even-length', label: 'M: even length (always halts)' },
  ];
  const getM = (id) => Object.assign({}, T.tmLib.get(id), { name: 'M' });
  const alphaOf = (id) => T.tmLib.entry(id).alphabet;
  const run = (M, x) => T.tm.run(M, x, { maxSteps: 4000, trace: false }).verdict;
  const said = (v) => ({ accept: 'accepts', reject: 'rejects', loop: 'loops for ever', limit: 'has not stopped after 4000 steps' }[v] || v);
  const lampOf = (v) => (v === 'accept' ? 'accept' : v === 'reject' ? 'reject' : 'loop');

  // what each reduction is about, and the twist its picture shows
  const RED = {
    'ATM-HALT': { A: 'A_TM', B: 'HALT_TM', Adef: '{⟨M, w⟩ : M accepts w}', Bdef: '{⟨M, w⟩ : M halts on w}', out: (w) => '⟨M′, ' + eps(w) + '⟩', names: ['M′'],
      twist: 'The one change: where M would reject, M′ loops for ever instead. So M′ halts exactly when M accepts.' },
    'ATM-coETM': { A: 'A_TM', B: 'the complement of E_TM', Adef: '{⟨M, w⟩ : M accepts w}', Bdef: '{⟨M⟩ : L(M) ≠ ∅}', out: () => '⟨M₁⟩', names: ['M₁'],
      twist: 'M₁ is a gate: it turns every x other than w away at once, so its language is {w} when M accepts w and ∅ otherwise.' },
    'ATM-REGULAR': { A: 'A_TM', B: 'REGULAR_TM', Adef: '{⟨M, w⟩ : M accepts w}', Bdef: '{⟨M⟩ : L(M) is regular}', out: () => '⟨M₂⟩', names: ['M₂'],
      twist: 'M₂ always lets in the strings 0ⁿ1ⁿ; everything else gets in only if M accepts w. So L(M₂) is Σ* (regular) or 0ⁿ1ⁿ (not regular).' },
    'HALT-EQTM': { A: 'HALT_TM', B: 'EQ_TM', Adef: '{⟨M, w⟩ : M halts on w}', Bdef: '{⟨M₁, M₂⟩ : L(M₁) = L(M₂)}', out: () => '⟨M₁, M₂⟩', names: ['M₁', 'M₂'],
      twist: 'M₁ accepts everything. M₂ first waits for M to halt on w, then accepts: if M never halts, M₂ accepts nothing.' },
  };

  T.topic({
    id: 'red-transformer', family: 'reductions', order: 10, title: 'A reduction writes a machine',
    blurb: 'A mapping reduction is a program that reads ⟨M, w⟩ and writes out a new machine with M built into it. It never runs M. Then a test bench shows the new machine is in B exactly when M accepts (or halts on) w.',
    camera: 'follow',
    inputs: [
      { id: 'r', kind: 'choice', label: 'Reduction', def: 'ATM-HALT', options: [
        { value: 'ATM-HALT', label: 'A_TM ≤ HALT_TM' }, { value: 'ATM-coETM', label: 'A_TM ≤ complement of E_TM' },
        { value: 'ATM-REGULAR', label: 'A_TM ≤ REGULAR_TM' }, { value: 'HALT-EQTM', label: 'HALT_TM ≤ EQ_TM' }] },
      { id: 'm', kind: 'choice', label: 'Machine M', def: 'contains-11', options: MACHINES },
      { id: 'w', kind: 'string', label: 'w', def: '011', max: 5 },
    ],
    check: (inp) => { const al = alphaOf(inp.m); const bad = [...inp.w].find((c) => !al.includes(c)); return bad !== undefined ? 'w: "' + bad + '" is not in this M\'s alphabet {' + al.join(', ') + '}' : null; },
    presets: [
      { label: 'A_TM ≤ HALT: M accepts w', values: { r: 'ATM-HALT', m: 'contains-11', w: '011' } },
      { label: 'A_TM ≤ HALT: M rejects w', values: { r: 'ATM-HALT', m: 'anbn', w: 'aab' } },
      { label: 'A_TM ≤ co-E_TM: M loops on w', values: { r: 'ATM-coETM', m: 'aa-recogniser', w: 'ab' } },
      { label: 'A_TM ≤ REGULAR: M accepts w', values: { r: 'ATM-REGULAR', m: 'anbn', w: 'ab' } },
      { label: 'A_TM ≤ REGULAR: M rejects w', values: { r: 'ATM-REGULAR', m: 'contains-11', w: '10' } },
      { label: 'HALT ≤ EQ_TM: w = ε', values: { r: 'HALT-EQTM', m: 'aa-recogniser', w: '' } },
    ],
    counters: [{ id: 'lines', label: 'lines written' }, { id: 'tests', label: 'inputs tried' }],
    run(inp) {
      const R = RED[inp.r], M = getM(inp.m), w = inp.w, al = alphaOf(inp.m), entry = T.tmLib.entry(inp.m);
      const red = T.comp.reduce(inp.r, M, w);
      const ms = red.machines;
      const mw = run(M, w);
      const truth = inp.r === 'HALT-EQTM' ? mw === 'accept' || mw === 'reject' : mw === 'accept';
      const F = new T.Frames(['lines', 'tests']);
      const xAl = inp.r === 'ATM-REGULAR' ? ['0', '1'] : al;
      const fLines = ['1. Read ⟨M, w⟩ as plain text.', '2. Write out the text of ' + R.names.join(' and ') + '.', '3. Output ' + R.out(w) + '. Never run M.'];
      const mDesc = { title: 'M, copied in: ' + entry.title.replace(/ \(.*\)$/, ''), cls: 'r2', lines: [entry.kind === 'recogniser' ? 'may loop instead of rejecting' : 'halts on every input'] };
      const runIx = (m) => m.lines.findIndex((l) => /Run M/.test(l));
      // the output machines, stacked; shown: how many lines of each are written so far
      const FX = 130; // room for the arrows coming in from the left
      const fBox = (hot, extra) => K.mbox.draw(Object.assign({ prefix: 'f', x: FX, y: 0, w: 380, title: 'f, the transformer', tag: 'always halts', input: '⟨M, ' + eps(w) + '⟩', lines: fLines, hot: hot }, extra || {}));
      const f0 = fBox([]);
      const outY = f0.box.y + f0.box.h + 86;
      const machinesAt = (y0, shown, state) => {
        const items = [];
        let y = y0;
        const boxes = [];
        ms.forEach((m, k) => {
          const n = shown[k];
          if (n <= 0) return;
          const st = state && state[k];
          const at = st ? st.at : -1;
          const inner = n >= m.lines.length && runIx(m) >= 0 ? [Object.assign({}, mDesc, { prefix: 'm' + k + ':M', hot: at === runIx(m) ? [0] : [], cls: at === runIx(m) ? 'r2 hot' : 'r2' })] : [];
          const b = K.mbox.draw({ prefix: 'm' + k, x: FX, y, w: 380, title: R.names[k], lines: m.lines.slice(0, n), hot: at >= 0 ? [at] : [], inner, input: st ? 'x = ' + eps(st.x) : 'x', inLen: 110, outs: n >= m.lines.length ? K.mbox.answers(st ? lampOf(st.v) : null, { loop: true }) : [], enter: 'drop' });
          items.push(...b.items);
          boxes.push(b);
          y += b.box.h + 26;
        });
        return { items, boxes, bottom: y };
      };
      const frameAround = (mm, lit) => {
        if (!mm.boxes.length) return [];
        const u = Geo.union(mm.boxes.map((b) => b.box));
        return [{ key: 'outframe', kind: 'region', x: u.x - 14, y: u.y - 34, w: u.w + 28, h: u.h + 48, text: 'what f writes', cls: 'frame' + (lit ? ' hot' : ''), rx: 16 }];
      };
      const wire = (lit) => K.mbox.wire('fwire', { x: FX + 190, y: f0.box.y + f0.box.h + 2 }, { x: FX + 190, y: outY - 36 }, { label: R.out(w), lx: FX + 190 + Geo.textWidth(R.out(w), 15, { bold: true }) / 2 + 16, ly: f0.box.y + f0.box.h + 40, cls: lit ? 'hot' : '' });

      // phase 1: f writes the machine, line by line
      const total = ms.map((m) => m.lines.length);
      const shown = ms.map(() => 0);
      F.add({ phase: 1, items: fBox([0]).items, say: 'The instance is ⟨M, ' + eps(w) + '⟩ with M the machine for "' + entry.title + '": does M ' + (inp.r === 'HALT-EQTM' ? 'halt on' : 'accept') + ' ' + eps(w) + '? That is a question about ' + R.A + '. The transformer f will turn it into a question about ' + R.B + '.', hl: { def: [0, 1] } });
      ms.forEach((m, k) => {
        for (let n = 1; n <= total[k]; n++) {
          shown[k] = n;
          F.count('lines');
          const mm = machinesAt(outY, shown.slice());
          const line = m.lines[n - 1];
          F.add({ phase: 1, items: fBox([1]).items.concat(wire(true), frameAround(mm, true), mm.items), say: n === 1 ? 'f starts writing ' + R.names[k] + ': "' + line + '"' : n === total[k] && runIx(m) >= 0 ? 'f writes "' + line + '" and copies the text of M into ' + R.names[k] + ', so ' + R.names[k] + ' carries M inside it.' : 'f writes "' + line + '"', hl: { def: [2] } });
        }
      });
      const mmDone = machinesAt(outY, total);
      F.add({ phase: 1, items: fBox([2], { done: [0, 1] }).items.concat(wire(true), frameAround(mmDone, false), mmDone.items), say: 'f outputs ' + R.out(w) + ' and halts. It never ran M: it only wrote text, which is why f always halts, even when M would loop. ' + R.twist, hl: { def: [2, 4] } });

      // phase 2: the test bench
      let xs;
      if (inp.r === 'ATM-REGULAR') xs = ['', '01', '0011', '1', '10', '001'];
      else { const pool = [w].concat(byLength(al, 2).flat()); xs = [...new Set(pool)].slice(0, 5); }
      const rows = [];
      const benchHead = inp.r === 'ATM-HALT' ? ['x', 'M on x', 'M′ on x'] : inp.r === 'HALT-EQTM' ? ['x', 'M₁ on x', 'M₂ on x'] : ['x', 'stops at', R.names[0] + ' on x'];
      const short = (v) => ({ accept: 'accepts', reject: 'rejects', loop: 'loops ∞', limit: 'no answer' }[v]);
      const benchCls = (v) => (v === 'accept' ? 'good' : v === 'reject' ? 'bad' : 'hot');
      const benchY = machinesAt(outY, total).bottom + 30;
      const bench = (hotRow) => K.table.draw({ prefix: 'bench', x: FX, y: benchY, cw: 128, colHead: benchHead, rows: rows.map((r) => r.cells), size: 15, cls: (r, c) => (c === 0 ? 'mono' : rows[r].cls[c] || '') + (r === hotRow ? ' act' : '') }).items.concat([{ key: 'bench:title', kind: 'text', x: FX, y: benchY - 12, text: 'test bench', cls: 'title' }]);
      xs.forEach((x, k) => {
        const results = ms.map((m) => m.run(x, 4000));
        const state = results.map((r) => ({ x, at: r.at, v: r.verdict }));
        const mm = machinesAt(outY, total, state);
        F.count('tests');
        const cells = [eps(x)], cls = [''];
        if (inp.r === 'ATM-HALT') { const v = run(M, x); cells.push(short(v)); cls.push(benchCls(v)); }
        else if (inp.r !== 'HALT-EQTM') { cells.push('line ' + results[0].at); cls.push(''); }
        results.forEach((r) => { cells.push(short(r.verdict)); cls.push(benchCls(r.verdict)); });
        rows.push({ cells, cls });
        const r0 = results[0];
        let say;
        if (inp.r === 'ATM-HALT') say = 'On x = ' + eps(x) + ', M ' + said(run(M, x)) + ', so M′ ' + (r0.verdict === 'accept' ? 'accepts too' : r0.verdict === 'loop' ? 'loops for ever: a rejection has become a loop' : said(r0.verdict)) + '.';
        else if (inp.r === 'ATM-coETM') say = x !== w ? 'x = ' + eps(x) + ' is not ' + eps(w) + ', so M₁ rejects it at line 1 without running M.' : 'x = ' + eps(w) + ' gets past the gate, and M₁ runs M on ' + eps(w) + ': M ' + said(mw) + ', so M₁ ' + said(r0.verdict) + '.';
        else if (inp.r === 'ATM-REGULAR') say = r0.at === 1 ? eps(x) + ' has the form 0ⁿ1ⁿ, so M₂ accepts at line 1 whatever M does.' : eps(x) + ' is not of the form 0ⁿ1ⁿ, so M₂ runs M on ' + eps(w) + ': M ' + said(mw) + ', so M₂ ' + said(r0.verdict) + '.';
        else say = 'On x = ' + eps(x) + ': M₁ accepts, as always. M₂ runs M on ' + eps(w) + ', which ' + (mw === 'accept' || mw === 'reject' ? 'halts, so M₂ accepts.' : 'never halts, so M₂ never answers.');
        F.add({ phase: 2, items: mm.items.concat(bench(k)), say, meta: { lamp: 'm' + (inp.r === 'HALT-EQTM' ? 1 : 0) + ':o:' + lampOf((inp.r === 'HALT-EQTM' ? results[1] : r0).verdict), x }, hl: { def: [3] } });
      });

      // phase 3: the language of the new machine, and the "exactly when"
      const n = inp.r === 'ATM-REGULAR' ? 4 : 3;
      const langOf = (m) => (s) => m.run(s, 4000).verdict;
      const items3 = [];
      let sy = 30;
      const stripCls = (v) => (v === 'accept' ? 'good' : 'lout');
      if (inp.r === 'ATM-HALT') {
        const st = strip('lang0', 0, sy, al, n, (s) => { const v = langOf(ms[0])(s); return v === 'loop' || v === 'limit' ? 'hot' : 'good'; }, 'M′ halts (green) or loops (orange); w ringed', w);
        items3.push(...st.items); sy += st.box.h + 64;
      } else if (inp.r === 'HALT-EQTM') {
        for (let k = 0; k < 2; k++) { const st = strip('lang' + k, 0, sy, al, n, (s) => stripCls(langOf(ms[k])(s)), 'L(' + R.names[k] + ')'); items3.push(...st.items); sy += st.box.h + 64; }
      } else {
        const st = strip('lang0', 0, sy, xAl, n, (s) => stripCls(langOf(ms[0])(s)) + (inp.r === 'ATM-REGULAR' && /^0*1*$/.test(s) && s.indexOf('1') === s.length / 2 ? ' ring' : ''), 'L(' + R.names[0] + ')' + (inp.r === 'ATM-REGULAR' ? ': 0ⁿ1ⁿ ringed' : ': w ringed'), inp.r === 'ATM-coETM' ? w : undefined);
        items3.push(...st.items); sy += st.box.h + 64;
      }
      const sw = Math.max(...items3.filter((i) => i.kind === 'cell').map((i) => i.x + i.w));
      const lhs = (inp.r === 'HALT-EQTM' ? 'M halts on ' : 'M accepts ') + eps(w) + '?', rhs = R.out(w) + ' in ' + R.B + '?';
      const ans = (b) => (b ? 'yes' : 'no');
      const langSay = {
        'ATM-HALT': 'M′ halts on exactly the strings M accepts. Here M ' + said(mw) + ' on ' + eps(w) + ', so M′ ' + (truth ? 'halts' : 'does not halt') + ' on it.',
        'ATM-coETM': 'L(M₁) is ' + (truth ? '{' + eps(w) + '}, not empty,' : '∅,') + ' because M ' + said(mw) + ' on ' + eps(w) + '.',
        'ATM-REGULAR': truth ? 'M accepts ' + eps(w) + ', so every string gets in: L(M₂) = Σ*, a regular language.' : 'M ' + said(mw) + ' on ' + eps(w) + ', so only the 0ⁿ1ⁿ strings get in: L(M₂) = {0ⁿ1ⁿ}, which is not regular.',
        'HALT-EQTM': truth ? 'M halts on ' + eps(w) + ', so M₂ accepts everything too: the two languages are the same.' : 'M never halts on ' + eps(w) + ', so L(M₂) = ∅ while L(M₁) = Σ*: different.',
      }[inp.r];
      F.add({ phase: 3, items: items3, say: langSay, hl: { def: [3] } });
      const cy = sy;
      const cw = Math.max(200, (sw - 60) / 2, card('t', 0, 0, [lhs]).w, card('t', 0, 0, [rhs]).w);
      const c1 = card('claimL', 0, cy, [lhs, ans(truth)], { cls: truth ? 'good' : 'bad', w: cw });
      const c2 = card('claimR', c1.x + c1.w + 60, cy, [rhs, ans(truth)], { cls: truth ? 'good' : 'bad', w: cw });
      const iff = { key: 'iff', kind: 'text', x: c1.x + c1.w + 30, y: cy + 39, text: '⇔', anchor: 'middle', cls: 'big' };
      F.add({ phase: 3, items: items3.concat([c1, c2, iff]), say: 'Both answers are ' + ans(truth) + ', as the reduction promises: x ∈ ' + R.A + ' exactly when f(x) ∈ ' + R.B + '. So a decider for ' + R.B + ' would decide ' + R.A + ', which is impossible: ' + R.B + ' is undecidable.', mark: truth ? 'accepted' : 'rejected', meta: { truth }, hl: { def: [3, 4] } });
      phaseViews(F.list);
      return { frames: F.list, def: { sections: [
        { id: 'def', kind: 'math', title: 'The reduction', text: 'A = ' + R.A + ' = ' + R.Adef + '\nB = ' + R.B + ' = ' + R.Bdef + '\nf(⟨M, w⟩) = ' + R.out(w) + '\n⟨M, w⟩ ∈ A ⇔ f(⟨M, w⟩) ∈ B\nf is computable: it only writes text' },
        { id: 'mach', kind: 'text', title: 'M', text: entry.title + ': ' + (entry.blurb || '') + ' On w = ' + eps(w) + ' it ' + said(mw) + '.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => f.phase === 2 && fr[i + 1] && fr[i + 1].phase === 2 && fr[i + 1].meta && fr[i + 1].meta.lamp, once: true, pick: 'item', ask: (fr, i) => 'Next the machine runs on x = ' + eps(fr[i + 1].meta.x) + '. Click the lamp it will light.', answer: (fr, i) => fr[i + 1].meta.lamp, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => f.phase === 3 && i === fr.length - 2, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Is the machine f wrote in B?', answer: (fr) => (fr[fr.length - 1].meta.truth ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why does the transformer f always halt, even when M loops on w?', options: ['It runs M with a step limit', 'It never runs M: it only writes the text of a new machine', 'It asks a decider first', 'Because M is a decider'], answer: 1, why: 'f is a text-to-text program: it copies ⟨M⟩ and w into a template. Running the new machine is someone else\'s problem.' },
      { q: 'In A_TM ≤ HALT_TM, what does M′ do where M would reject?', options: ['Rejects', 'Accepts', 'Loops for ever', 'Halts with no answer'], answer: 2, why: 'Turning a rejection into a loop makes "halts" mean exactly "accepts".' },
      { q: 'In the reduction to REGULAR_TM, why does M₂ accept 0ⁿ1ⁿ no matter what?', options: ['So that L(M₂) is never empty', 'So that when M does not accept w, L(M₂) is exactly the non-regular 0ⁿ1ⁿ', 'Because 0ⁿ1ⁿ is regular', 'To make M₂ halt'], answer: 1, why: 'The two possible languages are Σ* (regular) and 0ⁿ1ⁿ (not regular); which one we get depends on whether M accepts w.' },
      { q: 'A_TM ≤ B has been shown. What follows?', options: ['B is decidable', 'B is undecidable', 'A_TM is decidable', 'Nothing'], answer: 1, why: 'A decider for B composed with f would decide A_TM, which has no decider.' },
      { q: 'In HALT_TM ≤ EQ_TM, when are L(M₁) and L(M₂) equal?', options: ['Always', 'Exactly when M halts on w', 'Exactly when M accepts w', 'Never'], answer: 1, why: 'M₁ accepts everything; M₂ accepts everything once M halts on w, and nothing if it never does.' },
    ],
  });

  // ---------- which way a reduction carries what ----------
  const CASES = {
    'atm-halt': { A: 'A_TM', B: 'HALT_TM', known: 'A', status: 'undecidable', goal: 'B', ok: true, by: 'M′ loops where M would reject' },
    'atm-etm': { A: 'A_TM', B: 'co-E_TM', known: 'A', status: 'undecidable', goal: 'B', ok: true, by: 'M₁ rejects every x ≠ w, then runs M on w' },
    'eqdfa-edfa': { A: 'EQ_DFA', B: 'E_DFA', known: 'B', status: 'decidable', goal: 'A', ok: true, by: 'build a DFA for the symmetric difference' },
    'halt-atm': { A: 'HALT_TM', B: 'A_TM', known: 'B', status: 'undecidable', goal: 'A', ok: false, by: 'M′ accepts whenever M halts', wrong: 'B being undecidable says nothing about A: an easy problem can also be turned into a hard one.', counter: 'A_DFA ≤ A_TM too (a DFA is a TM), yet A_DFA is decidable.' },
    'adfa-atm': { A: 'A_DFA', B: 'A_TM', known: 'B', status: 'undecidable', goal: 'A', ok: false, by: 'a DFA is a Turing machine that only moves right', wrong: 'Turning A_DFA into the hard problem A_TM proves nothing: A_DFA is in fact decidable.', counter: 'Simulate the DFA on w: it stops after |w| moves.' },
    'adfa-dec': { A: 'A_DFA', B: 'A_TM', known: 'A', status: 'decidable', goal: 'B', ok: false, by: 'a DFA is a Turing machine that only moves right', wrong: 'Knowing that A is easy says nothing about B: decidability flows backwards along ≤, not forwards.', counter: 'A_TM is undecidable, though the easy A_DFA reduces to it.' },
  };
  T.topic({
    id: 'red-direction', family: 'reductions', order: 20, title: 'Which way does a reduction point?',
    blurb: 'A ≤ B means "A is no harder than B". Decidability flows backwards along the arrow, from B to A; undecidability flows forwards, from A to B. Reduce the wrong way and the proof proves nothing.',
    inputs: [{ id: 'c', kind: 'choice', label: 'Argument', def: 'atm-halt', options: [
      { value: 'atm-halt', label: 'A_TM ≤ HALT_TM, A_TM undecidable' }, { value: 'atm-etm', label: 'A_TM ≤ co-E_TM, A_TM undecidable' },
      { value: 'eqdfa-edfa', label: 'EQ_DFA ≤ E_DFA, E_DFA decidable' }, { value: 'halt-atm', label: 'HALT_TM ≤ A_TM, A_TM undecidable' },
      { value: 'adfa-atm', label: 'A_DFA ≤ A_TM, A_TM undecidable' }, { value: 'adfa-dec', label: 'A_DFA ≤ A_TM, A_DFA decidable' }] }],
    presets: [
      { label: 'Right way: A_TM ≤ HALT_TM', values: { c: 'atm-halt' } },
      { label: 'Right way: EQ_DFA ≤ E_DFA', values: { c: 'eqdfa-edfa' } },
      { label: 'Wrong way: HALT_TM ≤ A_TM', values: { c: 'halt-atm' } },
      { label: 'Wrong way: A_DFA ≤ A_TM', values: { c: 'adfa-atm' } },
      { label: 'Right way, through a complement', values: { c: 'atm-etm' } },
    ],
    run(inp) {
      const C = CASES[inp.c];
      const F = new T.Frames();
      const W = 210, H = 92, GAP = 200;
      const bx = { A: 0, B: W + GAP };
      const col = { decidable: 'good', undecidable: 'bad' };
      const box = (id, st, extra) => card('p' + id, bx[id], 0, [C[id], st || '?'], Object.assign({ w: W, h: H, pick: true, cls: st ? col[st.replace(/^not /, '')] || '' : '' }, extra || {}));
      const arrow = (cls) => ({ key: 'arrow', kind: 'edge', from: 'pA', to: 'pB', label: 'f: ' + C.A + ' ≤ ' + C.B, lx: W + GAP / 2, ly: H / 2 - 18, cls: 'mflow ' + (cls || '') });
      const neither = card('neither', W + GAP / 2 - 80, H + 150, ['neither: no conclusion'], { w: 160 + 40, pick: true });
      neither.x = (2 * W + GAP) / 2 - neither.w / 2;
      const rule1 = card('r1', 0, H + 40, ['B decidable ⇒ A decidable'], { w: W + GAP / 2 - 10, cls: C.status === 'decidable' && C.known === 'B' ? 'good' : 'off' });
      const rule2 = card('r2', W + GAP / 2 + 10, H + 40, ['A undecidable ⇒ B undecidable'], { w: W + GAP / 2 - 10, cls: C.status === 'undecidable' && C.known === 'A' ? 'bad' : 'off' });
      const base = (a, b, extra) => [box('A', a), box('B', b), arrow(extra && extra.arrowCls)];
      F.add({ items: base(null, null).concat([neither]), say: 'f turns every instance of ' + C.A + ' into an instance of ' + C.B + ' (' + C.by + '), keeping the answer: x ∈ ' + C.A + ' exactly when f(x) ∈ ' + C.B + '. We write ' + C.A + ' ≤ ' + C.B + '.' });
      const kn = C.known, other = kn === 'A' ? 'B' : 'A';
      const st0 = { A: null, B: null };
      st0[kn] = C.status;
      F.add({ items: base(st0.A, st0.B).concat([neither]), say: 'What we know: ' + C[kn] + ' is ' + C.status + '. Which box can we colour from that?', meta: { ans: C.ok ? 'p' + other : 'neither' } });
      F.add({ items: base(st0.A, st0.B).concat([rule1, rule2, neither]), say: 'Only two things follow from A ≤ B: if B is decidable then so is A (run f, then B\'s decider), and if A is undecidable then so is B. Decidability flows backwards, undecidability forwards.' });
      if (C.ok) {
        const flows = C.known === 'A' ? 'forwards' : 'backwards';
        const tok = (t) => ({ key: 'tok', kind: 'token', x: C.known === 'A' ? t * (W + GAP) + W / 2 : (1 - t) * (W + GAP) + W / 2, y: -26, r: 11, cls: C.status === 'decidable' ? 'good' : 'bad' });
        F.add({ items: base(st0.A, st0.B, { arrowCls: 'hot' }).concat([rule1, rule2, tok(0.15)]), say: C[kn] + ' is ' + C.status + ' and it is the ' + (kn === 'A' ? 'source' : 'target') + ' of the arrow, so the colour flows ' + flows + ' along it.' });
        F.add({ items: base(st0.A, st0.B, { arrowCls: 'hot' }).concat([rule1, rule2, tok(0.85)]), say: 'Along the arrow …' });
        const st1 = Object.assign({}, st0); st1[other] = C.status;
        F.add({ items: base(st1.A, st1.B).concat([rule1, rule2]), say: 'So ' + C[other] + ' is ' + C.status + ' too. ' + (C.status === 'decidable' ? 'Its decider: compute f(x), then run ' + C.B + '\'s decider on it.' : 'If it had a decider, composing f with it would decide ' + C.A + '.'), mark: 'accepted' });
        const dec = K.mbox.draw({ prefix: 'dec', x: 0, y: H + 130, title: C.status === 'decidable' ? 'decider for ' + C.A : 'would-be decider for ' + C.A, input: 'x', lines: ['1. Compute f(x).'], inner: [{ title: (C.status === 'decidable' ? '' : 'claimed ') + 'decider for ' + C.B, cls: C.status === 'decidable' ? 'r1' : 'r4', lines: ['2. Run it on f(x); give its answer.'] }], outs: K.mbox.answers() });
        F.add({ items: base(st1.A, st1.B).concat(dec.items), say: C.status === 'decidable' ? 'The composed machine is a real decider for ' + C.A + ': f always halts and so does the decider for ' + C.B + '.' : 'This composed machine would decide ' + C.A + ', which is impossible. So no decider for ' + C.B + ' exists.' });
      } else {
        const bad = card('badproof', 0, H + 150, ['"' + C[kn] + ' is ' + C.status + ', so ' + C[other] + ' is ' + C.status + '" ✗'], { w: 2 * W + GAP, cls: 'bad' });
        F.add({ items: base(st0.A, st0.B, { arrowCls: 'bad' }).concat([rule1, rule2, bad]), say: 'The tempting proof: "' + C[kn] + ' is ' + C.status + ', so ' + C[other] + ' is too." Neither rule says that: ' + C.wrong });
        const cx = card('counter', 0, H + 240, [C.counter], { w: 2 * W + GAP, cls: 'act' });
        F.add({ items: base(st0.A, st0.B).concat([rule1, rule2, bad, cx]), say: 'A counterexample to that reasoning: ' + C.counter + ' To learn something about ' + C[other] + ', reduce the other way round.', mark: 'rejected' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'def', kind: 'math', title: 'A ≤ B', text: 'a computable f with x ∈ A ⇔ f(x) ∈ B\nB decidable ⇒ A decidable\nA undecidable ⇒ B undecidable\nB recognisable ⇒ A recognisable' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ans, once: true, pick: 'item', ask: 'Click the box whose status now follows, or "neither" if nothing follows.', answer: (fr, i) => fr[i].meta.ans, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'To show a new problem P is undecidable, which reduction do you build?', options: ['P ≤ A_TM', 'A_TM ≤ P', 'Either', 'P ≤ E_DFA'], answer: 1, why: 'Undecidability flows forwards along ≤: from the known-hard A_TM to P.' },
      { q: 'You know B is decidable and have A ≤ B. What do you know about A?', options: ['A is decidable', 'A is undecidable', 'Nothing', 'A is regular'], answer: 0, why: 'Decide A by computing f(x) and running B\'s decider on it.' },
      { q: 'HALT_TM ≤ A_TM holds. What does it tell us about HALT_TM?', options: ['It is undecidable', 'It is decidable', 'Nothing, on its own', 'It is regular'], answer: 2, why: 'Knowing the target is hard says nothing about the source; HALT_TM is undecidable, but we need A_TM ≤ HALT_TM to show it.' },
      { q: 'Why is A_DFA ≤ A_TM harmless?', options: ['It is false', 'A hard target can receive easy problems; A_DFA stays decidable', 'It shows A_TM is decidable', 'It shows A_DFA is undecidable'], answer: 1, why: 'Every problem we can solve trivially reduces to A_TM; the arrow points from easy to hard.' },
    ],
  });

  // ---------- Turing reductions: ask an oracle ----------
  const OC = {
    'co-atm': { title: 'decider for the complement of A_TM', q: 'complement of A_TM' },
    'halt': { title: 'decider for HALT_TM', q: 'HALT_TM' },
    'etm': { title: 'decider for E_TM', q: 'E_TM' },
  };
  T.topic({
    id: 'red-turing', family: 'reductions', order: 30, title: 'Ask the oracle: Turing reductions',
    blurb: 'Imagine a box that answers "does M accept w?" in one step. A decider allowed to ask it questions, and to do anything with the answers, solves more problems than a mapping reduction can reach.',
    camera: 'follow',
    inputs: [
      { id: 'c', kind: 'choice', label: 'Problem to decide', def: 'co-atm', options: [{ value: 'co-atm', label: 'complement of A_TM (flip the answer)' }, { value: 'halt', label: 'HALT_TM (ask twice)' }, { value: 'etm', label: 'E_TM (ask about a searcher)' }] },
      { id: 'm', kind: 'choice', label: 'Machine M', def: 'aa-recogniser', options: MACHINES },
      { id: 'w', kind: 'string', label: 'w', def: 'ab', max: 5 },
    ],
    check: (inp) => { const al = alphaOf(inp.m); const bad = [...inp.w].find((c) => !al.includes(c)); return bad !== undefined ? 'w: "' + bad + '" is not in this M\'s alphabet {' + al.join(', ') + '}' : null; },
    presets: [
      { label: 'Complement of A_TM: M loops on w', values: { c: 'co-atm', m: 'aa-recogniser', w: 'ab' } },
      { label: 'Complement of A_TM: M accepts w', values: { c: 'co-atm', m: 'contains-11', w: '110' } },
      { label: 'HALT_TM with two questions: M rejects', values: { c: 'halt', m: 'anbn', w: 'ba' } },
      { label: 'HALT_TM: M loops', values: { c: 'halt', m: 'aa-recogniser', w: 'bab' } },
      { label: 'E_TM: is L(M) empty?', values: { c: 'etm', m: 'anbn', w: '' } },
    ],
    counters: [{ id: 'q', label: 'questions asked' }],
    run(inp) {
      const C = OC[inp.c], M = getM(inp.m), w = inp.w, al = alphaOf(inp.m);
      const F = new T.Frames(['q']);
      let lines, input;
      if (inp.c === 'co-atm') { lines = ['1. Ask the oracle: ⟨M, w⟩ ∈ A_TM?', '2. If it says yes, reject.', '3. If it says no, accept.']; input = '⟨M, ' + eps(w) + '⟩'; }
      else if (inp.c === 'halt') { lines = ['1. Ask: does M accept w?', '2. Let N be M with accept and reject swapped.', '3. Ask: does N accept w?', '4. Accept if either answer is yes; else reject.']; input = '⟨M, ' + eps(w) + '⟩'; }
      else { lines = ['1. Write N: on any input, try every string', '   x with M, step limits growing; accept', '   as soon as M accepts some x.', '2. Ask the oracle: does N accept ε?', '3. If yes, reject (L(M) ≠ ∅); if no, accept.']; input = '⟨M⟩'; }
      const BW = 400;
      const dec = (hot, ans, done) => K.mbox.draw({ prefix: 'dec', x: 0, y: 0, w: BW, title: C.title, input, lines, hot, done, outs: K.mbox.answers(ans), outGap: 50 });
      const d0 = dec([]);
      const OY = d0.box.h + 110;
      const oracle = (q, ans, hot) => K.mbox.draw({ prefix: 'or', x: 0, y: OY, w: BW, title: 'oracle for A_TM', tag: 'oracle', tagCls: 'hot', cls: 'r3' + (hot ? ' hot' : ''), lines: [q ? 'asked: ' + q : 'answers any ⟨N, x⟩ in one step'], outs: [{ id: 'yes', text: 'yes', cls: 'good', lit: ans === true, dim: ans === false }, { id: 'no', text: 'no', cls: 'bad', lit: ans === false, dim: ans === true }], outGap: 50 });
      const ask = (k, lit) => K.mbox.wire('ask' + k, { x: 110, y: d0.box.h + 2 }, { x: 110, y: OY - 2 }, { label: 'question', lx: 110 - 52, ly: d0.box.h + 55, cls: lit ? 'hot' : 'soft' });
      const reply = (lit) => K.mbox.wire('reply', { x: 290, y: OY - 2 }, { x: 290, y: d0.box.h + 2 }, { label: 'answer', lx: 290 + 46, ly: d0.box.h + 55, cls: lit ? 'good' : 'soft' });
      const runV = run(M, w);
      F.add({ items: dec([]).items.concat(oracle(null, null).items, ask(0, false), reply(false)), say: 'The oracle is a black box that answers "does N accept x?" for any machine N and string x, in one step. No real machine can be this box; we imagine it to compare problems.' });
      let answer;
      if (inp.c === 'co-atm') {
        const a = runV === 'accept';
        F.count('q');
        F.add({ items: dec([0]).items.concat(oracle('⟨M, ' + eps(w) + '⟩', null, true).items, ask(0, true), reply(false)), say: 'The decider asks the oracle whether M accepts ' + eps(w) + '.' });
        F.add({ items: dec([0]).items.concat(oracle('⟨M, ' + eps(w) + '⟩', a, true).items, ask(0, false), reply(true)), say: 'The oracle says ' + (a ? 'yes' : 'no') + ': M ' + said(runV) + ' on ' + eps(w) + '. (For these small machines we can work out the answer by running them; in general no program can.)', meta: { lamp: 'dec:o:' + (a ? 'reject' : 'accept') } });
        answer = a ? 'reject' : 'accept';
        F.add({ items: dec([a ? 1 : 2], answer, [0]).items.concat(oracle('⟨M, ' + eps(w) + '⟩', a).items, ask(0, false), reply(false)), say: 'It flips the answer and ' + answer + 's: ⟨M, ' + eps(w) + '⟩ is ' + (a ? 'not ' : '') + 'in the complement of A_TM.', mark: answer === 'accept' ? 'accepted' : 'rejected' });
        const why = card('why', 0, OY + 130, ['Not a mapping reduction: that would make', 'the complement of A_TM recognisable,', 'as A_TM is. It is not. The flip after', 'the question is what mapping cannot do.'], { w: BW, cls: 'act' });
        F.add({ items: dec([], answer, [0, a ? 1 : 2]).items.concat(oracle('⟨M, ' + eps(w) + '⟩', a).items, ask(0, false), reply(false), why), say: 'So the complement of A_TM ≤ A_TM as a Turing reduction, but not as a mapping reduction: a mapping reduction must pass the answer on untouched, and would make the complement recognisable, which it is not.' });
      } else if (inp.c === 'halt') {
        const a1 = runV === 'accept', a2 = runV === 'reject';
        F.count('q');
        F.add({ items: dec([0]).items.concat(oracle('⟨M, ' + eps(w) + '⟩', a1, true).items, ask(0, true), reply(true)), say: 'First question: does M accept ' + eps(w) + '? The oracle says ' + (a1 ? 'yes' : 'no') + '.' });
        F.count('q');
        F.add({ items: dec([1, 2], null, [0]).items.concat(oracle('⟨N, ' + eps(w) + '⟩', a2, true).items, ask(0, true), reply(true)), say: 'Second question, about N (M with its accept and reject states swapped): does N accept ' + eps(w) + ', that is, does M reject it? The oracle says ' + (a2 ? 'yes' : 'no') + '.', meta: { lamp: 'dec:o:' + (a1 || a2 ? 'accept' : 'reject') } });
        answer = a1 || a2 ? 'accept' : 'reject';
        F.add({ items: dec([3], answer, [0, 1, 2]).items.concat(oracle('⟨N, ' + eps(w) + '⟩', a2).items, ask(0, false), reply(false)), say: a1 || a2 ? 'One answer is yes, so M halts on ' + eps(w) + ': accept.' : 'Both answers are no: M neither accepts nor rejects ' + eps(w) + ', so it runs for ever. Reject.', mark: answer === 'accept' ? 'accepted' : 'rejected' });
      } else {
        const some = byLength(al, 4).flat().find((x) => run(M, x) === 'accept');
        const a = some !== undefined;
        F.add({ items: dec([0, 1, 2]).items.concat(oracle(null, null).items, ask(0, false), reply(false)), say: 'The decider writes a new machine N that searches for any string M accepts, giving every string a growing step budget in turn, so one endless run cannot block the search.' });
        F.count('q');
        F.add({ items: dec([3], null, [0, 1, 2]).items.concat(oracle('⟨N, ε⟩', a, true).items, ask(0, true), reply(true)), say: 'It asks whether N accepts ε. N accepts some input exactly when M accepts some string. The oracle says ' + (a ? 'yes: M accepts ' + eps(some) + ', for one' : 'no') + '.', meta: { lamp: 'dec:o:' + (a ? 'reject' : 'accept') } });
        answer = a ? 'reject' : 'accept';
        F.add({ items: dec([4], answer, [0, 1, 2, 3]).items.concat(oracle('⟨N, ε⟩', a).items, ask(0, false), reply(false)), say: a ? 'L(M) is not empty, so ⟨M⟩ is not in E_TM: reject.' : 'L(M) is empty, so accept.', mark: answer === 'accept' ? 'accepted' : 'rejected' });
      }
      phaseViews(F.list);
      return { frames: F.list, def: { sections: [
        { id: 'def', kind: 'math', title: 'Turing reduction', text: 'A ≤T B: A is decided by a machine\nthat may ask an oracle for B\nany number of questions, and use\nthe answers in any way.' },
        { id: 'cmp', kind: 'text', title: 'Compared with mapping', text: 'A mapping reduction asks exactly one question, at the very end, and must give its answer unchanged. Every mapping reduction is a Turing reduction, not the other way round.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.lamp, once: true, pick: 'item', ask: 'The oracle has answered. Click the lamp the decider will light.', answer: (fr, i) => fr[i].meta.lamp, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What may a machine with an oracle for B do that a mapping reduction to B may not?', options: ['Run longer', 'Ask several questions and change the answers it gets', 'Use more tape', 'Guess'], answer: 1, why: 'A mapping reduction asks one question and passes the answer on unchanged.' },
      { q: 'Why is the complement of A_TM not mapping-reducible to A_TM?', options: ['Because A_TM is decidable', 'Because it would make the complement of A_TM recognisable, and it is not', 'Because the flip is not computable', 'It is'], answer: 1, why: 'If A ≤m B and B is recognisable then A is recognisable. A_TM is recognisable; its complement is not.' },
      { q: 'How does the HALT_TM decider use an A_TM oracle?', options: ['Asks once and flips', 'Asks whether M accepts and whether M (with accept and reject swapped) accepts', 'Runs M for a while', 'It cannot'], answer: 1, why: 'M halts on w exactly when it accepts or rejects; two questions find out which, if either.' },
      { q: 'Is an oracle for A_TM a real machine?', options: ['Yes, a universal machine', 'No: it is an imagined box for comparing how hard problems are', 'Yes, with a step limit', 'Only for small machines'], answer: 1, why: 'A_TM is undecidable, so no machine answers it. Oracles let us say "if we could solve B, we could solve A".' },
    ],
  });
})();
