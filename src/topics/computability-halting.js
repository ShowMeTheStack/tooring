// The halting problem, three ways. The diagonal table: programs down the side, their own descriptions across
// the top, and a machine D that does the opposite of every entry on the diagonal, so it cannot be any row.
// The machine D built on screen around a claimed halting decider H and fed its own description, with both of
// H's possible answers followed to a contradiction. And a game: pick a strategy for H, watch it do well on
// ordinary programs, then watch D defeat it.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, C = T.comp, Geo = T.geom;

  T.family({ id: 'halting', part: 'computability', order: 20, title: 'The halting problem', blurb: 'No program can tell, for every program and input, whether it will ever stop. The proof feeds a machine its own description and makes it do the opposite of the prediction.' });

  /** A card of text on the stage: lines wrapped to a width, a rounded box behind */
  function wrap(text, width, size) {
    const words = String(text).split(' '), out = [];
    let cur = '';
    for (const w of words) { const t = cur ? cur + ' ' + w : w; if (cur && Geo.textWidth(t, size || 15) > width) { out.push(cur); cur = w; } else cur = t; }
    if (cur) out.push(cur);
    return out;
  }
  function card(key, x, y, w, text, cls, extra) {
    const lines = wrap(text, w - 28, 15);
    const h = lines.length * 21 + 18;
    return Object.assign({ key, kind: 'cell', x, y, w, h, lines, size: 15, cls: 'card ' + (cls || ''), rx: 12 }, extra || {});
  }
  const cardH = (text, w) => wrap(text, w - 28, 15).length * 21 + 18;
  T.compCard = T.compCard || { card, cardH, wrap };

  /** Give each run of frames with the same phase one camera, so a new picture is framed for itself */
  const phase = (F, name) => { for (const f of F.list) if (f.phase === undefined) f.phase = name; };
  const phaseViews = (frames) => { const by = new Map(); for (const f of frames) { const b = T.stageBounds(f.items); if (b) by.set(f.phase, by.has(f.phase) ? T.geom.union([by.get(f.phase), b]) : b); } for (const f of frames) if (by.has(f.phase)) f.view = by.get(f.phase); return frames; };

  // ---------------------------------------------------------------------------------------------------
  // The diagonal table
  // ---------------------------------------------------------------------------------------------------
  // Each program reads a description (its input is text) and accepts, rejects or runs forever. Its own
  // description is the sentence that says what it does, so running it on itself is a real question.
  const CATALOGUE = [
    { desc: 'accept every input', act: () => ['accept', 'it accepts every input'] },
    { desc: 'reject every input', act: () => ['reject', 'it rejects every input'] },
    { desc: 'run forever', act: () => ['loop', 'it never stops on any input'] },
    { desc: 'accept even lengths, reject odd ones', act: (x) => ([...x].length % 2 ? ['reject', 'the input has odd length ' + [...x].length] : ['accept', 'the input has even length ' + [...x].length]) },
    { desc: 'loop if it says loop, else accept', act: (x) => (/loop/.test(x) ? ['loop', 'the input contains the word loop'] : ['accept', 'the input does not contain loop']) },
    { desc: 'reject if it starts with r, else loop', act: (x) => (x[0] === 'r' ? ['reject', 'the input starts with r'] : ['loop', 'the input does not start with r']) },
    { desc: 'accept if it has a y, else reject', act: (x) => (/y/.test(x) ? ['accept', 'the input contains a y'] : ['reject', 'the input has no y']) },
  ];
  const progs = CATALOGUE.map((c, i) => C.program('P' + (i + 1) + '·diag', ['On input x: ' + c.desc + '.'], function* (x) {
    const [v] = c.act(x);
    for (let k = 0; k < Math.min(6, x.length); k++) yield 'step'; // read the input
    if (v === 'loop') { while (true) yield 'loop'; }
    return v === 'accept';
  }));
  const short = { accept: 'acc', reject: 'rej', loop: '∞' };
  const vcls = { accept: 'v-acc', reject: 'v-rej', loop: 'v-loop' };
  const flipOf = (v) => (v === 'accept' ? 'reject' : 'accept');

  const checkList = (v) => {
    if (!Array.isArray(v)) return 'Programs: a list of numbers';
    for (const x of v) if (!/^[1-7]$/.test(x)) return 'Programs: "' + x + '" is not one of the programs 1 to 7';
    if (new Set(v).size !== v.length) return 'Programs: each program once';
    return null;
  };

  T.topic({
    id: 'halt-diagonal', family: 'halting', order: 10, title: 'The diagonal table',
    blurb: 'Run every program on every program\'s description and write down what happens. A machine that flips the diagonal disagrees with every row somewhere, so it is not in the list.',
    inputs: [
      { id: 'list', kind: 'list', label: 'Programs (1–7, in order)', def: ['1', '2', '3', '4', '5', '6'], min: 3, max: 6, check: checkList },
    ],
    presets: [
      { label: 'Six programs', values: { list: ['1', '2', '3', '4', '5', '6'] } },
      { label: 'Accept, reject, run forever', values: { list: ['1', '2', '3'] } },
      { label: 'Programs that read their input', values: { list: ['4', '5', '6', '7'] } },
      { label: 'A program that loops on itself', values: { list: ['5', '7', '2', '4'] } },
    ],
    counters: [{ id: 'runs', label: 'runs made' }, { id: 'loops', label: 'runs that never stop' }, { id: 'flipped', label: 'entries flipped' }],
    run(inp) {
      const ids = inp.list.map((x) => +x - 1), n = ids.length;
      const P = ids.map((i) => CATALOGUE[i]);
      const names = ids.map((i) => 'P' + (i + 1));
      const descs = P.map((p) => p.desc);
      // what program r does on description c, from the engine (a provable loop counts as running forever)
      const res = ids.map((i) => descs.map((d) => { const r = C.runProgram(progs[i], d, 500); return r.verdict === 'limit' ? 'loop' : r.verdict; }));
      const why = ids.map((i) => descs.map((d) => CATALOGUE[i].act(d)[1]));
      const F = new T.Frames(['runs', 'loops', 'flipped']);
      const filled = new Set(), dFilled = new Set();
      const CW = 70;
      const scene = (o) => {
        o = o || {};
        const rows = [];
        for (let r = 0; r < n; r++) rows.push(descs.map((_, c) => (filled.has(r) ? short[res[r][c]] : '')));
        rows.push(descs.map((_, c) => (dFilled.has(c) ? short[flipOf(res[c][c])] : '')));
        const tb = K.table.draw({ prefix: 'dg', rows, colHead: names.map((x) => '⟨' + x + '⟩'), rowHead: names.concat(['D']), corner: 'runs on', cw: CW, x: 0, y: 0,
          cls: (r, c) => {
            const cl = [];
            if (r < n && filled.has(r)) cl.push(vcls[res[r][c]]);
            if (r === n && dFilled.has(c)) cl.push('flip');
            if (o.diag && r === c && r < n) cl.push('diag');
            if (o.hotRow === r && r < n) cl.push('hot');
            if (o.hot && o.hot[0] === r && o.hot[1] === c) cl.push('hot');
            if (o.dim && r < n && r !== c) cl.push('dim');
            return cl.join(' ');
          } });
        const items = tb.items;
        // the legend: what each program does
        const ly = tb.box.y + tb.box.h + 30;
        items.push({ key: 'lg:t', kind: 'text', x: 0, y: ly, text: 'The programs', cls: 'title' });
        P.forEach((p, k) => items.push({ key: 'lg:' + k, kind: 'text', x: 0, y: ly + 28 + k * 24, text: names[k] + ' = "' + p.desc + '"', cls: 'strong' + (o.hotRow === k ? ' hot' : '') }));
        items.push({ key: 'lg:d', kind: 'text', x: 0, y: ly + 28 + n * 24, text: 'D = "accept ⟨Pᵢ⟩ exactly when Pᵢ does not accept ⟨Pᵢ⟩"', cls: dFilled.size ? 'strong' : 'strong dim' });
        return { items, tb };
      };
      F.add({ items: scene().items, say: 'Rows are programs, columns are their descriptions used as inputs. Entry (row Pᵢ, column ⟨Pⱼ⟩) will say what Pᵢ does when it reads Pⱼ\'s description: accept, reject or run forever (∞).', hl: { progs: [] } });
      for (let r = 0; r < n; r++) {
        filled.add(r);
        F.count('runs', n).count('loops', res[r].filter((v) => v === 'loop').length);
        const kinds = [...new Set(res[r])];
        const say = kinds.length === 1 ? names[r] + ' does the same on every description: ' + (res[r][0] === 'loop' ? 'it runs forever (∞) each time' : res[r][0] === 'accept' ? 'it accepts each one' : 'it rejects each one') + '.'
          : names[r] + ' ("' + descs[r] + '") ' + kinds.map((v) => (v === 'loop' ? 'runs forever on ' : v === 'accept' ? 'accepts ' : 'rejects ') + descs.map((_, c) => (res[r][c] === v ? '⟨' + names[c] + '⟩' : null)).filter(Boolean).join(', ')).join('; ') + '.';
        F.add({ items: scene({ hotRow: r }).items, say, hl: { progs: [r] } });
      }
      F.add({ items: scene({ diag: true }).items, say: 'Now look only at the diagonal: each program run on its own description. ' + names.map((x, i) => x + ' on ⟨' + x + '⟩: ' + short[res[i][i]]).join(', ') + '.', meta: { diagAsk: true }, hl: { progs: [] } });
      for (let c = 0; c < n; c++) {
        dFilled.add(c);
        F.count('flipped');
        const v = res[c][c], f = flipOf(v);
        F.add({ items: scene({ diag: true, hot: [n, c] }).items, say: names[c] + ' on its own description ' + (v === 'loop' ? 'runs forever, which is not accepting' : v + 's') + ' (' + why[c][c] + '), so D does the opposite: it ' + f + 's ⟨' + names[c] + '⟩.', meta: { dcol: c, dval: f }, hl: { progs: [c], rule: [0] } });
      }
      F.add({ items: scene({ diag: true, dim: true }).items, say: 'Compare D\'s row with every row: it differs from row Pᵢ in column ⟨Pᵢ⟩, by construction. So D is none of ' + names.join(', ') + '.', hl: { rule: [1] } });
      F.add({ items: scene({ diag: true, dim: true }).items, say: 'The same trick works against any list, even a list of every program there is: no program behaves like D. Building D would need to know which runs go on for ever, and that is the halting question.', mark: 'not in the list', hl: { rule: [2] } });
      return { frames: F.list, def: { sections: [
        { id: 'progs', kind: 'math', title: 'The programs', text: P.map((p, k) => names[k] + ': on input x, ' + p.desc).join('\n') },
        { id: 'rule', kind: 'math', title: 'The diagonal machine', text: 'D(⟨Pᵢ⟩) = accept if Pᵢ does not accept ⟨Pᵢ⟩, reject if it does\nD differs from Pᵢ on the input ⟨Pᵢ⟩\nso D is not any Pᵢ in the list' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.diagAsk, once: true, pick: 'item', ask: (fr, i, inp) => 'Click the cell where P' + inp.list[Math.min(2, inp.list.length - 1)] + ' runs on its own description.', answer: (fr, i, inp) => { const k = Math.min(2, inp.list.length - 1); return 'dg:' + k + ',' + k; }, explain: 'Its own description is the column with the same name: the diagonal cell of its row.' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.dcol === 2, once: true, pick: 'option', options: ['accept', 'reject'], ask: (fr, i, inp) => 'What does D do on ⟨P' + inp.list[2] + '⟩? Look at the diagonal cell above.', answer: (fr, i) => fr[i + 1].meta.dval, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does entry (row Pᵢ, column ⟨Pⱼ⟩) record?', options: ['What Pⱼ does on input ⟨Pᵢ⟩', 'What Pᵢ does when its input is the description of Pⱼ', 'Whether Pᵢ and Pⱼ are equal', 'How long Pᵢ is'], answer: 1, why: 'Rows are the programs that run; columns are the descriptions they are given as input.' },
      { q: 'A program runs forever on its own description. What does D do on that description?', options: ['Runs forever too', 'Accepts', 'Rejects', 'It depends on the other rows'], answer: 1, why: 'Running forever is not accepting, so D, which accepts exactly when the program does not accept, accepts.' },
      { q: 'Why can D not be the program in row 5?', options: ['Row 5 is too short', 'D and P5 disagree on the input ⟨P5⟩', 'D is longer than P5', 'P5 loops'], answer: 1, why: 'D was built to do the opposite of the diagonal entry of every row, so it differs from P5 exactly in column ⟨P5⟩.' },
      { q: 'What would a program for D need to work out on input ⟨Pᵢ⟩?', options: ['Whether Pᵢ accepts its own description, including telling a long run from an endless one', 'Only the length of ⟨Pᵢ⟩', 'Nothing: D just accepts', 'Whether Pᵢ is a DFA'], answer: 0, why: 'To flip ∞ to accept, D must know a run will never stop. Simulating cannot find that out in general; that is the halting problem.' },
      { q: 'Which earlier idea is this argument a copy of?', options: ['The pumping lemma', 'Cantor\'s diagonal argument that the reals are uncountable', 'Subset construction', 'Induction on the length of a string'], answer: 1, why: 'Both list objects in rows and build a new one that differs from row i in position i.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // D built from H, run on itself
  // ---------------------------------------------------------------------------------------------------
  const D_LINES = ['On input ⟨M⟩:', '1. Write ⟨M, ⟨M⟩⟩: M with its own description.', '2. Ask H: does M halt on ⟨M⟩?', '3. If H says halts: loop forever.', '4. If H says loops: halt and accept.'];
  const H_LINES = ['Given ⟨M, x⟩, always answers, always right:', 'halts if M stops on x,', 'loops if M runs forever on x.'];
  const hOuts = (lit) => [{ id: 'h', text: 'halts', cls: 'good', lit: lit === 'h', dim: lit && lit !== 'h' }, { id: 'l', text: 'loops', cls: 'hot', lit: lit === 'l', dim: lit && lit !== 'l' }];
  const dOuts = (lit) => [{ id: 'h', text: 'halts', cls: 'good', lit: lit === 'h', dim: lit && lit !== 'h' }, { id: 'l', text: 'loops ∞', cls: 'hot', lit: lit === 'l', dim: lit && lit !== 'l' }];

  T.topic({
    id: 'halt-build-d', family: 'halting', order: 20, title: 'Build D and feed it itself',
    blurb: 'Suppose a machine H decides halting. Wrap it in a machine D that does the opposite of what H predicts, then give D its own description. Whatever H says about D, D proves it wrong.',
    inputs: [
      { id: 'branch', kind: 'choice', label: 'Follow', def: 'both', options: [{ value: 'both', label: 'both of H\'s answers' }, { value: 'halts', label: 'H says D halts' }, { value: 'loops', label: 'H says D loops' }] },
      { id: 'real', kind: 'number', label: 'Then try a real H that simulates for N steps (0: none)', def: 0, min: 0, max: 400 },
    ],
    presets: [
      { label: 'Both branches', values: { branch: 'both', real: 0 } },
      { label: 'Only: H says D halts', values: { branch: 'halts', real: 0 } },
      { label: 'Only: H says D loops', values: { branch: 'loops', real: 0 } },
      { label: 'Then a real attempt: simulate 40 steps', values: { branch: 'both', real: 40 } },
    ],
    counters: [{ id: 'asked', label: 'questions to H' }, { id: 'contra', label: 'contradictions' }],
    run(inp) {
      const F = new T.Frames(['asked', 'contra']);
      const MB = K.mbox;
      const def = { sections: [
        { id: 'd', kind: 'math', title: 'The machine D', text: D_LINES.join('\n') },
        { id: 'h', kind: 'math', title: 'The claimed decider H', text: 'H(⟨M, x⟩) = halts if M halts on x\nH(⟨M, x⟩) = loops if M runs forever on x\nH itself always halts' },
      ] };
      const Hbox = (o) => Object.assign({ title: 'H', tag: 'claimed decider', lines: H_LINES, cls: 'r2' }, o || {});
      // 1: H alone
      F.add({ items: MB.draw(Object.assign(Hbox(), { prefix: 'H0', input: '⟨M, x⟩', outs: hOuts() })).items, say: 'Suppose someone hands us H: given any machine M and input x, it always stops and correctly says whether M halts on x.', hl: { h: [0, 1, 2] } });
      phase(F, 'h');
      // 2..: D around H
      const Dscene = (o) => {
        const r = MB.draw({ prefix: 'D', title: 'D', tag: 'built from H', input: o.input || '⟨M⟩', lines: D_LINES, hot: o.hot || [], done: o.done || [], cls: 'r0', inner: [Hbox({ prefix: 'DH', lines: o.hLines || H_LINES, hot: o.hHot || [] })], outs: dOuts(o.lit) });
        const items = r.items;
        if (o.copy) items.push(card('copy', r.box.x, r.box.y - 74, r.box.w, o.copy, 'act'));
        return items;
      };
      F.add({ items: Dscene({ hot: [0] }), say: 'Build a new machine D with H inside it. D takes one input: the description of a machine M.', hl: { d: [0] } });
      F.add({ items: Dscene({ hot: [1], copy: '⟨M⟩  ↦  ⟨M, ⟨M⟩⟩   (the machine, and its own description as its input)' }), say: 'Line 1 only copies text: from ⟨M⟩ it writes the pair ⟨M, ⟨M⟩⟩, the question "M run on its own description".', hl: { d: [1] } });
      F.add({ items: Dscene({ hot: [2], done: [1], hHot: [1, 2] }), say: 'Line 2 hands that pair to H, which always answers: halts or loops.', hl: { d: [2] } });
      F.add({ items: Dscene({ hot: [3, 4], done: [1, 2] }), say: 'Lines 3 and 4 do the opposite of H\'s answer: told "halts", D loops forever; told "loops", D halts at once.', hl: { d: [3, 4] } });
      F.count('asked');
      F.add({ items: Dscene({ input: '⟨D⟩', hot: [2], done: [1], copy: '⟨D⟩  ↦  ⟨D, ⟨D⟩⟩   (D asks H about itself!)', hLines: ['Asked: does D halt on ⟨D⟩?', 'halts if D stops on ⟨D⟩,', 'loops if D runs forever on ⟨D⟩.'], hHot: [0] }), say: 'Now the twist: D is a machine, so it has a description ⟨D⟩. Run D on ⟨D⟩. Line 1 writes ⟨D, ⟨D⟩⟩, and H is asked whether D halts on ⟨D⟩, which is the very run we are in.', hl: { d: [1, 2] }, mark: 'D on ⟨D⟩' });
      phase(F, 'd');
      // the branches, one above the other
      const branches = inp.branch === 'both' ? ['halts', 'loops'] : [inp.branch];
      const state = {};
      const BW = 420;
      const branchScene = () => {
        const items = [];
        let y = 0;
        branches.forEach((b, k) => {
          const s = state[b] || {};
          const says = b === 'halts' ? 'halts' : 'loops';
          const does = b === 'halts' ? 'loops' : 'halts';
          const lines = ['H answers: D ' + (b === 'halts' ? 'halts' : 'loops forever') + ' on ⟨D⟩.', 'So D takes line ' + (b === 'halts' ? '3: it loops forever.' : '4: it halts and accepts.'), 'H said D ' + says + ', but D ' + does + '.'];
          const shown = lines.slice(0, s.stage || 0);
          const r = MB.draw({ prefix: 'B' + b, x: 0, y, w: BW, title: 'Branch ' + (k + 1) + ': suppose H says "' + says + '"', tag: s.stage >= 3 ? 'contradiction' : 'what would H say?', tagCls: s.stage >= 3 ? 'bad' : 'hot', lines: shown.length ? shown : ['…'], hot: s.stage === 1 ? [0] : s.stage === 2 ? [1] : [], done: s.stage >= 2 ? [0] : [], bad: s.stage >= 3 ? [2] : [], cls: (s.stage >= 3 ? 'bad ' : '') + (b === 'halts' ? 'r5' : 'r2'), outGap: 36, outs: dOuts(s.stage >= 2 ? (b === 'halts' ? 'l' : 'h') : null), enter: 'drop' });
          items.push(...r.items);
          y += r.box.h + 34;
        });
        return items;
      };
      F.add({ items: branchScene(), say: 'H must give one of two answers. We do not know which, so follow ' + (branches.length === 2 ? 'both possibilities, one above the other.' : 'the one where H says D ' + branches[0] + '.') });
      branches.forEach((b) => {
        state[b] = { stage: 1 };
        F.add({ items: branchScene(), say: b === 'halts' ? 'Suppose H answers "halts": it claims D stops when run on ⟨D⟩.' : 'Suppose H answers "loops": it claims D runs forever on ⟨D⟩.', meta: { branch: b } });
        state[b].stage = 2;
        F.add({ items: branchScene(), say: b === 'halts' ? 'D does the opposite of what H says: told "halts", it takes line 3 and loops forever.' : 'D does the opposite: told "loops", it takes line 4 and halts at once.', hl: { d: [b === 'halts' ? 3 : 4] }, meta: { did: b } });
        state[b].stage = 3;
        F.count('contra');
        F.add({ items: branchScene(), say: b === 'halts' ? 'But H said D halts on ⟨D⟩, and D loops on ⟨D⟩. H is wrong: a contradiction.' : 'But H said D runs forever on ⟨D⟩, and D halts on ⟨D⟩. H is wrong again: a contradiction.' });
      });
      const items = branchScene();
      const lastY = Math.max(...items.filter((x) => x.kind === 'region' && /:box$/.test(x.key)).map((x) => x.y + x.h)) + 30;
      const concl = branches.length === 2 ? 'Both answers lead to a contradiction, and H had to give one of them. So the H we assumed cannot exist: no machine decides whether every machine halts on every input.' : 'This answer leads to a contradiction; the other one does too (try it). So no such H can exist: halting is undecidable.';
      items.push(card('concl', 0, lastY, BW, concl, 'good', { enter: 'drop' }));
      F.add({ items, say: concl, mark: 'H cannot exist' });
      phase(F, 'b');
      // a real attempt
      if (inp.real > 0) {
        const r = C.diagonal(inp.real, { maxSteps: 20000 });
        const ask = r.trace.find((t) => t.kind === 'answer');
        const steps = r.trace.find((t) => t.kind === 'run');
        const hl = ['Simulate M on x for ' + inp.real + ' steps;', 'if it stopped, say halts,', 'otherwise say loops.'];
        const it2 = MB.draw({ prefix: 'D', title: 'D', tag: 'built from H' + inp.real, input: '⟨D⟩', lines: D_LINES, done: [1, 2], hot: [r.answer ? 3 : 4], cls: 'r0', inner: [{ prefix: 'DH', title: 'H' + inp.real, tag: 'a real attempt', lines: hl, cls: 'r2', hot: [r.answer ? 1 : 2] }], outs: dOuts(r.halted ? 'h' : 'l') }).items;
        F.add({ items: it2, say: 'Now a real H: simulate for ' + inp.real + ' steps and say "halts" only if the simulation stopped. Asked about D on ⟨D⟩, it simulates D, which itself asks H, and the budget runs out: H' + inp.real + ' answers "' + (r.answer ? 'halts' : 'loops') + '" after ' + (ask && /after (\d+)/.test(ask.say) ? ask.say.match(/after (\d+)/)[1] : '?') + ' steps of its own.' });
        F.add({ items: it2, say: 'Running D on ⟨D⟩ for real: ' + (r.halted ? 'it halts after ' + (steps ? steps.steps : '?') + ' steps' : 'it loops forever') + '. H' + inp.real + ' was wrong, exactly as the argument says every H must be on this input.', mark: 'H' + inp.real + ' fooled' });
      }
      phase(F, 'real');
      return { frames: phaseViews(F.list), def };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.did, pick: 'item', ask: (fr, i) => 'H has answered "' + fr[i + 1].meta.did + '". Click what D does next.', answer: (fr, i) => 'B' + fr[i + 1].meta.did + ':o:' + (fr[i + 1].meta.did === 'halts' ? 'l' : 'h'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What input does D give to H?', options: ['⟨M⟩ alone', '⟨M, ⟨M⟩⟩: the machine with its own description as input', '⟨D, w⟩ for a fixed w', 'Nothing; D ignores H'], answer: 1, why: 'Line 1 turns ⟨M⟩ into the question "does M halt on its own description?".' },
      { q: 'H says D halts on ⟨D⟩. What does D then do on ⟨D⟩?', options: ['Halts', 'Loops forever', 'Asks H again', 'Rejects'], answer: 1, why: 'D does the opposite of H\'s answer, so it takes the "loop forever" line, and H turns out wrong.' },
      { q: 'Which assumption is shown false?', options: ['That D can copy its input', 'That a machine H deciding halting exists', 'That machines have descriptions', 'That ⟨D⟩ is a string'], answer: 1, why: 'Everything else is a plain construction; the only assumption is H. Both of its possible answers fail, so H cannot exist.' },
      { q: 'Why is it fine for D to ask H about D itself?', options: ['It is not; the proof is circular', 'D is an ordinary machine, so ⟨D⟩ is an ordinary input and H must handle it', 'H refuses such questions', 'Because D halts'], answer: 1, why: 'H was claimed to answer for every machine and every input. ⟨D, ⟨D⟩⟩ is one more such question.' },
      { q: 'A real H that simulates for 1000 steps is asked about D on ⟨D⟩. What happens?', options: ['It answers correctly', 'Its budget runs out, it says "loops", and D then halts, so it is wrong', 'It never answers', 'D crashes'], answer: 1, why: 'D runs H inside it, so D always outlasts H\'s budget; told "loops", D halts.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Fool the decider
  // ---------------------------------------------------------------------------------------------------
  const STRATS = {
    yes: { name: 'H-optimist', lines: ['Always say halts.'] },
    no: { name: 'H-pessimist', lines: ['Always say loops.'] },
    sim: { name: 'H-patient', lines: ['Simulate M on x for N steps.', 'Stopped? say halts; else say loops.'] },
    watch: { name: 'H-watcher', lines: ['Simulate for N steps, watching for a', 'repeated configuration (a sure loop).', 'Stopped: halts. Repeat: loops. Else guess.'] },
    shortdesc: { name: 'H-skimmer', lines: ['Read ⟨M⟩ only: if it mentions loop,', 'say loops; otherwise say halts.'] },
  };
  // the test programs H is tried on first; their truth is known by construction
  const TESTS = [
    { name: 'quick', text: 'count to 3, accept', halts: true, body: function* () { for (let i = 0; i < 3; i++) yield 'step'; return true; } },
    { name: 'spin', text: 'loop: go back to loop', halts: false, body: function* () { while (true) yield 'loop'; } },
    { name: 'slow', text: 'count to 120, accept', halts: true, body: function* () { for (let i = 0; i < 120; i++) yield 'step'; return true; } },
    { name: 'wander', text: 'count upwards for ever', halts: false, body: function* () { while (true) yield 'step'; } },
  ];
  const testProgs = TESTS.map((t) => Object.assign(C.program(t.name + '·fool', [t.text], t.body), { text: t.text }));

  function makeH(kind, N, guess) {
    if (kind === 'sim') return N;
    let depth = 0;
    const H = (code, input) => {
      const P = C.registry.get(code);
      if (kind === 'yes') return true;
      if (kind === 'no') return false;
      if (kind === 'shortdesc') return !(P && /loop/.test(P.lines.join(' ') + (P.text || '')));
      // watch: simulate with a step budget; a nested question (the program asking H about itself) is
      // answered by the guess once the nesting gets deep, as a real budget would force
      if (!P) return false;
      if (depth > 2) return guess === 'halts';
      depth++;
      try { const r = C.runProgram(P, input, N); return r.verdict === 'accept' || r.verdict === 'reject' ? true : r.verdict === 'loop' ? false : guess === 'halts'; } finally { depth--; }
    };
    H.label = STRATS[kind].name;
    return H;
  }
  function askH(kind, N, guess, P, x) {
    if (kind === 'sim') { const r = C.runProgram(P, x, N); return { says: r.verdict === 'accept' || r.verdict === 'reject', steps: Math.min(r.steps, N) }; }
    const H = makeH(kind, N, guess);
    return { says: H(P.code, x), steps: kind === 'yes' || kind === 'no' || kind === 'shortdesc' ? 0 : Math.min(C.runProgram(P, x, N).steps, N) };
  }

  T.topic({
    id: 'halt-fool', family: 'halting', order: 30, title: 'Fool the decider',
    blurb: 'Pick a strategy for a halting decider H. It may do well on ordinary programs, but the machine D built from it always catches it out.',
    inputs: [
      { id: 'kind', kind: 'choice', label: 'Strategy for H', def: 'sim', options: [{ value: 'yes', label: 'always say halts' }, { value: 'no', label: 'always say loops' }, { value: 'sim', label: 'simulate N steps' }, { value: 'watch', label: 'simulate, watch for a repeat' }, { value: 'shortdesc', label: 'read the description only' }] },
      { id: 'N', kind: 'number', label: 'N (steps)', def: 50, min: 1, max: 500 },
      { id: 'guess', kind: 'choice', label: 'When unsure, guess', def: 'loops', options: [{ value: 'loops', label: 'loops' }, { value: 'halts', label: 'halts' }] },
    ],
    presets: [
      { label: 'Simulate 50 steps', values: { kind: 'sim', N: 50, guess: 'loops' } },
      { label: 'Simulate 200 steps (beats slow)', values: { kind: 'sim', N: 200, guess: 'loops' } },
      { label: 'Always say halts', values: { kind: 'yes', N: 50, guess: 'loops' } },
      { label: 'Always say loops', values: { kind: 'no', N: 50, guess: 'loops' } },
      { label: 'Watch for repeats, guess halts', values: { kind: 'watch', N: 150, guess: 'halts' } },
      { label: 'Read the description only', values: { kind: 'shortdesc', N: 50, guess: 'loops' } },
    ],
    counters: [{ id: 'right', label: 'H right' }, { id: 'wrong', label: 'H wrong' }],
    run(inp) {
      const S = STRATS[inp.kind];
      const hLines = S.lines.map((l) => l.replace('N steps', inp.N + ' steps')).concat(inp.kind === 'watch' ? ['(guess: ' + inp.guess + ')'] : []);
      const F = new T.Frames(['right', 'wrong']);
      const MB = K.mbox;
      const board = [];
      const boardItems = (hot, y) => {
        const tb = K.table.draw({ prefix: 'sb', rows: board.map((r) => [r.prog, r.says, r.truth, r.ok ? '✓' : '✗']), colHead: ['program', 'H says', 'truth', ''], x: 0, y, minW: 60,
          cls: (r, c) => (c === 3 ? (board[r].ok ? 'good' : 'bad') : c === 1 && r === hot ? 'hot' : r === board.length - 1 && board[r].isD ? 'act' : '') });
        return tb;
      };
      const layout = (o) => {
        const items = [];
        const hb = MB.draw({ prefix: 'H', title: S.name, tag: 'claimed decider', lines: hLines, cls: 'r2', x: 0, y: 0, input: o.hInput || '⟨M, x⟩', outs: [{ id: 'h', text: 'halts', cls: 'good', lit: o.says === true, dim: o.says === false }, { id: 'l', text: 'loops', cls: 'hot', lit: o.says === false, dim: o.says === true }] });
        if (!o.d) items.push(...hb.items);
        let y = o.d ? 0 : hb.box.h + 44;
        if (o.d) {
          const r = MB.draw({ prefix: 'D', title: 'D', tag: 'built from ' + S.name, input: '⟨D⟩', lines: ['On input ⟨M⟩:', '1. Ask H: does M halt on ⟨M⟩?', '2. If H says halts: loop forever.', '3. If H says loops: halt.'], hot: o.dHot || [], done: o.dDone || [], cls: 'r0', inner: [{ prefix: 'DH', title: S.name, tag: 'inside D', lines: hLines.concat(o.says === undefined ? [] : ['→ answers: ' + (o.says ? 'halts' : 'loops')]), hot: o.says === undefined ? [] : [hLines.length], cls: 'r2' }], outs: dOuts(o.dLit), x: 0, y: 0 });
          items.push(...r.items);
          y = r.box.h + 44;
        }
        if (board.length) { const tb = boardItems(o.hotRow, y + 24); items.push({ key: 'sb:t', kind: 'text', x: 0, y: y + 10, text: 'H\'s record', cls: 'title' }); items.push(...tb.items); }
        return items;
      };
      F.add({ items: layout({}), say: 'Your claimed decider ' + S.name + ': ' + hLines.join(' ') + ' First, try it on four programs whose behaviour we know.', hl: { h: hLines.map((_, i) => i) } });
      TESTS.forEach((t, k) => {
        const a = askH(inp.kind, inp.N, inp.guess, testProgs[k], '');
        const ok = a.says === t.halts;
        board.push({ prog: t.name, says: a.says ? 'halts' : 'loops', truth: t.halts ? 'halts' : 'loops', ok });
        F.count(ok ? 'right' : 'wrong');
        const how = inp.kind === 'sim' || inp.kind === 'watch' ? ' after simulating ' + a.steps + ' step' + (a.steps === 1 ? '' : 's') : '';
        F.add({ items: layout({ says: a.says, hInput: '⟨' + t.name + ', ε⟩', hotRow: k }), say: '"' + t.name + '" (' + t.text + ') really ' + (t.halts ? 'halts' : 'runs forever') + '. ' + S.name + ' says ' + (a.says ? 'halts' : 'loops') + how + ': ' + (ok ? 'right.' : 'wrong!' + (t.name === 'slow' ? ' A patient enough simulation would get this one, but some program is always slower.' : '')), meta: { test: k, says: a.says } });
      });
      phase(F, 'h');
      const H = makeH(inp.kind, inp.N, inp.guess);
      const r = C.diagonal(H, { maxSteps: 20000 });
      const ansT = r.trace.find((t) => t.kind === 'answer');
      const hSteps = ansT && /after (\d+)/.test(ansT.say) ? +ansT.say.match(/after (\d+)/)[1] : 0;
      F.add({ items: layout({ d: true, dHot: [1] }), say: 'Now build D around ' + S.name + ', and run D on its own description ⟨D⟩. Line 1 asks ' + S.name + ' whether D halts on ⟨D⟩.' });
      F.add({ items: layout({ d: true, dHot: [1], says: r.answer }), say: S.name + ' answers "' + (r.answer ? 'halts' : 'loops') + '"' + (inp.kind === 'sim' ? ' after ' + hSteps + ' steps of its own: inside, D asks H again, so the simulation never finishes within its budget' : inp.kind === 'watch' ? ': inside its simulation, D asks H the same question again, and what the simulated D then does decides the verdict' : '') + '.', meta: { dAns: r.answer } });
      const did = r.halted ? 'h' : 'l';
      F.add({ items: layout({ d: true, dDone: [1], dHot: [r.answer ? 2 : 3], says: r.answer, dLit: did }), say: 'D does the opposite: ' + (r.halted ? 'it halts (after ' + r.trace.find((t) => t.kind === 'run').steps + ' step' + (r.trace.find((t) => t.kind === 'run').steps === 1 ? ')' : 's)') : 'it loops forever (the engine sees the same configuration come round again)') + '.', meta: { dDid: did } });
      board.push({ prog: 'D on ⟨D⟩', says: r.answer ? 'halts' : 'loops', truth: r.halted ? 'halts' : 'loops', ok: false, isD: true });
      F.count('wrong');
      F.add({ items: layout({ d: true, dDone: [1], dHot: [r.answer ? 2 : 3], says: r.answer, dLit: did, hotRow: board.length - 1 }), say: S.name + ' said D ' + (r.answer ? 'halts' : 'loops') + ' on ⟨D⟩, but D ' + (r.halted ? 'halts' : 'loops') + '. Whatever the strategy, the D built from it lands in the ✗ row: try another strategy.', mark: 'fooled' });
      phase(F, 'd');
      return { frames: phaseViews(F.list), def: { sections: [
        { id: 'h', kind: 'math', title: 'Your H', text: hLines.join('\n') },
        { id: 'd', kind: 'math', title: 'D, built from H', text: 'On input ⟨M⟩:\n1. Ask H: does M halt on ⟨M⟩?\n2. If H says halts: loop forever.\n3. If H says loops: halt.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.dDid, once: true, pick: 'item', ask: (fr, i) => 'H answered "' + (fr[i].meta.dAns ? 'halts' : 'loops') + '". Click what D does on ⟨D⟩.', answer: (fr, i) => 'D:o:' + fr[i + 1].meta.dDid, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.test === 2, once: true, pick: 'option', options: ['halts', 'loops'], ask: 'Next test: "slow" counts to 120 and accepts. What will your H say?', answer: (fr, i) => (fr[i + 1].meta.says ? 'halts' : 'loops'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'H simulates for 1,000,000 steps. Which program does it get wrong besides D?', options: ['None', 'Any program that halts after more than 1,000,000 steps', 'Programs that halt quickly', 'Programs that loop with a repeated configuration'], answer: 1, why: 'A program that halts on step 1,000,001 looks, to that H, exactly like one that never halts.' },
      { q: 'Watching for a repeated configuration catches which loops?', options: ['All of them', 'Loops that come back to exactly the same state, tape and head position', 'None', 'Only loops in DFAs'], answer: 1, why: 'A machine that keeps writing new cells never repeats a configuration, yet may run forever: the watcher must still guess.' },
      { q: 'Why does every strategy lose to its own D?', options: ['The strategies are badly written', 'D is built to do the opposite of whatever H says about D on ⟨D⟩', 'D is very long', 'Because H is nondeterministic'], answer: 1, why: 'The construction does not depend on how H works, only on H always answering.' },
      { q: 'H-patient says "loops" about D on ⟨D⟩. Why does its simulation never finish in time?', options: ['D is slow on purpose', 'D runs H inside it, so simulating D means simulating H simulating D…, which always needs more steps than the budget', 'D has no description', 'The budget is chosen at random'], answer: 1, why: 'Each level of simulation adds overhead, so D on ⟨D⟩ outlasts any fixed budget, and then D halts.' },
      { q: 'Does this mean no program can ever tell whether a given program halts?', options: ['Yes, never', 'No: many programs can be analysed; what fails is one method that is right on every program', 'Only for short programs', 'Only for DFAs'], answer: 1, why: 'Undecidability rules out a single always-correct decider, not useful partial checkers that sometimes say "don\'t know".' },
    ],
  });
})();
