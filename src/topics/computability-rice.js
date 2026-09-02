// Rice's theorem: a classifier that asks of a property "is it about the language only?" and "do some
// machines have it and some not?", using a catalogue of small machines grouped by the language they
// recognise; and the proof template, building M_w for a property and showing it decides A_TM.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'rice', part: 'computability', order: 50, title: 'Rice\'s theorem', blurb: 'Any property of what a machine recognises, unless every machine has it or none does, is undecidable. Learn to tell such properties from ones about the machine itself.' });

  const eps = (s) => (s === '' ? 'ε' : s);
  function card(key, x, y, lines, opts) {
    opts = opts || {};
    lines = [].concat(lines);
    const w = opts.w || Math.ceil(Math.max(...lines.map((l) => Geo.textWidth(l, 15, { bold: true }))) + 34);
    const h = opts.h || lines.length * 22 + 22;
    const it = { key, kind: 'cell', x, y, w, h, size: 15, rx: 12, cls: 'card ' + (opts.cls || ''), pick: !!opts.pick };
    if (lines.length > 1) it.lines = lines; else it.text = lines[0];
    return it;
  }

  // ---------- the catalogue: small machines over {0, 1}, grouped by language ----------
  const LANGS = [
    { id: 'all', label: 'L = Σ* (everything)' },
    { id: 'empty', label: 'L = ∅ (nothing)' },
    { id: 'starts1', label: 'L = strings starting with 1' },
    { id: 'has1', label: 'L = strings containing a 1' },
    { id: 'eps', label: 'L = {ε}' },
  ];
  const CAT = [
    { name: 'A1', lang: 'all', text: 'q0, 0|1|_ -> qa, *, S' },
    { name: 'A2', lang: 'all', text: 'q0, 0|1 -> q0, *, R\nq0, _ -> q1, _, L\nq1, * -> q2, *, R\nq2, * -> q3, *, S\nq3, * -> qa, *, S' },
    { name: 'E1', lang: 'empty', text: 'q0, 0|1|_ -> qr, *, S' },
    { name: 'E2', lang: 'empty', text: 'q0, 0|1|_ -> q0, *, S' },
    { name: 'S1', lang: 'starts1', text: 'q0, 1 -> qa, *, S\nq0, 0|_ -> qr, *, S' },
    { name: 'S2', lang: 'starts1', text: 'q0, 0|1|_ -> q1, *, S\nq1, 1 -> q2, *, R\nq1, 0|_ -> qr, *, S\nq2, * -> qa, *, S' },
    { name: 'H1', lang: 'has1', text: 'q0, 0 -> q0, *, R\nq0, 1 -> qa, *, S\nq0, _ -> qr, *, S' },
    { name: 'P1', lang: 'eps', text: 'q0, _ -> qa, *, S\nq0, 0|1 -> qr, *, S' },
  ];
  let catalogue = null;
  const cat = () => {
    if (catalogue) return catalogue;
    catalogue = CAT.map((c) => {
      const machine = T.tm.compile('input: 0 1\nstart: q0\n' + c.text, { name: c.name });
      const verdict = (x) => T.tm.run(machine, x, { maxSteps: 300, trace: false }).verdict;
      return Object.assign({}, c, { machine, states: machine.states.length, verdict, member: (x) => verdict(x) === 'accept' });
    });
    return catalogue;
  };
  const strs = (n) => { const out = ['']; let layer = ['']; for (let l = 1; l <= n; l++) { layer = layer.flatMap((s) => [s + '0', s + '1']); out.push(...layer); } return out; };
  const PROPS = {
    'empty': { label: 'L(M) = ∅', semantic: true, test: (e) => e.lang === 'empty' },
    'has-1': { label: 'L(M) contains the string 1', semantic: true, test: (e) => e.member('1') },
    'infinite': { label: 'L(M) is infinite', semantic: true, test: (e) => ['all', 'starts1', 'has1'].includes(e.lang) },
    'has-eps': { label: 'ε ∈ L(M)', semantic: true, test: (e) => e.member('') },
    'recognisable': { label: 'L(M) is recognisable', semantic: true, test: () => true },
    'states': { label: 'M has at most 3 states', semantic: false, test: (e) => e.states <= 3, note: 'Counting states is easy: this one is decidable, by reading ⟨M⟩.' },
    'halts': { label: 'M halts on every input', semantic: false, test: (e) => strs(3).every((x) => e.verdict(x) !== 'loop'), note: 'It is still undecidable, but Rice\'s theorem cannot be the reason: show it with a reduction from HALT_TM.' },
  };
  const PROP_OPTS = Object.entries(PROPS).map(([value, p]) => ({ value, label: p.label }));

  /** The catalogue drawn as one region per language, machines as cards inside */
  function catalogueItems(cls, extra) {
    const items = [];
    const CW = 112, CH = 58, PAD = 14, RW = 2 * CW + 3 * PAD, RH = CH + 50;
    const pos = {};
    LANGS.forEach((L, i) => {
      const x = (i % 2) * (RW + 26), y = Math.floor(i / 2) * (RH + 22);
      const mem = cat().filter((e) => e.lang === L.id);
      items.push({ key: 'lang:' + L.id, kind: 'region', x, y, w: RW, h: RH, text: L.label, rx: 14, cls: 'r' + (i % 6) + ((extra && extra.region && extra.region[L.id]) || '') });
      mem.forEach((e, k) => {
        pos[e.name] = { x: x + PAD + k * (CW + PAD), y: y + 34 };
        items.push({ key: 'm:' + e.name, kind: 'cell', x: pos[e.name].x, y: pos[e.name].y, w: CW, h: CH, lines: [e.name, e.states + ' states'], size: 15, rx: 10, cls: 'card ' + ((cls && cls[e.name]) || ''), pick: true });
      });
    });
    return { items, pos, w: 2 * RW + 26, h: 3 * (RH + 22) - 22 };
  }

  T.topic({
    id: 'rice-classify', family: 'rice', order: 10, title: 'Is it a property Rice\'s theorem covers?',
    blurb: 'Two questions decide it. Does the property depend only on the language the machine recognises? Do some machines have it and some not? Yes to both: undecidable.',
    inputs: [{ id: 'p', kind: 'choice', label: 'Property', def: 'has-1', options: PROP_OPTS }],
    presets: [
      { label: 'L(M) contains 1', values: { p: 'has-1' } },
      { label: 'L(M) is empty (∅ has it)', values: { p: 'empty' } },
      { label: 'Trivial: L(M) is recognisable', values: { p: 'recognisable' } },
      { label: 'About the machine: at most 3 states', values: { p: 'states' } },
      { label: 'About behaviour: halts on every input', values: { p: 'halts' } },
    ],
    counters: [{ id: 'yes', label: 'machines with it' }, { id: 'no', label: 'machines without' }],
    run(inp) {
      const P = PROPS[inp.p];
      const F = new T.Frames(['yes', 'no']);
      const res = T.comp.riceCheck({ test: (e) => P.test(e) }, cat());
      const cls = {};
      const c0 = catalogueItems(cls);
      const by = c0.h + 30;
      const prop = card('prop', 0, by, ['Property: ' + P.label], { w: c0.w, cls: 'act' });
      const yesKeys = cat().filter((e) => P.test(e)).map((e) => 'm:' + e.name);
      F.add({ items: c0.items.concat(prop), say: 'Eight small machines, grouped by the language they recognise. Machines in one box recognise the same language, though they work differently. The property: "' + P.label + '".', meta: { yes: yesKeys }, hl: { rice: [0] } });
      for (const e of cat()) {
        const v = P.test(e);
        cls[e.name] = v ? 'good' : 'bad';
        F.count(v ? 'yes' : 'no');
        F.add({ items: catalogueItems(Object.assign({}, cls)).items.concat(prop), say: e.name + ' (' + e.states + ' states, ' + LANGS.find((l) => l.id === e.lang).label.replace(/^L = /, 'language ') + ') ' + (v ? 'has' : 'lacks') + ' the property.' });
      }
      const q1y = by + 76;
      const q = (k, txt, c) => card('q' + k, 0, q1y + (k - 1) * 70, txt, { w: c0.w, cls: c });
      if (!res.semantic) {
        const [a, b] = res.witnesses;
        const hot = Object.assign({}, cls); hot[a] += ' pulse'; hot[b] += ' pulse';
        const L = cat().find((e) => e.name === a).lang;
        const pair = { key: 'pair', kind: 'edge', from: 'm:' + a, to: 'm:' + b, bend: -30, cls: 'hot', head: false };
        F.add({ items: catalogueItems(hot, { region: { [L]: ' hot' } }).items.concat(prop, pair, q(1, 'Q1. About the language only? No: ' + a + ' and ' + b + ' differ.', 'bad')), say: res.trace[0].say, hl: { rice: [1] }, meta: { verdict: 'no' } });
        F.add({ items: catalogueItems(hot, { region: { [L]: ' hot' } }).items.concat(prop, pair, q(1, 'Q1. About the language only? No: ' + a + ' and ' + b + ' differ.', 'bad'), q(2, 'Rice\'s theorem does not apply.', '')), say: 'Rice\'s theorem is silent here. ' + P.note, mark: 'rejected', hl: { rice: [1] } });
      } else {
        const region = {};
        for (const L of LANGS) region[L.id] = cat().filter((e) => e.lang === L.id).every((e) => P.test(e)) ? ' good' : ' bad';
        F.add({ items: catalogueItems(cls, { region }).items.concat(prop, q(1, 'Q1. About the language only? Yes: each box is all one colour.', 'good')), say: 'Within every box all machines agree: the property depends only on the language. It is a property of languages.', hl: { rice: [1] } });
        if (res.trivial) {
          F.add({ items: catalogueItems(cls, { region }).items.concat(prop, q(1, 'Q1. About the language only? Yes.', 'good'), q(2, 'Q2. Some have it, some not? No: it is trivial.', 'bad')), say: res.trace[res.trace.length - 1].say, meta: { verdict: 'no' }, hl: { rice: [2] } });
          F.add({ items: catalogueItems(cls, { region }).items.concat(prop, q(1, 'Q1. About the language only? Yes.', 'good'), q(2, 'Q2. Some have it, some not? No: it is trivial.', 'bad'), q(3, 'Decidable: always answer "yes".', 'good')), say: 'A trivial property is decidable by a machine that ignores its input and always gives the same answer. Rice\'s theorem needs both yes answers.', mark: 'rejected' });
        } else {
          const sel = Object.assign({}, cls); sel[res.yes] += ' pulse'; sel[res.no] += ' pulse';
          F.add({ items: catalogueItems(sel, { region }).items.concat(prop, q(1, 'Q1. About the language only? Yes.', 'good'), q(2, 'Q2. Non-trivial? Yes: ' + res.yes + ' has it, ' + res.no + ' does not.', 'good')), say: res.trace[0].say + ' Both questions say yes.', meta: { verdict: 'yes' }, hl: { rice: [2] } });
          F.add({ items: catalogueItems(sel, { region }).items.concat(prop, q(1, 'Q1. About the language only? Yes.', 'good'), q(2, 'Q2. Non-trivial? Yes: ' + res.yes + ' has it, ' + res.no + ' does not.', 'good'), q(3, 'Undecidable, by Rice\'s theorem.', 'bad')), say: 'So by Rice\'s theorem no machine decides whether ' + P.label + '. ' + res.trace[1].say, mark: 'accepted', hl: { rice: [3] } });
        }
      }
      return { frames: F.list, def: { sections: [
        { id: 'rice', kind: 'math', title: 'Rice\'s theorem', text: 'P = {⟨M⟩ : L(M) has the property}\n1. if L(M₁) = L(M₂) then both or neither in P\n2. some ⟨M⟩ ∈ P and some ⟨M⟩ ∉ P\n⇒ P is undecidable' },
        { id: 'cat', kind: 'table', title: 'The catalogue', colHead: ['language', 'states'], rowHead: cat().map((e) => e.name), rows: cat().map((e) => [LANGS.find((l) => l.id === e.lang).label.replace(/^L = /, ''), String(e.states)]) },
      ] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'item', ask: 'Click any machine that you think has the property.', answer: (fr) => (fr[0].meta.yes.length ? fr[0].meta.yes : null), explain: 'Each card turns green or red as it is tested, starting now.' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.verdict, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will Rice\'s theorem apply to this property?', answer: (fr, i) => (fr[i + 1].meta.verdict === 'yes' ? 'Yes' : 'No'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: '"M has at most 3 states". Does Rice\'s theorem make it undecidable?', options: ['Yes', 'No: it is about the machine, not its language, and it is decidable', 'No: it is trivial', 'Only for deciders'], answer: 1, why: 'Two machines with the same language can have different numbers of states; and the number of states can be read off ⟨M⟩.' },
      { q: '"L(M) is recognisable". Undecidable by Rice?', options: ['Yes', 'No: every machine has it, so it is trivial', 'No: it is not about languages', 'Only sometimes'], answer: 1, why: 'Every L(M) is recognisable, by M itself; the always-yes machine decides it.' },
      { q: '"L(M) = ∅": which two machines show it is non-trivial?', options: ['Two that loop', 'One with an empty language and one with a non-empty language', 'Two with the same language', 'None are needed'], answer: 1, why: 'Non-trivial means at least one machine has the property and at least one lacks it.' },
      { q: '"M halts on every input" separates E1 (rejects all) from E2 (loops on all). What follows?', options: ['It is decidable', 'It is not a property of languages, so Rice\'s theorem is silent', 'It is trivial', 'It is a property of languages'], answer: 1, why: 'Both recognise ∅ but only one halts everywhere. The property is undecidable, but that needs its own reduction.' },
      { q: 'Which is a non-trivial property of languages?', options: ['M has a rule reading 1', 'M takes 5 steps on ε', 'L(M) contains 1', 'M has 4 states'], answer: 2, why: 'Only "L(M) contains 1" depends on the language alone.' },
    ],
  });

  // ---------- the proof template ----------
  const SEM = ['has-1', 'infinite', 'has-eps', 'empty'];
  const MACHINES = [
    { value: 'contains-11', label: 'M: contains 11 (always halts)' },
    { value: 'anbn', label: 'M: aⁿbⁿ (always halts)' },
    { value: 'aa-recogniser', label: 'M: contains aa (loops otherwise)' },
  ];
  T.topic({
    id: 'rice-proof', family: 'rice', order: 20, title: 'Rice\'s theorem: the proof, built',
    blurb: 'Given ⟨M, w⟩, build M_w: it first runs M on w, and only if M accepts does it behave like a machine T whose language has the property. So M_w has the property exactly when M accepts w.',
    camera: 'follow',
    inputs: [
      { id: 'p', kind: 'choice', label: 'Property', def: 'has-1', options: SEM.map((v) => ({ value: v, label: PROPS[v].label })) },
      { id: 'm', kind: 'choice', label: 'Machine M', def: 'contains-11', options: MACHINES },
      { id: 'w', kind: 'string', label: 'w', def: '11', max: 5 },
    ],
    check: (inp) => { const al = T.tmLib.entry(inp.m).alphabet; const bad = [...inp.w].find((c) => !al.includes(c)); return bad !== undefined ? 'w: "' + bad + '" is not in this M\'s alphabet {' + al.join(', ') + '}' : null; },
    presets: [
      { label: 'L contains 1; M accepts w', values: { p: 'has-1', m: 'contains-11', w: '11' } },
      { label: 'L infinite; M rejects w', values: { p: 'infinite', m: 'anbn', w: 'aab' } },
      { label: 'ε ∈ L; M loops on w', values: { p: 'has-eps', m: 'aa-recogniser', w: 'bab' } },
      { label: 'L = ∅: the complement case', values: { p: 'empty', m: 'contains-11', w: '011' } },
      { label: 'w = ε', values: { p: 'has-1', m: 'anbn', w: '' } },
    ],
    run(inp) {
      const P = PROPS[inp.p];
      const res = T.comp.riceCheck({ test: (e) => P.test(e) }, cat());
      const target = cat().find((e) => e.name === res.target);
      const M = Object.assign({}, T.tmLib.get(inp.m), { name: 'M' });
      const w = inp.w;
      const Mw = res.template(M, w);
      const mv = T.tm.run(M, w, { maxSteps: 4000, trace: false }).verdict;
      const acc = mv === 'accept';
      const F = new T.Frames();
      const tLang = LANGS.find((l) => l.id === target.lang).label;
      const BW = 420;
      // phase 1: choose T
      const c1 = card('empty', 0, 0, ['∅ ' + (res.emptyHas ? 'has' : 'lacks') + ' the property'], { w: BW, cls: res.emptyHas ? 'hot' : '' });
      const c2 = card('target', 0, 70, ['T = ' + target.name + ': ' + tLang, 'which ' + (res.emptyHas ? 'lacks' : 'has') + ' the property'], { w: BW, cls: 'act' });
      const head = card('prop', 0, -70, ['P: ' + P.label], { w: BW });
      F.add({ phase: 1, items: [head, c1], say: 'First look at the empty language: it ' + (res.emptyHas ? 'has' : 'lacks') + ' the property. ' + (res.emptyHas ? 'So we work with the complement of P instead, which ∅ lacks; a decider for P would decide its complement too.' : 'Good: machines that never accept will stand for "no".'), hl: { proof: [0] } });
      F.add({ phase: 1, items: [head, c1, c2], say: 'Since P is non-trivial, some machine\'s language ' + (res.emptyHas ? 'lacks' : 'has') + ' it: take T = ' + target.name + ', whose language is ' + tLang.replace(/^L = /, '') + '.', hl: { proof: [1] } });
      // phase 2: build M_w
      const lines = Mw.lines;
      const box = (n, hot, done) => K.mbox.draw({ prefix: 'mw', x: 0, y: 0, w: BW, title: 'M_w', input: 'x', lines: lines.slice(0, n), hot, done, inner: n >= lines.length ? [{ prefix: 'mw:M', title: 'M, copied in', cls: 'r2', lines: ['runs on w = ' + eps(w)] }, { prefix: 'mw:T', title: 'T = ' + target.name + ', copied in', cls: 'r1', lines: ['runs on x'] }] : [] });
      for (let n = 1; n <= lines.length; n++) F.add({ phase: 2, items: box(n, [n - 1]).items, say: n === 1 ? 'Build M_w from ⟨M, w⟩. It takes an input x …' : n === 2 ? '… first it runs M on w, ignoring x. If M rejects or loops, so does M_w, on every x.' : '… and only if M accepted, it runs T on x and answers as T does.', hl: { proof: [2] } });
      // phase 3: the two cases
      const b0 = box(lines.length, []);
      const by = b0.box.h + 40, half = (BW - 20) / 2;
      const yes = card('caseYes', 0, by, ['M accepts w:', 'L(M_w) = L(T)', res.emptyHas ? 'lacks P' : 'has P'], { w: half, pick: true });
      const no = card('caseNo', half + 20, by, ['M does not:', 'L(M_w) = ∅', res.emptyHas ? 'has P' : 'lacks P'], { w: half, pick: true });
      F.add({ phase: 3, items: b0.items.concat([yes, no]), say: 'Two cases. If M accepts w, M_w passes every x on to T, so L(M_w) = L(T). If not, M_w never accepts anything: L(M_w) = ∅.', meta: { branch: acc ? 'caseYes' : 'caseNo' }, hl: { proof: [3] } });
      yes.cls += acc ? ' good' : ' off'; no.cls += acc ? ' off' : ' bad';
      const run1 = box(lines.length, [1]);
      F.add({ phase: 3, items: run1.items.concat([yes, no]), say: 'Here M ' + ({ accept: 'accepts', reject: 'rejects', loop: 'loops for ever on', limit: 'does not stop on' }[mv] || mv) + ' ' + eps(w) + (mv === 'loop' ? '' : '') + ', so ' + (acc ? 'L(M_w) = L(T).' : 'L(M_w) = ∅.'), hl: { proof: [3] } });
      // the language of M_w, drawn
      const sy = by + 140;
      const rows = [[''], ['0', '1'], ['00', '01', '10', '11'], ['000', '001', '010', '011', '100', '101', '110', '111']];
      const strip = [{ key: 'lt', kind: 'text', x: BW / 2, y: sy - 12, text: 'L(M_w), strings up to length 3', anchor: 'middle', cls: 'title' }];
      rows.forEach((r, l) => r.forEach((s, k) => { const v = Mw.run(s, 3000).verdict; strip.push({ key: 'ls:' + (s || 'e'), kind: 'cell', x: BW / 2 - (r.length * 48 - 4) / 2 + k * 48, y: sy + l * 40, w: 44, h: 34, text: eps(s), size: 14, cls: 'mono ' + (v === 'accept' ? 'good' : 'lout'), rx: 5 }); }));
      F.add({ phase: 3, items: run1.items.concat([yes, no], strip), say: acc ? 'Running M_w on short strings: it accepts exactly what T accepts.' : 'Running M_w on short strings: it accepts none of them' + (mv === 'loop' ? ' (it is stuck running M on w for ever)' : '') + '.', hl: { proof: [3] } });
      // phase 4: the decider for A_TM it would give
      const d = K.mbox.draw({ prefix: 'atm', x: 0, y: 0, w: BW, title: 'would-be decider for A_TM', input: '⟨M, ' + eps(w) + '⟩', lines: ['1. Build ⟨M_w⟩ (just writing text).', '2. Ask the decider for P about ⟨M_w⟩.', res.emptyHas ? '3. Give the opposite answer.' : '3. Give its answer.'], inner: [{ title: 'claimed decider for P', cls: 'r4', lines: ['says ' + ((acc !== res.emptyHas) ? 'yes' : 'no') + ' for ⟨M_w⟩'] }], hot: [2], outs: K.mbox.answers(acc ? 'accept' : 'reject') });
      const fin = card('fin', 0, d.box.h + 30, ['No such decider exists, so P is undecidable.'], { w: BW, cls: 'bad' });
      F.add({ phase: 4, items: d.items.concat(fin), say: 'Put together: a decider for P would tell us whether M accepts w' + (res.emptyHas ? ' (flipping its answer, since ∅ has P)' : '') + '. That decides A_TM, which is impossible. So P is undecidable.', mark: 'accepted', hl: { proof: [4] } });
      // one camera per phase
      const boxes = new Map();
      for (const f of F.list) { const b = T.stageBounds(f.items); boxes.set(f.phase, boxes.has(f.phase) ? Geo.union([boxes.get(f.phase), b]) : b); }
      for (const f of F.list) f.view = boxes.get(f.phase);
      return { frames: F.list, def: { sections: [
        { id: 'proof', kind: 'math', title: 'The template', text: (res.emptyHas ? '∅ ∈ P: use the complement of P\n' : '∅ ∉ P\n') + 'T: a machine with L(T) ' + (res.emptyHas ? '∉' : '∈') + ' P\nM_w(x): run M on w; if it accepts, run T on x\nM accepts w ⇒ L(M_w) = L(T); else L(M_w) = ∅\ndecider for P ⇒ decider for A_TM' },
        { id: 'm', kind: 'text', title: 'M on w', text: T.tmLib.entry(inp.m).title + ': on ' + eps(w) + ' it ' + mv + 's.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.branch, once: true, pick: 'item', ask: 'Which case are we in? Click it.', answer: (fr, i) => fr[i].meta.branch, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does M_w do with its own input x before M has accepted w?', options: ['Runs T on it', 'Ignores it while running M on w', 'Rejects it', 'Copies it'], answer: 1, why: 'x matters only after M accepts w; that is what makes L(M_w) either L(T) or ∅.' },
      { q: 'Why do we need ∅ to lack the property (or switch to the complement)?', options: ['So that the "M does not accept w" case, where L(M_w) = ∅, gives the answer no', 'Because ∅ is not recognisable', 'To make M_w halt', 'It does not matter'], answer: 0, why: 'If M does not accept w, L(M_w) = ∅; we need that case to land on the other side of the property from L(T).' },
      { q: 'Why does the theorem need the property to be non-trivial?', options: ['To find a T whose language has the property', 'To make the proof shorter', 'Because trivial properties are about machines', 'It does not'], answer: 0, why: 'Without some T with the property (and ∅ without it) there is nothing to build M_w from; and trivial properties are decidable.' },
      { q: 'Does building M_w require running M?', options: ['Yes, to see if it accepts', 'No: it only writes M\'s text into a template', 'Only when w = ε', 'Only for deciders'], answer: 1, why: 'The reduction is computable because it only writes text; M_w runs M later, if anyone runs M_w.' },
    ],
  });
})();
