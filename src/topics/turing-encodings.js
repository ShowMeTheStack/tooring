// Machines as data: a Turing machine written as a string of 0s and 1s, read back again (with the ways a
// string can fail to be a machine), a universal machine running such a string on three tapes, and the
// busy beavers, the champions among small machines.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const TK = () => T.TK;

  T.family({ id: 'tm-encodings', part: 'turing', order: 60, title: 'Encodings and universality', blurb: 'A machine is finite, so it can be written down as a string, and a string can be the input of another machine. One machine, the universal one, runs them all.' });

  const ENC = { even: { id: 'even-length', alpha: 'ab' }, c11: { id: 'contains-11', alpha: '01' }, flip: { id: 'complement', alpha: '01' }, div3: { id: 'div3', alpha: '01' } };
  const encOpts = [{ value: 'even', label: 'even length' }, { value: 'c11', label: 'contains 11' }, { value: 'flip', label: 'flip every bit' }, { value: 'div3', label: 'binary multiple of 3' }];
  const BW = 14, BH = 24;
  /** bits as small cells, one class per field: fields are runs of 0s, separated by single 1s */
  function bitRow(prefix, bits, x, y, clsOf, enter) {
    return [...bits].map((b, i) => ({ key: prefix + i, kind: 'cell', x: x + i * BW, y, w: BW, h: BH, text: b, rx: 2, cls: 'tu-bit mono ' + (clsOf ? clsOf(i, b) : ''), size: 12, enter: enter || 'fade' }));
  }
  /** for a rule's code, the field (0..4) each bit belongs to, or -1 for a separating 1 */
  const fieldsOf = (code) => { const out = []; let f = 0; for (const b of code) { if (b === '1') { out.push(-1); f++; } else out.push(f); } return out; };
  const FIELD = ['state', 'reads', 'next state', 'writes', 'move'];

  // ======================================================================================================
  // Encoding: number the states and symbols, write each rule as five runs of 0s
  // ======================================================================================================
  T.topic({
    id: 'tm-encode', family: 'tm-encodings', order: 10, title: 'A machine as a string of bits',
    blurb: 'Number the states and the symbols, write each number as a run of 0s, separate the five parts of a rule with 1 and the rules with 11. The whole machine becomes one string ⟨M⟩, and ⟨M, w⟩ adds its input after 111.',
    inputs: [{ id: 'm', kind: 'choice', label: 'Machine', def: 'even', options: encOpts }, { id: 'w', kind: 'string', label: 'Input w', def: 'ab', max: 4, check: (v, inp) => ([...v].some((c) => !ENC[inp.m].alpha.includes(c)) ? 'Input w: use only ' + [...ENC[inp.m].alpha].join(' and ') : null) }],
    presets: [
      { label: 'Even length, w = ab', values: { m: 'even', w: 'ab' } },
      { label: 'Contains 11, w = 011', values: { m: 'c11', w: '011' } },
      { label: 'Flip every bit: three rules', values: { m: 'flip', w: '10' } },
      { label: 'Multiple of 3, w = ε', values: { m: 'div3', w: '' } },
    ],
    counters: [{ id: 'rules', label: 'rules written' }, { id: 'bits', label: 'bits' }],
    run(inp) {
      const tk = TK();
      const M = T.tmLib.get(ENC[inp.m].id);
      const e = T.enc.encodeTM(M);
      const io = T.enc.encodeTMInput(M, inp.w);
      const q = Object.entries(e.states).sort((a, b) => a[1] - b[1]), s = Object.entries(e.symbols).sort((a, b) => a[1] - b[1]);
      const tq = K.table.draw({ x: 0, y: 0, prefix: 'tq', colHead: ['state', 'number'], rows: q.map(([n, i]) => [n, 'q' + i]), size: 14 });
      const ts = K.table.draw({ x: 0, y: tq.box.h + 30, prefix: 'ts', colHead: ['symbol', 'number'], rows: s.map(([n, i]) => [tk.sym(n), String(i)]), size: 14 });
      const tm = K.table.draw({ x: 0, y: tq.box.h + ts.box.h + 60, prefix: 'tmv', colHead: ['move', 'number'], rows: [['L', '1'], ['R', '2'], ['S', '3']], size: 14 });
      const RX = Math.max(tq.box.w, ts.box.w) + 60, RY = 0, RH = 54;
      const F = new T.Frames(['rules', 'bits']);
      const nameQ = (i) => q.find((x) => x[1] === i)[0], nameS = (i) => tk.sym(s.find((x) => x[1] === i)[0]);
      const ruleRows = (upto, hot) => {
        const items = [];
        for (let k = 0; k < upto; k++) {
          const f = e.rules[k], code = f.map((n) => '0'.repeat(n)).join('1');
          const y = RY + k * RH;
          items.push({ key: 'rt' + k, kind: 'text', x: RX, y: y + 12, text: 'δ(' + nameQ(f[0]) + ', ' + nameS(f[1]) + ') = (' + nameQ(f[2]) + ', ' + nameS(f[3]) + ', ' + T.enc.MOVE_NAME[f[4]] + ')   →   δ(q' + f[0] + ', ' + f[1] + ') = (q' + f[2] + ', ' + f[3] + ', ' + f[4] + ')', cls: 'mono', mono: true, size: 13 });
          const fl = fieldsOf(code);
          items.push(...bitRow('rb' + k + ':', code, RX, y + 20, (i) => (fl[i] < 0 ? '' : 'tu-k' + (fl[i] + 1)) + (k === hot ? '' : ''), k === hot ? 'grow' : 'fade'));
        }
        return items;
      };
      const tables = (lit) => tq.items.concat(ts.items, tm.items).map((it) => (lit && it.key.startsWith(lit) ? Object.assign({}, it, { cls: (it.cls || '') + ' hot' }) : it));
      F.add({ items: tables().concat([{ key: 'hT', kind: 'text', x: RX, y: -24, text: 'RULES', cls: 'title' }]), say: 'First number everything: the start state is q1, the accepting state q2, the rejecting one q3, the rest q4 on; the blank is symbol 1; moves L, R, S are 1, 2, 3. Each number n will be written as n zeros.' });
      e.rules.forEach((f, k) => {
        F.count('rules').count('bits', f.reduce((a, n) => a + n, 0) + 4);
        const code = f.map((n) => '0'.repeat(n)).join('1');
        F.add({ items: tables().concat(ruleRows(k + 1, k), [{ key: 'hT', kind: 'text', x: RX, y: -24, text: 'RULES', cls: 'title' }]), say: 'δ(' + nameQ(f[0]) + ', ' + nameS(f[1]) + ') = (' + nameQ(f[2]) + ', ' + nameS(f[3]) + ', ' + T.enc.MOVE_NAME[f[4]] + ') is the five numbers ' + f.join(', ') + ', written ' + code + ': runs of 0s for the numbers, a single 1 between them.', meta: { code, f } });
      });
      // the whole code wrapped in lines, then the input after 111
      const PER = 34, all = io.code;
      const ribbonY = RY + e.rules.length * RH + 40;
      const ribbon = (upto) => {
        const items = [{ key: 'ribT', kind: 'text', x: RX, y: ribbonY - 10, text: upto > e.code.length ? '⟨M, w⟩' : '⟨M⟩', cls: 'title' }];
        const sepAt = new Set();
        for (let i = 0; i + 1 < e.code.length; i++) if (e.code[i] === '1' && e.code[i + 1] === '1') { sepAt.add(i); sepAt.add(i + 1); }
        for (let i = 0; i < Math.min(upto, all.length); i++) {
          const inW = i >= e.code.length + 3, mid = i >= e.code.length && i < e.code.length + 3;
          items.push({ key: 'rib' + i, kind: 'cell', x: RX + (i % PER) * BW, y: ribbonY + Math.floor(i / PER) * (BH + 6), w: BW, h: BH, text: all[i], rx: 2, size: 12, cls: 'tu-bit mono' + (sepAt.has(i) ? ' hot' : mid ? ' bad' : inW ? ' tu-k2' : '') });
        }
        return items;
      };
      F.add({ items: tables().concat(ruleRows(e.rules.length, -1), ribbon(e.code.length)), say: 'Join the rules with 11. Inside a rule there is never 11, since every number is at least one 0, so 11 can only be a separator: ⟨M⟩ is ' + e.code.length + ' bits.', mark: '⟨M⟩' });
      F.set('bits', all.length);
      F.add({ items: tables('ts').concat(ruleRows(e.rules.length, -1), ribbon(all.length)), say: 'Then 111, which never occurs inside ⟨M⟩, and the input ' + (inp.w || 'ε') + ' symbol by symbol (' + ([...inp.w].map((c) => c + ' = ' + e.symbols[c]).join(', ') || 'nothing') + '), written as runs of 0s joined by 1: ⟨M, w⟩ has ' + all.length + ' bits.', mark: '⟨M, w⟩' });
      const fr = F.list;
      if (fr.length > 3 && fr[2].meta) { const right = fr[2].meta.code; const wrong = fr[2].meta.f.map((n) => '1'.repeat(n)).join('0'); const w2 = fr[2].meta.f.map((n) => '0'.repeat(n)).join('11'); fr[1].predict = { ask: 'How will the next rule, with numbers ' + fr[2].meta.f.join(', ') + ', be written?', options: [right, wrong, w2].sort(), answer: right, explain: 'Each number n is n zeros, and single 1s separate the five numbers.', pick: 'option' }; }
      return { frames: fr, def: { sections: [{ id: 'conv', kind: 'math', title: 'The convention', text: 'states q1 (start), q2 (accept), q3 (reject), q4, …\nsymbols 1 (blank), 2, 3, …   moves L = 1, R = 2, S = 3\nδ(qi, j) = (qk, l, m)  ↦  0^i 1 0^j 1 0^k 1 0^l 1 0^m\nrules joined by 11;  ⟨M, w⟩ = ⟨M⟩ 111 ⟨w⟩' }, tk.defOf(M).sections[1]] } };
    },
    quiz: [
      { q: 'Why can 11 only appear between rules?', options: ['By luck', 'Every number is written as at least one 0, so two 1s in a row never occur inside a rule', 'Rules end in 1', 'It can appear anywhere'], answer: 1, why: 'Inside a rule, 1s separate non-empty runs of 0s.' },
      { q: 'How is δ(q4, 2) = (q1, 3, L) written?', options: ['0000100101000101', '000010010100010', '4 2 1 3 1', '00001001010001'], answer: 0, why: '0000 1 00 1 0 1 000 1 0: four, two, one, three and one 0s.' },
      { q: 'Why does it matter that machines can be written as strings?', options: ['For storage only', 'Machines can then be inputs to machines: universal machines, and questions like "does M halt on w?"', 'It makes them faster', 'It does not'], answer: 1, why: 'The halting problem, Rice\'s theorem and the universal machine all need machines as data.' },
      { q: 'Are there more machines than binary strings?', options: ['Yes', 'No: every machine has a code, so there are countably many machines', 'Equally many as real numbers', 'Finitely many'], answer: 1, why: 'Each machine is named by a finite string, so the machines can be listed one by one.' },
    ],
  });

  // ======================================================================================================
  // Decoding: split, count, rebuild, or find what is wrong
  // ======================================================================================================
  const codeOf = (id) => T.enc.encodeTM(T.tmLib.get(id)).code;
  T.topic({
    id: 'tm-decode', family: 'tm-encodings', order: 20, title: 'Reading a string as a machine',
    blurb: 'Split at 11 into rules, split each rule at 1 into five runs of 0s, count them, and the table comes back. Not every string makes it: a 111, a missing field or two rules for one situation, and the string is no machine.',
    inputs: [{ id: 'c', kind: 'string', label: 'Bits', def: codeOf('complement'), alphabet: '01', max: 170 }],
    presets: [
      { label: 'Flip every bit', values: { c: codeOf('complement') } },
      { label: 'Even length', values: { c: codeOf('even-length') } },
      { label: 'Not a machine: 111 inside', values: { c: '010100100100111010' } },
      { label: 'Not a machine: four fields', values: { c: '010010100' } },
      { label: 'Not a machine: two rules for q1 on 1', values: { c: '0101010101101010100100' } },
      { label: 'The empty string: no rules at all', values: { c: '' } },
    ],
    counters: [{ id: 'rules', label: 'rules read' }],
    run(inp) {
      const tk = TK();
      const code = inp.c;
      const chk = T.enc.checkTM(code);
      const PER = 34;
      const F = new T.Frames(['rules']);
      const parts = code ? code.split('11') : [];
      // where each part starts in the string
      const starts = []; { let p = 0; for (const x of parts) { starts.push(p); p += x.length + 2; } }
      const ribbon = (hot, bad) => {
        const items = [{ key: 'ribT', kind: 'text', x: 0, y: -12, text: 'THE STRING', cls: 'title' }];
        if (!code.length) items.push({ key: 'eps', kind: 'cell', x: 0, y: 0, w: 46, h: BH, text: 'ε', cls: 'mono empty' });
        for (let i = 0; i < code.length; i++) {
          const pi = starts.findIndex((s0, j) => i >= s0 && i < s0 + parts[j].length);
          const inPart = pi >= 0;
          items.push({ key: 'b' + i, kind: 'cell', x: (i % PER) * BW, y: Math.floor(i / PER) * (BH + 6), w: BW, h: BH, text: code[i], rx: 2, size: 12, cls: 'tu-bit mono' + (!inPart ? ' read' : pi === bad ? ' bad' : pi === hot ? ' hot' : pi < hot || hot === Infinity ? ' tu-k' + ((pi % 2) + 1) : '') });
        }
        return items;
      };
      const ribH = Math.max(1, Math.ceil(code.length / PER)) * (BH + 6);
      const listY = ribH + 50;
      const decoded = (upto, bad, msg) => {
        const items = [{ key: 'dT', kind: 'text', x: 0, y: listY - 12, text: 'RULES READ', cls: 'title' }];
        for (let k = 0; k < upto && k < 12; k++) {
          const f = parts[k].split('1').map((x) => x.length);
          const ok = f.length === 5 && f.every((n) => n > 0);
          items.push({ key: 'd' + k, kind: 'text', x: 0, y: listY + 12 + k * 26, text: (k + 1) + '.  ' + f.join(' · ') + (ok ? '   δ(q' + f[0] + ', ' + f[1] + ') = (q' + f[2] + ', ' + f[3] + ', ' + (T.enc.MOVE_NAME[f[4]] || '?' + f[4]) + ')' : ''), cls: k === bad ? 'bad' : 'mono', mono: true, size: 14 });
        }
        if (msg) items.push({ key: 'msg', kind: 'text', x: 0, y: listY + 20 + Math.min(upto, 12) * 26, text: msg, cls: 'bad' });
        return items;
      };
      if (!code.length) {
        F.add({ items: ribbon(-1), say: 'The empty string. Split into rules, it has none.' });
        const D = T.enc.decodeTM('');
        F.add({ items: ribbon(-1).concat(decoded(0)), say: 'With no rules, the machine is in q1 and has no move on anything: it halts at once and rejects every input. A legal machine, and a dull one.', mark: 'decoded', meta: { M: D.machine } });
        F.list[0].predict = { ask: 'Is the empty string a machine?', options: ['Yes', 'No'], answer: 'Yes', explain: 'A machine with no rules is still a machine; it rejects everything.', pick: 'option' };
        return { frames: F.list, def: { sections: [{ id: 'conv', kind: 'math', title: 'Reading the code', text: 'split at 11 into rules\nsplit a rule at 1 into five runs of 0s\ncount: (i, j, k, l, m) is δ(qi, j) = (qk, l, move m)\nmove 1 = L, 2 = R, 3 = S' }] } };
      }
      F.add({ items: ribbon(-1), say: 'A string of ' + code.length + ' bits. Is it a machine? Start by cutting it at every 11.' + (code.includes('111') ? ' (There is a 111 in it: that cannot happen inside a machine, as we will see.)' : '') });
      let firstBad = -1;
      parts.forEach((p, k) => {
        const f = p.split('1').map((x) => x.length);
        const empty = f.some((n) => n === 0), five = f.length === 5;
        const bad = empty || !five || (five && f[4] > 3) || (five && (f[0] === 2 || f[0] === 3));
        if (k < 14) F.count('rules');
        if (bad && firstBad < 0) firstBad = k;
        if (k >= 14) return;
        const what = empty ? 'a field with no 0s in it, which no number can be written as' : !five ? f.length + ' fields instead of 5' : f[4] > 3 ? 'move ' + f[4] + ', and only 1, 2 and 3 are moves' : f[0] === 2 || f[0] === 3 ? 'a move out of the halting state q' + f[0] : null;
        F.add({ items: ribbon(k, bad ? k : -1).concat(decoded(k + 1, bad ? k : -1)), say: 'Part ' + (k + 1) + ', ' + (p || 'empty') + ': runs of ' + f.join(', ') + ' zeros. ' + (what ? 'That is ' + what + '.' : 'So δ(q' + f[0] + ', ' + f[1] + ') = (q' + f[2] + ', ' + f[3] + ', ' + T.enc.MOVE_NAME[f[4]] + ').'), meta: { bad, k } });
      });
      if (!chk.ok) {
        F.add({ items: ribbon(Infinity, firstBad).concat(decoded(Math.min(parts.length, 12), firstBad, chk.errors[0])), say: 'Not a machine: ' + chk.errors.join('; ') + '. A machine that lists every code would skip this string (or read it as a machine that rejects everything, by convention).', mark: 'not a machine' });
      } else {
        const D = T.enc.decodeTM(code);
        const M = D.machine;
        const d = tk.diagram(M), pos = K.graph.layout(d).pos;
        const g0 = K.graph.draw(d, { pos });
        const gy = listY + Math.min(parts.length, 12) * 26 + 70 - g0.box.y;
        const g = K.graph.draw(d, { pos, y: gy, x: -g0.box.x + 20 });
        F.add({ items: ribbon(Infinity).concat(decoded(Math.min(parts.length, 12)), g.items), say: 'Every part is a well-formed rule and no two disagree: the string is the machine drawn here, with states q1 (start), q2 (accept), q3 (reject) and symbols 1 = ⊔, 2 = 0, 3 = 1.', mark: 'decoded' });
      }
      const fr = F.list;
      fr[0].predict = { ask: 'Is this string the code of a machine?', options: ['Yes', 'No'], answer: chk.ok ? 'Yes' : 'No', explain: chk.ok ? 'Every part decodes to a rule and no two rules clash.' : chk.errors[0] + '.', pick: 'option' };
      return { frames: fr, def: { sections: [{ id: 'conv', kind: 'math', title: 'Reading the code', text: 'split at 11 into rules\nsplit a rule at 1 into five runs of 0s\ncount: (i, j, k, l, m) is δ(qi, j) = (qk, l, move m)\nmove 1 = L, 2 = R, 3 = S\nsymbol 1 = ⊔, 2 = 0, 3 = 1, 4 = X, …' }, { id: 'bad', kind: 'text', title: 'Ways to fail', text: '111 inside; a field with no 0s; not five fields; a move above 3; a rule leaving q2 or q3; two rules for the same state and symbol.' }] } };
    },
    quiz: [
      { q: 'Why can a machine code never contain 111?', options: ['It is reserved', 'Inside a rule 1s separate runs of 0s, and rules are separated by exactly 11, so three 1s in a row never arise', 'It means halt', 'It can'], answer: 1, why: 'That is why 111 can mark the end of ⟨M⟩ in ⟨M, w⟩.' },
      { q: 'Two rules start 0^1 1 0^2. What is wrong?', options: ['Nothing', 'Both say what to do in q1 reading symbol 2: the machine would not be deterministic', 'The state is too small', 'They must be adjacent'], answer: 1, why: 'A deterministic machine has at most one rule per state and symbol.' },
      { q: 'A listing of all machines M1, M2, … meets a string that is no machine. What can it do?', options: ['Stop', 'Skip it, or agree that it stands for a fixed machine that rejects everything', 'Crash', 'Guess'], answer: 1, why: 'Either way every string names some machine, which keeps the listing simple.' },
      { q: 'Is it decidable whether a bit string is a machine code?', options: ['Yes: the checks are simple scans', 'No', 'Only for short strings', 'Only with an oracle'], answer: 0, why: 'Counting runs and comparing pairs of rules always finishes.' },
    ],
  });

  // ======================================================================================================
  // The universal machine: ⟨M⟩ on tape 1, M's tape in blocks on tape 2, the state on tape 3
  // ======================================================================================================
  T.topic({
    id: 'utm-run', family: 'tm-encodings', order: 30, title: 'The universal machine',
    blurb: 'One fixed machine runs any machine given as a string. Tape 1 holds ⟨M⟩, tape 2 holds M\'s tape with each symbol as a block of 0s, tape 3 holds M\'s state. Each step: find the matching rule on tape 1, then carry it out.',
    inputs: [{ id: 'm', kind: 'choice', label: 'Machine to run', def: 'c11', options: encOpts }, { id: 'w', kind: 'string', label: 'Its input', def: '0110', max: 5, check: (v, inp) => ([...v].some((c) => !ENC[inp.m].alpha.includes(c)) ? 'Its input: use only ' + [...ENC[inp.m].alpha].join(' and ') : null) }],
    presets: [
      { label: 'Contains 11, on 0110', values: { m: 'c11', w: '0110' } },
      { label: 'Even length, on aba (rejected)', values: { m: 'even', w: 'aba' } },
      { label: 'Flip every bit, on 101', values: { m: 'flip', w: '101' } },
      { label: 'Multiple of 3, on 110', values: { m: 'div3', w: '110' } },
    ],
    counters: [{ id: 'sim', label: 'steps of M' }, { id: 'cost', label: 'cells the UTM passes' }],
    run(inp) {
      const tk = TK();
      const M = T.tmLib.get(ENC[inp.m].id);
      const io = T.enc.encodeTMInput(M, inp.w);
      const names = io.enc.symbolNames;
      const qname = Object.fromEntries(Object.entries(io.enc.states).map(([k, v]) => [v, k]));
      const u = T.utm.run(io.code, { maxSteps: 60 });
      const desc = io.machine, spans = [];
      { let p = 0; for (const r of desc.split('11')) { spans.push([p, p + r.length]); p += r.length + 2; } }
      const N = 30, CW = 18, gap = 78;
      const s1 = K.tape.scroller({ cells: N, origin: -1, margin: 4 }), s2 = K.tape.scroller({ cells: N, origin: -1, margin: 4 });
      const F = new T.Frames(['sim', 'cost']);
      const decodeWork = (t2, head2) => { const blocks = t2.split('1').map((b) => b.length); const hb = t2.slice(0, head2).split('').filter((c) => c === '1').length; return { syms: blocks.map((n) => names[n - 1] || '?'), hb }; };
      const scene = (n, headCls) => {
        const items = [];
        const sp = n.rule !== undefined ? spans[n.rule] : null;
        const fl = sp ? fieldsOf(desc.slice(sp[0], sp[1])) : null;
        items.push(...K.tape.draw({ tape: [...n.tape1], head: n.head1, state: 'rules', cells: N, cw: CW, ch: 24, origin: s1.at(n.head1), prevOrigin: s1.prev, x: 0, y: 0, prefix: 'u1', label: '⟨M⟩', headCls: 'read', cls: (i) => 'tu-bit' + (sp && i >= sp[0] && i < sp[1] ? (fl[i - sp[0]] < 0 ? ' hot' : ' tu-k' + (fl[i - sp[0]] + 1)) : '') }).items);
        items.push(...K.tape.draw({ tape: [...n.tape2], head: n.head2, state: 'block', cells: N, cw: CW, ch: 24, origin: s2.at(n.head2), prevOrigin: s2.prev, x: 0, y: gap, prefix: 'u2', label: 'tape of M', headCls: 'read', cls: () => 'tu-bit' }).items);
        items.push(...K.tape.draw({ tape: [...n.tape3], head: 0, state: 'q' + n.tape3.length, cells: 10, cw: CW, ch: 24, origin: -1, x: 0, y: 2 * gap, prefix: 'u3', label: 'state', headCls: headCls || 'read', cls: () => 'tu-bit' }).items);
        // what it all means: M's own tape, decoded
        const dw = decodeWork(n.tape2, n.head2);
        const dy = 3 * gap + 40;
        items.push({ key: 'dT', kind: 'text', x: 0, y: dy - 12, text: 'WHAT THE TAPES MEAN: M IN ' + (qname[n.tape3.length] || 'q' + n.tape3.length).toUpperCase(), cls: 'title' });
        dw.syms.forEach((s, i) => items.push({ key: 'dm' + i, kind: 'cell', x: i * 40, y: dy, w: 40, h: 36, text: tk.sym(s), rx: 4, cls: 'mono' + (i === dw.hb ? ' act' : '') + (tk.sym(s) === tk.BL ? ' blank' : '') }));
        return items;
      };
      for (const n of u.trace) {
        let say = n.say;
        if (n.kind === 'utm-start') say = 'Tape 1 holds ⟨M⟩ (' + desc.length + ' bits). Tape 2 holds ' + (inp.w || 'ε') + ' as blocks of 0s separated by 1s. Tape 3 holds 0, the start state q1. The row underneath decodes what M itself would see.';
        else if (n.kind === 'utm-find') { const f = n.fields; say = 'M is in q' + n.tape3.length + ' reading symbol ' + f[1] + ' (' + tk.sym(names[f[1] - 1]) + '). Scanning tape 1 rule by rule, rule ' + (n.rule + 1) + ' starts with 0^' + f[0] + ' 1 0^' + f[1] + ': write ' + tk.sym(names[f[3] - 1]) + ', move ' + T.enc.MOVE_NAME[f[4]] + ', go to q' + f[2] + '.'; }
        else if (n.kind === 'utm-step') { F.count('sim'); say = 'Carry it out: rewrite the block on tape 2, move to the neighbouring block, and write 0^' + n.tape3.length + ' on tape 3. One step of M done.'; }
        const fin = n.kind === 'accept' || n.kind === 'reject';
        if (fin) F.set('cost', u.cost);
        F.add({ items: scene(n, fin ? (n.kind === 'accept' ? 'good' : 'bad') : ''), say: fin ? say + ' It took ' + u.cost + ' cell visits to simulate ' + u.steps + ' steps: slower by a factor depending on the size of ⟨M⟩, but the same answer.' : say, mark: fin ? n.kind + 'ed' : undefined, meta: { kind: n.kind, rule: n.rule } });
      }
      const fr = F.list;
      const f1 = fr.findIndex((f) => f.meta && f.meta.kind === 'utm-find');
      if (f1 > 0) fr[f1 - 1].predict = { ask: 'Which rule on tape 1 will the universal machine use first? (counting from 1)', options: Array.from({ length: Math.min(4, spans.length) }, (_, i) => String(i + 1)), answer: String(fr[f1].meta.rule + 1), explain: fr[f1].say, pick: 'option' };
      if (fr[f1 - 1] && fr[f1 - 1].predict && !fr[f1 - 1].predict.options.includes(fr[f1 - 1].predict.answer)) delete fr[f1 - 1].predict;
      if (!fr.some((f) => f.predict)) fr[0].predict = { ask: 'Will M accept ' + (inp.w || 'ε') + '?', options: ['Yes', 'No'], answer: u.verdict === 'accept' ? 'Yes' : 'No', explain: fr[fr.length - 1].say, pick: 'option' };
      return { frames: fr, def: { sections: [{ id: 'utm', kind: 'text', title: 'The universal machine U', text: 'U(⟨M, w⟩) does what M does on w: accepts if M accepts, rejects if M rejects, runs for ever if M does. U is one fixed machine with a fixed number of states, yet it runs machines with any number of states, because their states and symbols are numbers written on its tapes.' }, tk.defOf(M).sections[1]] } };
    },
    quiz: [
      { q: 'How can a machine with a fixed number of states run machines with more states than it has?', options: ['It cannot', 'The simulated state is written on a tape as a number, not held in U\'s own states', 'It grows new states', 'By nondeterminism'], answer: 1, why: 'Tape 3 holds 0^i for state qi; any i fits.' },
      { q: 'What does U do when M runs for ever on w?', options: ['Rejects', 'Runs for ever too', 'Accepts', 'Halts with an error'], answer: 1, why: 'U faithfully simulates M, step by step; it cannot know in advance that M will not halt.' },
      { q: 'Why does U store each symbol as a block of 0s?', options: ['To save space', 'M may have more symbols than U, so they are written as numbers', 'Blocks are faster', 'For neatness'], answer: 1, why: 'U\'s alphabet is fixed (0, 1, blank), while M may use any number of symbols.' },
      { q: 'Which idea does the universal machine make real?', options: ['Hardware and software: one machine, any program as data', 'Parallelism', 'Nondeterminism', 'Finite memory'], answer: 0, why: 'A single general-purpose machine that reads its program, which is what a stored-program computer is.' },
    ],
  });

  // ======================================================================================================
  // Busy beavers: the small machines that run longest and write most before halting
  // ======================================================================================================
  const BB = {
    bb2: { id: 'bb2', n: 2 }, bb3: { id: 'bb3', n: 3 }, bb3o: { id: 'bb3-ones', n: 3 }, bb4: { id: 'bb4', n: 4 },
    runaway: { text: 'blank: 0\ninput: 1\nstart: A\nhalt: H\nA, 0 -> B, 1, R\nB, 0 -> A, 1, R\nA, 1 -> H, 1, R\nB, 1 -> H, 1, R', n: 2, name: 'a 2-state contender that never halts' },
  };
  const RECORD = [['1', '1', '1'], ['2', '6', '4'], ['3', '21', '6'], ['4', '107', '13'], ['5', '47,176,870', '4,098'], ['6', 'unknown', 'unknown']];
  T.topic({
    id: 'tm-busy-beaver', family: 'tm-encodings', order: 40, title: 'Busy beavers',
    blurb: 'Among all machines with n states and symbols 0 and 1 that halt on a blank tape, which runs longest, and which leaves the most 1s? Watch the champions, and see why the record for every n can never be computed.',
    inputs: [{ id: 'm', kind: 'choice', label: 'Machine', def: 'bb3', options: [{ value: 'bb2', label: '2-state champion' }, { value: 'bb3', label: '3-state, most steps' }, { value: 'bb3o', label: '3-state, most 1s' }, { value: 'bb4', label: '4-state champion' }, { value: 'runaway', label: 'a contender that never halts' }] }],
    presets: [
      { label: '2 states: 6 steps', values: { m: 'bb2' } },
      { label: '3 states: 21 steps', values: { m: 'bb3' } },
      { label: '3 states: 6 ones', values: { m: 'bb3o' } },
      { label: '4 states: 107 steps', values: { m: 'bb4' } },
      { label: 'A contender that never halts', values: { m: 'runaway' } },
    ],
    counters: [{ id: 'steps', label: 'steps' }, { id: 'ones', label: '1s on the tape' }],
    run(inp) {
      const tk = TK();
      const X = BB[inp.m];
      const M = X.text ? tk.compile(X.text).M : T.tmLib.get(X.id);
      const run = tk.trace(M, '', { max: X.text ? 24 : 200, loops: false });
      const d = tk.diagram(M), pos = K.graph.layout(d).pos;
      const g0 = K.graph.draw(d, { pos });
      const N = 15, CW = 36;
      const tx = g0.box.x + g0.box.w / 2 - (N * CW) / 2, ty = g0.box.y + g0.box.h + 70;
      const sc = K.tape.scroller({ cells: N, origin: -7, margin: 3 });
      const ones = (cfg) => cfg.tapes[0].trimmed().filter((s) => s === '1').length;
      const tbX = tx + N * CW + 60;
      const record = (lit) => K.table.draw({ x: tbX, y: g0.box.y, prefix: 'rec', colHead: ['n', 'most steps', 'most 1s'], rows: RECORD, hot: lit ? [[X.n - 1, 0], [X.n - 1, 1], [X.n - 1, 2]] : [], size: 14 }).items;
      const F = new T.Frames(['steps', 'ones']);
      const scene = (cfg, gopts, headCls, lit) => K.graph.draw(d, Object.assign({ pos }, gopts)).items.concat(tk.tape(cfg, { state: cfg.state, cells: N, cw: CW, origin: sc.at(cfg.heads[0].p), prevOrigin: sc.prev, x: tx, y: ty, label: 'tape', headCls, blank: M.blank, cls: (i, s) => (s === '1' ? 'tu-k3' : '') }).items, record(lit));
      F.add({ items: scene(run.list[0].cfg, { active: [M.start], startHot: true }), say: 'A ' + X.n + '-state machine on a tape of 0s. It has a rule for every state and symbol except the ones that lead to the halting state H. How long can it run before halting?' });
      for (let k = 1; k < run.list.length; k++) {
        const { cfg, rule } = run.list[k];
        F.count('steps').set('ones', ones(cfg));
        F.add({ items: scene(cfg, { active: [cfg.state], taken: [rule.from + '>' + rule.to] }), say: tk.sayRule(rule).replace(/ goes to H\./, ' halts.') });
      }
      const fin = run.last;
      if (run.verdict === 'accept') F.add({ items: scene(fin, { good: [fin.state] }, 'good', true), say: 'Halted after ' + (run.list.length - 1) + ' steps with ' + ones(fin) + ' ones on the tape. ' + (M.name === 'bb3' ? 'No 3-state machine that halts runs longer; the most 1s any leaves is 6.' : M.name === 'bb3-ones' ? 'No halting 3-state machine leaves more 1s, though one runs longer (21 steps).' : 'No halting ' + X.n + '-state machine runs longer or leaves more 1s.') + ' The records grow faster than any computable function.', mark: 'halted' });
      else F.add({ items: scene(fin, { bad: [fin.state] }, 'bad', true), say: 'Still running after ' + (run.list.length - 1) + ' steps, and it always will: it only ever sees 0s ahead of it. It is not a contender at all. Telling which machines will never halt is exactly what no program can do in general, and that is why the records cannot be computed.', mark: 'never halts' });
      const fr = F.list;
      if (run.verdict === 'accept' && fr.length > 3) { const n1 = ones(fin); fr[1].predict = { ask: 'How many 1s will be on the tape when it halts?', options: [...new Set([n1, n1 + 2, Math.max(1, n1 - 2), n1 * 2])].map(String).sort((a, b) => a - b), answer: String(n1), explain: 'It leaves ' + n1 + ' ones.', pick: 'option' }; }
      else fr[1].predict = { ask: 'Will this machine ever halt?', options: ['Yes', 'No'], answer: 'No', explain: 'Reading only 0s, it moves right every step and never reaches a rule into H.', pick: 'option' };
      return { frames: fr, def: { sections: [tk.defOf(M).sections[1], { id: 'why', kind: 'text', title: 'Why the record cannot be computed', text: 'If a program could compute S(n), the most steps of a halting n-state machine, it would decide the halting problem on blank tapes: run M for S(n) steps; if it has not halted by then, it never will. So S grows faster than every computable function. Only the first few values are known: S(5) = 47,176,870 was settled only recently, with computer-checked proofs.' }] } };
    },
    quiz: [
      { q: 'Why does knowing S(n) solve the halting problem for n-state machines on a blank tape?', options: ['It does not', 'Run the machine S(n) steps; if it has not halted, it never will', 'S(n) is the number of machines', 'Because S(n) is small'], answer: 1, why: 'No halting n-state machine runs longer than S(n), by definition.' },
      { q: 'How fast does S(n) grow?', options: ['Exponentially', 'Like Ackermann\'s function', 'Faster than every computable function', 'Polynomially'], answer: 2, why: 'If a computable f had f(n) ≥ S(n) for all n, it would decide halting; so no such f exists.' },
      { q: 'Is S(n) a well-defined number for each n?', options: ['No', 'Yes: finitely many n-state machines, take the longest halting run', 'Only for n ≤ 5', 'Only with an oracle'], answer: 1, why: 'It exists for every n; what fails is any single program computing it for all n.' },
      { q: 'Why do some values of S stay unknown even with huge computers?', options: ['Too many machines to run', 'For some machines nobody can prove whether they halt', 'The tape is too short', 'They are all known'], answer: 1, why: 'Holdouts behave like open problems in mathematics; settling them needs proofs, not just running.' },
    ],
  });
})();
