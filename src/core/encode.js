// Machines as binary strings: encoding and decoding Turing machines, DFAs, grammars and pairs, with
// validity checks; machines listed in the order of their encodings; and a universal machine that runs
// an encoded machine on three tapes (description, work tape, state).
//
// TM convention: states are numbered q1 (start), q2 (accept), q3 (reject), q4, …; tape symbols are
// numbered 1 (blank), then the input symbols, then the rest; moves L = 1, R = 2, S = 3. The rule
// δ(qi, sj) = (qk, sl, m) is written 0^i 1 0^j 1 0^k 1 0^l 1 0^m, and rules are joined by 11.
// Since every field is a non-empty run of 0s, 11 can only be a separator, and 111 separates parts.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Z = (n) => '0'.repeat(n);
  const MOVE_CODE = { L: 1, R: 2, S: 3 }, MOVE_NAME = { 1: 'L', 2: 'R', 3: 'S' };
  const DEFAULT_SYMS = ['_', '0', '1', 'X', 'Y', 'Z', 'a', 'b', 'c', '#'];

  // ---------- Turing machines ----------
  function encodeTM(M) {
    if (M.k !== 1 || M.mode !== 'standard') throw new Error('only single-tape standard machines are encoded');
    if (!M.deterministic) throw new Error('only deterministic machines are encoded');
    const acc = M.accept.concat(M.halt), rej = M.reject;
    // a decoded machine keeps its original numbers, so decoding and encoding again gives the same code
    const stateNum = new Map(M.stateNumbers ? Object.entries(M.stateNumbers) : [[M.start, 1]]);
    acc.forEach((q) => stateNum.set(q, stateNum.get(q) || 2));
    rej.forEach((q) => stateNum.set(q, stateNum.get(q) || 3));
    let next = 4;
    for (const q of M.states) if (!stateNum.has(q)) stateNum.set(q, next++);
    const symNum = new Map([[M.blank, 1]]);
    let sn = 2;
    for (const s of M.input.concat(M.gamma)) if (!symNum.has(s)) symNum.set(s, sn++);
    const parts = [];
    const rules = M.rules.filter((r) => !acc.includes(r.from) && !rej.includes(r.from))
      .map((r) => [stateNum.get(r.from), symNum.get(r.read[0]), stateNum.get(r.to), symNum.get(r.write[0]), MOVE_CODE[r.move[0]]])
      .sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    for (const f of rules) parts.push(f.map(Z).join('1'));
    const code = parts.join('11');
    const trace = [{ kind: 'number', say: `Number the states (${[...stateNum].map(([q, i]) => `${q} = q${i}`).join(', ')}) and the symbols (${[...symNum].map(([s, i]) => `${s} = ${i}`).join(', ')}).`, states: Object.fromEntries(stateNum), symbols: Object.fromEntries(symNum) }];
    rules.forEach((f, i) => trace.push({ kind: 'rule', say: `δ(q${f[0]}, ${f[1]}) = (q${f[2]}, ${f[3]}, ${MOVE_NAME[f[4]]}) becomes ${f.map(Z).join('1')}.`, fields: f, code: f.map(Z).join('1'), index: i }));
    trace.push({ kind: 'join', say: `Join the ${rules.length} rules with 11: ${code.length} bits in all.`, code });
    return { code, states: Object.fromEntries(stateNum), symbols: Object.fromEntries(symNum), symbolNames: [...symNum.keys()], rules, trace };
  }

  // Parse a TM code into numbered rules, reporting every problem found.
  function checkTM(code) {
    const errors = [];
    if (!/^[01]*$/.test(code)) return { ok: false, errors: ['only 0 and 1 may appear'] };
    if (code === '') return { ok: true, rules: [], states: 3, symbols: 1, errors };
    if (code.includes('111')) errors.push('111 may not appear inside a machine description');
    const rules = [];
    const seen = new Set();
    code.split('11').forEach((part, idx) => {
      const f = part.split('1');
      if (f.some((x) => x === '')) { errors.push(`rule ${idx + 1} has an empty field`); return; }
      if (f.length !== 5) { errors.push(`rule ${idx + 1} has ${f.length} fields, not 5`); return; }
      const n = f.map((x) => x.length);
      if (n[4] > 3) errors.push(`rule ${idx + 1} has move ${n[4]}; only 1 (L), 2 (R), 3 (S) exist`);
      if (n[0] === 2 || n[0] === 3) errors.push(`rule ${idx + 1} leaves the halting state q${n[0]}`);
      const k = n[0] + ',' + n[1];
      if (seen.has(k)) errors.push(`two rules for state q${n[0]} on symbol ${n[1]}: not deterministic`);
      seen.add(k);
      rules.push(n);
    });
    const states = Math.max(3, ...rules.map((r) => Math.max(r[0], r[2])));
    const symbols = Math.max(1, ...rules.map((r) => Math.max(r[1], r[3])));
    return { ok: !errors.length, errors, rules, states, symbols };
  }

  // Decode into an ordinary machine; names: symbol i is names[i-1] (default _, 0, 1, X, …).
  function decodeTM(code, opts = {}) {
    const c = checkTM(code);
    if (!c.ok) return { ok: false, errors: c.errors };
    const names = opts.symbols || DEFAULT_SYMS;
    const nm = (i) => names[i - 1] || 's' + i;
    const input = opts.input || [nm(2), nm(3)].filter((s, i) => i + 2 <= Math.max(3, c.symbols));
    const M = T.tm.fromRules({ name: opts.name || 'decoded', start: 'q1', accept: ['q2'], reject: ['q3'], blank: nm(1), input, extra: Array.from({ length: c.symbols }, (_, i) => nm(i + 1)) },
      c.rules.map((r) => ({ from: 'q' + r[0], read: [nm(r[1])], to: 'q' + r[2], write: [nm(r[3])], move: [MOVE_NAME[r[4]]] })));
    M.stateNumbers = Object.fromEntries(M.states.map((q) => [q, +q.slice(1)]));
    return { ok: true, machine: M, rules: c.rules, states: c.states, symbols: c.symbols, errors: [] };
  }

  // ⟨w⟩: symbol numbers as runs of 0s separated by 1; ⟨M, w⟩ = ⟨M⟩ 111 ⟨w⟩.
  const encodeWord = (w, symNum) => w.map((s) => Z(symNum[s])).join('1');
  const decodeWord = (code) => (code === '' ? [] : code.split('1').map((x) => x.length));
  function encodeTMInput(M, w) {
    const e = encodeTM(M);
    const syms = T.tm.symbols(M, w);
    const bad = syms.find((s) => !(s in e.symbols));
    if (bad) throw new Error(`symbol ${bad} is not in the machine's alphabet`);
    return { code: e.code + '111' + encodeWord(syms, e.symbols), machine: e.code, word: encodeWord(syms, e.symbols), enc: e };
  }
  function splitTMInput(code) {
    const i = code.indexOf('111');
    if (i < 0) return { ok: false, errors: ['no 111 between the machine and its input'] };
    return { ok: true, machine: code.slice(0, i), word: code.slice(i + 3) };
  }

  // A self-delimiting pair of binary strings: every bit of x doubled, then 01, then y.
  const pair = (x, y) => [...x].map((b) => b + b).join('') + '01' + y;
  function unpair(code) {
    let i = 0, x = '';
    while (i + 1 < code.length && code[i] === code[i + 1]) { x += code[i]; i += 2; }
    if (code.slice(i, i + 2) !== '01') return null;
    return [x, code.slice(i + 2)];
  }

  // ---------- DFAs: 0^n 1 0^k 111 rules (0^i 1 0^a 1 0^j joined by 11) 111 accepting states joined by 1 ----------
  // DFA object: {states:[..], alphabet:[..], start, accept:[..], delta:{q:{a:q'}}}; the start state is numbered 1.
  function encodeDFA(D) {
    const order = [D.start, ...D.states.filter((q) => q !== D.start)];
    const sn = new Map(order.map((q, i) => [q, i + 1])), an = new Map(D.alphabet.map((a, i) => [a, i + 1]));
    const rules = [];
    for (const q of order) for (const a of D.alphabet) if (D.delta[q] && D.delta[q][a] != null) rules.push([sn.get(q), an.get(a), sn.get(D.delta[q][a])].map(Z).join('1'));
    const code = Z(order.length) + '1' + Z(D.alphabet.length) + '111' + rules.join('11') + '111' + D.accept.map((q) => Z(sn.get(q))).join('1');
    return { code, states: Object.fromEntries(sn), symbols: Object.fromEntries(an) };
  }
  function decodeDFA(code, opts = {}) {
    const errors = [];
    const parts = code.split('111');
    if (parts.length !== 3) return { ok: false, errors: ['a DFA code has three parts separated by 111'] };
    const head = parts[0].split('1');
    if (head.length !== 2 || !head[0] || !head[1]) return { ok: false, errors: ['the header must be 0^n 1 0^k'] };
    const n = head[0].length, k = head[1].length;
    const names = opts.alphabet || 'abcdefghij'.slice(0, k).split('');
    const states = Array.from({ length: n }, (_, i) => 'q' + (i + 1));
    const delta = {};
    states.forEach((q) => { delta[q] = {}; });
    if (parts[1]) parts[1].split('11').forEach((r, idx) => {
      const f = r.split('1');
      if (f.length !== 3 || f.some((x) => !x)) { errors.push(`rule ${idx + 1} is not 0^i 1 0^a 1 0^j`); return; }
      const [i, a, j] = f.map((x) => x.length);
      if (i > n || j > n || a > k) { errors.push(`rule ${idx + 1} names a state or symbol out of range`); return; }
      if (delta['q' + i][names[a - 1]] != null) errors.push(`two rules for q${i} on ${names[a - 1]}`);
      delta['q' + i][names[a - 1]] = 'q' + j;
    });
    for (const q of states) for (const a of names) if (delta[q][a] == null) errors.push(`no rule for ${q} on ${a}`);
    const accept = parts[2] ? parts[2].split('1').map((x) => x.length) : [];
    if (accept.some((i) => i < 1 || i > n)) errors.push('an accepting state is out of range');
    return errors.length ? { ok: false, errors } : { ok: true, errors, dfa: { states, alphabet: names, start: 'q1', accept: [...new Set(accept)].map((i) => 'q' + i), delta } };
  }

  // ---------- CFGs: 0^v 1 0^t 111 productions joined by 11; a production is A 1 X1 1 … 1 Xm,
  // variable i written 0^i and terminal j written 0^(v+j); variable 1 is the start ----------
  // CFG object: {start, variables:[..], terminals:[..], rules:[{lhs, rhs:[..]}]} (rhs [] for ε).
  function encodeCFG(G) {
    const vars = [G.start, ...G.variables.filter((v) => v !== G.start)];
    const vn = new Map(vars.map((x, i) => [x, i + 1])), tn = new Map(G.terminals.map((x, i) => [x, vars.length + i + 1]));
    const num = (s) => vn.get(s) || tn.get(s);
    const prods = G.rules.map((r) => [vn.get(r.lhs), ...r.rhs.map(num)].map(Z).join('1'));
    return { code: Z(vars.length) + '1' + Z(G.terminals.length) + '111' + prods.join('11') };
  }
  function decodeCFG(code, opts = {}) {
    const parts = code.split('111'), errors = [];
    if (parts.length !== 2) return { ok: false, errors: ['a grammar code has two parts separated by 111'] };
    const head = parts[0].split('1');
    if (head.length !== 2 || !head[0] || !head[1]) return { ok: false, errors: ['the header must be 0^v 1 0^t'] };
    const v = head[0].length, t = head[1].length;
    const variables = opts.variables || Array.from({ length: v }, (_, i) => (i === 0 ? 'S' : String.fromCharCode(64 + i)));
    const terminals = opts.terminals || 'abcdefghij'.slice(0, t).split('');
    const rules = [];
    if (parts[1]) parts[1].split('11').forEach((p, idx) => {
      const f = p.split('1');
      if (f.some((x) => !x)) { errors.push(`production ${idx + 1} has an empty field`); return; }
      const n = f.map((x) => x.length);
      if (n[0] > v) { errors.push(`production ${idx + 1} rewrites a terminal`); return; }
      if (n.some((x) => x > v + t)) { errors.push(`production ${idx + 1} uses a symbol out of range`); return; }
      rules.push({ lhs: variables[n[0] - 1], rhs: n.slice(1).map((x) => (x <= v ? variables[x - 1] : terminals[x - v - 1])) });
    });
    return errors.length ? { ok: false, errors } : { ok: true, errors, cfg: { start: variables[0], variables, terminals, rules } };
  }

  // ---------- machines in the order of their encodings ----------
  // Walk the binary strings in shortlex order and keep the valid TM codes: M1, M2, … .
  function enumerateMachines(count, opts = {}) {
    const maxLen = opts.maxLen || 18, out = [];
    for (let len = 0; len <= maxLen && out.length < count; len++) {
      const total = 2 ** len;
      for (let x = 0; x < total && out.length < count; x++) {
        const code = len ? x.toString(2).padStart(len, '0') : '';
        if (code && code[0] !== '0') break; // valid codes start with 0, and shortlex puts those first
        const c = checkTM(code);
        if (c.ok) out.push({ index: out.length + 1, code, rules: c.rules, machine: decodeTM(code).machine });
      }
    }
    return out;
  }

  // ---------- the universal machine ----------
  // Tape 1 holds ⟨M⟩, tape 2 holds the work tape as blocks 0^j separated by 1, tape 3 holds 0^i for state qi.
  // Each simulated step: read the block under the simulated head, scan tape 1 rule by rule for one whose
  // first two fields match tape 3 and that block, then rewrite the block, move, and replace tape 3.
  // `cost` counts the cells the UTM's heads pass over: a rough step count for the three-tape machine.
  function utm(code, opts = {}) {
    const sp = splitTMInput(code);
    if (!sp.ok) return { verdict: 'invalid', errors: sp.errors, trace: [] };
    const c = checkTM(sp.machine);
    if (!c.ok) return { verdict: 'invalid', errors: c.errors, trace: [] };
    const maxSteps = opts.maxSteps || 5000, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 2000;
    const work = decodeWord(sp.word);
    if (!work.length) work.push(1);
    let head = 0, state = 1, steps = 0, cost = 0;
    const trace = [], desc = sp.machine;
    // starting offset of every rule on tape 1, so the scan can be shown and costed
    const offsets = [];
    { let p = 0; desc.split('11').forEach((r) => { if (desc) offsets.push(p); p += r.length + 2; }); }
    const tape2 = () => work.map(Z).join('1');
    const blockAt = (h) => { let p = 0; for (let i = 0; i < h; i++) p += work[i] + 1; return p; };
    const note = (s) => { if (wantTrace && trace.length < traceLimit) trace.push(Object.assign({ tape1: desc, tape2: tape2(), tape3: Z(state), head2: blockAt(head) }, s)); };
    note({ kind: 'utm-start', say: `Tape 1 holds ⟨M⟩ (${desc.length} bits), tape 2 the input as blocks, tape 3 the start state q1.`, head1: 0 });
    let verdict;
    while (true) {
      if (state === 2) { verdict = 'accept'; break; }
      if (state === 3) { verdict = 'reject'; break; }
      if (steps >= maxSteps) { verdict = 'limit'; break; }
      const sym = work[head];
      let found = -1;
      for (let i = 0; i < c.rules.length; i++) {
        cost += c.rules[i][0] + c.rules[i][1] + 2; // compare the first two fields
        if (c.rules[i][0] === state && c.rules[i][1] === sym) { found = i; break; }
        cost += c.rules[i][2] + c.rules[i][3] + c.rules[i][4] + 5; // skip the rest of the rule
      }
      if (found < 0) { note({ kind: 'utm-none', say: `No rule on tape 1 starts with q${state} and symbol ${sym}: the machine rejects.`, head1: desc.length }); verdict = 'reject'; break; }
      const [, , k, l, m] = c.rules[found];
      note({ kind: 'utm-find', say: `Scanning tape 1: rule ${found + 1} starts with q${state} and symbol ${sym}, and says write ${l}, move ${MOVE_NAME[m]}, go to q${k}.`, head1: offsets[found], rule: found, fields: c.rules[found] });
      cost += blockAt(work.length) - blockAt(head); // rewriting a block may shift the rest of tape 2
      work[head] = l;
      if (m === 1) { if (head === 0) work.unshift(1); else head--; }
      else if (m === 2) { head++; if (head === work.length) work.push(1); }
      cost += Math.max(work[head], 1) + k + state + 2;
      state = k; steps++;
      note({ kind: 'utm-step', say: `Block rewritten, head moved ${MOVE_NAME[m]}, tape 3 now reads q${state} (simulated step ${steps}).`, head1: offsets[found], step: steps });
    }
    const say = { accept: `M accepts: the universal machine accepts after ${steps} simulated steps.`, reject: `M rejects after ${steps} simulated steps, and so does the universal machine.`, limit: `Stopped after ${maxSteps} simulated steps without a verdict.` }[verdict];
    note({ kind: verdict, say, head1: 0 });
    return { verdict, steps, cost, work: work.slice(), head, state, trace };
  }

  T.enc = { encodeTM, checkTM, decodeTM, encodeWord, decodeWord, encodeTMInput, splitTMInput, pair, unpair, encodeDFA, decodeDFA, encodeCFG, decodeCFG, enumerateMachines, MOVE_CODE, MOVE_NAME, DEFAULT_SYMS };
  T.utm = { run: utm };
})();
