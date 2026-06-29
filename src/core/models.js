// Other models of computation: register machines (with random-access extras), counter machines,
// linear-bounded automata, and unrestricted grammars with a bounded derivation search.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  // ---------- register machine / RAM ----------
  // The tiny core is inc, dec (never below 0), jz, jmp, halt. The random-access extras are set, copy,
  // add, sub (stops at 0), jnz, load r s (r := R[R[s]]) and store r s (R[R[r]] := s).
  const RAM_OPS = { inc: 1, dec: 1, jz: 2, jnz: 2, jmp: 1, halt: 0, set: 2, copy: 2, add: 2, sub: 2, load: 2, store: 2 };
  const CORE = new Set(['inc', 'dec', 'jz', 'jmp', 'halt']);
  function ramParse(text) {
    const prog = [], labels = {}, errors = [];
    String(text).split('\n').forEach((line0, ln) => {
      let line = line0.replace(/\/\/.*$/, '').trim();
      let m;
      while ((m = /^([A-Za-z_]\w*)\s*:\s*(.*)$/.exec(line))) { labels[m[1]] = prog.length; line = m[2].trim(); }
      if (!line) return;
      const w = line.split(/[\s,]+/).filter(Boolean), op = w[0].toLowerCase();
      if (!(op in RAM_OPS)) { errors.push({ line: ln + 1, msg: `unknown instruction ${w[0]}` }); return; }
      if (w.length - 1 !== RAM_OPS[op]) { errors.push({ line: ln + 1, msg: `${op} takes ${RAM_OPS[op]} operand${RAM_OPS[op] === 1 ? '' : 's'}` }); return; }
      const reg = (s) => { const r = /^r(\d+)$/i.exec(s); if (!r) errors.push({ line: ln + 1, msg: `${s} is not a register (r0, r1, …)` }); return r ? +r[1] : 0; };
      const ins = { op, line: ln + 1, text: line };
      if (op === 'jmp') ins.label = w[1];
      else if (op === 'jz' || op === 'jnz') { ins.a = reg(w[1]); ins.label = w[2]; }
      else if (op === 'set') { ins.a = reg(w[1]); ins.k = parseInt(w[2], 10); if (!(ins.k >= 0)) errors.push({ line: ln + 1, msg: 'set needs a number ≥ 0' }); }
      else if (op !== 'halt') { ins.a = reg(w[1]); if (RAM_OPS[op] === 2) ins.b = reg(w[2]); }
      prog.push(ins);
    });
    for (const ins of prog) if (ins.label != null && !(ins.label in labels)) errors.push({ line: ins.line, msg: `no label ${ins.label}` });
    return { prog, labels, errors, core: prog.every((i) => CORE.has(i.op)) };
  }

  // Run with registers given as an array (r0, r1, …) or a map {index: value}. Output is r0.
  function ramRun(P, regs0, opts = {}) {
    const p = typeof P === 'string' ? ramParse(P) : P;
    if (p.errors.length) throw new Error(p.errors.map((e) => `line ${e.line}: ${e.msg}`).join('; '));
    const maxSteps = opts.maxSteps || 100000, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 3000;
    const R = new Map();
    if (Array.isArray(regs0)) regs0.forEach((v, i) => v && R.set(i, v)); else for (const k in regs0) if (regs0[k]) R.set(+k, regs0[k]);
    const get = (i) => R.get(i) || 0, set = (i, v) => { if (v) R.set(i, v); else R.delete(i); };
    const snapshot = () => Object.fromEntries([...R.entries()].sort((a, b) => a[0] - b[0]));
    const trace = [];
    let pc = 0, steps = 0, verdict = 'halt';
    while (true) {
      if (pc >= p.prog.length) break;
      if (steps >= maxSteps) { verdict = 'limit'; break; }
      const ins = p.prog[pc], before = snapshot();
      let next = pc + 1, say = '';
      const a = ins.a, b = ins.b;
      switch (ins.op) {
        case 'inc': set(a, get(a) + 1); say = `r${a} goes up to ${get(a)}.`; break;
        case 'dec': set(a, Math.max(0, get(a) - 1)); say = `r${a} goes down to ${get(a)}.`; break;
        case 'jz': if (!get(a)) next = p.labels[ins.label]; say = get(a) ? `r${a} is ${get(a)}, not zero: carry on.` : `r${a} is zero: jump to ${ins.label}.`; break;
        case 'jnz': if (get(a)) next = p.labels[ins.label]; say = get(a) ? `r${a} is ${get(a)}: jump to ${ins.label}.` : `r${a} is zero: carry on.`; break;
        case 'jmp': next = p.labels[ins.label]; say = `Jump to ${ins.label}.`; break;
        case 'halt': next = p.prog.length; say = `Halt with r0 = ${get(0)}.`; break;
        case 'set': set(a, ins.k); say = `r${a} := ${ins.k}.`; break;
        case 'copy': set(a, get(b)); say = `r${a} := r${b} = ${get(b)}.`; break;
        case 'add': set(a, get(a) + get(b)); say = `r${a} := r${a} + r${b} = ${get(a)}.`; break;
        case 'sub': set(a, Math.max(0, get(a) - get(b))); say = `r${a} := r${a} − r${b} (not below 0) = ${get(a)}.`; break;
        case 'load': set(a, get(get(b))); say = `r${b} holds ${get(b)}, so r${a} := r${get(b)} = ${get(a)}.`; break;
        case 'store': set(get(a), get(b)); say = `r${a} holds ${get(a)}, so r${get(a)} := r${b} = ${get(b)}.`; break;
      }
      steps++;
      if (wantTrace && trace.length < traceLimit) {
        const after = snapshot(), changed = {};
        for (const k of new Set([...Object.keys(before), ...Object.keys(after)])) if ((before[k] || 0) !== (after[k] || 0)) changed[k] = [before[k] || 0, after[k] || 0];
        trace.push({ kind: 'exec', say, pc, next, ins: ins.text, line: ins.line, regs: after, changed, step: steps });
      }
      pc = next;
    }
    trace.push({ kind: verdict, say: verdict === 'halt' ? `Halted after ${steps} instructions; r0 = ${get(0)}.` : `Stopped after ${maxSteps} instructions without halting.`, regs: snapshot() });
    return { verdict, steps, output: get(0), regs: snapshot(), get, trace };
  }

  const ramLib = [
    { id: 'add', title: 'r0 := r1 + r2', inputs: 2, oracle: (x, y) => x + y, text: `
loop1: jz r1 next
  dec r1
  inc r0
  jmp loop1
next: jz r2 done
  dec r2
  inc r0
  jmp next
done: halt` },
    { id: 'mul', title: 'r0 := r1 × r2', inputs: 2, oracle: (x, y) => x * y, text: `
outer: jz r1 done
  dec r1
inner: jz r2 restore
  dec r2
  inc r0
  inc r3
  jmp inner
restore: jz r3 outer
  dec r3
  inc r2
  jmp restore
done: halt` },
    { id: 'monus', title: 'r0 := r1 − r2 (not below 0)', inputs: 2, oracle: (x, y) => Math.max(0, x - y), text: `
loop: jz r2 move
  jz r1 done
  dec r1
  dec r2
  jmp loop
move: jz r1 done
  dec r1
  inc r0
  jmp move
done: halt` },
    { id: 'max', title: 'r0 := max(r1, r2)', inputs: 2, oracle: (x, y) => Math.max(x, y), text: `
loop: jz r1 rest2
  jz r2 rest1
  dec r1
  dec r2
  inc r0
  jmp loop
rest1: jz r1 done
  dec r1
  inc r0
  jmp rest1
rest2: jz r2 done
  dec r2
  inc r0
  jmp rest2
done: halt` },
    { id: 'half', title: 'r0 := ⌊r1 / 2⌋', inputs: 1, oracle: (x) => x >> 1, text: `
loop: jz r1 done
  dec r1
  jz r1 done
  dec r1
  inc r0
  jmp loop
done: halt` },
    { id: 'pow2', title: 'r0 := 2^r1', inputs: 1, oracle: (x) => 2 ** x, text: `
  inc r0
outer: jz r1 done
  dec r1
move: jz r0 back
  dec r0
  inc r2
  inc r2
  jmp move
back: jz r2 outer
  dec r2
  inc r0
  jmp back
done: halt` },
    { id: 'sum-array', title: 'r0 := sum of the r1 numbers stored from r10 on (RAM)', inputs: 'array', oracle: (arr) => arr.reduce((a, b) => a + b, 0), text: `
  set r2 10
loop: jz r1 done
  load r3 r2
  add r0 r3
  inc r2
  dec r1
  jmp loop
done: halt` },
    { id: 'max-array', title: 'r0 := largest of the r1 numbers stored from r10 on (RAM)', inputs: 'array', oracle: (arr) => arr.reduce((a, b) => Math.max(a, b), 0), text: `
  set r2 10
loop: jz r1 done
  load r3 r2
  copy r4 r3
  sub r4 r0
  jz r4 skip
  copy r0 r3
skip: inc r2
  dec r1
  jmp loop
done: halt` },
  ];

  // ---------- counter machines ----------
  // Lines: `q: inc A next`, `q: dec A next ifzero` (if A > 0 take 1 and go to next, else go to ifzero),
  // `q: halt`. Counters are named by letters; a machine with two of them is a 2-counter machine.
  function counterParse(text) {
    const prog = {}, errors = [], counters = new Set();
    let start = null;
    String(text).split('\n').forEach((line0, ln) => {
      const line = line0.replace(/\/\/.*$/, '').trim();
      if (!line) return;
      const m = /^(\w+)\s*:\s*(\w+)\s*(.*)$/.exec(line);
      if (!m) { errors.push({ line: ln + 1, msg: 'expected  label: inc C next | dec C next zero | halt' }); return; }
      const [, q, op0, rest] = m, op = op0.toLowerCase(), w = rest.split(/[\s,]+/).filter(Boolean);
      if (start == null) start = q;
      if (op === 'inc' && w.length === 2) { prog[q] = { op, c: w[0], next: w[1], line: ln + 1 }; counters.add(w[0]); }
      else if (op === 'dec' && w.length === 3) { prog[q] = { op, c: w[0], next: w[1], zero: w[2], line: ln + 1 }; counters.add(w[0]); }
      else if (op === 'halt' && !w.length) prog[q] = { op, line: ln + 1 };
      else errors.push({ line: ln + 1, msg: `cannot read "${line}"` });
    });
    for (const q in prog) for (const t of [prog[q].next, prog[q].zero]) if (t != null && !(t in prog)) errors.push({ line: prog[q].line, msg: `no line labelled ${t}` });
    return { prog, start, errors, counters: [...counters].sort() };
  }

  function counterRun(P, init, opts = {}) {
    const p = typeof P === 'string' ? counterParse(P) : P;
    if (p.errors.length) throw new Error(p.errors.map((e) => `line ${e.line}: ${e.msg}`).join('; '));
    const maxSteps = opts.maxSteps || 1000000, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 3000;
    const C = Object.assign({}, init);
    p.counters.forEach((c) => { C[c] = C[c] || 0; });
    let q = p.start, steps = 0, verdict = 'halt';
    const trace = [];
    while (true) {
      const ins = p.prog[q];
      if (ins.op === 'halt') break;
      if (steps >= maxSteps) { verdict = 'limit'; break; }
      let say, next;
      if (ins.op === 'inc') { C[ins.c]++; next = ins.next; say = `${ins.c} goes up to ${C[ins.c]}.`; }
      else if (C[ins.c] > 0) { C[ins.c]--; next = ins.next; say = `${ins.c} was positive: down to ${C[ins.c]}.`; }
      else { next = ins.zero; say = `${ins.c} is zero: go to ${ins.zero}.`; }
      steps++;
      if (wantTrace && trace.length < traceLimit) trace.push({ kind: 'exec', say, at: q, next, counters: Object.assign({}, C), step: steps });
      q = next;
    }
    trace.push({ kind: verdict, say: verdict === 'halt' ? `Halted at ${q} after ${steps} steps.` : `No halt after ${maxSteps} steps.`, counters: Object.assign({}, C) });
    return { verdict, state: q, steps, counters: C, trace };
  }

  const counterLib = [
    { id: 'double', title: 'A := 2A', oracle: (c) => ({ A: 2 * c.A, B: 0 }), text: `
d: dec A d1 m
d1: inc B d2
d2: inc B d
m: dec B m1 h
m1: inc A m
h: halt` },
    { id: 'half', title: 'A := ⌊A / 2⌋', oracle: (c) => ({ A: c.A >> 1, B: 0 }), text: `
d: dec A d1 m
d1: dec A d2 m
d2: inc B d
m: dec B m1 h
m1: inc A m
h: halt` },
    { id: 'parity', title: 'Halt in even or odd', oracle: (c) => (c.A % 2 ? 'odd' : 'even'), state: true, text: `
e: dec A o even
o: dec A e odd
even: halt
odd: halt` },
    // with A = 2^x 3^y, end with A = 2^(x+y): one counter holds a product of prime powers, the other is scratch
    { id: 'prime-powers', title: 'A = 2^x·3^y becomes 2^(x+y)', oracle: (c) => { let a = c.A, x = 0, y = 0; while (a % 2 === 0) { a /= 2; x++; } while (a % 3 === 0) { a /= 3; y++; } return { A: 2 ** (x + y), B: 0 }; }, text: `
d0: dec A d1 ok
d1: dec A d2 r1
d2: dec A d3 r2
d3: inc B d0
ok: dec B m1 d0
m1: inc A m2
m2: inc A ok
r1: dec B s1 t1
s1: inc A s2
s2: inc A s3
s3: inc A r1
t1: inc A h
r2: dec B u1 t2
u1: inc A u2
u2: inc A u3
u3: inc A r2
t2: inc A t3
t3: inc A h
h: halt` },
  ];
  // prime-powers: when A is already 0 the divide loop would spin; inputs are always ≥ 1 by definition.

  // ---------- linear-bounded automata ----------
  // A machine in mode lba never leaves the input between its endmarkers, so it has at most
  // |Q| · (n + 2) · |Γ|^n configurations: running that long either halts or repeats, so acceptance is decidable.
  function lbaBound(M, n) { return M.states.length * (n + 2) * Math.pow(M.gamma.length, n); }
  function lbaRun(M, w, opts = {}) {
    if (M.mode !== 'lba') throw new Error('not a linear-bounded automaton (mode: lba)');
    const n = T.tm.symbols(M, w).length, bound = lbaBound(M, n);
    const r = T.tm.run(M, w, Object.assign({}, opts, { loops: true, maxSteps: Math.min(bound + 1, opts.maxSteps || 1e6) }));
    if (r.verdict === 'loop') r.trace.push({ kind: 'lba-loop', say: `A configuration repeated, so this run never halts: the decider for this LBA answers reject. (At most ${bound} configurations exist.)`, bound });
    return Object.assign(r, { bound, decided: r.verdict !== 'limit' ? (r.verdict === 'accept' ? 'accept' : 'reject') : null });
  }

  // ---------- unrestricted grammars ----------
  // Productions α -> β with α non-empty; symbols are single characters, uppercase = variables,
  // ε (or nothing) = empty. Alternatives with |.
  function grammarParse(text) {
    const prods = [], errors = [];
    let start = null;
    String(text).split('\n').forEach((line0, ln) => {
      const line = line0.replace(/\/\/.*$/, '').replace(/\s+/g, '');
      if (!line) return;
      const parts = line.split(/->|→/);
      if (parts.length !== 2 || !parts[0]) { errors.push({ line: ln + 1, msg: 'expected  α -> β | γ' }); return; }
      const lhs = parts[0].replace(/ε/g, '');
      if (!lhs) { errors.push({ line: ln + 1, msg: 'the left side may not be empty' }); return; }
      if (start == null) start = lhs.length === 1 ? lhs : 'S';
      for (const r of parts[1].split('|')) prods.push({ lhs, rhs: r.replace(/ε/g, ''), line: ln + 1 });
    });
    const isVar = (c) => /[A-Z]/.test(c);
    // noncontracting: no rule shrinks the form, except S -> ε when S never appears on a right side
    const startOnRight = prods.some((p) => p.rhs.includes(start || 'S'));
    const noncontracting = prods.every((p) => p.rhs.length >= p.lhs.length || (p.lhs === start && p.rhs === '' && !startOnRight));
    const contextFree = prods.every((p) => p.lhs.length === 1 && isVar(p.lhs));
    const terminalFreeLeft = prods.every((p) => ![...p.lhs].some((c) => !isVar(c)));
    return { prods, start: start || 'S', errors, noncontracting, contextFree, terminalFreeLeft, isVar };
  }

  // Breadth-first search for a derivation of w. Sentential forms longer than |w| + slack are dropped
  // (exact for noncontracting grammars, where slack 0 suffices); when no left side contains a terminal,
  // forms whose terminal prefix disagrees with w are dropped too. Returns the derivation if one exists in bounds.
  function derive(G0, w, opts = {}) {
    const G = typeof G0 === 'string' ? grammarParse(G0) : G0;
    const slack = opts.slack != null ? opts.slack : G.noncontracting ? 0 : 2;
    const maxLen = Math.max(w.length, 1) + slack, maxNodes = opts.maxNodes || 200000, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 400;
    const parent = new Map([[G.start, null]]), trace = [];
    let frontier = [G.start], explored = 0, cut = false;
    const prefixOk = (f) => { if (!G.terminalFreeLeft) return true; let i = 0; while (i < f.length && !G.isVar(f[i])) { if (f[i] !== w[i]) return false; i++; } return i === f.length ? f === w : true; };
    const build = (f) => { const path = []; for (let x = f; x != null; x = parent.get(x) && parent.get(x).from) path.unshift({ form: x, via: parent.get(x) }); return path; };
    if (G.start === w) return { found: true, derivation: build(w), explored: 0, trace };
    while (frontier.length) {
      const next = [];
      for (const f of frontier) {
        explored++;
        if (explored > maxNodes) { cut = true; break; }
        const made = [];
        for (const p of G.prods) for (let i = f.indexOf(p.lhs); i >= 0; i = f.indexOf(p.lhs, i + 1)) {
          const g = f.slice(0, i) + p.rhs + f.slice(i + p.lhs.length);
          if (g.length > maxLen) { cut = cut || !G.noncontracting; continue; }
          if (parent.has(g) || !prefixOk(g)) continue;
          parent.set(g, { from: f, rule: p.lhs + ' → ' + (p.rhs || 'ε'), at: i });
          made.push(g);
          if (g === w) {
            const derivation = build(g);
            trace.push({ kind: 'found', say: `Derived ${w || 'ε'} in ${derivation.length - 1} steps: ` + derivation.map((d) => d.form || 'ε').join(' ⇒ '), derivation });
            return { found: true, derivation, explored, trace };
          }
          next.push(g);
        }
        if (wantTrace && trace.length < traceLimit) trace.push({ kind: 'expand', say: `${f} rewrites to ${made.length ? made.join(', ') : 'nothing new within bounds'}.`, form: f, made });
      }
      if (cut && explored > maxNodes) break;
      frontier = next;
    }
    const exact = G.noncontracting && !(explored > maxNodes);
    trace.push({ kind: exact ? 'none' : 'limit', say: exact ? `Every sentential form of length ≤ ${maxLen} has been tried: ${w || 'ε'} cannot be derived.` : `No derivation found within the bounds (forms up to length ${maxLen}, ${maxNodes} forms).` });
    return { found: false, exact, explored, trace };
  }

  const grammarLib = [
    { id: 'anbncn', title: 'aⁿbⁿcⁿ (n ≥ 1), noncontracting', text: `S -> aBc | aSBc
cB -> Bc
aB -> ab
bB -> bb`, alphabet: ['a', 'b', 'c'], oracle: (w) => { const n = w.length / 3; return n >= 1 && w === 'a'.repeat(n) + 'b'.repeat(n) + 'c'.repeat(n); } },
    { id: 'equal-abc', title: 'Equal numbers of a, b and c, in any order', text: `S -> ABCS | ε
AB -> BA
BA -> AB
AC -> CA
CA -> AC
BC -> CB
CB -> BC
A -> a
B -> b
C -> c`, alphabet: ['a', 'b', 'c'], oracle: (w) => { const c = (x) => [...w].filter((y) => y === x).length; return c('a') === c('b') && c('b') === c('c'); } },
    { id: 'double-a', title: 'a^(2^n) by a doubling sweep (unrestricted)', text: `S -> LaR
L -> LD
Da -> aaD
DR -> R
L -> ε
R -> ε`, alphabet: ['a'], oracle: (w) => /^a+$/.test(w) && (w.length & (w.length - 1)) === 0 },
  ];

  T.ram = { parse: ramParse, run: ramRun, lib: ramLib, CORE };
  T.counter = { parse: counterParse, run: counterRun, lib: counterLib };
  T.lba = { run: lbaRun, bound: lbaBound };
  T.ugrammar = { parse: grammarParse, derive, lib: grammarLib };
})();
