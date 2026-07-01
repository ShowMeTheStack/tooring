// The computability engine: programs that run one step at a time, the halting-problem diagonal acted
// out, the diagonal table, real deciders for problems about DFAs and grammars, mapping reductions as
// machine transformers, a Rice's-theorem checker, and Kolmogorov-complexity helpers.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const TM = T.tm;

  // ---------- programs ----------
  // A program is {name, code, lines, body(input)} where body is a generator that yields once per step
  // (yielding 'loop' marks a step of a loop that provably repeats forever) and returns true or false.
  // `code` stands for its description ⟨P⟩; the registry maps descriptions back to programs.
  const registry = new Map();
  let serial = 0;
  function program(name, lines, body) {
    const code = '⟨' + name + '⟩';
    const P = { name, code, lines, body, id: ++serial };
    registry.set(code, P);
    return P;
  }
  // Run with a step budget. verdict: accept | reject | loop (provably) | limit.
  function runProgram(P, input, maxSteps = 10000) {
    const g = P.body(input);
    let steps = 0;
    while (true) {
      const r = g.next();
      if (r.done) return { verdict: r.value ? 'accept' : 'reject', steps };
      if (r.value === 'loop') return { verdict: 'loop', steps };
      if (++steps >= maxSteps) return { verdict: 'limit', steps };
    }
  }
  // A Turing machine as a program: one yield per machine step; a repeated configuration is a provable loop.
  function tmProgram(M, name) {
    return program(name || M.name, [`the Turing machine ${M.name}`], function* (input) {
      const c = TM.initial(M, input), seen = new Set();
      while (true) {
        if (TM.isAccept(M, c.state)) return true;
        if (TM.isReject(M, c.state)) return false;
        const k = TM.key(c);
        if (seen.has(k)) { while (true) yield 'loop'; }
        seen.add(k);
        const rs = TM.rulesFor(M, c);
        if (!rs.length) return false;
        TM.apply(c, rs[0]);
        yield 'step';
      }
    });
  }
  // Simulate program P on x inside another program, step for step (each inner step costs one outer step).
  function* simulate(P, x, budget = Infinity) {
    const g = P.body(x);
    let n = 0;
    while (true) {
      const r = g.next();
      if (r.done) return { halted: true, accepted: r.value, steps: n };
      if (r.value === 'loop') { yield 'step'; return { halted: false, looping: true, steps: n }; }
      if (++n > budget) return { halted: false, steps: n };
      yield 'step';
    }
  }

  // ---------- the halting problem, acted out ----------
  // H is a claimed halting decider: a JS function (code, input) -> true ("halts") / false, or a number N
  // meaning "simulate for N steps and say halts iff it halted". D(⟨M⟩) asks H about M on ⟨M⟩ and does
  // the opposite. Running D on ⟨D⟩ shows H is wrong about D.
  function diagonal(H, opts = {}) {
    const maxSteps = opts.maxSteps || 20000;
    const trace = [];
    let Hname, ask;
    if (typeof H === 'number') {
      const N = H;
      Hname = `H${N} (simulate ${N} steps)`;
      ask = function* (code, input) {
        yield 'step'; // set up the simulation
        const P = registry.get(code);
        if (!P) return false;
        const r = yield* simulate(P, input, N);
        return r.halted;
      };
    } else {
      Hname = H.label || 'H';
      ask = function* (code, input) { yield 'step'; return !!H(code, input); };
    }
    const D = program('D', [`On input ⟨M⟩:`, `1. Run ${Hname} on ⟨M, ⟨M⟩⟩.`, `2. If it says M halts on ⟨M⟩, loop forever.`, `3. If it says M does not halt, accept.`], function* (code) {
      const halts = yield* ask(code, code);
      if (halts) { while (true) yield 'loop'; }
      return true;
    });
    trace.push({ kind: 'build', say: `Build D from ${Hname}: D(⟨M⟩) asks whether M halts on its own description, then does the opposite.`, lines: D.lines });
    // what H says about D on ⟨D⟩ (run H by itself, with a generous budget)
    const hRun = (function () { const g = ask(D.code, D.code); let n = 0; while (true) { const r = g.next(); if (r.done) return { answer: r.value, steps: n }; if (++n > maxSteps) return { answer: null, steps: n }; } })();
    trace.push({ kind: 'ask', say: `Ask ${Hname}: does D halt on ⟨D⟩?`, answer: hRun.answer });
    trace.push({ kind: 'answer', say: hRun.answer == null ? `${Hname} did not answer within ${maxSteps} steps, so it is not a decider at all.` : `${Hname} answers: D ${hRun.answer ? 'halts' : 'does not halt'} on ⟨D⟩ (after ${hRun.steps} steps of its own).`, answer: hRun.answer });
    const actual = runProgram(D, D.code, maxSteps);
    const halted = actual.verdict === 'accept' || actual.verdict === 'reject';
    trace.push({ kind: 'act', say: hRun.answer ? 'So D, by its construction, loops forever on ⟨D⟩.' : 'So D, by its construction, accepts ⟨D⟩ and halts.', expected: hRun.answer ? 'loop' : 'accept' });
    trace.push({ kind: 'run', say: `Running D on ⟨D⟩ for real: ${actual.verdict === 'loop' ? 'it enters its endless loop' : actual.verdict === 'accept' ? `it halts and accepts after ${actual.steps} steps` : actual.verdict}.`, verdict: actual.verdict, steps: actual.steps });
    const wrong = hRun.answer != null && hRun.answer !== halted;
    trace.push({ kind: 'contradiction', say: wrong ? `${Hname} said D ${hRun.answer ? 'halts' : 'does not halt'} on ⟨D⟩, but it ${halted ? 'halts' : 'does not'}: the claimed decider is wrong on this input, as it must be for every claimed decider.` : `${Hname} gave no answer, so it fails to be a decider.` });
    return { D, answer: hRun.answer, actual: actual.verdict, halted, wrong, contradiction: wrong || hRun.answer == null, trace };
  }

  // Rows: machines; columns: their descriptions as inputs. Entry: what machine i does on ⟨machine j⟩.
  // The diagonal machine flips the diagonal, so it differs from every row there.
  function diagonalTable(machines, opts = {}) {
    const maxSteps = opts.maxSteps || 200;
    const codes = machines.map((m) => m.code);
    const rows = machines.map((m) => codes.map((c) => TM.run(m.machine, c, { maxSteps, trace: false }).verdict));
    const diag = rows.map((r, i) => r[i]);
    const flipped = diag.map((v) => (v === 'accept' ? 'reject' : 'accept'));
    const trace = [{ kind: 'table', say: `Run each of the ${machines.length} machines on each description for at most ${maxSteps} steps.`, rows }];
    diag.forEach((v, i) => trace.push({ kind: 'diagonal', say: `Machine ${i + 1} on its own description: ${v}. D does the opposite: ${flipped[i]}.`, i, value: v, flipped: flipped[i] }));
    trace.push({ kind: 'differs', say: 'D disagrees with every machine in the list somewhere (on the diagonal), so D is not in the list.' });
    return { rows, diag, flipped, trace };
  }

  // ---------- small DFA and CFG helpers for the deciders ----------
  // DFA: {states, alphabet, start, accept:[..], delta:{q:{a:q'}}}; a missing move goes to an implicit dead state.
  const dstep = (D, q, a) => (q != null && D.delta[q] && D.delta[q][a] != null ? D.delta[q][a] : null);
  function A_DFA(D, w) {
    const trace = [{ kind: 'start', say: `Start in ${D.start}.`, state: D.start }];
    let q = D.start;
    for (const a of w) { const n = dstep(D, q, a); trace.push({ kind: 'read', say: n == null ? `Reading ${a} from ${q}: no move, the run dies.` : `Reading ${a}: ${q} → ${n}.`, from: q, symbol: a, to: n }); q = n; if (q == null) break; }
    const acc = q != null && D.accept.includes(q);
    trace.push({ kind: acc ? 'accept' : 'reject', say: acc ? `${q} is accepting: accept.` : `The run ends ${q == null ? 'in the dead state' : 'in ' + q + ', which is not accepting'}: reject.` });
    return { accepted: acc, trace };
  }
  // Mark the reachable states; empty iff no accepting state gets marked.
  function E_DFA(D) {
    const marked = new Set([D.start]), order = [D.start], trace = [{ kind: 'mark', say: `Mark the start state ${D.start}.`, marked: [D.start] }];
    for (let i = 0; i < order.length; i++) for (const a of D.alphabet) {
      const n = dstep(D, order[i], a);
      if (n != null && !marked.has(n)) { marked.add(n); order.push(n); trace.push({ kind: 'mark', say: `${order[i]} reaches ${n} on ${a}: mark ${n}.`, from: order[i], symbol: a, to: n, marked: [...marked] }); }
    }
    const hit = D.accept.filter((q) => marked.has(q));
    trace.push({ kind: hit.length ? 'nonempty' : 'empty', say: hit.length ? `The accepting state ${hit[0]} is reachable: the language is not empty.` : 'No accepting state is reachable: the language is empty.' });
    return { empty: !hit.length, marked: [...marked], trace };
  }
  // Explore pairs of states breadth-first; a pair where exactly one side accepts gives a shortest counterexample.
  function EQ_DFA(D1, D2) {
    const alpha = [...new Set([...D1.alphabet, ...D2.alphabet])];
    const k = (p, q) => p + '\u0001' + q;
    const start = [D1.start, D2.start], seen = new Map([[k(...start), null]]), queue = [start], trace = [];
    const acc = (D, q) => q != null && D.accept.includes(q);
    trace.push({ kind: 'pair', say: `Start from the pair (${D1.start}, ${D2.start}).`, pair: start });
    while (queue.length) {
      const [p, q] = queue.shift();
      if (acc(D1, p) !== acc(D2, q)) {
        let w = '';
        for (let x = k(p, q); seen.get(x); x = seen.get(x).from) w = seen.get(x).a + w;
        trace.push({ kind: 'differ', say: `In (${p ?? '∅'}, ${q ?? '∅'}) only one side accepts: ${w || 'ε'} tells the two machines apart.`, pair: [p, q], witness: w });
        return { equal: false, witness: w, trace };
      }
      for (const a of alpha) {
        const n = [dstep(D1, p, a), dstep(D2, q, a)], nk = k(...n);
        if (!seen.has(nk)) { seen.set(nk, { from: k(p, q), a }); queue.push(n); trace.push({ kind: 'pair', say: `(${p ?? '∅'}, ${q ?? '∅'}) on ${a} goes to (${n[0] ?? '∅'}, ${n[1] ?? '∅'}).`, pair: n, via: a }); }
      }
    }
    trace.push({ kind: 'equal', say: 'Every reachable pair agrees on acceptance: the languages are equal.' });
    return { equal: true, witness: null, trace };
  }

  // CFG text: one rule per line, `S -> a S b | ε`; symbols separated by spaces when a right side has spaces,
  // else one character each. Variables are the left sides.
  function parseCFG(text) {
    const rules = [], vars = [];
    String(text).split('\n').forEach((line0) => {
      const line = line0.replace(/\/\/.*$/, '').trim();
      if (!line) return;
      const [l, r] = line.split(/->|→/).map((x) => x.trim());
      if (!vars.includes(l)) vars.push(l);
      for (const alt of r.split('|')) {
        const a = alt.trim();
        const rhs = a === 'ε' || a === '' ? [] : /\s/.test(a) ? a.split(/\s+/) : [...a];
        rules.push({ lhs: l, rhs: rhs.filter((s) => s !== 'ε') });
      }
    });
    const terminals = [...new Set(rules.flatMap((r) => r.rhs).filter((s) => !vars.includes(s)))];
    return { start: vars[0], variables: vars, terminals, rules };
  }

  // Chomsky normal form in the usual stages, each traced: new start, ε-rules, unit rules, terminals in long rules, binarising.
  function toCNF(G) {
    const trace = [], isVar = new Set(G.variables);
    const fresh = (base) => { let n = base; while (isVar.has(n)) n += "'"; isVar.add(n); return n; };
    const S0 = fresh(G.start + '0');
    let rules = [{ lhs: S0, rhs: [G.start] }, ...G.rules.map((r) => ({ lhs: r.lhs, rhs: r.rhs.slice() }))];
    const key = (r) => r.lhs + '→' + r.rhs.join(' ');
    const dedupe = (rs) => { const s = new Set(); return rs.filter((r) => (s.has(key(r)) ? false : (s.add(key(r)), true))); };
    trace.push({ kind: 'start', say: `Add a new start variable ${S0} → ${G.start}, so the start never appears on a right side.`, rules: rules.map(key) });
    // nullable variables
    const nullable = new Set();
    for (let ch = true; ch;) { ch = false; for (const r of rules) if (!nullable.has(r.lhs) && r.rhs.every((s) => nullable.has(s))) { nullable.add(r.lhs); ch = true; } }
    const noEps = [];
    for (const r of rules) {
      const opts = [[]];
      for (const s of r.rhs) { const n = []; for (const o of opts) { n.push(o.concat([s])); if (nullable.has(s)) n.push(o); } opts.length = 0; opts.push(...n); }
      for (const o of opts) if (o.length || r.lhs === S0) noEps.push({ lhs: r.lhs, rhs: o });
    }
    rules = dedupe(noEps.filter((r) => r.rhs.length || r.lhs === S0));
    if (!nullable.has(S0)) rules = rules.filter((r) => r.rhs.length);
    trace.push({ kind: 'epsilon', say: nullable.size ? `The nullable variables are ${[...nullable].join(', ')}; add every version of each rule with some of them left out, and drop the ε-rules${nullable.has(S0) ? ` (keeping ${S0} → ε, since ε is in the language)` : ''}.` : 'No variable is nullable.', nullable: [...nullable], rules: rules.map(key) });
    // unit rules: A -> B
    const isUnit = (r) => r.rhs.length === 1 && isVar.has(r.rhs[0]);
    const unitPairs = new Map();
    for (const v of isVar) { const reach = new Set([v]), st = [v]; while (st.length) { const x = st.pop(); for (const r of rules) if (r.lhs === x && isUnit(r) && !reach.has(r.rhs[0])) { reach.add(r.rhs[0]); st.push(r.rhs[0]); } } unitPairs.set(v, reach); }
    const noUnit = [];
    for (const [a, reach] of unitPairs) for (const b of reach) for (const r of rules) if (r.lhs === b && !isUnit(r)) noUnit.push({ lhs: a, rhs: r.rhs.slice() });
    rules = dedupe(noUnit);
    trace.push({ kind: 'unit', say: 'Replace unit rules A → B by copying B\'s other rules up to A.', rules: rules.map(key) });
    // terminals inside long rules
    const termVar = new Map();
    const tv = (t) => { if (!termVar.has(t)) { const v = fresh('T' + t); termVar.set(t, v); rules.push({ lhs: v, rhs: [t] }); } return termVar.get(t); };
    for (const r of rules.slice()) if (r.rhs.length >= 2) r.rhs = r.rhs.map((s) => (isVar.has(s) ? s : tv(s)));
    trace.push({ kind: 'terminals', say: termVar.size ? `Give each terminal in a long rule its own variable: ${[...termVar].map(([t, v]) => `${v} → ${t}`).join(', ')}.` : 'No terminal sits inside a long rule.', rules: rules.map(key) });
    // binarise
    const out = [];
    let n = 0;
    for (const r of rules) {
      if (r.rhs.length <= 2) { out.push(r); continue; }
      let lhs = r.lhs;
      for (let i = 0; i < r.rhs.length - 2; i++) { const nv = fresh(r.lhs + '_' + (++n)); out.push({ lhs, rhs: [r.rhs[i], nv] }); lhs = nv; }
      out.push({ lhs, rhs: r.rhs.slice(-2) });
    }
    rules = dedupe(out);
    trace.push({ kind: 'binary', say: 'Break every right side longer than two into a chain of two-symbol rules.', rules: rules.map(key) });
    const variables = [...isVar]; // the originals (some may have lost all their rules) and the new ones
    return { cnf: { start: S0, variables, terminals: G.terminals.slice(), rules }, trace };
  }

  // CYK on a CNF grammar: cell (i, len) holds the variables deriving w[i .. i+len-1], with back-pointers.
  function cyk(C, w) {
    const n = w.length, trace = [];
    if (n === 0) { const yes = C.rules.some((r) => r.lhs === C.start && !r.rhs.length); return { accepted: yes, table: [], trace: [{ kind: yes ? 'accept' : 'reject', say: yes ? `${C.start} → ε is a rule: ε is in the language.` : 'There is no rule for ε: reject.' }] }; }
    const table = Array.from({ length: n }, () => []);
    for (let i = 0; i < n; i++) {
      const cell = new Map();
      for (const r of C.rules) if (r.rhs.length === 1 && r.rhs[0] === w[i]) cell.set(r.lhs, { rule: r });
      table[i][1] = cell;
      trace.push({ kind: 'cell', say: `${w[i]} at position ${i + 1} comes from ${[...cell.keys()].join(', ') || 'no variable'}.`, i, len: 1, vars: [...cell.keys()] });
    }
    for (let len = 2; len <= n; len++) for (let i = 0; i + len <= n; i++) {
      const cell = new Map();
      for (let s = 1; s < len; s++) {
        const L = table[i][s], R = table[i + s][len - s];
        for (const r of C.rules) if (r.rhs.length === 2 && L.has(r.rhs[0]) && R.has(r.rhs[1]) && !cell.has(r.lhs)) cell.set(r.lhs, { rule: r, split: s });
      }
      table[i][len] = cell;
      trace.push({ kind: 'cell', say: `${w.slice(i, i + len)} comes from ${[...cell.keys()].join(', ') || 'no variable'}.`, i, len, vars: [...cell.keys()], from: [...cell.values()].map((x) => ({ split: x.split, rule: x.rule.lhs + ' → ' + x.rule.rhs.join(' ') })) });
    }
    const yes = table[0][n].has(C.start);
    trace.push({ kind: yes ? 'accept' : 'reject', say: yes ? `${C.start} is in the top cell: ${w} is generated.` : `${C.start} is not in the top cell: ${w} is not generated.` });
    return { accepted: yes, table: table.map((row) => row.map((c) => (c ? [...c.keys()] : null))), trace };
  }
  function A_CFG(G, w) {
    const { cnf, trace: t1 } = toCNF(G);
    const sym = typeof w === 'string' ? [...w] : w;
    const r = cyk(cnf, sym);
    return { accepted: r.accepted, cnf, table: r.table, trace: t1.concat(r.trace) };
  }
  // Mark the variables that generate some terminal string; empty iff the start is never marked.
  function E_CFG(G) {
    const gen = new Set(), trace = [], why = new Map();
    for (let ch = true; ch;) {
      ch = false;
      for (const r of G.rules) if (!gen.has(r.lhs) && r.rhs.every((s) => gen.has(s) || !G.variables.includes(s))) { gen.add(r.lhs); why.set(r.lhs, r); ch = true; trace.push({ kind: 'mark', say: `${r.lhs} → ${r.rhs.join(' ') || 'ε'} uses only terminals and marked variables: mark ${r.lhs}.`, variable: r.lhs, marked: [...gen] }); }
    }
    const empty = !gen.has(G.start);
    trace.push({ kind: empty ? 'empty' : 'nonempty', say: empty ? `${G.start} is never marked: the language is empty.` : `${G.start} is marked: the grammar generates some string.` });
    // a witness: expand each variable by the rule that marked it (those rules only use earlier-marked variables)
    const expand = (v) => why.get(v).rhs.map((s) => (G.variables.includes(s) ? expand(s) : s)).join('');
    return { empty, generating: [...gen], witness: empty ? null : expand(G.start), trace };
  }
  // All strings of length ≤ n the grammar generates, by a fixed point over the variables (a test oracle).
  function cfgLanguage(G, n) {
    const L = new Map(G.variables.map((v) => [v, new Set()]));
    for (let ch = true; ch;) {
      ch = false;
      for (const r of G.rules) {
        let cur = new Set(['']);
        for (const s of r.rhs) {
          const next = new Set(), opts = G.variables.includes(s) ? L.get(s) : new Set([s]);
          for (const a of cur) for (const b of opts) if (a.length + b.length <= n) next.add(a + b);
          cur = next;
        }
        for (const x of cur) if (!L.get(r.lhs).has(x)) { L.get(r.lhs).add(x); ch = true; }
      }
    }
    return L.get(G.start);
  }

  // ---------- mapping reductions as machine transformers ----------
  // A composed machine has numbered steps (for drawing) and a bounded run(x). Simulating M on w uses
  // the real runner; a step that "loops forever" is reported as a provable loop.
  function composed(name, lines, run) { return { name, lines, run }; }
  const simVerdict = (M, w, budget) => TM.run(M, w, { maxSteps: budget, trace: false });
  const is0n1n = (x) => { const n = x.length / 2; return x === '0'.repeat(n) + '1'.repeat(n); };

  const REDUCTIONS = {
    'ATM-coETM': {
      from: 'A_TM', to: 'the complement of E_TM', claim: '⟨M, w⟩ ∈ A_TM exactly when L(M₁) ≠ ∅',
      build(M, w) {
        return [composed('M₁', ['On input x:', `1. If x ≠ ${w || 'ε'}, reject.`, `2. Run ${M.name} on ${w || 'ε'}.`, `3. If ${M.name} accepts, accept.`], (x, budget = 5000) => {
          if (x !== w) return { verdict: 'reject', at: 1 };
          const r = simVerdict(M, w, budget);
          return { verdict: r.verdict === 'accept' ? 'accept' : r.verdict === 'reject' ? 'reject' : r.verdict, at: r.verdict === 'accept' ? 3 : 2, inner: r.verdict };
        })];
      },
    },
    'ATM-REGULAR': {
      from: 'A_TM', to: 'REGULAR_TM', claim: 'L(M₂) is Σ* (regular) when M accepts w, and {0ⁿ1ⁿ} (not regular) otherwise',
      build(M, w) {
        return [composed('M₂', ['On input x:', '1. If x has the form 0ⁿ1ⁿ, accept.', `2. Otherwise run ${M.name} on ${w || 'ε'}.`, `3. If ${M.name} accepts, accept.`], (x, budget = 5000) => {
          if (is0n1n(x)) return { verdict: 'accept', at: 1 };
          const r = simVerdict(M, w, budget);
          return { verdict: r.verdict === 'accept' ? 'accept' : r.verdict === 'reject' ? 'reject' : r.verdict, at: r.verdict === 'accept' ? 3 : 2, inner: r.verdict };
        })];
      },
    },
    'HALT-EQTM': {
      from: 'HALT_TM', to: 'EQ_TM', claim: 'L(M₁) = L(M₂) exactly when M halts on w',
      build(M, w) {
        return [composed('M₁', ['On input x:', '1. Accept.'], () => ({ verdict: 'accept', at: 1 })),
          composed('M₂', ['On input x:', `1. Run ${M.name} on ${w || 'ε'}.`, '2. When it halts (either way), accept.'], (x, budget = 5000) => {
            const r = simVerdict(M, w, budget);
            return { verdict: r.halted ? 'accept' : r.verdict, at: r.halted ? 2 : 1, inner: r.verdict };
          })];
      },
    },
    'ATM-HALT': {
      from: 'A_TM', to: 'HALT_TM', claim: 'M′ halts on w exactly when M accepts w',
      build(M) {
        return [composed('M′', ['On input x:', `1. Run ${M.name} on x.`, '2. If it accepts, accept.', '3. If it rejects, loop forever.'], (x, budget = 5000) => {
          const r = simVerdict(M, x, budget);
          return { verdict: r.verdict === 'accept' ? 'accept' : r.verdict === 'reject' ? 'loop' : r.verdict, at: r.verdict === 'accept' ? 2 : r.verdict === 'reject' ? 3 : 1, inner: r.verdict };
        })];
      },
    },
    'HALT-ATM': {
      from: 'HALT_TM', to: 'A_TM', claim: 'M′ accepts w exactly when M halts on w',
      build(M) {
        return [composed('M′', ['On input x:', `1. Run ${M.name} on x.`, '2. If it halts, accept.'], (x, budget = 5000) => {
          const r = simVerdict(M, x, budget);
          return { verdict: r.halted ? 'accept' : r.verdict, at: r.halted ? 2 : 1, inner: r.verdict };
        })];
      },
    },
  };
  // Apply a reduction to ⟨M, w⟩: the new machines, their descriptions, and the claim to check.
  function reduce(id, M, w) {
    const R = REDUCTIONS[id];
    if (!R) throw new Error('no reduction ' + id);
    const machines = R.build(M, w);
    const trace = [{ kind: 'input', say: `Start from the instance ⟨${M.name}, ${w || 'ε'}⟩ of ${R.from}.`, machine: M.name, input: w }];
    machines.forEach((m) => trace.push({ kind: 'build', say: `Write down ${m.name}: ${m.lines.slice(1).join(' ')}`, name: m.name, lines: m.lines }));
    trace.push({ kind: 'output', say: `Output ⟨${machines.map((m) => m.name).join(', ')}${id === 'ATM-HALT' || id === 'HALT-ATM' ? ', ' + (w || 'ε') : ''}⟩ as an instance of ${R.to}. The construction only writes text; it never runs ${M.name}.`, claim: R.claim });
    return { id, from: R.from, to: R.to, claim: R.claim, machines, trace };
  }

  // ---------- Rice's theorem ----------
  // A catalogue entry: {name, machine, lang (an id shared by machines with the same language), member(w)}.
  // property(entry) -> boolean. The checker looks for two machines with the same language that the
  // property separates (then it is not a property of languages), and for one machine with it and one
  // without (then it is non-trivial). A semantic, non-trivial property gets the reduction template.
  function riceCheck(property, catalogue, opts = {}) {
    const n = opts.n || 6, alphabet = opts.alphabet;
    const trace = [], vals = catalogue.map((e) => ({ e, v: !!property.test(e) }));
    let separated = null;
    for (let i = 0; i < vals.length && !separated; i++) for (let j = i + 1; j < vals.length && !separated; j++) {
      const a = vals[i], b = vals[j];
      if (a.v !== b.v && a.e.lang === b.e.lang) separated = [a.e, b.e];
    }
    if (separated) {
      trace.push({ kind: 'not-semantic', say: `${separated[0].name} and ${separated[1].name} recognise the same language, yet the property holds for ${vals.find((x) => x.e === separated[0]).v ? separated[0].name : separated[1].name} only: it is about the machines, not their languages, so Rice's theorem says nothing.`, pair: separated.map((e) => e.name) });
      return { semantic: false, trivial: null, witnesses: separated.map((e) => e.name), trace };
    }
    const yes = vals.find((x) => x.v), no = vals.find((x) => !x.v);
    if (!yes || !no) {
      trace.push({ kind: 'trivial', say: `Every machine in the catalogue ${yes ? 'has' : 'lacks'} the property: it looks trivial (it holds for all recognisable languages or for none), so it is decidable, by a machine that always says ${yes ? 'yes' : 'no'}.` });
      return { semantic: true, trivial: true, trace };
    }
    const empty = catalogue.find((e) => e.lang === 'empty');
    const emptyHas = empty ? !!property.test(empty) : false;
    const target = emptyHas ? no.e : yes.e;
    trace.push({ kind: 'nontrivial', say: `${yes.e.name} has the property and ${no.e.name} does not: it is non-trivial.`, yes: yes.e.name, no: no.e.name });
    trace.push({ kind: 'empty', say: `The empty language ${emptyHas ? 'has' : 'lacks'} the property, so pick ${target.name}, whose language ${emptyHas ? 'lacks' : 'has'} it${emptyHas ? ', and reduce to the complement of the property' : ''}.` });
    trace.push({ kind: 'template', say: `Given ⟨M, w⟩ build M_w: on input x, run M on w; if M accepts, run ${target.name} on x and answer as it does. If M accepts w then L(M_w) = L(${target.name}); otherwise L(M_w) = ∅. A decider for the property would decide A_TM, which is impossible.`, lines: ['On input x:', '1. Run M on w; if it rejects or loops, so does M_w.', `2. If M accepted, run ${target.name} on x and give its answer.`] });
    const template = (M, w) => composed('M_w', ['On input x:', `1. Run ${M.name} on ${w || 'ε'}.`, `2. If it accepts, run ${target.name} on x and answer as it does.`], (x, budget = 5000) => {
      const r = simVerdict(M, w, budget);
      if (r.verdict !== 'accept') return { verdict: r.verdict, at: 1, inner: r.verdict };
      const s = simVerdict(target.machine, x, budget);
      return { verdict: s.verdict, at: 2, inner: r.verdict };
    });
    return { semantic: true, trivial: false, yes: yes.e.name, no: no.e.name, emptyHas, target: target.name, template, trace, alphabet, n };
  }

  // ---------- Kolmogorov complexity: upper bounds by actual short descriptions ----------
  // LZ78: the string as (earlier phrase, next symbol) pairs; the bit cost is an upper bound on K(s) plus a constant.
  function lz78(s, alphabet) {
    const al = alphabet || [...new Set(s)].sort();
    const dict = new Map([['', 0]]), out = [];
    let cur = '';
    for (const ch of s) { if (dict.has(cur + ch)) { cur += ch; continue; } out.push([dict.get(cur), ch]); dict.set(cur + ch, dict.size); cur = ''; }
    if (cur) out.push([dict.get(cur.slice(0, -1)), cur.slice(-1)]);
    const symBits = Math.max(1, Math.ceil(Math.log2(Math.max(2, al.length))));
    let bits = 0;
    out.forEach((p, i) => { bits += Math.max(1, Math.ceil(Math.log2(i + 1))) + symBits; });
    return { pairs: out, bits, symBits };
  }
  function unlz78(pairs) { const dict = ['']; let s = ''; for (const [i, c] of pairs) { const p = dict[i] + c; dict.push(p); s += p; } return s; }
  // The shortest "repeat u k times" description that reproduces s, if any.
  function repeatDescription(s) {
    for (let len = 1; len <= s.length / 2; len++) if (s.length % len === 0 && s.slice(0, len).repeat(s.length / len) === s) return { unit: s.slice(0, len), times: s.length / len, text: `repeat "${s.slice(0, len)}" ${s.length / len} times` };
    return null;
  }
  function kolmogorov(s, alphabet) {
    const al = alphabet || [...new Set(s)].sort();
    const symBits = Math.max(1, Math.ceil(Math.log2(Math.max(2, al.length))));
    const literal = s.length * symBits, lz = lz78(s, al), rep = repeatDescription(s);
    const repBits = rep ? rep.unit.length * symBits + Math.ceil(Math.log2(rep.times + 1)) * 2 : Infinity;
    const best = Math.min(literal, lz.bits, repBits);
    const trace = [
      { kind: 'literal', say: `Writing ${s.length} symbols plainly costs ${literal} bits.`, bits: literal },
      { kind: 'lz', say: `LZ78 splits it into ${lz.pairs.length} phrases costing ${lz.bits} bits.`, bits: lz.bits, phrases: lz.pairs },
    ];
    if (rep) trace.push({ kind: 'repeat', say: `It is ${rep.text}: about ${repBits} bits.`, bits: repBits, text: rep.text });
    trace.push({ kind: 'bound', say: `So K(s) is at most about ${best} bits (plus a constant for the decoder). No method can certify a lower bound.`, bits: best });
    return { literal, lz: lz.bits, repeat: rep ? repBits : null, best, trace };
  }
  // Counting: there are 2^n strings of length n but only 2^(n-c) - 1 descriptions shorter than n - c bits.
  function incompressible(n, c) {
    const total = 2 ** n, short = 2 ** Math.max(0, n - c) - 1;
    return { total, short, atLeast: total - short, fraction: (total - short) / total, say: `Of the ${total} strings of length ${n}, at most ${short} have a description shorter than ${n - c} bits, so at least ${total - short} (${(((total - short) / total) * 100).toFixed(1)}%) are incompressible by ${c} bits.` };
  }

  T.comp = {
    program, runProgram, tmProgram, simulate, registry, diagonal, diagonalTable,
    A_DFA, E_DFA, EQ_DFA, parseCFG, toCNF, cyk, A_CFG, E_CFG, cfgLanguage,
    REDUCTIONS, reduce, composed, riceCheck,
  };
  T.kolmo = { lz78, unlz78, repeatDescription, kolmogorov, incompressible };
})();
