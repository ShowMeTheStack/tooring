// Part 5 exercises: Turing machines and other models. Machines to build (deciders and transducers, run
// on every short string with a step limit), configurations to trace, machines to encode and decode,
// recursive functions to evaluate and write, λ-terms to reduce, register-machine and macro programs to
// write, and questions on the variants and the models. The chapters are registered in 50-turing.js.
//
// Answers that the generic kinds cannot judge on their own (a configuration, a code, a program, a
// λ-term) are string exercises with an accept(text) test written here; the text arrives with its
// whitespace collapsed, so programs are typed on one line with ; between statements.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const H = (a, b, c) => [a, b, c];
  const ex = (x) => C.exercise(Object.assign({ level: 1 }, x));

  // ---- small checkers for string answers -----------------------------------------------------------------
  const squash = (s) => String(s).replace(/\s+/g, '').replace(/⊔/g, '_');
  /** A configuration u q v, spaces optional, trailing blanks optional */
  const config = (...want) => (t) => { const n = (s) => squash(s).replace(/_+$/, ''); return want.some((w) => n(w) === n(t)); };
  /** A list of whole numbers, whatever separates them */
  const numbers = (...want) => (t) => (String(t).match(/\d+/g) || []).join(',') === want.join(',');
  /** A bit string, spaces allowed */
  const bits = (want) => (t) => squash(t) === want;
  /** A λ-term equal (up to renaming bound variables) to the normal form of term */
  const lambda = (term) => {
    let target = null;
    return (t) => {
      const L = T.lambda;
      if (!target) target = L.normalize(term, { trace: false }).term;
      try { return L.alphaEq(L.parse(String(t)), target); } catch (e) { return false; }
    };
  };
  /** A primitive recursive expression (library names allowed, μ not) of n arguments that agrees with f */
  const primrec = (n, f, max) => (t) => {
    const R = T.rec, env = R.library();
    let e;
    try { e = R.parseExpr(String(t)); } catch (err) { return false; }
    const usesMu = (x, seen) => {
      if (x.t === 'M') return true;
      if (x.t === 'N') { if (!env[x.name] || seen.has(x.name)) return !env[x.name]; seen.add(x.name); return usesMu(env[x.name].expr, seen); }
      return (x.f && usesMu(x.f, seen)) || (x.g && usesMu(x.g, seen)) || (x.gs && x.gs.some((g) => usesMu(g, seen)));
    };
    if (usesMu(e, new Set())) return false;
    try { const a = R.arity(e, env); if (a !== null && a !== n) return false; } catch (err) { return false; }
    const top = max || 4;
    const grid = n === 1 ? Array.from({ length: top + 1 }, (_, x) => [x]) : [].concat(...Array.from({ length: top + 1 }, (_, x) => Array.from({ length: top + 1 }, (_, y) => [x, y])));
    for (const args of grid) {
      let r;
      try { r = R.evaluate(e, args, env, { trace: false, maxCalls: 300000 }); } catch (err) { return false; }
      if (r.verdict !== 'value' || r.value !== f(...args)) return false;
    }
    return true;
  };
  /** A register-machine program (statements separated by ;) computing r0 = f(r1, r2) */
  const ramProg = (n, f, coreOnly) => (t) => {
    const p = T.ram.parse(String(t).split(';').join('\n'));
    if (p.errors.length || !p.prog.length || (coreOnly && !p.core)) return false;
    const vals = [0, 1, 2, 3, 4, 5, 7];
    const inputs = n === 1 ? vals.map((x) => [x]) : [].concat(...vals.map((x) => vals.map((y) => [x, y])));
    for (const a of inputs) {
      let r;
      try { r = T.ram.run(p, [0].concat(a), { trace: false, maxSteps: 20000 }); } catch (e) { return false; }
      if (r.verdict !== 'halt' || r.output !== f(...a)) return false;
    }
    return true;
  };
  /** A macro program (statements separated by ;) that decides member, or computes out, on every short string */
  const macroProg = (alpha, opts) => (t) => {
    let r;
    try { r = T.tmMacro.compile(String(t).split(';').join('\n')); } catch (e) { return false; }
    if (r.errors.length || !r.machine) return false;
    for (const w of T.tm.strings([...alpha], opts.maxLen || 5)) {
      const run = T.tm.run(r.machine, w, { trace: false, maxSteps: 5000 });
      if (!run.halted) return false;
      if (opts.member && run.accepted !== !!opts.member(w)) return false;
      if (opts.output && (!run.accepted || T.tm.outputOf(r.machine, run.config) !== opts.output(w))) return false;
    }
    return true;
  };
  const count = (w, c) => [...w].filter((x) => x === c).length;

  // =========================================================================================================
  // Chapter 1: the Turing machine
  // =========================================================================================================
  const CH1 = 'tur-machines';

  // ---- build: deciders --------------------------------------------------------------------------------------
  ex({ id: 'tur-x-starts-b', chapter: CH1, title: 'Starts with b', kind: 'machine', machine: 'tm', alphabet: 'ab',
    text: 'Build a Turing machine over {a, b} that accepts exactly the strings whose first symbol is b, and rejects every other string (ε included). It must halt on every input.',
    member: (w) => w[0] === 'b',
    solution: 'start: s\naccept: yes\ns, b -> yes, b, S',
    wrong: ['start: s\naccept: yes\ns, b -> yes, b, S\ns, _ -> yes, _, S', 'start: s\naccept: yes\ns, a -> s, a, R\ns, b -> yes, b, S', 'start: s\naccept: yes\ns, a -> s, a, S\ns, b -> yes, b, S'],
    hints: H('The head starts on the first symbol: one look is enough.', 'A state with no rule for what it reads halts and rejects, so you only need to say what happens on b.', 'One rule: s, b → yes, b, S, with yes accepting. On a or on a blank there is no rule, so the machine rejects at once.') });

  ex({ id: 'tur-x-odd-ones', chapter: CH1, title: 'An odd number of 1s', kind: 'machine', machine: 'tm', alphabet: '01',
    text: 'Build a Turing machine over {0, 1} that accepts the strings with an odd number of 1s and rejects the rest. It must halt on every input.',
    member: (w) => count(w, '1') % 2 === 1,
    solution: 'start: even\naccept: yes\neven, 0 -> even, 0, R\neven, 1 -> odd, 1, R\nodd, 0 -> odd, 0, R\nodd, 1 -> even, 1, R\nodd, _ -> yes, _, S',
    wrong: ['start: even\naccept: yes\neven, 0 -> even, 0, R\neven, 1 -> odd, 1, R\nodd, 0 -> odd, 0, R\nodd, 1 -> even, 1, R\neven, _ -> yes, _, S', 'start: even\naccept: yes\neven, 0 -> even, 0, R\neven, 1 -> odd, 1, R\nodd, 1 -> even, 1, R\nodd, _ -> yes, _, S', 'start: even\naccept: yes\neven, 0 -> even, 0, R\neven, 1 -> odd, 1, R\nodd, 0 -> odd, 0, R\nodd, 1 -> even, 1, R\nodd, _ -> odd, _, S'],
    hints: H('The machine never needs to write anything: it only reads left to right, like a finite automaton.', 'Two states remember the parity of the 1s seen so far. The verdict comes when the head reaches the blank after the input.', 'even and odd each loop on 0 and swap on 1, moving right; odd, _ → yes. In even on a blank there is no rule, so it rejects.') });

  ex({ id: 'tur-x-len3', chapter: CH1, title: 'Length a multiple of three', kind: 'machine', machine: 'tm', alphabet: 'ab',
    text: 'Build a Turing machine over {a, b} that accepts the strings whose length is 0, 3, 6, … and rejects the rest.',
    member: (w) => w.length % 3 === 0,
    solution: 'start: r0\naccept: yes\nr0, a -> r1, a, R\nr0, b -> r1, b, R\nr1, a -> r2, a, R\nr1, b -> r2, b, R\nr2, a -> r0, a, R\nr2, b -> r0, b, R\nr0, _ -> yes, _, S',
    wrong: ['start: r0\naccept: yes\nr0, a -> r1, a, R\nr0, b -> r1, b, R\nr1, a -> r2, a, R\nr1, b -> r2, b, R\nr2, a -> r0, a, R\nr2, b -> r0, b, R\nr2, _ -> yes, _, S', 'start: r0\naccept: yes\nr0, a|b -> r1, *, R\nr1, a|b -> r0, *, R\nr0, _ -> yes, _, S', 'start: r0\naccept: yes\nr0, a -> r1, a, R\nr0, b -> r1, b, R\nr1, a -> r2, a, R\nr1, b -> r2, b, R\nr2, a -> r0, a, R\nr2, b -> r0, b, R\nr0, _ -> r0, _, S'],
    hints: H('Count modulo 3 with three states.', 'Every symbol, a or b, moves you one state on in a cycle r0 → r1 → r2 → r0.', 'r0, r1, r2 move right round the cycle on a and on b; r0, _ → yes. A rule like r0, a|b → r1, *, R covers both symbols at once.') });

  ex({ id: 'tur-x-bab', chapter: CH1, title: 'Contains bab', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 2,
    text: 'Build a Turing machine over {a, b} that accepts the strings containing bab somewhere, such as abab or babb, and rejects the others.',
    member: (w) => w.includes('bab'),
    solution: 'start: s\naccept: yes\ns, a -> s, a, R\ns, b -> b1, b, R\nb1, b -> b1, b, R\nb1, a -> ba, a, R\nba, a -> s, a, R\nba, b -> yes, b, S',
    wrong: ['start: s\naccept: yes\ns, a -> s, a, R\ns, b -> b1, b, R\nb1, b -> s, b, R\nb1, a -> ba, a, R\nba, a -> s, a, R\nba, b -> yes, b, S', 'start: s\naccept: yes\ns, a -> s, a, R\ns, b -> b1, b, R\nb1, b -> b1, b, R\nb1, a -> ba, a, R\nba, a -> b1, a, R\nba, b -> yes, b, S'],
    hints: H('Remember how much of bab you have just seen: nothing, b, or ba.', 'After bb you have still just seen a b; after baa you have seen nothing useful.', 's loops on a; s, b → b1; b1 loops on b; b1, a → ba; ba, b → yes; ba, a → s.') });

  ex({ id: 'tur-x-same-ends', chapter: CH1, title: 'Same first and last symbol', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 2,
    text: 'Build a Turing machine over {a, b} that accepts the non-empty strings whose first and last symbols are equal (a, abba, bab, …) and rejects the rest, ε included.',
    member: (w) => w.length > 0 && w[0] === w[w.length - 1],
    solution: 'start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> ca, _, L\nca, a -> yes, a, S\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, _ -> cb, _, L\ncb, b -> yes, b, S',
    wrong: ['start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\nra, a -> yes, a, S\nrb, b -> yes, b, S', 'start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\ns, _ -> yes, _, S\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> ca, _, L\nca, a -> yes, a, S\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, _ -> cb, _, L\ncb, b -> yes, b, S', 'start: s\naccept: yes\ns, a -> r, a, R\ns, b -> r, b, R\nr, a -> r, a, R\nr, b -> r, b, R\nr, _ -> c, _, L\nc, a -> yes, a, S\nc, b -> yes, b, S'],
    hints: H('The first symbol has to be remembered all the way to the end. A state is the only place to keep it.', 'Split into two runs right: one for "began with a", one for "began with b". At the blank, step back once and look.', 's, a → ra and s, b → rb; each runs right over everything; on the blank step left into ca (or cb), which accepts only on a (or b). A one-symbol string works because the step back lands on that same symbol.') });

  ex({ id: 'tur-x-anban', chapter: CH1, title: 'As many a\'s after the b as before', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 2,
    text: 'Build a Turing machine that decides { aⁿ b aⁿ : n ≥ 0 }: some a\'s, one b, then the same number of a\'s. So b, aba and aabaa are in; ε, ab, abaa and bb are not.',
    member: (w) => { const m = /^(a*)b(a*)$/.exec(w); return !!m && m[1].length === m[2].length; },
    tests: ['aaabaaa', 'aaabaa'],
    solution: 'start: p\naccept: yes\np, a -> r, X, R\np, b -> c, b, R\nr, a -> r, a, R\nr, b -> r, b, R\nr, _ -> m, _, L\nr, Y -> m, Y, L\nm, a -> l, Y, L\nl, a -> l, a, L\nl, b -> l, b, L\nl, X -> p, X, R\nc, Y -> c, Y, R\nc, _ -> yes, _, S',
    wrong: ['start: p\naccept: yes\np, a -> r, X, R\np, b -> yes, b, R\nr, a -> r, a, R\nr, b -> r, b, R\nr, _ -> m, _, L\nr, Y -> m, Y, L\nm, a -> l, Y, L\nl, a -> l, a, L\nl, b -> l, b, L\nl, X -> p, X, R', 'start: p\naccept: yes\np, a -> r, X, R\np, b -> c, b, R\nr, a -> r, a, R\nr, b -> r, b, R\nr, _ -> m, _, L\nr, Y -> m, Y, L\nm, a -> l, Y, L\nl, a -> l, a, L\nl, b -> l, b, L\nl, X -> p, X, R\nc, _ -> yes, _, S', 'start: p\naccept: yes\np, a -> r, X, R\np, b -> c, b, R\nr, a -> r, a, R\nr, b -> r, b, R\nr, _ -> m, _, L\nr, Y -> m, Y, L\nm, a -> l, Y, L\nm, b -> l, b, L\nl, a -> l, a, L\nl, b -> l, b, L\nl, X -> p, X, R\nc, Y -> c, Y, R\nc, _ -> yes, _, S'],
    hints: H('Pair the outermost a\'s off one at a time: cross the leftmost a with X and the rightmost a with Y.', 'Going right, stop at the first blank or Y and step back: that cell must be an a. Coming back, stop at the X and step right.', 'When the leftmost unmarked symbol is the b, everything after it must be Y\'s and then a blank. p, a → r, X, R; r runs right to _ or Y, then m, a → l, Y, L; l runs back to X; p, b → c; c skips Y and accepts on _.') });

  ex({ id: 'tur-x-pal01', chapter: CH1, title: 'Binary palindromes', kind: 'machine', machine: 'tm', alphabet: '01', level: 2,
    text: 'Build a Turing machine that decides the palindromes over {0, 1}: the strings that read the same backwards, such as ε, 0, 0110 and 10101.',
    member: (w) => w === [...w].reverse().join(''),
    solution: 'start: p\naccept: yes\np, 0 -> r0, _, R\np, 1 -> r1, _, R\np, _ -> yes, _, S\nr0, 0 -> r0, 0, R\nr0, 1 -> r0, 1, R\nr0, _ -> c0, _, L\nr1, 0 -> r1, 0, R\nr1, 1 -> r1, 1, R\nr1, _ -> c1, _, L\nc0, 0 -> back, _, L\nc0, _ -> yes, _, S\nc1, 1 -> back, _, L\nc1, _ -> yes, _, S\nback, 0 -> back, 0, L\nback, 1 -> back, 1, L\nback, _ -> p, _, R',
    wrong: ['start: p\naccept: yes\np, 0 -> r0, _, R\np, 1 -> r1, _, R\np, _ -> yes, _, S\nr0, 0 -> r0, 0, R\nr0, 1 -> r0, 1, R\nr0, _ -> c0, _, L\nr1, 0 -> r1, 0, R\nr1, 1 -> r1, 1, R\nr1, _ -> c1, _, L\nc0, 0 -> back, _, L\nc1, 1 -> back, _, L\nback, 0 -> back, 0, L\nback, 1 -> back, 1, L\nback, _ -> p, _, R', 'start: p\naccept: yes\np, 0 -> r0, _, R\np, 1 -> r1, _, R\np, _ -> yes, _, S\nr0, 0 -> r0, 0, R\nr0, 1 -> r0, 1, R\nr0, _ -> c0, _, L\nr1, 0 -> r1, 0, R\nr1, 1 -> r1, 1, R\nr1, _ -> c1, _, L\nc0, 0 -> back, _, L\nc0, 1 -> back, _, L\nc0, _ -> yes, _, S\nc1, 1 -> back, _, L\nc1, _ -> yes, _, S\nback, 0 -> back, 0, L\nback, 1 -> back, 1, L\nback, _ -> p, _, R'],
    hints: H('Zig-zag: erase the first symbol, remembering it in the state, run to the far end, and compare with the last symbol.', 'Erase the last symbol too when it matches, run back to the blank on the left, and repeat. Watch the middle of an odd-length string: when you step back from the end you may find a blank.', 'p erases and goes to r0 or r1; at the right blank step left into c0 or c1; c0 needs 0 (c1 needs 1), erases it and runs back; c0 or c1 on a blank means everything matched, so accept; p on a blank accepts too.') });

  ex({ id: 'tur-x-equal-ab', chapter: CH1, title: 'As many a\'s as b\'s, in any order', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 3,
    text: 'Build a Turing machine that decides the strings over {a, b} with as many a\'s as b\'s, in any order: ε, ab, ba, abba and baab are in; a, aab and bbba are not.',
    member: (w) => count(w, 'a') === count(w, 'b'),
    solution: 'start: p\naccept: yes\np, X -> p, X, R\np, _ -> yes, _, S\np, a -> fb, X, R\np, b -> fa, X, R\nfb, a -> fb, a, R\nfb, X -> fb, X, R\nfb, b -> back, X, L\nfa, b -> fa, b, R\nfa, X -> fa, X, R\nfa, a -> back, X, L\nback, a -> back, a, L\nback, b -> back, b, L\nback, X -> back, X, L\nback, _ -> p, _, R',
    wrong: ['start: p\naccept: yes\np, X -> p, X, R\np, _ -> yes, _, S\np, a -> fb, X, R\np, b -> fa, X, R\nfb, a -> fb, a, R\nfb, b -> back, X, L\nfa, b -> fa, b, R\nfa, a -> back, X, L\nback, a -> back, a, L\nback, b -> back, b, L\nback, X -> back, X, L\nback, _ -> p, _, R', 'start: p\naccept: yes\np, a -> q, a, R\np, b -> q, b, R\nq, a -> p, a, R\nq, b -> p, b, R\np, _ -> yes, _, S', 'start: p\naccept: yes\np, X -> p, X, R\np, _ -> yes, _, S\np, a -> fb, X, R\np, b -> fa, X, R\nfb, a -> fb, a, R\nfb, X -> fb, X, R\nfb, b -> back, X, L\nfa, b -> fa, b, R\nfa, X -> fa, X, R\nfa, a -> back, X, L\nback, a -> back, a, L\nback, b -> back, b, L\nback, X -> back, X, L\nback, _ -> p, _, R\nfb, _ -> yes, _, S'],
    hints: H('Cross symbols off in pairs: one a and one b each round.', 'Find the first symbol not yet crossed off. If it is an a, cross it off and hunt to the right for a b (stepping over a\'s and crossed cells), and the other way round. If the hunt meets the blank, reject.', 'p skips X; p on a blank accepts; p, a → fb, X, R; fb skips a and X and crosses the first b, then back runs left to the blank and steps right into p. fa is the same with a and b swapped. Forgetting to skip X during the hunt rejects aabb.') });

  ex({ id: 'tur-x-reverse-hash', chapter: CH1, title: 'u#v with v the reverse of u', kind: 'machine', machine: 'tm', alphabet: 'ab#', level: 3, maxLen: 5,
    text: 'Build a Turing machine over {a, b, #} that decides { u#v : u, v ∈ {a, b}*, v is u written backwards }. So #, a#a and ab#ba are in; ab#ab, a#, aba and a#a#a are not.',
    member: (w) => { const m = /^([ab]*)#([ab]*)$/.exec(w); return !!m && m[2] === [...m[1]].reverse().join(''); },
    tests: ['abb#bba', 'abb#abb', 'ba#ab', '##'],
    solution: 'start: p\naccept: yes\np, a -> ra, _, R\np, b -> rb, _, R\np, # -> mid, _, R\nmid, _ -> yes, _, S\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, # -> ra, #, R\nra, _ -> ca, _, L\nca, a -> back, _, L\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, # -> rb, #, R\nrb, _ -> cb, _, L\ncb, b -> back, _, L\nback, a -> back, a, L\nback, b -> back, b, L\nback, # -> back, #, L\nback, _ -> p, _, R',
    wrong: ['start: p\naccept: yes\np, a -> ra, _, R\np, b -> rb, _, R\np, # -> yes, _, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, # -> ra, #, R\nra, _ -> ca, _, L\nca, a -> back, _, L\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, # -> rb, #, R\nrb, _ -> cb, _, L\ncb, b -> back, _, L\nback, a -> back, a, L\nback, b -> back, b, L\nback, # -> back, #, L\nback, _ -> p, _, R', 'start: p\naccept: yes\np, a -> ra, _, R\np, b -> rb, _, R\np, _ -> yes, _, S\np, # -> mid, _, R\nmid, _ -> yes, _, S\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, # -> ra, #, R\nra, _ -> ca, _, L\nca, a -> back, _, L\nca, _ -> yes, _, S\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, # -> rb, #, R\nrb, _ -> cb, _, L\ncb, b -> back, _, L\ncb, _ -> yes, _, S\nback, a -> back, a, L\nback, b -> back, b, L\nback, # -> back, #, L\nback, _ -> p, _, R'],
    hints: H('This is a palindrome check with a twist: the centre must be exactly one #.', 'Erase the outer pair of symbols each round, as for palindromes. When the first symbol left is #, the # must be the only thing left.', 'p, a → ra, _, R; ra runs right over a, b and # to the blank, steps left, and ca must read a, which it erases before running back (b likewise). p, # → mid, _, R, and mid accepts only on a blank. A # anywhere else leaves some state with no rule, so the machine rejects.') });

  ex({ id: 'tur-x-sum-ab-c', chapter: CH1, title: 'aⁱbʲcᵏ with i + j = k', kind: 'machine', machine: 'tm', alphabet: 'abc', level: 3, maxLen: 5,
    text: 'Build a Turing machine that decides { aⁱ bʲ cᵏ : i + j = k }: first a\'s, then b\'s, then exactly as many c\'s as there were a\'s and b\'s together. So ε, ac, bc, abcc and aacc are in; ca, bacc, abc and acc are not.',
    member: (w) => { const m = /^(a*)(b*)(c*)$/.exec(w); return !!m && m[1].length + m[2].length === m[3].length; },
    tests: ['aabccc', 'abbccc', 'abccc', 'bacc'],
    solution: 'start: fa\naccept: yes\nfa, a -> fa, a, R\nfa, b -> fb, b, R\nfa, c -> fc, c, R\nfa, _ -> home, _, L\nfb, b -> fb, b, R\nfb, c -> fc, c, R\nfb, _ -> home, _, L\nfc, c -> fc, c, R\nfc, _ -> home, _, L\nhome, a -> home, a, L\nhome, b -> home, b, L\nhome, c -> home, c, L\nhome, _ -> p, _, R\np, X -> p, X, R\np, a -> find, X, R\np, b -> find, X, R\np, Y -> chk, Y, R\np, _ -> yes, _, S\nfind, a -> find, a, R\nfind, b -> find, b, R\nfind, Y -> find, Y, R\nfind, c -> ret, Y, L\nret, a -> ret, a, L\nret, b -> ret, b, L\nret, Y -> ret, Y, L\nret, X -> p, X, R\nchk, Y -> chk, Y, R\nchk, _ -> yes, _, S',
    wrong: ['start: p\naccept: yes\np, X -> p, X, R\np, a -> find, X, R\np, b -> find, X, R\np, Y -> chk, Y, R\np, _ -> yes, _, S\nfind, a -> find, a, R\nfind, b -> find, b, R\nfind, Y -> find, Y, R\nfind, c -> ret, Y, L\nret, a -> ret, a, L\nret, b -> ret, b, L\nret, Y -> ret, Y, L\nret, X -> p, X, R\nchk, Y -> chk, Y, R\nchk, _ -> yes, _, S', 'start: fa\naccept: yes\nfa, a -> fa, a, R\nfa, b -> fb, b, R\nfa, c -> fc, c, R\nfa, _ -> home, _, L\nfb, b -> fb, b, R\nfb, c -> fc, c, R\nfb, _ -> home, _, L\nfc, c -> fc, c, R\nfc, _ -> home, _, L\nhome, a -> home, a, L\nhome, b -> home, b, L\nhome, c -> home, c, L\nhome, _ -> p, _, R\np, X -> p, X, R\np, a -> find, X, R\np, b -> find, X, R\np, Y -> yes, Y, R\np, _ -> yes, _, S\nfind, a -> find, a, R\nfind, b -> find, b, R\nfind, Y -> find, Y, R\nfind, c -> ret, Y, L\nret, a -> ret, a, L\nret, b -> ret, b, L\nret, Y -> ret, Y, L\nret, X -> p, X, R'],
    hints: H('Two jobs: check the shape a…ab…bc…c, then check the counts. Do them in two phases.', 'Phase one is a finite-automaton pass to the right, then a run back to the left end. Phase two crosses off one a or b with X and the first c with Y, round after round.', 'Phase one: fa, fb, fc move right and reject on a symbol out of order; at the blank go home to the left end. Phase two: p skips X; p on a or b writes X and find runs right over a, b and Y to the first c, which becomes Y; ret runs back to the X. When p reads Y, chk must see only Y\'s and then a blank. Without phase one, bacc is wrongly accepted.') });

  // ---- build: transducers -------------------------------------------------------------------------------------
  ex({ id: 'tur-x-times2', chapter: CH1, title: 'Double a binary number', kind: 'machine', machine: 'tm', alphabet: '01',
    text: 'Build a Turing machine that doubles a binary number by putting a 0 on its right end: 101 becomes 1010, and ε becomes 0. It must halt in an accepting state with exactly the result on the tape.',
    output: (w) => w + '0',
    solution: 'start: s\naccept: done\ns, 0 -> s, 0, R\ns, 1 -> s, 1, R\ns, _ -> done, 0, S',
    wrong: ['start: s\naccept: done\ns, 0 -> s, 0, R\ns, 1 -> s, 1, R\ns, _ -> done, 1, S', 'start: s\naccept: done\ns, 0 -> s, 0, R\ns, 1 -> s, 1, R\ns, _ -> s, 0, R', 'start: s\naccept: done\ns, 0 -> done, 0, R\ns, 1 -> s, 1, R\ns, _ -> done, 0, S'],
    hints: H('Shifting left by one place in binary multiplies by two.', 'Run right over the digits; the first blank is where the new digit goes.', 's moves right over 0 and 1; s, _ → done, 0, S.') });

  ex({ id: 'tur-x-unary-succ', chapter: CH1, title: 'Unary successor, from the left', kind: 'machine', machine: 'tm', alphabet: '1',
    text: 'In unary, n is written as n 1s. Build a Turing machine that turns 1ⁿ into 1ⁿ⁺¹ in at most three steps, whatever n is. (The tape goes on for ever in both directions.)',
    output: (w) => w + '1',
    tests: ['1111111111'],
    steps: 3,
    solution: 'start: s\naccept: done\ns, 1 -> t, 1, L\ns, _ -> done, 1, S\nt, _ -> done, 1, S',
    wrong: ['start: s\naccept: done\ns, 1 -> s, 1, R\ns, _ -> done, 1, S', 'start: s\naccept: done\ns, 1 -> t, 1, L\nt, _ -> done, 1, S', 'start: s\naccept: done\ns, 1 -> t, 1, L\ns, _ -> done, 1, S\nt, _ -> done, _, S'],
    hints: H('Running to the right end takes n steps, which is too many.', 'The cell just left of the input is blank, and it is only one step away.', 's, 1 → t, 1, L then t, _ → done, 1, S; for ε, s, _ → done, 1, S. The result is one more 1, added on the left.') });

  ex({ id: 'tur-x-rotate', chapter: CH1, title: 'Move the first symbol to the end', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 2,
    text: 'Build a Turing machine over {a, b} that moves the first symbol of its input to the end: abb becomes bba, ba becomes ab, and ε and single symbols stay as they are.',
    output: (w) => (w ? w.slice(1) + w[0] : ''),
    solution: 'start: s\naccept: done\ns, a -> ca, _, R\ns, b -> cb, _, R\ns, _ -> done, _, S\nca, a -> ca, a, R\nca, b -> ca, b, R\nca, _ -> done, a, S\ncb, a -> cb, a, R\ncb, b -> cb, b, R\ncb, _ -> done, b, S',
    wrong: ['start: s\naccept: done\ns, a -> ca, a, R\ns, b -> cb, b, R\ns, _ -> done, _, S\nca, a -> ca, a, R\nca, b -> ca, b, R\nca, _ -> done, a, S\ncb, a -> cb, a, R\ncb, b -> cb, b, R\ncb, _ -> done, b, S', 'start: s\naccept: done\ns, a -> ca, _, R\ns, b -> cb, _, R\ns, _ -> done, _, S\nca, a -> ca, a, R\nca, b -> ca, b, R\nca, _ -> done, b, S\ncb, a -> cb, a, R\ncb, b -> cb, b, R\ncb, _ -> done, a, S'],
    hints: H('The symbol you pick up has to travel in the state, since the head carries nothing else.', 'Erase the first cell (blanks at the ends of the output are ignored), then run right.', 's, a → ca, _, R; ca runs right and writes a on the first blank; cb does the same for b; s, _ → done.') });

  ex({ id: 'tur-x-bin-dec', chapter: CH1, title: 'Binary decrement', kind: 'machine', machine: 'tm', alphabet: '01', level: 2,
    text: 'Build a Turing machine that subtracts one from a binary number, keeping its width: 100 becomes 011 and 1011 becomes 1010. A string of zeros (and ε) stays exactly as it is.',
    output: (w) => (!/1/.test(w) ? w : (parseInt(w, 2) - 1).toString(2).padStart(w.length, '0')),
    solution: 'start: r\naccept: done\nr, 0 -> r, 0, R\nr, 1 -> r, 1, R\nr, _ -> c, _, L\nc, 0 -> c, 1, L\nc, 1 -> done, 0, S\nc, _ -> z, _, R\nz, 1 -> z, 0, R\nz, _ -> done, _, S',
    wrong: ['start: r\naccept: done\nr, 0 -> r, 0, R\nr, 1 -> r, 1, R\nr, _ -> c, _, L\nc, 0 -> c, 1, L\nc, 1 -> done, 0, S\nc, _ -> done, _, S', 'start: r\naccept: done\nr, 0 -> r, 0, R\nr, 1 -> r, 1, R\nr, _ -> c, _, L\nc, 0 -> c, 0, L\nc, 1 -> done, 0, S\nc, _ -> done, _, S', 'start: r\naccept: done\nr, 0 -> r, 0, R\nr, 1 -> r, 1, R\nr, _ -> c, _, L\nc, 0 -> done, 1, S\nc, 1 -> done, 0, S\nc, _ -> done, _, S'],
    hints: H('Work from the right end, like subtraction on paper: a 0 needs a borrow, a 1 pays it.', 'Each 0 becomes 1 and the borrow moves left; the first 1 becomes 0 and you are done. But if you fall off the left end, the number was zero and you have spoiled it.', 'r runs right; c, 0 → c, 1, L; c, 1 → done, 0, S; c, _ → z, _, R, and z turns the 1s back into 0s up to the blank.') });

  ex({ id: 'tur-x-unary-double', chapter: CH1, title: 'Unary doubling', kind: 'machine', machine: 'tm', alphabet: '1', level: 2, maxLen: 7,
    text: 'Build a Turing machine that turns 1ⁿ into 1²ⁿ. Extra tape symbols such as X and Y are allowed while it works, but only 1s may be left at the end.',
    output: (w) => w + w,
    solution: 'start: p\naccept: done\np, 1 -> r, X, R\np, Y -> f, 1, R\np, _ -> done, _, S\nr, 1 -> r, 1, R\nr, Y -> r, Y, R\nr, _ -> l, Y, L\nl, 1 -> l, 1, L\nl, Y -> l, Y, L\nl, X -> p, X, R\nf, Y -> f, 1, R\nf, _ -> g, _, L\ng, 1 -> g, 1, L\ng, X -> g, 1, L\ng, _ -> done, _, R',
    wrong: ['start: p\naccept: done\np, 1 -> r, X, R\np, Y -> done, Y, S\np, _ -> done, _, S\nr, 1 -> r, 1, R\nr, Y -> r, Y, R\nr, _ -> l, Y, L\nl, 1 -> l, 1, L\nl, Y -> l, Y, L\nl, X -> p, X, R', 'start: p\naccept: done\np, 1 -> p, 1, R\np, _ -> done, 1, S', 'start: p\naccept: done\np, 1 -> r, X, R\np, Y -> f, 1, R\np, _ -> done, _, S\nr, 1 -> r, 1, R\nr, Y -> r, Y, R\nr, _ -> l, Y, L\nl, 1 -> l, 1, L\nl, Y -> l, Y, L\nl, X -> p, X, R\nf, Y -> f, 1, R\nf, _ -> done, _, S'],
    hints: H('For every 1 of the input, add one new symbol on the right end.', 'Mark the input 1 you are working on with X so you can find your way back; write the new symbols as Y so you can tell them from the input.', 'p, 1 → r, X, R; r runs right over 1 and Y and writes Y on the blank; l runs back to the X. When p meets a Y, every input 1 is done: turn the Y\'s into 1s going right, then the X\'s into 1s going left.') });

  ex({ id: 'tur-x-sort', chapter: CH1, title: 'Sort the a\'s before the b\'s', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 3,
    text: 'Build a Turing machine over {a, b} that sorts its input so that all a\'s come first: baba becomes aabb, and bba becomes abb.',
    output: (w) => 'a'.repeat(count(w, 'a')) + 'b'.repeat(count(w, 'b')),
    solution: 'start: s\naccept: done\ns, a -> s, a, R\ns, b -> sb, b, R\ns, _ -> done, _, S\nsb, b -> sb, b, R\nsb, a -> sw, b, L\nsb, _ -> done, _, S\nsw, b -> home, a, L\nhome, a -> home, a, L\nhome, b -> home, b, L\nhome, _ -> s, _, R',
    wrong: ['start: s\naccept: done\ns, a -> s, a, R\ns, b -> sb, b, R\ns, _ -> done, _, S\nsb, b -> sb, b, R\nsb, a -> sw, b, L\nsb, _ -> done, _, S\nsw, b -> s, a, R', 'start: s\naccept: done\ns, a -> s, a, R\ns, b -> sb, b, R\ns, _ -> done, _, S\nsb, b -> sb, b, R\nsb, a -> sw, a, L\nsb, _ -> done, _, S\nsw, b -> home, b, L\nhome, a -> home, a, L\nhome, b -> home, b, L\nhome, _ -> s, _, R', 'start: s\naccept: done\ns, a -> s, a, R\ns, b -> s, a, R\ns, _ -> done, _, S'],
    hints: H('The tape is sorted exactly when it contains no b directly followed by an a.', 'Find such a pair ba and swap it into ab. Then start again from the left end. Each swap moves one a one place left, so this ends.', 's runs right over a\'s; on b go to sb, which runs over b\'s; sb, a → sw, b, L and sw, b → home, a, L swap the pair; home runs back to the left blank and steps right into s. Reaching a blank in s or sb means nothing is out of order.') });

  ex({ id: 'tur-x-stutter', chapter: CH1, title: 'Say every symbol twice', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 3, maxLen: 5,
    text: 'Build a Turing machine over {a, b} that writes every symbol twice: ab becomes aabb and bab becomes bbaabb. Extra tape symbols are allowed while it works, but the tape must hold only the result at the end.',
    output: (w) => [...w].map((c) => c + c).join(''),
    solution: 'start: m\naccept: done\nm, a -> m, a, R\nm, b -> m, b, R\nm, _ -> ret, #, L\nret, a -> ret, a, L\nret, b -> ret, b, L\nret, # -> ret, #, L\nret, _ -> p, _, R\np, a -> ga, _, R\np, b -> gb, _, R\np, # -> done, _, S\nga, a -> ga, a, R\nga, b -> ga, b, R\nga, # -> ga, #, R\nga, _ -> ga2, a, R\nga2, _ -> ret, a, L\ngb, a -> gb, a, R\ngb, b -> gb, b, R\ngb, # -> gb, #, R\ngb, _ -> gb2, b, R\ngb2, _ -> ret, b, L',
    wrong: ['start: m\naccept: done\nm, a -> m, a, R\nm, b -> m, b, R\nm, _ -> ret, #, L\nret, a -> ret, a, L\nret, b -> ret, b, L\nret, # -> ret, #, L\nret, _ -> p, _, R\np, a -> ga, _, R\np, b -> gb, _, R\np, # -> done, #, S\nga, a -> ga, a, R\nga, b -> ga, b, R\nga, # -> ga, #, R\nga, _ -> ga2, a, R\nga2, _ -> ret, a, L\ngb, a -> gb, a, R\ngb, b -> gb, b, R\ngb, # -> gb, #, R\ngb, _ -> gb2, b, R\ngb2, _ -> ret, b, L', 'start: m\naccept: done\nm, a -> m, a, R\nm, b -> m, b, R\nm, _ -> ret, #, L\nret, a -> ret, a, L\nret, b -> ret, b, L\nret, # -> ret, #, L\nret, _ -> p, _, R\np, a -> ga, _, R\np, b -> gb, _, R\np, # -> done, _, S\nga, a -> ga, a, R\nga, b -> ga, b, R\nga, # -> ga, #, R\nga, _ -> ret, a, L\ngb, a -> gb, a, R\ngb, b -> gb, b, R\ngb, # -> gb, #, R\ngb, _ -> ret, b, L'],
    hints: H('Build the result to the right of the input, behind a separator, and use up the input as you go.', 'Put # after the input. Then, each round, erase the leftmost input symbol and write it twice at the far right end.', 'm writes # on the first blank and ret runs back to the left. p, a → ga, _, R; ga runs right over everything and writes a a on the two blanks; ret runs back to the erased cell. When p reads # the input is used up: erase # and halt. Leaving # behind gives the wrong output.') });

  ex({ id: 'tur-x-drop-b', chapter: CH1, title: 'Delete every b', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 3,
    text: 'Build a Turing machine over {a, b} that deletes every b and closes the gaps: abba becomes aa, bab becomes a, and bbb becomes ε. (Blanks in the middle of the tape count as part of the output, so gaps must really be closed.)',
    output: (w) => w.replace(/b/g, ''),
    solution: 'start: s\naccept: done\ns, a -> s, a, R\ns, b -> sb, b, R\ns, _ -> er, _, L\nsb, b -> sb, b, R\nsb, a -> sw, b, L\nsb, _ -> er, _, L\nsw, b -> home, a, L\nhome, a -> home, a, L\nhome, b -> home, b, L\nhome, _ -> s, _, R\ner, b -> er, _, L\ner, a -> done, a, S\ner, _ -> done, _, S',
    wrong: ['start: s\naccept: done\ns, a -> s, a, R\ns, b -> s, _, R\ns, _ -> done, _, S', 'start: s\naccept: done\ns, a -> s, a, R\ns, b -> sb, b, R\ns, _ -> done, _, S\nsb, b -> sb, b, R\nsb, a -> sw, b, L\nsb, _ -> done, _, S\nsw, b -> home, a, L\nhome, a -> home, a, L\nhome, b -> home, b, L\nhome, _ -> s, _, R'],
    hints: H('Overwriting each b with a blank leaves holes in the middle, and holes count.', 'Push the b\'s to the right end first (swap every ba into ab, as when sorting), and then erase them there.', 'The sorting machine, except that reaching the right blank goes to er: er walks left turning b into blank, and halts at the first a or at the left blank.') });

  // ---- trace the configurations -------------------------------------------------------------------------------
  const M_MARK = 'start: p\naccept: h\np, a -> q, X, R\np, b -> p, b, R\nq, a -> q, a, R\nq, b -> r, Y, L\nr, a -> r, a, L\nr, X -> p, X, R\np, Y -> p, Y, R\np, _ -> h, _, S';
  const M_INC = 'start: s\naccept: done\ns, 0 -> s, 0, R\ns, 1 -> s, 1, R\ns, _ -> c, _, L\nc, 1 -> c, 0, L\nc, 0 -> done, 1, S\nc, _ -> done, 1, S';
  const M_PAR = 'start: q0\naccept: q2\nq0, a -> q1, a, R\nq1, a -> q0, b, R\nq0, b -> q0, b, R\nq1, b -> q1, a, R\nq0, _ -> q2, _, L';
  const machineBlock = (t) => ({ code: t, lang: 'machine' });

  ex({ id: 'tur-x-cfg-inc', chapter: CH1, title: 'Where is the head after five steps?', kind: 'string',
    text: ['This machine adds one to a binary number. It starts in s with 1011 on the tape and the head on the first 1.', machineBlock(M_INC), 'Write its configuration after exactly five steps, in the form u q v: the tape left of the head, the state, then the tape from the head on. For instance the start is s 1011.'],
    accept: config('101 c 1'), solution: '101 c 1', wrong: ['1011 c', '101c1_x', '10 c 11', 'c 1011'],
    whyNot: 'Count the moves one at a time: four moves right reach the blank, the fifth goes back left.',
    hints: H('Steps 1 to 4 move right over 1, 0, 1, 1 in state s.', 'After step 4 the head is on the blank after the input: 1011 s ⊔. The rule for s on a blank moves left into c.', '101 c 1: the head is back on the last 1, in state c.') });

  ex({ id: 'tur-x-cfg-mark', chapter: CH1, title: 'Marking and coming back', kind: 'string', level: 2,
    text: ['This machine pairs a\'s with later b\'s. Run it on aab.', machineBlock(M_MARK), 'Write the configuration after four steps, as u q v.'],
    accept: config('r XaY'), solution: 'r X a Y', wrong: ['X r aY', 'Xa q b', 'X p aY', 'Xr aY'],
    whyNot: 'Steps 1 to 3 are p → q → q → r. Where does r\'s move to the left land?',
    hints: H('Step 1: p reads a, writes X, moves right: X q ab.', 'Step 2: q passes a: Xa q b. Step 3: q reads b, writes Y and moves left: X r aY.', 'Step 4: r reads a and moves left onto the X, still in r: r XaY.') });

  ex({ id: 'tur-x-cfg-table', chapter: CH1, title: 'A run, step by step', kind: 'table', table: 'custom', level: 2,
    text: ['This machine reads a\'s and b\'s and rewrites some of them. Run it on aab and fill in the state, the whole tape (without blanks at the ends) and the head position after each step. Cells are numbered from 0, where the input starts.', machineBlock(M_PAR)],
    rows: ['after step 1', 'after step 2', 'after step 3', 'after step 4'], cols: ['state', 'tape', 'head at cell'],
    cells: { 'after step 1|state': 'q1', 'after step 1|tape': 'aab', 'after step 1|head at cell': '1', 'after step 2|state': 'q0', 'after step 2|tape': 'abb', 'after step 2|head at cell': '2', 'after step 3|state': 'q0', 'after step 3|tape': 'abb', 'after step 3|head at cell': '3', 'after step 4|state': 'q2', 'after step 4|tape': 'abb', 'after step 4|head at cell': '2' },
    solution: { 'after step 1|state': 'q1', 'after step 1|tape': 'aab', 'after step 1|head at cell': '1', 'after step 2|state': 'q0', 'after step 2|tape': 'abb', 'after step 2|head at cell': '2', 'after step 3|state': 'q0', 'after step 3|tape': 'abb', 'after step 3|head at cell': '3', 'after step 4|state': 'q2', 'after step 4|tape': 'abb', 'after step 4|head at cell': '2' },
    wrong: [{ 'after step 1|state': 'q1', 'after step 1|tape': 'aab', 'after step 1|head at cell': '1', 'after step 2|state': 'q0', 'after step 2|tape': 'aab', 'after step 2|head at cell': '2', 'after step 3|state': 'q0', 'after step 3|tape': 'aab', 'after step 3|head at cell': '3', 'after step 4|state': 'q2', 'after step 4|tape': 'aab', 'after step 4|head at cell': '2' },
      { 'after step 1|state': 'q1', 'after step 1|tape': 'aab', 'after step 1|head at cell': '1', 'after step 2|state': 'q0', 'after step 2|tape': 'abb', 'after step 2|head at cell': '2', 'after step 3|state': 'q1', 'after step 3|tape': 'aba', 'after step 3|head at cell': '3', 'after step 4|state': 'q2', 'after step 4|tape': 'aba', 'after step 4|head at cell': '2' }],
    hints: H('Step 1: q0 reads the a in cell 0, keeps it, moves right into q1.', 'Step 2: q1 reads the a in cell 1 and writes b over it. Step 3: q0 passes the b in cell 2.', 'q1, aab, 1; q0, abb, 2; q0, abb, 3; q2, abb, 2 (the last rule moves left as it halts).') });

  ex({ id: 'tur-x-steps-inc', chapter: CH1, title: 'How long does the carry take?', kind: 'number', level: 2,
    text: ['Run the binary increment machine on 0111.', machineBlock(M_INC), 'How many steps does it take to halt?'],
    answer: 9, solution: '9', wrong: ['8', '5', '12'],
    hints: H('Four steps right reach the blank, and one step goes back.', 'Then each of the three 1s becomes a 0 with one step left each.', '4 + 1 + 3 + 1 = 9: the last step turns the 0 into 1 and halts.') });

  // ---- deciders, recognisers, transducers ---------------------------------------------------------------------------
  ex({ id: 'tur-x-ch-decider', chapter: CH1, title: 'Decider or recogniser?', kind: 'choice',
    text: 'A Turing machine R accepts every string in L. On strings outside L it sometimes rejects and sometimes runs for ever. What can you say?',
    options: ['R decides L', 'R recognises L, but does not decide it', 'R recognises the complement of L', 'R neither recognises nor decides L'],
    answer: 1, why: 'Recognising only asks that the accepted strings are exactly L; deciding also asks for a halt on every input.',
    whyNot: { 0: 'A decider must halt on every input, and R does not.', 2: 'The strings R accepts are those of L, not of its complement.', 3: 'The language of a machine is the set of strings it accepts, and that is L.' },
    solution: 1, wrong: [0, 3],
    hints: H('The language of a machine is the set of strings it accepts.', 'Which of the two definitions needs a halt on every input?', 'R recognises L. It does not decide it, since it loops on some strings.') });

  ex({ id: 'tur-x-ch-loop-reject', chapter: CH1, title: 'Can you tell a loop from a slow machine?', kind: 'choice', level: 2,
    text: 'You run a machine on w and watch it. Which of these lets you conclude, for sure, that it will never halt on w? Choose all that do.',
    options: ['It has run a million steps without halting', 'It comes back to exactly the same configuration it was in earlier', 'Its head has moved right for 1000 steps in a row and only ever reads blanks, in the same state each time', 'Its tape has grown longer than the input'],
    answer: [1, 2], why: 'A repeated configuration repeats for ever; and a machine in one state reading only blanks while moving right meets nothing new.',
    solution: [1, 2], wrong: [[0, 1, 2], [1], [3]],
    hints: H('A machine is deterministic: the same configuration always leads to the same future.', 'A long run proves nothing on its own: the machine may halt at step one million and one.', 'A repeated configuration, and a head running right over blanks in a fixed state. The other two prove nothing.') });

  ex({ id: 'tur-x-ch-transducer', chapter: CH1, title: 'What does this machine compute?', kind: 'choice',
    text: ['What does this machine leave on its tape, for input w over {0, 1}?', machineBlock('start: s\naccept: h\ns, 0 -> s, 1, R\ns, 1 -> s, 0, R\ns, _ -> b, _, L\nb, 0 -> b, 0, L\nb, 1 -> b, 1, L\nb, _ -> h, _, R')],
    options: ['w unchanged, with the head back at the start', 'w with every bit flipped, head back at the start', 'w reversed', 'w with every bit flipped, head at the right end'],
    answer: 1, solution: 1, wrong: [0, 3],
    hints: H('Look at what s writes.', 'b only walks left; it writes back what it reads.', 'Every bit is flipped on the way right; b brings the head back to the first cell and h halts there.') });

  // =========================================================================================================
  // Chapter 2: building machines from parts
  // =========================================================================================================
  const CH2 = 'tur-building';
  ex({ id: 'tur-x-macro-ends-ab', chapter: CH2, title: 'A program that checks the ending', kind: 'string', level: 2,
    text: ['Write a program in the macro language that accepts the strings over {a, b} ending in ab and rejects the rest. Type it on one line, with ; between statements, starting with alphabet: a b.', { code: 'alphabet: a b; seek R _; left; …', lang: 'machine' }, 'The statements are left, right, write s, map a:b, seek L|R s1|s2, if s goto label, if s accept, if s reject, goto label, accept, reject and call name, and a label is written label: before a statement.'],
    accept: macroProg('ab', { member: (w) => w.endsWith('ab') }),
    solution: 'alphabet: a b; seek R _; left; if a reject; if _ reject; left; if a accept; reject',
    wrong: ['alphabet: a b; seek R _; left; if b accept; reject', 'alphabet: a b; seek R _; left; left; if a accept; reject', 'alphabet: a b; left; if a accept; reject'],
    whyNot: 'Try your program on b, on ab and on ε in your head: where is the head when each test runs?',
    hints: H('Go to the end first: seek R _ stops on the blank after the input.', 'Step left: that cell must be b (not a, and not the blank of an empty input). Step left again: that must be a.', 'alphabet: a b; seek R _; left; if a reject; if _ reject; left; if a accept; reject') });

  ex({ id: 'tur-x-macro-plus3', chapter: CH2, title: 'Add three by calling a machine', kind: 'string', level: 2,
    text: ['The library machine tm:bin-inc adds one to a binary number (111 becomes 1000, and ε counts as 0). Write a macro program that adds three to its binary input. One line, with ; between statements.'],
    accept: macroProg('01', { maxLen: 4, output: (w) => { const inc = T.tmLib.entry('bin-inc').oracle; return inc(inc(inc(w))); } }),
    solution: 'alphabet: 0 1; call tm:bin-inc; call tm:bin-inc; call tm:bin-inc; accept',
    wrong: ['alphabet: 0 1; call tm:bin-inc; call tm:bin-inc; accept', 'alphabet: 0 1; call tm:bin-inc; accept', 'alphabet: 0 1; call tm:bin-inc; call tm:bin-inc; call tm:bin-inc; call tm:bin-inc; accept'],
    whyNot: 'Count the calls: each one adds exactly one.',
    hints: H('A call pastes in a fresh copy of the machine; when it halts, the program carries on with the next statement.', 'bin-inc leaves its head back at the start of the number, so it can be called again straight away.', 'alphabet: 0 1; call tm:bin-inc; call tm:bin-inc; call tm:bin-inc; accept') });

  ex({ id: 'tur-x-macro-swap', chapter: CH2, title: 'Swap a and b, then check', kind: 'string', level: 3,
    text: ['Write a macro program that accepts the strings over {a, b} whose last symbol is a after every a has been turned into b and every b into a. (In other words: strings ending in b. But do it by really swapping first, with a loop and a label.) One line, with ; between statements.'],
    accept: macroProg('ab', { member: (w) => w.endsWith('b') }),
    solution: 'alphabet: a b; next: if _ goto check; map a:b b:a; right; goto next; check: left; if a accept; reject',
    wrong: ['alphabet: a b; next: if _ goto check; map a:b b:a; right; goto next; check: left; if b accept; reject', 'alphabet: a b; map a:b b:a; seek R _; left; if a accept; reject', 'alphabet: a b; next: if _ goto check; right; goto next; check: left; if a accept; reject'],
    whyNot: 'After the loop, the head is on the blank past the input. What should the last symbol be now?',
    hints: H('A loop is a label, a test that leaves the loop, the work, a move, and a goto back.', 'map a:b b:a swaps the symbol under the head. Leave the loop on the blank; step left to look at the last symbol.', 'alphabet: a b; next: if _ goto check; map a:b b:a; right; goto next; check: left; if a accept; reject') });

  ex({ id: 'tur-x-combine-count', chapter: CH2, title: 'Gluing machines together', kind: 'number', level: 2,
    text: 'Machine M₁ has 4 states, one of which is accepting and one rejecting. Machine M₂ has 5 states, one accepting and one rejecting. You build "M₁ then M₂": rename their states apart, and send every rule of M₁ that enters M₁\'s accepting state into M₂\'s start state instead. M₁\'s rejecting state stays as a rejecting state, and M₁\'s accepting state is now never entered, so you drop it. How many states does the combined machine have?',
    answer: 8, solution: '8', wrong: ['9', '7', '20'],
    hints: H('All states of both machines are kept, apart from one.', 'M₁\'s accepting state is no longer reached: its incoming rules go to M₂\'s start.', '4 − 1 + 5 = 8.') });

  ex({ id: 'tur-x-ch-macro-cost', chapter: CH2, title: 'What a call costs', kind: 'choice', level: 2,
    text: 'In the macro language, a program calls the same subroutine at three different places. What happens when the program is compiled to a plain machine?',
    options: ['The subroutine\'s states appear once, and a stack remembers where to return', 'The subroutine\'s states are copied three times, each copy wired to return to its own call site', 'The subroutine runs on a second tape', 'Calling a subroutine more than once is not allowed'],
    answer: 1, why: 'A Turing machine has no stack of return addresses, so the only way to "return" is to have a separate copy for each place to return to.',
    solution: 1, wrong: [0, 3],
    hints: H('Where would a plain Turing machine keep a return address?', 'Only in its state. So each call needs its own states.', 'Three copies, one per call site. That is also why recursion is not allowed: the copies would never end.') });

  // =========================================================================================================
  // Chapter 3: variants of the machine
  // =========================================================================================================
  const CH3 = 'tur-variants';
  ex({ id: 'tur-x-ch-ktape-power', chapter: CH3, title: 'Are more tapes more powerful?', kind: 'choice',
    text: 'Which statement about k-tape Turing machines is true?',
    options: ['They decide more languages than one-tape machines', 'They decide the same languages, and a one-tape machine can simulate t steps of a k-tape machine in about t² steps', 'They decide the same languages, and the simulation costs only a constant factor', 'They decide the same languages, but the simulation can take exponential time'],
    answer: 1, why: 'Each simulated step sweeps over the used part of the tape, which is at most about t cells long.',
    solution: 1, wrong: [0, 2, 3],
    hints: H('Power and speed are two different questions.', 'One simulated step means sweeping over all the cells used so far. How many can there be after t steps?', 'Same languages; the slowdown is quadratic, about t² steps for t.') });

  ex({ id: 'tur-x-tracks', chapter: CH3, title: 'Tracks for three tapes', kind: 'number',
    text: 'One tape simulates a 3-tape machine by giving each cell several tracks: one track holding the contents of each tape, and one track holding a mark under the cell where that tape\'s head is. How many tracks does each cell have?',
    answer: 6, solution: '6', wrong: ['3', '4', '9'],
    hints: H('Each simulated tape needs its own contents and its own head position.', 'That is two tracks per tape.', '2 × 3 = 6.') });

  ex({ id: 'tur-x-ktape-alpha', chapter: CH3, title: 'How big is the new alphabet?', kind: 'number', level: 2,
    text: 'A 2-tape machine has tape alphabet Γ with 4 symbols. One tape simulates it with 4 tracks per cell (two tape tracks with a symbol of Γ, and two mark tracks that hold a mark or nothing). Each cell of the single tape holds one combined symbol, a choice for every track at once. Not counting the plain input symbols the tape starts with, how many combined symbols are there?',
    answer: 64, solution: '64', wrong: ['16', '32', '8'],
    hints: H('Count the choices per track and multiply.', 'Each tape track: 4 choices. Each mark track: 2 choices.', '4 × 2 × 4 × 2 = 64.') });

  ex({ id: 'tur-x-fold', chapter: CH3, title: 'Folding a two-way tape', kind: 'string', level: 2,
    text: 'A one-way tape (a left end, cell 0 holding a marker) simulates a two-way tape by folding it: cell p ≥ 0 of the two-way tape goes to the upper track of folded cell p + 1, and cell p < 0 goes to the lower track of folded cell −p. Where do cells 4 and −3 go? Answer like 5 upper, 3 lower.',
    accept: (t) => { const s = String(t).toLowerCase().replace(/[^a-z0-9]+/g, ' ').trim(); return s === '5 upper 3 lower'; },
    solution: '5 upper, 3 lower', wrong: ['4 upper, 3 lower', '5 upper, 4 lower', '5 lower, 3 upper'],
    whyNot: 'Apply the two rules exactly: p + 1 on the upper track for p ≥ 0, and −p on the lower track for p < 0.',
    hints: H('Cell 0 of the two-way tape goes to folded cell 1, upper track: the marker is in folded cell 0.', 'Cell 4 is not negative, so it goes up, to 4 + 1.', '5 upper, 3 lower.') });

  ex({ id: 'tur-x-pairing', chapter: CH3, title: 'Numbering the cells of a grid', kind: 'number', level: 2,
    text: 'A 2-D tape is laid out on a one-dimensional tape by numbering its cells (x, y) with x, y ≥ 0 along the diagonals: π(x, y) = (x + y)(x + y + 1)/2 + y. So (0, 0) is cell 0, (1, 0) is cell 1, (0, 1) is cell 2. Which cell does (2, 1) go to?',
    answer: 7, solution: '7', wrong: ['6', '8', '5'],
    hints: H('x + y = 3, so (2, 1) is on the fourth diagonal.', '(3 · 4)/2 = 6 cells come before that diagonal.', '6 + y = 6 + 1 = 7.') });

  ex({ id: 'tur-x-addresses', chapter: CH3, title: 'Counting addresses', kind: 'number', level: 2,
    text: 'A deterministic machine simulates a nondeterministic one whose configurations have at most 2 choices each, by trying addresses: strings over {1, 2} in shortlex order, each telling which choice to take at each step. It tries ε first, then 1, 2, 11, 12, … . How many addresses does it try before it starts on those of length 4? (Count ε.)',
    answer: 15, solution: '15', wrong: ['14', '8', '16'],
    hints: H('Count the addresses of each length: 1 of length 0, 2 of length 1, …', 'Lengths 0 to 3: 1 + 2 + 4 + 8.', '15.') });

  ex({ id: 'tur-x-ch-ntm', chapter: CH3, title: 'Depth first or breadth first?', kind: 'choice', level: 2,
    text: 'A deterministic machine simulates a nondeterministic machine N on w by exploring N\'s computation tree. Why should it explore the tree breadth first (or by addresses in shortlex order) rather than depth first?',
    options: ['Depth first uses too much tape', 'Depth first may follow one branch for ever, never reaching an accepting branch elsewhere', 'Breadth first finds rejecting branches faster', 'Depth first only works for deciders'],
    answer: 1, solution: 1, wrong: [0, 2],
    why: 'A branch can be infinite; breadth first reaches every node at depth d after finitely many others.',
    hints: H('Can a branch of the tree be infinite?', 'If the first branch you follow never ends, what happens to the accepting branch beside it?', 'Depth first can be lost on an infinite branch; breadth first reaches every finite depth.') });

  ex({ id: 'tur-x-ch-enum', chapter: CH3, title: 'Enumerators', kind: 'choice', level: 2,
    text: 'Which of these are true? Choose all that are.',
    options: ['A language is recognisable exactly when some enumerator prints it (in any order, repeats allowed)', 'A language is decidable exactly when some enumerator prints it in shortlex order', 'Every enumerator prints its strings in shortlex order', 'An enumerator for a finite language must eventually halt'],
    answer: [0, 1], why: 'With shortlex order you can stop waiting once the enumerator has printed past w, so the language is decidable (for an infinite language; a finite one is decidable anyway).',
    solution: [0, 1], wrong: [[0], [0, 1, 3], [2]],
    hints: H('From an enumerator, a recogniser waits until w is printed.', 'If the strings come in shortlex order, when can you give up waiting for w?', 'The first two. An enumerator may print in any order, and may keep running for ever without printing anything new.') });

  ex({ id: 'tur-x-dovetail', chapter: CH3, title: 'The dovetailing schedule', kind: 'string', level: 2,
    text: 'A recogniser R is dovetailed over the strings s₁, s₂, s₃, … : in round n it runs R for n steps on each of s₁, …, sₙ, from the start each time. In which round does R get its first chance to accept s₂, if R accepts s₂ after exactly 4 steps? And how many steps does R run on s₁ in that round? Answer like round 3, 3 steps.',
    accept: numbers(4, 4), solution: 'round 4, 4 steps', wrong: ['round 2, 2 steps', 'round 5, 5 steps', 'round 4, 3 steps'],
    hints: H('s₂ is first run in round 2, but only for 2 steps.', 'It needs a round of at least 4 steps: round 4. In round n every string gets n steps.', 'Round 4, and s₁ gets 4 steps in it too.') });

  // =========================================================================================================
  // Chapter 4: other models
  // =========================================================================================================
  const CH4 = 'tur-models';
  ex({ id: 'tur-x-ram-plus2', chapter: CH4, title: 'r0 := r1 + 2', kind: 'string',
    text: ['Write a register-machine program that leaves r1 + 2 in r0 (all other registers start at 0). Use only inc, dec, jz r label, jmp label and halt; put ; between statements and label a statement with name: in front.', { code: 'loop: jz r1 done; dec r1; …', lang: 'machine' }],
    accept: ramProg(1, (x) => x + 2, true),
    solution: 'inc r0; inc r0; loop: jz r1 done; dec r1; inc r0; jmp loop; done: halt',
    wrong: ['loop: jz r1 done; dec r1; inc r0; jmp loop; done: halt', 'inc r0; inc r0; done: halt', 'set r0 2; loop: jz r1 done; dec r1; inc r0; jmp loop; done: halt'],
    whyNot: 'Check r1 = 0 and r1 = 3. Only the five core instructions are allowed.',
    hints: H('A register can only be read by counting it down to zero.', 'Move r1 into r0 one at a time with a loop, and add two more with inc.', 'inc r0; inc r0; loop: jz r1 done; dec r1; inc r0; jmp loop; done: halt') });

  ex({ id: 'tur-x-ram-triple', chapter: CH4, title: 'r0 := 3·r1', kind: 'string', level: 2,
    text: 'Write a register-machine program that leaves 3·r1 in r0, using only inc, dec, jz, jmp and halt, with ; between statements.',
    accept: ramProg(1, (x) => 3 * x, true),
    solution: 'loop: jz r1 done; dec r1; inc r0; inc r0; inc r0; jmp loop; done: halt',
    wrong: ['loop: jz r1 done; dec r1; inc r0; inc r0; jmp loop; done: halt', 'loop: jz r1 done; inc r0; inc r0; inc r0; jmp loop; done: halt', 'inc r0; loop: jz r1 done; dec r1; inc r0; inc r0; inc r0; jmp loop; done: halt'],
    whyNot: 'Does every round of your loop take exactly one away from r1 and add exactly three to r0?',
    hints: H('One round of the loop for each unit of r1.', 'In each round, take one from r1 and add three to r0.', 'loop: jz r1 done; dec r1; inc r0; inc r0; inc r0; jmp loop; done: halt') });

  ex({ id: 'tur-x-ram-mod3', chapter: CH4, title: 'r0 := r1 mod 3', kind: 'string', level: 3,
    text: 'Write a register-machine program that leaves the remainder of r1 divided by 3 in r0, using only inc, dec, jz, jmp and halt.',
    accept: ramProg(1, (x) => x % 3, true),
    solution: 'z: jz r1 done; dec r1; inc r0; jz r1 done; dec r1; inc r0; jz r1 done; dec r1; dec r0; dec r0; jmp z; done: halt',
    wrong: ['z: jz r1 done; dec r1; inc r0; jz r1 done; dec r1; inc r0; jz r1 done; dec r1; jmp z; done: halt', 'z: jz r1 done; dec r1; inc r0; jz r1 done; dec r1; inc r0; jmp z; done: halt', 'z: jz r1 done; dec r1; inc r0; jmp z; done: halt'],
    whyNot: 'Try r1 = 3 and r1 = 4: the answer must start again from 0 after every three.',
    hints: H('Count r1 down, keeping a running remainder 0, 1, 2 in r0.', 'Unroll three decrements per round; check for zero before each. After the third, r0 has gone 0 → 1 → 2, so bring it back to 0.', 'z: jz r1 done; dec r1; inc r0; jz r1 done; dec r1; inc r0; jz r1 done; dec r1; dec r0; dec r0; jmp z; done: halt') });

  ex({ id: 'tur-x-ram-add', chapter: CH4, title: 'r0 := r1 + r2, line by line', kind: 'program', level: 2,
    text: 'Finish this register-machine program so that it leaves r1 + r2 in r0. Write one instruction per line; a label goes in front, like loop:. Only inc, dec, jz r label, jmp label and halt are allowed. Press Check to run it on many inputs.',
    start: 'one: jz r1 two\n  dec r1\n  \n  jmp one\ntwo: jz r2 done\n  dec r2\n  inc r0\n  jmp two\ndone: halt',
    test: (text) => {
      const p = T.ram.parse(text);
      if (p.errors.length) return 'Line ' + p.errors[0].line + ': ' + p.errors[0].msg + '.';
      if (!p.core) return 'Use only inc, dec, jz, jmp and halt.';
      for (const a of [0, 1, 2, 5]) for (const b of [0, 1, 3]) {
        const r = T.ram.run(p, [0, a, b], { maxSteps: 5000, trace: false });
        const at = 'r1 = ' + a + ', r2 = ' + b;
        if (r.verdict !== 'halt') return { ok: false, why: 'On ' + at + ' your program does not halt.', counterexample: at };
        if (r.output !== a + b) return { ok: false, why: 'On ' + at + ' your program leaves r0 = ' + r.output + '; it should leave ' + (a + b) + '.', counterexample: at };
      }
      return { ok: true, why: 'Right: r0 = r1 + r2 on every input tried.' };
    },
    solution: 'one: jz r1 two\n  dec r1\n  inc r0\n  jmp one\ntwo: jz r2 done\n  dec r2\n  inc r0\n  jmp two\ndone: halt',
    wrong: ['one: jz r1 two\n  dec r1\n  \n  jmp one\ntwo: jz r2 done\n  dec r2\n  inc r0\n  jmp two\ndone: halt', 'one: jz r1 done\n  dec r1\n  inc r0\n  jmp one\ndone: halt', 'one: jz r1 two\n  dec r1\n  inc r0\n  jmp one\ntwo: jz r2 done\n  inc r0\n  jmp two\ndone: halt'],
    hints: H('The second loop already moves r2 into r0 one unit at a time.', 'The first loop counts r1 down but forgets to add anything to r0.', 'Put inc r0 on the empty line of the first loop.') });

  ex({ id: 'tur-x-ram-trace', chapter: CH4, title: 'Run a register machine', kind: 'number',
    text: ['Run this program with r1 = 4 and every other register 0. What is in r0 when it halts?', { code: 'top: jz r1 end\n  dec r1\n  jz r1 end\n  dec r1\n  inc r0\n  jmp top\nend: halt', lang: 'machine' }],
    answer: 2, solution: '2', wrong: ['4', '1', '8'],
    hints: H('Each full round takes 2 from r1 and adds 1 to r0.', 'r1 goes 4 → 2 → 0.', '2: the program halves r1, rounding down.') });

  ex({ id: 'tur-x-godel-counters', chapter: CH4, title: 'Three counters in one number', kind: 'number', level: 2,
    text: 'A machine with one counter simulates three counters c₁, c₂, c₃ by storing the single number 2^c₁ · 3^c₂ · 5^c₃. Which number stands for c₁ = 2, c₂ = 0, c₃ = 1?',
    answer: 20, solution: '20', wrong: ['10', '12', '30'],
    hints: H('3⁰ = 1.', '2² = 4 and 5¹ = 5.', '4 · 1 · 5 = 20.') });

  ex({ id: 'tur-x-godel-inc', chapter: CH4, title: 'Adding one to a hidden counter', kind: 'choice', level: 2,
    text: 'Counters c₁, c₂, c₃ are packed into one number N = 2^c₁ · 3^c₂ · 5^c₃. Which operations on N correspond to "add one to c₂" and to "is c₃ zero?"',
    options: ['Add 3 to N; test whether N is odd', 'Multiply N by 3; test whether N is not divisible by 5', 'Multiply N by 2; test whether N is divisible by 5', 'Add 1 to N; test whether N equals 1'],
    answer: 1, solution: 1, wrong: [0, 2],
    hints: H('Adding one to an exponent multiplies by the base.', 'c₃ is zero exactly when 5 is not a factor of N.', 'Multiply by 3, and test divisibility by 5. Both are done with a second counter as scratch.') });

  ex({ id: 'tur-x-counter-run', chapter: CH4, title: 'Run a two-counter machine', kind: 'number', level: 2,
    text: ['Each line is label: inc C next, or label: dec C next ifzero (if C > 0 take one away and go to next, else go to ifzero), or label: halt. Start at the first line with A = 5 and B = 0. What is A when the machine halts?', { code: 'd: dec A d1 m\nd1: dec A d2 m\nd2: inc B d\nm: dec B m1 h\nm1: inc A m\nh: halt', lang: 'machine' }],
    answer: 2, solution: '2', wrong: ['5', '3', '10'],
    hints: H('The first three lines take two from A and add one to B, again and again.', 'With A = 5, two full rounds leave A = 1 and B = 2. Then d takes the last 1, and d1 finds A empty and moves on to m.', 'A: 5 → 3 → 1, then d takes the last 1 and d1 finds A = 0 and goes to m with B = 2; m moves B back into A: A = 2. It halves A, rounding down.') });

  ex({ id: 'tur-x-lba-bound', chapter: CH4, title: 'How many configurations has an LBA?', kind: 'number', level: 2,
    text: 'A linear-bounded automaton has 5 states and a tape alphabet of 4 symbols (endmarkers not counted). On an input of length 3 it works on the 3 input cells only, and its head can also sit on either endmarker. How many different configurations (state, head position, contents of the 3 cells) can it be in?',
    answer: 1600, solution: '1600', wrong: ['320', '960', '64'],
    hints: H('Multiply the choices: states × head positions × tape contents.', 'Head positions: 3 cells + 2 endmarkers = 5. Tape contents: 4³ = 64.', '5 × 5 × 64 = 1600. Run longer than that, and some configuration has repeated: it will never halt.') });

  ex({ id: 'tur-x-ch-lba', chapter: CH4, title: 'Why acceptance by an LBA is decidable', kind: 'choice', level: 2,
    text: 'Why can a decider tell whether a linear-bounded automaton accepts w, while no decider can do the same for Turing machines in general?',
    options: ['LBAs are deterministic', 'An LBA has finitely many configurations on w, so a run either halts or repeats a configuration within a known number of steps', 'LBAs only accept context-free languages', 'An LBA cannot write on its tape'],
    answer: 1, solution: 1, wrong: [0, 2, 3],
    hints: H('What limits the space an LBA can use on w?', 'Bounded space, a fixed number of states and symbols: how many configurations are there?', 'Finitely many configurations, so run past the bound and any run still going must be in a loop.') });

  ex({ id: 'tur-x-ugrammar-lengths', chapter: CH4, title: 'What a doubling grammar makes', kind: 'choice', level: 2,
    text: ['This unrestricted grammar starts at S; capitals are variables, and a rule may rewrite a whole group of symbols. Which strings can it derive? Choose all that it can.', { code: 'S → L a R\nL → L D\nD a → a a D\nD R → R\nL → ε\nR → ε', lang: 'grammar' }],
    options: ['a', 'aa', 'aaa', 'aaaa', 'aaaaaa'],
    answer: [0, 1, 3], why: 'Each D walks through the a\'s from left to right, doubling every one it passes, so the lengths are the powers of two.',
    solution: [0, 1, 3], wrong: [[0, 1, 2, 3, 4], [0, 1, 3, 4], [1, 3]],
    hints: H('L a R with no D gives a.', 'One D doubles every a it passes before it disappears into R.', 'a, aa and aaaa: the lengths 1, 2, 4, 8, … .') });

  ex({ id: 'tur-x-ugrammar-equal', chapter: CH4, title: 'Equal counts in any order', kind: 'string', level: 2,
    text: ['This grammar derives strings over {a, b, c}. Give a string of length 6 that it derives and that starts with cc.', { code: 'S → A B C S | ε\nA B → B A     B A → A B\nA C → C A     C A → A C\nB C → C B     C B → B C\nA → a   B → b   C → c', lang: 'grammar' }],
    accept: (t) => { const w = String(t).replace(/\s/g, ''); return /^[abc]{6}$/.test(w) && w.startsWith('cc') && count(w, 'a') === 2 && count(w, 'b') === 2 && count(w, 'c') === 2; },
    solution: 'ccabab', wrong: ['cccaab', 'ccabb', 'ccaabb c'],
    whyNot: 'Every use of S → A B C S adds one a, one b and one c, and the swap rules can put them in any order.',
    hints: H('Use S → A B C S twice, then S → ε: two each of A, B, C.', 'The swap rules let any two neighbouring variables trade places.', 'For instance ccabab, ccaabb or ccbbaa: two of each letter, starting with cc.') });

  ex({ id: 'tur-x-ch-chomsky', chapter: CH4, title: 'The smallest class', kind: 'choice', level: 2,
    text: 'Which language is context-sensitive but not context-free?',
    options: ['{ (ab)ⁿ : n ≥ 0 }', '{ aⁿ bⁿ : n ≥ 0 }', '{ aⁿ bⁿ aⁿ : n ≥ 0 }', 'the strings ⟨M, w⟩ where M halts on w'],
    answer: 2, solution: 2, wrong: [0, 1, 3],
    hints: H('One of these is regular, one is context-free but not regular, and one is not even decidable.', 'Three blocks of equal length need more than a stack.', '{ aⁿ bⁿ aⁿ }: a linear-bounded automaton can check it by crossing off, a pushdown automaton cannot.') });

  ex({ id: 'tur-x-ch-hierarchy', chapter: CH4, title: 'Grammars and machines', kind: 'choice',
    text: 'Which pairing of grammar type with machine is right?',
    options: ['Context-sensitive grammars ↔ pushdown automata', 'Unrestricted grammars ↔ Turing machines (the recognisable languages)', 'Context-free grammars ↔ linear-bounded automata', 'Regular grammars ↔ linear-bounded automata'],
    answer: 1, solution: 1, wrong: [0, 2],
    hints: H('Type 0 is the most general.', 'Context-sensitive goes with linear-bounded automata; context-free with pushdown automata.', 'Unrestricted grammars generate exactly the Turing-recognisable languages.') });

  // =========================================================================================================
  // Chapter 5: recursive functions and λ
  // =========================================================================================================
  const CH5 = 'tur-functions';
  ex({ id: 'tur-x-pr-eval', chapter: CH5, title: 'Evaluate a primitive recursion', kind: 'number',
    text: ['The function h of two arguments is defined by primitive recursion on its last argument:', { math: 'h = R(P(1,1), C(S; C(S; P(3,3))))\nh(x, 0) = P(1,1)(x) = x\nh(x, y + 1) = S(S(h(x, y)))' }, 'What is h(3, 4)?'],
    answer: 11, solution: '11', wrong: ['7', '10', '12'],
    hints: H('h(3, 0) = 3.', 'Each step of y adds 2.', 'h(x, y) = x + 2y, so h(3, 4) = 11.') });

  ex({ id: 'tur-x-pr-eval2', chapter: CH5, title: 'Doubling, again and again', kind: 'number', level: 2,
    text: ['With add(x, y) = x + y, the one-argument function g is', { math: 'g = R(C(S; Z), C(add; P(2,2), P(2,2)))\ng(0) = 1\ng(y + 1) = add(g(y), g(y))' }, 'What is g(5)?'],
    answer: 32, solution: '32', wrong: ['10', '16', '25'],
    hints: H('g(0) = S(Z()) = 1.', 'Each step doubles the previous value.', 'g(y) = 2^y, so g(5) = 32.') });

  ex({ id: 'tur-x-pr-write-plus2', chapter: CH5, title: 'Write x + 2', kind: 'string',
    text: 'Write a primitive recursive expression for f(x) = x + 2, using Z, S, P(i,n), C(f; g₁, …) and R(f, g). For example C(S; Z) is the constant 1.',
    accept: primrec(1, (x) => x + 2), solution: 'C(S; S)', wrong: ['C(S; Z)', 'S', 'C(S; C(S; Z))'],
    whyNot: 'Test it at 0 and at 3.',
    hints: H('S adds one. Apply it twice.', 'Composition C(f; g) means f(g(x)).', 'C(S; S), or C(S; C(S; P(1,1))).') });

  ex({ id: 'tur-x-pr-write-xyx', chapter: CH5, title: 'Write x·y + x', kind: 'string', level: 2,
    text: 'Write a primitive recursive expression for f(x, y) = x·y + x. You may use the library functions add and mult (each of two arguments) as well as Z, S, P, C and R.',
    accept: primrec(2, (x, y) => x * y + x), solution: 'C(add; mult, P(1,2))', wrong: ['C(add; mult, P(2,2))', 'mult', 'C(mult; P(1,2), C(S; P(1,2)))'],
    whyNot: 'Check f(2, 3) = 8 and f(3, 0) = 3.',
    hints: H('f is add applied to two things computed from (x, y).', 'The two things are mult(x, y) and x.', 'C(add; mult, P(1,2)). Another answer: C(mult; P(1,2), C(S; P(2,2))), which is x·(y + 1).') });

  ex({ id: 'tur-x-pr-write-pow3', chapter: CH5, title: 'Write 3 to the power n', kind: 'string', level: 3,
    text: 'Write a primitive recursive expression for f(n) = 3ⁿ, using R for the recursion. You may use mult and add.',
    accept: primrec(1, (n) => 3 ** n), solution: 'R(C(S; Z), C(mult; C(S; C(S; C(S; Z))), P(2,2)))',
    wrong: ['R(C(S; Z), C(mult; C(S; C(S; Z)), P(2,2)))', 'R(Z, C(mult; C(S; C(S; C(S; Z))), P(2,2)))', 'R(C(S; Z), C(add; P(2,2), C(S; C(S; C(S; Z)))))'],
    whyNot: 'Check f(0) = 1 and f(2) = 9.',
    hints: H('R(f, g) with no other arguments: f is a constant (the value at 0), and g(y, previous) gives the next value.', 'f(0) = 1 is C(S; Z). The step multiplies the previous value, P(2,2), by the constant 3.', 'R(C(S; Z), C(mult; C(S; C(S; C(S; Z))), P(2,2))).') });

  ex({ id: 'tur-x-mu-eval', chapter: CH5, title: 'An unbounded search', kind: 'number', level: 2,
    text: ['With monus(x, y) = x − y (but not below 0), what is f(5) for', { math: 'f = M(C(monus; C(S; C(S; P(1,2))), P(2,2)))\nf(x) = the least z with monus(x + 2, z) = 0' }],
    answer: 7, solution: '7', wrong: ['5', '6', '0'],
    hints: H('monus(x + 2, z) is 0 exactly when z ≥ x + 2.', 'The search tries z = 0, 1, 2, … and stops at the first z that works.', 'z = 7.') });

  ex({ id: 'tur-x-ch-mu', chapter: CH5, title: 'When the search never stops', kind: 'choice', level: 2,
    text: 'Let f(x, z) = 1 for every x and z. What is μf, that is, g(x) = the least z with f(x, z) = 0?',
    options: ['g(x) = 0 for every x', 'g(x) = 1 for every x', 'g is undefined at every x: the search never ends', 'g is not a function at all, so μ cannot be applied'],
    answer: 2, solution: 2, wrong: [0, 1, 3],
    why: 'μ may produce partial functions; that is exactly the power primitive recursion lacks.',
    hints: H('Is there any z with f(x, z) = 0?', 'The search tries z = 0, 1, 2, … for ever.', 'g is undefined everywhere: a perfectly good partial function, the empty one.') });

  ex({ id: 'tur-x-ack-value', chapter: CH5, title: 'A small Ackermann value', kind: 'number', level: 2,
    text: ['With A(0, n) = n + 1, A(m + 1, 0) = A(m, 1) and A(m + 1, n + 1) = A(m, A(m + 1, n)), what is A(2, 2)?'],
    answer: 7, solution: '7', wrong: ['6', '5', '9'],
    hints: H('A(1, n) = n + 2.', 'A(2, n) = A(1, A(2, n − 1)) adds 2 each time, starting from A(2, 0) = A(1, 1) = 3.', 'A(2, n) = 2n + 3, so A(2, 2) = 7.') });

  ex({ id: 'tur-x-ack-table', chapter: CH5, title: 'The first rows of Ackermann', kind: 'table', table: 'custom', level: 2,
    text: 'Fill in A(m, n) for m = 0, 1, 2 and n = 0, 1, 2, 3.',
    rows: ['m = 0', 'm = 1', 'm = 2'], cols: ['n = 0', 'n = 1', 'n = 2', 'n = 3'],
    cells: { 'm = 0|n = 0': '1', 'm = 0|n = 1': '2', 'm = 0|n = 2': '3', 'm = 0|n = 3': '4', 'm = 1|n = 0': '2', 'm = 1|n = 1': '3', 'm = 1|n = 2': '4', 'm = 1|n = 3': '5', 'm = 2|n = 0': '3', 'm = 2|n = 1': '5', 'm = 2|n = 2': '7', 'm = 2|n = 3': '9' },
    solution: { 'm = 0|n = 0': '1', 'm = 0|n = 1': '2', 'm = 0|n = 2': '3', 'm = 0|n = 3': '4', 'm = 1|n = 0': '2', 'm = 1|n = 1': '3', 'm = 1|n = 2': '4', 'm = 1|n = 3': '5', 'm = 2|n = 0': '3', 'm = 2|n = 1': '5', 'm = 2|n = 2': '7', 'm = 2|n = 3': '9' },
    wrong: [{ 'm = 0|n = 0': '1', 'm = 0|n = 1': '2', 'm = 0|n = 2': '3', 'm = 0|n = 3': '4', 'm = 1|n = 0': '1', 'm = 1|n = 1': '3', 'm = 1|n = 2': '4', 'm = 1|n = 3': '5', 'm = 2|n = 0': '3', 'm = 2|n = 1': '5', 'm = 2|n = 2': '7', 'm = 2|n = 3': '9' },
      { 'm = 0|n = 0': '1', 'm = 0|n = 1': '2', 'm = 0|n = 2': '3', 'm = 0|n = 3': '4', 'm = 1|n = 0': '2', 'm = 1|n = 1': '3', 'm = 1|n = 2': '4', 'm = 1|n = 3': '5', 'm = 2|n = 0': '3', 'm = 2|n = 1': '4', 'm = 2|n = 2': '5', 'm = 2|n = 3': '6' }],
    hints: H('Row 0 is n + 1. Every row starts with A(m, 0) = A(m − 1, 1).', 'Along a row, A(m, n) = A(m − 1, A(m, n − 1)): look up the previous entry of this row as a column of the row above.', 'Row 0: 1 2 3 4. Row 1: 2 3 4 5. Row 2: 3 5 7 9.') });

  ex({ id: 'tur-x-ch-ack', chapter: CH5, title: 'Why Ackermann is special', kind: 'choice', level: 2,
    text: 'Which statements about Ackermann\'s function A are true? Choose all that are.',
    options: ['A is total: the recursion always ends', 'A is computable by a Turing machine', 'A is primitive recursive', 'A grows faster than every primitive recursive function, in the sense that A(n, n) eventually beats each of them'],
    answer: [0, 1, 3], solution: [0, 1, 3], wrong: [[0, 1, 2, 3], [2], [0, 1]],
    hints: H('The pair (m, n) gets smaller in the dictionary order with every call.', 'Computable, yes: the definition is a program.', 'Total, computable, and too fast-growing to be primitive recursive.') });

  ex({ id: 'tur-x-lam-id', chapter: CH5, title: 'A first β-reduction', kind: 'string',
    text: 'Reduce (λx. x x) (λy. y) to normal form. Type λ as λ or as a backslash \\.',
    accept: lambda('(λx. x x) (λy. y)'), solution: 'λy. y', wrong: ['(λy. y) (λy. y)', 'x x', 'λx. x x'],
    whyNot: 'Keep reducing while there is a (λv. …) applied to something.',
    hints: H('Substitute λy. y for both x\'s.', 'That gives (λy. y) (λy. y), which is still a redex.', 'λy. y, the identity (any bound name will do, like λz. z).') });

  ex({ id: 'tur-x-lam-twice', chapter: CH5, title: 'Twice the identity', kind: 'string', level: 2,
    text: 'Reduce (λf x. f (f x)) (λy. y) to normal form.',
    accept: lambda('(λf x. f (f x)) (λy. y)'), solution: 'λx. x', wrong: ['λx. (λy. y) ((λy. y) x)', 'λf x. f (f x)', 'λy. y y'],
    whyNot: 'Reduce inside the λx. too: normal form means no redex anywhere.',
    hints: H('First f := λy. y: λx. (λy. y) ((λy. y) x).', 'Now reduce the inner redexes; the identity applied to anything gives it back.', 'λx. x.') });

  ex({ id: 'tur-x-lam-capture', chapter: CH5, title: 'Do not capture', kind: 'string', level: 3,
    text: 'Reduce (λx. λy. x y) y to normal form. Careful: the argument y is free.',
    accept: lambda('(λx. λy. x y) y'), solution: 'λz. y z', wrong: ['λy. y y', 'y y', 'λy. x y'],
    whyNot: 'Substituting y inside λy. … would capture it. Rename the bound y first.',
    hints: H('The y passed in is a free variable, not the bound y of λy.', 'Rename the bound variable: λx. λz. x z, then substitute.', 'λz. y z: a function that applies the free y to its argument.') });

  ex({ id: 'tur-x-lam-succ', chapter: CH5, title: 'Church arithmetic', kind: 'number', level: 2,
    text: 'With Church numerals (n = λf x. f applied n times to x), PLUS = λm n f x. m f (n f x) and MULT = λm n f. m (n f), which numeral is the normal form of MULT 2 (PLUS 1 2)?',
    answer: 6, solution: '6', wrong: ['5', '3', '8'],
    hints: H('PLUS 1 2 reduces to 3.', 'MULT m n f = m (n f): apply "n times f" m times.', '2 · 3 = 6.') });

  ex({ id: 'tur-x-lam-k', chapter: CH5, title: 'Escaping a loop', kind: 'string', level: 2,
    text: 'Ω = (λx. x x) (λx. x x) has no normal form. Reduce (λx y. y) Ω a in normal order (always the leftmost outermost redex first). What is the normal form?',
    accept: lambda('(λx y. y) ((λx. x x) (λx. x x)) a'), solution: 'a', wrong: ['Ω', 'λy. y', '(λx. x x) (λx. x x)'],
    whyNot: 'Normal order reduces the outermost redex first, so Ω is passed in without being reduced.',
    hints: H('The outermost redex is (λx y. y) Ω: it throws Ω away.', 'That leaves (λy. y) a.', 'a. Reducing Ω first would never finish.') });

  ex({ id: 'tur-x-ch-normal-order', chapter: CH5, title: 'Which order finds normal forms?', kind: 'choice', level: 2,
    text: 'Which reduction strategy reaches a term\'s normal form whenever it has one?',
    options: ['Innermost first (reduce arguments before passing them)', 'Normal order: leftmost outermost first', 'Any order: they all reach it', 'Rightmost innermost first'],
    answer: 1, solution: 1, wrong: [0, 2],
    hints: H('Look back at (λx y. y) Ω a.', 'Innermost first tries to reduce Ω, for ever.', 'Normal order. If a term has a normal form, leftmost outermost reduction finds it.') });

  // =========================================================================================================
  // Chapter 6: encodings, the universal machine, the thesis
  // =========================================================================================================
  const CH6 = 'tur-universal';
  const C11 = '010010100100110100010000100010011000010010100100110000100010010001000';
  const conv = 'States are q1 (start), q2 (accept), q3 (reject), q4, …; symbols are 1 (blank), 2, 3, …; moves are L = 1, R = 2, S = 3. The rule δ(qi, j) = (qk, l, m) is written 0^i 1 0^j 1 0^k 1 0^l 1 0^m, and rules are joined by 11.';

  ex({ id: 'tur-x-enc-rule', chapter: CH6, title: 'Encode one rule', kind: 'string',
    text: [conv, 'Write the code of the rule δ(q1, 2) = (q4, 3, R).'],
    accept: bits('0100100001000100'), solution: '0100100001000100', wrong: ['0100100001000100100', '01001000010001', '0010000100010001'],
    whyNot: 'Five runs of 0s, of lengths 1, 2, 4, 3 and 2, with a single 1 between runs.',
    hints: H('The five numbers are i = 1, j = 2, k = 4, l = 3, m = 2 (R).', 'Write each as a run of that many 0s.', '0 1 00 1 0000 1 000 1 00 = 0100100001000100.') });

  ex({ id: 'tur-x-dec-rule', chapter: CH6, title: 'Decode one rule', kind: 'string',
    text: [conv, 'Decode the rule 0001001001010. Write the five numbers i, j, k, l, m.'],
    accept: numbers(3, 2, 2, 1, 1), solution: '3, 2, 2, 1, 1', wrong: ['3, 2, 2, 1, 2', '2, 2, 3, 1, 1', '3 2 2 1'],
    whyNot: 'Split at each 1 and count the 0s in each run.',
    hints: H('Split at the 1s: 000 | 00 | 00 | 0 | 0.', 'Count: 3, 2, 2, 1, 1.', 'δ(q3, 2) = (q2, 1, L): 3, 2, 2, 1, 1. (A rule leaving q3 is not allowed in a machine code, since q3 is the rejecting state; here it is just a rule to read.)') });

  ex({ id: 'tur-x-enc-word', chapter: CH6, title: 'Encode the input', kind: 'string',
    text: 'The input of ⟨M, w⟩ is written with symbol numbers as runs of 0s, separated by single 1s. With the numbering blank = 1, 0 = 2, 1 = 3, write the code of w = 0110.',
    accept: bits('0010001000100'), solution: '0010001000100', wrong: ['0110', '00100010001001', '00100100100'],
    hints: H('0 is symbol 2, written 00; 1 is symbol 3, written 000.', 'Join the four runs with a 1 between neighbours.', '00 1 000 1 000 1 00 = 0010001000100.') });

  ex({ id: 'tur-x-enc-machine', chapter: CH6, title: 'Encode a whole machine', kind: 'string', level: 3,
    text: [conv, 'This machine flips every bit. Number its states s = q1 and h = q2, and its symbols _ = 1, 0 = 2, 1 = 3. List its rules by state and then by symbol number, and write its code.', machineBlock('start: s\naccept: h\ns, 0 -> s, 1, R\ns, 1 -> s, 0, R\ns, _ -> h, _, S')],
    accept: bits('010100101000110100101000100110100010100100'), solution: '010100101000110100101000100110100010100100',
    wrong: ['0100101000100110100010100100110101001010001', '010100101000110100101000100110100010100100111', '010100101000101001010001001010001010010'],
    whyNot: 'Three rules: on symbol 1 (the blank), on 2 and on 3, in that order, joined by 11.',
    hints: H('The rules in order: δ(q1, 1) = (q2, 1, S), δ(q1, 2) = (q1, 3, R), δ(q1, 3) = (q1, 2, R).', 'They are 010100101000, 0100101000100 and 0100010100100.', 'Joined by 11: 010100101000 11 0100101000100 11 0100010100100.') });

  ex({ id: 'tur-x-dec-machine', chapter: CH6, title: 'What does this code do?', kind: 'choice', level: 3,
    text: [conv, 'Symbol 2 is 0 and symbol 3 is 1. Decode this machine and say which strings it accepts.', { code: C11, lang: 'machine' }],
    options: ['Strings containing 11', 'Strings ending in 1', 'Strings with an even number of 1s', 'Strings starting with 1'],
    answer: 0, solution: 0, wrong: [1, 2, 3],
    hints: H('Split at 11 into four rules, then each rule at 1 into five runs.', 'The rules are δ(q1, 2) = (q1, 2, R), δ(q1, 3) = (q4, 3, R), δ(q4, 2) = (q1, 2, R), δ(q4, 3) = (q2, 3, S).', 'q4 means "just read a 1". A second 1 right after goes to q2, which accepts: strings containing 11.') });

  ex({ id: 'tur-x-dec-count', chapter: CH6, title: 'Valid or not?', kind: 'choice', level: 2,
    text: [conv, 'Which of these bit strings are valid machine codes? Choose all that are.'],
    options: ['010100101000', '0101001010001', '01010010100011101', '0101001010001101010010100', 'the empty string ε'],
    answer: [0, 4], why: 'The empty string has no rules at all: a machine that rejects at once, which is still a machine.',
    solution: [0, 4], wrong: [[0], [0, 3, 4], [0, 1, 4]],
    hints: H('Every rule has exactly five non-empty runs of 0s, and 11 only appears between rules; 111 never appears.', 'Option 2 ends in a 1 that starts a sixth field; option 3 contains 111; option 4 has two rules for q1 on symbol 1.', 'Only the first one and the empty string.') });

  ex({ id: 'tur-x-unpair', chapter: CH6, title: 'Split a pair', kind: 'string', level: 2,
    text: 'A pair of bit strings (x, y) is written as x with every bit doubled, then 01, then y: so (10, 11) becomes 11 00 01 11 = 11000111. Which pair is 0011010? Answer like 10, 11.',
    accept: (t) => { const p = String(t).replace(/[()\s]/g, '').split(','); return p.length === 2 && p[0] === '01' && p[1] === '0'; },
    solution: '01, 0', wrong: ['0, 10', '01, 10', '001, 0'],
    hints: H('Read the code two bits at a time: 00, 11, then 01.', '00 and 11 are doubled bits: x = 01. 01 is the separator.', 'x = 01 and y = 0.') });

  ex({ id: 'tur-x-ch-utm', chapter: CH6, title: 'What the universal machine needs', kind: 'choice', level: 2,
    text: 'The universal machine U runs any machine M on any input w, given ⟨M, w⟩. Which statements are true? Choose all that are.',
    options: ['U has a fixed number of states, however many states M has', 'U accepts ⟨M, w⟩ exactly when M accepts w', 'U halts on every input', 'U needs a new rule added for every new machine M'],
    answer: [0, 1], solution: [0, 1], wrong: [[0, 1, 2], [1, 3], [0]],
    why: 'U keeps M\'s current state on its own tape as a string, so it never needs more states. And it loops whenever M does.',
    hints: H('Where does U keep M\'s state: in its own state, or on a tape?', 'If M loops on w, what does U do?', 'Fixed size, and the same verdict as M. It does not halt when M does not.') });

  ex({ id: 'tur-x-utm-steps', chapter: CH6, title: 'A step of the universal machine', kind: 'choice', level: 2,
    text: 'To simulate one step of M, the universal machine reads M\'s state on one tape and the simulated symbol on another. What does it do next?',
    options: ['Scans ⟨M⟩ rule by rule for the rule whose first two fields match the state and the symbol, then carries it out', 'Guesses the rule nondeterministically', 'Looks the rule up in its own transition table, which contains a copy of every machine', 'Asks M'],
    answer: 0, solution: 0, wrong: [1, 2],
    hints: H('The description of M is just data on a tape.', 'The first two fields of a rule are its state and symbol.', 'It scans tape 1 for the matching rule, then rewrites the work tape and the state tape.') });

  ex({ id: 'tur-x-bb2', chapter: CH6, title: 'The two-state champion', kind: 'number', level: 2,
    text: ['Run this 2-state machine on a blank tape (blank is 0, H halts). How many steps does it take to halt?', machineBlock('blank: 0\nstart: A\nhalt: H\nA, 0 -> B, 1, R\nA, 1 -> B, 1, L\nB, 0 -> A, 1, L\nB, 1 -> H, 1, R')],
    answer: 6, solution: '6', wrong: ['4', '5', '7'],
    hints: H('Step 1: A on 0 writes 1, moves right, B.', 'Keep a careful note of the head position: the machine moves back and forth over a few cells.', '6 steps, leaving four 1s on the tape.') });

  ex({ id: 'tur-x-bb-ones', chapter: CH6, title: 'How many 1s?', kind: 'number',
    text: 'The 2-state champion above halts after 6 steps. How many 1s does it leave on the tape?',
    answer: 4, solution: '4', wrong: ['6', '3', '2'],
    hints: H('Every rule writes 1.', 'Some cells are written more than once.', '4.') });

  ex({ id: 'tur-x-ch-bb', chapter: CH6, title: 'Why the record cannot be computed', kind: 'choice', level: 3,
    text: 'Let S(n) be the largest number of steps any n-state machine (two symbols) takes before halting, started on a blank tape. Why is S not computable?',
    options: ['Because S(n) is too large to write down', 'Because if S were computable, we could decide whether any n-state machine halts on a blank tape: run it S(n) steps', 'Because there are infinitely many n-state machines', 'Because S(n) is not defined for large n'],
    answer: 1, solution: 1, wrong: [0, 2, 3],
    hints: H('S(n) is a perfectly well-defined whole number for each n: finitely many machines, and each either halts or not.', 'Suppose a program computed S(n). What could you do with it?', 'Run the machine for S(n) steps: if it has not halted by then, it never will. That would decide a halting problem, which cannot be done.') });

  ex({ id: 'tur-x-ch-thesis', chapter: CH6, title: 'What the thesis says', kind: 'choice', level: 2,
    text: 'Which of these describes the Church–Turing thesis?',
    options: ['A theorem proving that Turing machines can compute every function', 'A claim, supported by evidence but not provable, that every effectively calculable function is computable by a Turing machine', 'The fact that lambda calculus and Turing machines are equivalent', 'A claim that every physical computer is a Turing machine'],
    answer: 1, why: 'The equivalence of the models is a theorem; the thesis is the step from "intuitively computable" to "Turing computable", and intuition cannot be proved.',
    whyNot: { 2: 'That equivalence is a theorem, and part of the evidence for the thesis, not the thesis itself.' },
    solution: 1, wrong: [0, 2],
    hints: H('Can a statement about "effectively calculable", an intuitive notion, be proved?', 'The equivalence of the many models is the evidence.', 'A claim, supported by every model ever proposed, that intuitive computability is Turing computability.') });

  ex({ id: 'tur-x-ch-models-equal', chapter: CH6, title: 'Same power, different machines', kind: 'choice',
    text: 'Which of these compute exactly the same functions on whole numbers as Turing machines? Choose all that do.',
    options: ['Register machines with inc, dec, jz', 'Two-counter machines (with the input coded as 2ⁿ)', 'μ-recursive functions', 'Primitive recursive functions', 'The λ-calculus with Church numerals'],
    answer: [0, 1, 2, 4], solution: [0, 1, 2, 4], wrong: [[0, 1, 2, 3, 4], [0, 2, 4], [3]],
    hints: H('Which one is always total?', 'Primitive recursive functions halt on every input, so they cannot be the whole story.', 'All but the primitive recursive functions.') });
})();
