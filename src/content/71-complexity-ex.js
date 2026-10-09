// Part 7, complexity: the exercises. Certificates are checked by the verifiers of T.cx, formulas by T.sat,
// and reductions run by hand are compared with what T.red builds. String answers are checked by accept
// hooks that leave the reason for a rejection in this.whyNot; ex() hands that sentence to the checker.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const K = T.cxContent;
  const H = (a, b, c) => [a, b, c];
  // an accept hook here sets this.whyNot on rejection; the checker is handed that sentence as the reason
  const ex = (x) => {
    if (x.accept) { const f = x.accept; x = Object.assign({}, x, { accept(w) { const ctx = { whyNot: '' }; return f.call(ctx, w) ? true : ctx.whyNot ? 'Not quite. ' + ctx.whyNot : false; } }); }
    return C.exercise(Object.assign({ level: 1 }, x));
  };
  const F = (s) => T.sat.parse(s);

  // ---- reading answers ------------------------------------------------------------------------------------
  /** A literal typed as x, ¬x, ~x, !x, -x or not x, in the form x or ¬x */
  const lit = (s) => {
    s = String(s).trim();
    let neg = false;
    for (;;) {
      if (/^[¬~!-]/.test(s)) s = s.slice(1).trim();
      else if (/^not\s+/i.test(s)) s = s.replace(/^not\s+/i, '');
      else break;
      neg = !neg;
    }
    return (neg ? '¬' : '') + s;
  };
  const litSet = (text) => String(text).replace(/[{}]/g, ' ').split(/[\s,;]+/).filter(Boolean).map(lit);
  const sameSet = (a, b) => { const A = [...new Set(a)].sort(), B = [...new Set(b)].sort(); return A.length === B.length && A.every((v, i) => v === B[i]); };
  /** An assignment typed as x=1 y=0, x=T, or as literals x ¬y: {a} or {err} */
  function assignment(f, text) {
    const a = new Array(f.n + 1).fill(null);
    const toks = String(text).replace(/\s*[=:]\s*/g, '=').replace(/[{}()]/g, ' ').split(/[\s,;]+/).filter(Boolean);
    for (const t of toks) {
      let name, val;
      const m = t.match(/^(.+?)=(.+)$/);
      if (m) {
        name = m[1];
        const v = m[2].toLowerCase();
        if (/^(1|t|true)$/.test(v)) val = true; else if (/^(0|f|false)$/.test(v)) val = false; else return { err: 'the value of ' + name + ' should be 1 or 0.' };
      } else { const l = lit(t); name = l.replace(/^¬/, ''); val = !l.startsWith('¬'); }
      const i = f.names.indexOf(name);
      if (i < 1) return { err: 'there is no variable ' + name + ' in this formula.' };
      if (a[i] !== null && a[i] !== val) return { err: name + ' is given two different values.' };
      a[i] = val;
    }
    const miss = f.names.slice(1).filter((n, i) => a[i + 1] === null);
    if (miss.length) return { err: 'give a value to every variable: ' + miss.join(', ') + (miss.length > 1 ? ' have' : ' has') + ' none.' };
    return { a };
  }
  /** Vertex names typed with spaces or commas, as indexes of names: {S} or {err} */
  function vertices(text, names) {
    const toks = String(text).replace(/[{}()[\]]/g, ' ').split(/[\s,;→>-]+/).filter(Boolean).map(lit);
    const bad = toks.find((t) => names.indexOf(t) < 0);
    return bad !== undefined ? { err: 'there is no vertex ' + bad + '.' } : { S: toks.map((t) => names.indexOf(t)) };
  }
  /** The first failed check of a verifier, told with vertex names instead of numbers */
  function reason(r, names) {
    const bad = r.trace.find((c) => c.kind === 'fail');
    let say = bad ? bad.say : r.reason;
    for (const i of (bad && (bad.pair || bad.edge)) || []) say = say.replace(new RegExp('(^|[^\\w])' + i + '(?![\\w])'), '$1' + names[i]);
    return 'The verifier says: ' + say;
  }
  /** An undirected edge list a1-c2, b1 - ¬c3, …: {set: Set('a1 c2'), bad: [..]} */
  function edgeSet(text) {
    const set = new Set(), bad = [];
    for (let e of String(text).split(/[,;\n]+/)) {
      e = e.trim();
      if (!e) continue;
      const m = e.match(/^(\S+?)\s*[-–—]\s*(\S+)$/) || e.match(/^(\S+)\s+(\S+)$/);
      if (!m) { bad.push(e); continue; }
      set.add([lit(m[1]), lit(m[2])].sort().join(' '));
    }
    return { set, bad };
  }
  /** The vertex names of a clause-by-literal reduction: the literal and its clause number, like a1 or ¬c3 */
  const occNames = (f) => T.red.occurrences(f).map((o) => T.sat.litText(f, o.lit) + (o.clause + 1));
  /** Compare an edge list with the edges of a reduction's graph */
  function sameEdges(x, text, f, G) {
    const names = occNames(f), want = new Set(G.edges.map(([a, b]) => [names[a], names[b]].sort().join(' ')));
    const got = edgeSet(text);
    if (got.bad.length) { x.whyNot = 'Write each edge as two vertex names joined by a dash, like ' + names[0] + '-' + names[names.length - 1] + '; this one cannot be read: ' + got.bad[0] + '.'; return false; }
    const unknown = [...got.set].flatMap((e) => e.split(' ')).find((v) => !names.includes(v));
    if (unknown) { x.whyNot = 'There is no vertex ' + unknown + '. The vertices are ' + names.join(', ') + '.'; return false; }
    const missing = [...want].filter((e) => !got.set.has(e)), extra = [...got.set].filter((e) => !want.has(e));
    if (!missing.length && !extra.length) return true;
    x.whyNot = [missing.length ? missing.length + (missing.length > 1 ? ' edges are' : ' edge is') + ' missing' : '', extra.length ? extra.length + (extra.length > 1 ? ' edges do' : ' edge does') + ' not belong (for example ' + extra[0].replace(' ', '-') + ')' : ''].filter(Boolean).join(', and ') + '.';
    return false;
  }
  const show = (f) => T.sat.toText(f);

  // =========================================================================================================
  // Chapter 1: measuring time
  // =========================================================================================================
  const CH1 = 'cx-ch-time';
  ex({ id: 'cx-ex-order-1', chapter: CH1, title: 'Put the growth rates in order', kind: 'string',
    text: ['Order these running times from the slowest-growing to the fastest-growing. Answer with the letters in order, like ABCDEF.', { table: [['A', 'B', 'C', 'D', 'E', 'F'], ['n³', 'log n', '2ⁿ', 'n', 'n!', 'n log n']] }],
    accept(w) { return w.toUpperCase().replace(/[^A-F]/g, '') === 'BDFACE'; },
    why: 'log n < n < n log n < n³ < 2ⁿ < n!.', whyNot: 'Compare them two at a time, for large n.',
    solution: 'B D F A C E', wrong: ['BDFACE'.split('').reverse().join(''), 'BDAFCE', 'BDFAEC'],
    hints: H('A logarithm grows slower than any power of n, and every polynomial slower than 2ⁿ.', 'n log n sits between n and n²; n! outgrows 2ⁿ since each new factor is bigger than 2.', 'B (log n), D (n), F (n log n), A (n³), C (2ⁿ), E (n!): BDFACE.') });
  ex({ id: 'cx-ex-order-2', chapter: CH1, title: 'Growth rates with traps', kind: 'string', level: 3,
    text: ['Order these from the slowest-growing to the fastest-growing, for large n. Answer with the letters in order.', { table: [['A', 'B', 'C', 'D', 'E', 'F'], ['2^(n/2)', 'n¹⁰', '(log n)³', '√n', 'n log n', '1.5ⁿ']] }],
    accept(w) { return w.toUpperCase().replace(/[^A-F]/g, '') === 'CDEBAF'; },
    why: '(log n)³ < √n < n log n < n¹⁰ < 2^(n/2) < 1.5ⁿ.', whyNot: 'Two of the six are exponentials: compare their bases.',
    solution: 'CDEBAF', wrong: ['DCEBAF', 'CDEBFA', 'CDEABF'],
    hints: H('Any power of log n is eventually below any power of n, even √n = n^0.5. That holds even though (log n)³ is larger for quite big n.', '2^(n/2) = (√2)ⁿ ≈ 1.414ⁿ, which is slower than 1.5ⁿ, but every exponential beats n¹⁰ in the end.', 'C, D, E, B, A, F: CDEBAF.') });
  ex({ id: 'cx-ex-bigo-true', chapter: CH1, title: 'Which big-O claims hold?', kind: 'choice', level: 2,
    text: 'Choose every true statement.',
    options: ['7n³ + 50n² = O(n³)', 'n² = O(n log n)', '2ⁿ⁺³ = O(2ⁿ)', '3ⁿ = O(2ⁿ)', 'log₂ n = O(log₁₀ n)', 'n log n = O(n^1.5)'], answer: [0, 2, 4, 5],
    why: '2ⁿ⁺³ = 8 · 2ⁿ, and logarithms of different bases differ by a constant factor; but 3ⁿ / 2ⁿ = 1.5ⁿ grows without bound.',
    solution: [0, 2, 4, 5], wrong: [[0, 2, 4], [0, 2, 3, 4, 5], [0, 1, 2, 4, 5]],
    hints: H('f = O(g) when f/g stays below some constant for large n.', 'Look at the ratios: 2ⁿ⁺³/2ⁿ = 8, 3ⁿ/2ⁿ = 1.5ⁿ, n²/(n log n) = n/log n.', 'True: the first, third, fifth and sixth.') });
  ex({ id: 'cx-ex-bigo-n0', chapter: CH1, title: 'Find the n₀', kind: 'number', level: 2,
    text: 'To show 2n² + 3n + 1 = O(n²) we use the constant c = 3. What is the smallest n₀ such that 2n² + 3n + 1 ≤ 3n² for every n ≥ n₀?',
    answer: 4, why: 'At n = 3: 28 > 27. At n = 4: 45 ≤ 48, and the gap only widens.', solution: '4', wrong: ['3', '1', '5'],
    hints: H('The inequality is the same as n² − 3n − 1 ≥ 0.', 'Try n = 3 and n = 4.', 'n = 3 gives 28 against 27, which fails; n = 4 gives 45 against 48, and from then on n² − 3n − 1 only grows: n₀ = 4.') });
  ex({ id: 'cx-ex-crossover', chapter: CH1, title: 'When does 2ⁿ win for good?', kind: 'number',
    text: 'What is the smallest n from which 2ⁿ > n³ holds for that n and every larger one? (Careful: it also holds at n = 1.)',
    answer: 10, solution: '10', wrong: ['1', '9', '11'],
    hints: H('Check n = 2, 3, … until 2ⁿ passes n³ and stays ahead.', 'At n = 9: 512 against 729. At n = 10: 1024 against 1000.', '10. Below it, n = 9 still fails; from 10 on, doubling beats the cube\'s growth factor ((n + 1)/n)³ < 2.') });
  ex({ id: 'cx-ex-poly-closure', chapter: CH1, title: 'Still a polynomial?', kind: 'choice', level: 2,
    text: 'f(n) and g(n) are polynomials with positive coefficients. Which of these are always bounded by a polynomial?',
    options: ['f(n) + g(n)', 'f(n) · g(n)', 'f(g(n))', '2^f(n)', 'f(n)^(log n)'], answer: [0, 1, 2],
    why: 'Sums, products and compositions of polynomials are polynomials. That is why "polynomial time" survives calling a subroutine.',
    solution: [0, 1, 2], wrong: [[0, 1], [0, 1, 2, 4]],
    hints: H('Composing n² with n³ gives n⁶.', 'n^(log n) = 2^((log n)²) beats every fixed power of n.', 'The first three.') });
  ex({ id: 'cx-ex-steps-anbn', chapter: CH1, title: 'Read a step count', kind: 'number',
    text: ['Run the aⁿbⁿ machine below on aaabbb to the end, then read the counter marked "steps of this run" in the box under the play controls. How many steps does the run take?', { topic: 'cx-steps', input: { m: 'anbn', w: 'aaabbb', n: 6 }, caption: 'Step to the end of the run, or play it.' }],
    answer: 25, solution: '25', wrong: ['13', '6', '36'],
    hints: H('The "steps of this run" counter is in the box under the play and step buttons, below the narration; the amber point on the chart, labelled aaabbb, climbs to the same number. Each move of the head is one step.', 'Each pass crosses off one a and one b and walks back.', '25 steps.') });
  ex({ id: 'cx-ex-tm-linear', chapter: CH1, title: 'A linear-time decider', kind: 'machine', machine: 'tm', alphabet: 'ab', level: 2, maxLen: 8, steps: 12,
    text: 'Build a Turing machine that accepts the non-empty strings over {a, b} whose first and last symbols are equal (a single symbol counts), and rejects all others, including ε. It must use at most n + 4 steps on inputs of length n: no going back and forth.',
    member: (w) => w.length > 0 && w[0] === w[w.length - 1],
    solution: 'start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> ca, _, L\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, _ -> cb, _, L\nca, a -> yes, a, S\ncb, b -> yes, b, S',
    wrong: ['start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> ra, b, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> ca, _, L\nca, a -> yes, a, S',
      'start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> ca, _, L\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, _ -> cb, _, L\nca, a -> back, a, L\ncb, b -> back, b, L\nback, a -> back, a, L\nback, b -> back, b, L\nback, _ -> yes, _, R',
      'start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> yes, _, S\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, _ -> yes, _, S'],
    hints: H('Remember the first symbol in the state: one state for "started with a", one for "started with b".', 'Run right to the blank, step back once, and compare. A missing rule rejects.', 's on a goes to ra, on b to rb; ra and rb run right; at the blank they step left into ca or cb; ca accepts on a, cb accepts on b. That is n + 2 steps.') });
  ex({ id: 'cx-ex-twotape', chapter: CH1, title: 'What a second tape is worth', kind: 'choice', level: 2,
    text: 'A two-tape machine decides a language in time t(n) ≥ n. What does the standard simulation guarantee for a one-tape machine deciding the same language?',
    options: ['Time O(t(n))', 'Time O(t(n)²)', 'Time 2^O(t(n))', 'Nothing: some two-tape languages have no one-tape decider'], answer: 1,
    why: 'Each simulated step sweeps over the O(t(n)) cells used so far: t(n) steps of O(t(n)) each.',
    solution: 1, wrong: [0, 2, 3], hints: H('The one-tape machine keeps both tapes side by side on its single tape.', 'To simulate one step it sweeps over everything written, which is at most O(t(n)) cells.', 'O(t(n)²).') });
  ex({ id: 'cx-ex-encoding-bits', chapter: CH1, title: 'How long is 1000?', kind: 'number',
    text: 'How many digits does the number 1000 have when written in binary? (In unary it would take 1000 strokes.)',
    answer: 10, solution: '10', wrong: ['4', '1000', '11'],
    hints: H('The length of N in binary is ⌊log₂ N⌋ + 1.', '2⁹ = 512 ≤ 1000 < 1024 = 2¹⁰.', '1000 = 1111101000 in binary: 10 digits.') });
  ex({ id: 'cx-ex-unary', chapter: CH1, title: 'Is trial division polynomial?', kind: 'choice', level: 2,
    text: 'An algorithm decides whether N is prime by trying every divisor from 2 to √N. Is it a polynomial-time algorithm?',
    options: ['Yes: √N is smaller than N', 'Only if N is written in unary; in binary, with b digits, √N is about 2^(b/2), exponential in the input length', 'No, under any encoding', 'Yes, because each single division is fast'], answer: 1,
    why: 'Time is measured against the length of the input. Unary makes the input exponentially long, which is why it is not a reasonable encoding.',
    solution: 1, wrong: [0, 3], hints: H('What is the length of N in binary?', 'About log₂ N. Write √N in terms of that length.', 'Exponential in the binary length; polynomial only against the unary length.') });

  // =========================================================================================================
  // Chapter 2: P and NP
  // =========================================================================================================
  const CH2 = 'cx-ch-np';
  ex({ id: 'cx-ex-in-p', chapter: CH2, title: 'Which are known to be in P?', kind: 'choice', level: 2,
    text: 'Choose every problem that is known to be in P.',
    options: ['PATH: is there a path from s to t in a directed graph?', 'RELPRIME: are two numbers (written in binary) relatively prime?', 'Is w generated by the fixed grammar S → a S b | S S | ε?', 'SAT', 'Does a graph have a clique of 3 vertices?', 'Does a graph have a clique of k vertices, with k part of the input?'], answer: [0, 1, 2, 4],
    why: 'A clique of fixed size 3 can be found by trying all O(n³) triples; with k part of the input that becomes the NP-complete CLIQUE.',
    solution: [0, 1, 2, 4], wrong: [[0, 1, 2], [0, 1, 2, 4, 5], [0, 1, 2, 3, 4]],
    hints: H('BFS, Euclid and CYK are all polynomial.', 'For a fixed k, trying all k-element sets takes O(nᵏ) time: a polynomial. When k grows with the input it does not.', 'PATH, RELPRIME, the grammar question and the triangle question.') });
  ex({ id: 'cx-ex-euclid', chapter: CH2, title: 'Euclid by hand', kind: 'number',
    text: 'Euclid\'s algorithm on (126, 49) replaces (a, b) by (b, a mod b) until b = 0. How many times does it compute a mod b?',
    answer: 4, why: '(126, 49) → (49, 28) → (28, 21) → (21, 7) → (7, 0); gcd 7, so the two are not relatively prime.',
    solution: '4', wrong: ['3', '5', '7'],
    hints: H('126 mod 49 = 28.', 'Then 49 mod 28 = 21, then 28 mod 21 = 7.', '126 mod 49, 49 mod 28, 28 mod 21, 21 mod 7 = 0: four.') });
  const BFS = { pos: { s: [30, 90], p: [120, 30], q: [120, 150], r: [220, 70], u: [220, 190], t: [320, 40], v: [320, 190] }, edges: 's-p s-q p-r q-r q-u r-t u-v' };
  ex({ id: 'cx-ex-bfs-layer', chapter: CH2, title: 'Two steps away', kind: 'string',
    text: ['Breadth-first search from s marks vertices in layers by distance. Which vertices are at distance exactly 2 from s? Write them as a set, like {a, b}.', { svg: K.svg(BFS.pos, BFS.edges, { label: 'A graph with vertices s, p, q, r, u, t, v' }) }],
    accept(w) { return sameSet(litSet(w), ['r', 'u']); }, whyNot: 'List the vertices whose shortest path from s has exactly two edges.',
    solution: '{r, u}', wrong: ['{p, q}', '{r, u, t}', '{r}'],
    hints: H('Layer 1 is the neighbours of s: p and q.', 'Layer 2 is everything new next to layer 1.', 'p and q lead to r and u: {r, u}.') });
  ex({ id: 'cx-ex-cyk-splits', chapter: CH2, title: 'Counting CYK\'s work', kind: 'number', level: 3,
    text: 'For a word of length 6, CYK fills one cell for each piece of the word, and for a piece of length L ≥ 2 it tries L − 1 split points. How many split points does it try in all?',
    answer: 35, why: 'Pieces of length L: 7 − L of them, each with L − 1 splits: 5 + 8 + 9 + 8 + 5 = 35, which is C(7, 3).',
    solution: '35', wrong: ['21', '36', '15'],
    hints: H('There are 7 − L pieces of length L in a word of length 6.', 'Add (7 − L)(L − 1) for L = 2 to 6.', '5·1 + 4·2 + 3·3 + 2·4 + 1·5 = 35.') });

  // certificates, checked by the verifiers
  const G1 = K.graph(K.G1.pos, K.G1.edges), G2 = K.graph(K.G2.pos, K.G2.edges), G3 = K.graph(K.G3.pos, K.G3.edges);
  const fig = (g, label) => ({ svg: K.svg(g.pos, g.edges, { label }) });
  const certEx = (x, G, verify) => ex(Object.assign({}, x, {
    accept(w) {
      this.whyNot = '';
      const v = vertices(w, G.names);
      if (v.err) { this.whyNot = 'Write vertex names separated by spaces: ' + v.err; return false; }
      const r = verify(G, v.S);
      if (!r.ok) this.whyNot = reason(r, G.names);
      return r.ok;
    },
  }));
  certEx({ id: 'cx-ex-cert-clique', chapter: CH2, title: 'A certificate for CLIQUE', kind: 'string', placeholder: 'vertex names, like a b c d',
    text: ['Find a clique of 4 vertices in this graph: four vertices that are all joined to each other. Write their names separated by spaces; the CLIQUE verifier checks them.', fig(K.G1, 'A graph on vertices a to g')],
    why: 'All six pairs are edges.', solution: 'a b c e', wrong: ['a b c d', 'b c e f', 'a b c'],
    hints: H('Look for vertices with at least three neighbours.', 'a, b, c form a triangle. Which vertex is joined to all three?', 'a b c e: the pairs ab, ac, ae, bc, be, ce are all edges.') }, G1, (G, S) => T.cx.verifyClique(G, 4, S));
  certEx({ id: 'cx-ex-cert-hampath', chapter: CH2, title: 'A certificate for HAM-PATH', kind: 'string', level: 2, placeholder: 'vertices in order, like a b c d e f',
    text: ['Give a Hamiltonian path from a to f: it visits every vertex exactly once and each step follows an edge. Write the vertices in order.', fig(K.G2, 'A graph on vertices a to f')],
    solution: 'a d e b c f', wrong: ['a b c f e d', 'a b e f', 'a d e f c b'],
    hints: H('From a you can go to b or to d.', 'If you go to b first, d is only reachable from a and e, so d would have to come last.', 'a d e b c f.') }, G2, (G, S) => T.cx.verifyHamPath(G, S, 0, 5));
  const NUMS = [14, 9, 22, 5, 17, 11];
  ex({ id: 'cx-ex-cert-subset', chapter: CH2, title: 'A certificate for SUBSET SUM', kind: 'string', placeholder: 'numbers, like 9 + 11',
    text: 'The numbers are 14, 9, 22, 5, 17, 11 and the target is 41. Write some of the numbers (each at most once) that add up to exactly 41.',
    accept(w) {
      this.whyNot = '';
      const vals = String(w).split(/[\s,+]+/).filter(Boolean).map(Number);
      if (vals.some((v) => !Number.isInteger(v))) { this.whyNot = 'Write the numbers separated by spaces or +.'; return false; }
      const used = new Set(), idx = [];
      for (const v of vals) { const i = NUMS.findIndex((n, k) => n === v && !used.has(k)); if (i < 0) { this.whyNot = v + ' is not one of the numbers, or is used twice.'; return false; } used.add(i); idx.push(i); }
      const r = T.cx.verifySubsetSum(NUMS, 41, idx);
      if (!r.ok) this.whyNot = reason(r, []);
      return r.ok;
    },
    solution: '14 22 5', wrong: ['22 17', '14 9 22', '22 22 -3'],
    hints: H('Start with the biggest number, 22: you then need 19 more.', '19 = 14 + 5.', '14 + 22 + 5 = 41.') });
  ex({ id: 'cx-ex-cert-colour', chapter: CH2, title: 'A certificate for 3-COLOUR', kind: 'string', level: 2, placeholder: 'a=1 b=2 …',
    text: ['Colour the vertices with colours 1, 2 and 3 so that no edge joins two vertices of the same colour. Write it like a=1 b=2 …', fig(K.G3, 'A graph on vertices a to h')],
    accept(w) {
      this.whyNot = '';
      const col = new Array(G3.n).fill(null);
      for (const t of String(w).replace(/\s*[=:]\s*/g, '=').split(/[\s,;]+/).filter(Boolean)) {
        const m = t.match(/^(\w+)=(\d)$/);
        if (!m || G3.names.indexOf(m[1]) < 0) { this.whyNot = 'Write each vertex with its colour, like a=1; ' + t + ' cannot be read.'; return false; }
        col[G3.names.indexOf(m[1])] = Number(m[2]) - 1;
      }
      const miss = G3.names.filter((n, i) => col[i] === null);
      if (miss.length) { this.whyNot = 'Every vertex needs a colour; ' + miss.join(', ') + ' ' + (miss.length > 1 ? 'have' : 'has') + ' none.'; return false; }
      const r = T.cx.verifyColouring(G3, 3, col);
      if (!r.ok) this.whyNot = reason(r, G3.names).replace(/colours (\d) and (\d)/, (s, a, b) => 'colours ' + (+a + 1) + ' and ' + (+b + 1));
      return r.ok;
    },
    solution: 'a=1 b=2 c=3 d=1 e=2 f=3 g=1 h=3', wrong: ['a=1 b=2 c=3 d=1 e=2 f=1 g=3 h=3', 'a=1 b=2 c=3 d=2 e=1 f=2 g=3 h=2', 'a=1 b=2 c=1 d=2 e=3 f=1 g=2 h=3'],
    hints: H('a, b, c form a triangle: they need three different colours. So do c, d, e and e, f, g.', 'Fix a=1, b=2, c=3. Then d and e avoid 3 and each other.', 'h is next to a, b and g, so g must not take colour 3. a=1 b=2 c=3 d=1 e=2 f=3 g=1 h=3 works.') });
  certEx({ id: 'cx-ex-cert-is', chapter: CH2, title: 'A certificate for INDEPENDENT SET', kind: 'string', level: 2,
    text: ['Find 3 vertices of this graph with no edge between any two of them.', fig(K.G3, 'A graph on vertices a to h')],
    solution: 'a d f', wrong: ['a d e', 'b d g h', 'a d'],
    hints: H('Vertices of the same triangle can never both be chosen.', 'Try a first; then everything next to a (b, c, h) is out.', 'a, d, f: none of ad, af, df is an edge.') }, G3, (G, S) => T.cx.verifyIndependentSet(G, 3, S));
  certEx({ id: 'cx-ex-cert-vc', chapter: CH2, title: 'A certificate for VERTEX COVER', kind: 'string', level: 2,
    text: ['Find at most 5 vertices of the same graph that touch every edge.', fig(K.G3, 'A graph on vertices a to h')],
    solution: 'b c e g h', wrong: ['a c e g', 'b c e g', 'a b c d e f'],
    hints: H('A vertex cover is what is left when you remove an independent set.', 'The independent set a, d, f leaves b, c, e, g, h.', 'b c e g h: every edge has an end among them.') }, G3, (G, S) => T.cx.verifyVertexCover(G, 5, S));
  ex({ id: 'cx-ex-verifier', chapter: CH2, title: 'What a verifier must do', kind: 'choice',
    text: 'A language A is in NP when it has a verifier V. Which condition is part of the definition?',
    options: ['V runs in time polynomial in |w|, so useful certificates are polynomially long', 'V must also be able to find the certificate in polynomial time', 'Certificates may be of any length', 'For w not in A, some certificate may still be accepted'], answer: 0,
    solution: 0, wrong: [1, 3], hints: H('Finding is the hard part that NP does not demand.', 'If w ∉ A, every certificate must be rejected.', 'V is polynomial in |w|.') });
  ex({ id: 'cx-ex-ntm-leaves', chapter: CH2, title: 'Leaves of a guessing tree', kind: 'number',
    text: 'A nondeterministic machine guesses one bit for each of 4 variables, then checks a formula deterministically. How many branches does its tree have after the guesses?',
    answer: 16, solution: '16', wrong: ['4', '8', '24'],
    hints: H('Each guess doubles the number of branches.', '2 · 2 · 2 · 2.', '16, one for each assignment.') });
  ex({ id: 'cx-ex-ntm-sim', chapter: CH2, title: 'Simulating guesses', kind: 'choice', level: 2,
    text: 'A nondeterministic machine runs in time t(n) with at most 2 choices per step. A deterministic machine simulates it by trying every branch. How long can that take?',
    options: ['O(t(n)²)', '2^O(t(n))', 'O(t(n) log t(n))', 'It cannot be simulated'], answer: 1,
    why: 'There can be 2^t(n) branches, each of length t(n). Whether this blow-up can be avoided in general is the P versus NP question.',
    solution: 1, wrong: [0, 3], hints: H('How many leaves can a binary tree of depth t have?', '2^t leaves, each a run of t steps.', '2^O(t(n)).') });
  ex({ id: 'cx-ex-pnp-consequence', chapter: CH2, title: 'If 3-COLOUR were easy', kind: 'choice',
    text: 'Someone finds a polynomial-time algorithm for 3-COLOUR, which is NP-complete. What follows?',
    options: ['P = NP', 'Only that 3-COLOUR is in P; nothing else changes', 'NP = co-NP, but P and NP may still differ', 'Nothing, because reductions go the other way'], answer: 0,
    why: 'Every NP problem reduces to 3-COLOUR in polynomial time; follow the reduction with the new algorithm.',
    solution: 0, wrong: [1, 3], hints: H('What does NP-complete mean?', 'Every A in NP has A ≤ₚ 3-COLOUR.', 'P = NP.') });
  ex({ id: 'cx-ex-conp-which', chapter: CH2, title: 'Which are in co-NP?', kind: 'choice', level: 2,
    text: 'Choose every problem that is known to be in co-NP.',
    options: ['TAUT: is φ true under every assignment?', 'UNSAT: is φ unsatisfiable?', 'Does a graph have no Hamiltonian path?', 'PATH', 'CLIQUE'], answer: [0, 1, 2, 3],
    why: 'TAUT, UNSAT and NO-HAM-PATH are complements of NP problems; PATH is in P, and P ⊆ co-NP. CLIQUE is in co-NP only if NP = co-NP.',
    solution: [0, 1, 2, 3], wrong: [[0, 1, 2], [0, 1, 2, 3, 4]],
    hints: H('A language is in co-NP when its no-instances have short certificates.', 'P is closed under complement, so P ⊆ NP ∩ co-NP.', 'All but CLIQUE.') });
  const TAUTF = F('(p ∨ ¬q ∨ r) ∧ (q ∨ ¬r) ∧ (¬p ∨ r ∨ q)');
  ex({ id: 'cx-ex-taut-refute', chapter: CH2, title: 'Refute a tautology claim', kind: 'string', level: 2,
    text: 'Someone claims φ = ' + show(TAUTF) + ' is true under every assignment. Prove them wrong with an assignment that makes φ false, like p=1 q=0 r=1.',
    accept(w) { this.whyNot = ''; const r = assignment(TAUTF, w); if (r.err) { this.whyNot = 'The assignment cannot be read: ' + r.err; return false; } if (T.sat.evaluate(TAUTF, r.a)) { this.whyNot = 'Under that assignment every clause is true, so it does not refute the claim.'; return false; } return true; },
    why: 'One falsifying row is a short certificate that the answer to TAUT is no.',
    solution: 'p=0 q=1 r=0', wrong: ['p=1 q=1 r=1', 'p=0 q=0 r=0', 'p=1 q=0'],
    hints: H('Make one clause false: all of its literals false.', 'For (q ∨ ¬r) to be false, q = 0 and r = 1.', 'p=0 q=1 r=0 falsifies the first clause; p=1 q=0 r=0 and p=0 q=0 r=1 work too.') });

  // =========================================================================================================
  // Chapter 3: satisfiability
  // =========================================================================================================
  const CH3 = 'cx-ch-sat';
  /** An exercise answered by an assignment of f, or by unsat when f has none */
  const satEx = (x, f) => ex(Object.assign({}, x, {
    accept(w) {
      this.whyNot = '';
      const unsat = !T.sat.brute(f).sat;
      if (/^\s*(un\s*sat(isfiable)?|none|no)\s*$/i.test(w)) { if (!unsat) this.whyNot = 'It is satisfiable: try harder to find an assignment.'; return unsat; }
      const r = assignment(f, w);
      if (r.err) { this.whyNot = 'The assignment cannot be read: ' + r.err; return false; }
      const v = T.cx.verifySat(f, r.a);
      if (!v.ok) this.whyNot = v.reason;
      return v.ok;
    },
  }));
  const SAT1 = F('(p ∨ q) ∧ (¬p ∨ r) ∧ (¬q ∨ ¬r) ∧ (q ∨ r) ∧ (¬p ∨ ¬q)');
  satEx({ id: 'cx-ex-sat-find', chapter: CH3, title: 'Find a satisfying assignment', kind: 'string', placeholder: 'p=1 q=0 r=1',
    text: 'Find an assignment that satisfies φ = ' + show(SAT1) + '. Write it like p=1 q=0 r=1.',
    solution: 'p=1 q=0 r=1', wrong: ['p=1 q=1 r=1', 'p=0 q=0 r=0', 'unsat'],
    hints: H('(p ∨ q) and (¬p ∨ ¬q) together say exactly one of p and q is true.', 'Try p = 1: then r must be 1 (from ¬p ∨ r), and q = 0.', 'p=1 q=0 r=1, or p=0 q=1 r=0.') }, SAT1);
  const SAT2 = F('(a ∨ b) ∧ (¬a ∨ c) ∧ (¬b ∨ c) ∧ (¬c ∨ d) ∧ (¬c ∨ ¬d)');
  satEx({ id: 'cx-ex-sat-or-unsat-a', chapter: CH3, title: 'Satisfy it or show it cannot be done', kind: 'string', level: 2, placeholder: 'a=1 b=0 … or unsat',
    text: 'φ = ' + show(SAT2) + '. Type a satisfying assignment, or unsat if there is none.',
    why: 'Whichever of a, b is true forces c, and c forces both d and ¬d.',
    solution: 'unsat', wrong: ['a=1 b=0 c=1 d=1', 'a=0 b=0 c=0 d=0', 'a=1 b=1 c=1 d=0'],
    hints: H('What does (a ∨ b) with (¬a ∨ c) and (¬b ∨ c) say about c?', 'c must be true. Now look at the last two clauses.', 'c = 1 forces d = 1 and d = 0: unsat.') }, SAT2);
  const SAT3 = F('(a ∨ b ∨ c) ∧ (¬a ∨ ¬b) ∧ (¬b ∨ ¬c) ∧ (¬a ∨ ¬c) ∧ (a ∨ d) ∧ (¬d ∨ c) ∧ (b ∨ ¬c ∨ ¬d)');
  satEx({ id: 'cx-ex-sat-or-unsat-b', chapter: CH3, title: 'One needle in sixteen', kind: 'string', level: 3, placeholder: 'a=1 b=0 … or unsat',
    text: 'φ = ' + show(SAT3) + '. Type a satisfying assignment, or unsat if there is none.',
    why: 'It is the only one of the 16 assignments that works.',
    solution: 'a=1 b=0 c=0 d=0', wrong: ['unsat', 'a=0 b=0 c=1 d=1', 'a=0 b=1 c=0 d=1'],
    hints: H('The first four clauses say exactly one of a, b, c is true.', 'If d = 1, then c = 1 (from ¬d ∨ c), and the last clause needs b = 1: too many true.', 'So d = 0, then a = 1 (from a ∨ d), and b = c = 0: a=1 b=0 c=0 d=0.') }, SAT3);
  ex({ id: 'cx-ex-sat-choice-1', chapter: CH3, title: 'Satisfiable or not? (1)', kind: 'choice',
    text: 'Is (x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) satisfiable?', options: ['Satisfiable', 'Unsatisfiable'], answer: 0,
    why: 'x = y = 1 makes every clause true. Only the fourth sign pattern (¬x ∨ ¬y) would rule it out.',
    solution: 0, wrong: [1], hints: H('Three of the four sign patterns of x, y are present.', 'Which pattern is missing? It names the one assignment not ruled out.', 'Satisfiable, by x = 1, y = 1.') });
  ex({ id: 'cx-ex-sat-choice-2', chapter: CH3, title: 'Satisfiable or not? (2)', kind: 'choice', level: 2,
    text: 'Is (p ∨ q ∨ r) ∧ (¬p ∨ q) ∧ (¬q ∨ r) ∧ (¬r ∨ p) ∧ (¬p ∨ ¬q ∨ ¬r) satisfiable?', options: ['Satisfiable', 'Unsatisfiable'], answer: 1,
    why: 'p → q → r → p forces all three equal; all true breaks the last clause, all false breaks the first.',
    solution: 1, wrong: [0], hints: H('Read the middle three clauses as implications.', 'p → q, q → r, r → p: the three values must be equal.', 'Both "all equal" assignments fail: unsatisfiable.') });
  const UP = F('(¬x ∨ y) ∧ (¬y ∨ ¬z) ∧ (z ∨ w ∨ ¬x) ∧ (¬w ∨ v) ∧ (u ∨ ¬v ∨ z) ∧ (t ∨ s)');
  ex({ id: 'cx-ex-unit-prop', chapter: CH3, title: 'Follow the forced moves', kind: 'string', level: 2,
    text: 'In φ = ' + show(UP) + ', DPLL guesses x = 1. Which literals does unit propagation then force, one after another? Write them as a set, like {y, ¬z}.',
    accept(w) { return sameSet(litSet(w), ['y', '¬z', 'w', 'v', 'u']); }, whyNot: 'Keep going until no clause has a single unset literal left.',
    solution: '{y, ¬z, w, v, u}', wrong: ['{y, ¬z}', '{y, ¬z, w, v, u, t}', '{y, z, w, v, u}'],
    hints: H('(¬x ∨ y) is unit once x = 1.', 'y = 1 makes (¬y ∨ ¬z) unit, and then (z ∨ w ∨ ¬x) has only w left.', 'y, then ¬z, then w, then v, then u. (t ∨ s) is never unit.') });
  const PURE = F('(a ∨ ¬b ∨ c) ∧ (¬a ∨ ¬b) ∧ (c ∨ d) ∧ (¬d ∨ a)');
  ex({ id: 'cx-ex-pure', chapter: CH3, title: 'Find the pure literals', kind: 'string',
    text: 'Which literals are pure in φ = ' + show(PURE) + '? Write them as a set.',
    accept(w) { return sameSet(litSet(w), ['¬b', 'c']); }, whyNot: 'A literal is pure when its negation appears nowhere.',
    solution: '{¬b, c}', wrong: ['{¬b}', '{c, d}', '{a, ¬b, c}'],
    hints: H('Go variable by variable: does it occur with both signs?', 'a occurs as a and ¬a; d as d and ¬d.', 'b only appears as ¬b, c only as c: {¬b, c}.') });
  ex({ id: 'cx-ex-empty', chapter: CH3, title: 'Empty clause, empty formula', kind: 'choice',
    text: 'Choose every true statement.',
    options: ['A clause with no literals can never be made true', 'A formula with no clauses is unsatisfiable', 'A formula containing an empty clause is satisfiable when all its other clauses are', 'A formula with no clauses is true under every assignment'], answer: [0, 3],
    solution: [0, 3], wrong: [[0, 1], [3], [0, 2, 3]],
    hints: H('An OR of nothing: is any literal true?', 'An AND of nothing: is any clause false?', 'The first and the last.') });
  const IMP = (text) => {
    const out = [];
    for (let part of String(text).split(/[,;\n]+/)) {
      part = part.trim();
      if (!part) continue;
      const m = part.match(/^(.+?)\s*(→|->|=>|⇒|>)\s*(.+)$/);
      if (!m) return null;
      out.push(lit(m[1]) + '→' + lit(m[3]));
    }
    return out;
  };
  ex({ id: 'cx-ex-2sat-implications', chapter: CH3, title: 'A clause as two arrows', kind: 'string', placeholder: 'x → y, ¬y → ¬x',
    text: 'Which two implications does the clause (a ∨ ¬b) put into the implication graph? Write them like x → y, ¬y → ¬x.',
    accept(w) { const g = IMP(w); return !!g && sameSet(g, ['¬a→¬b', 'b→a']); }, whyNot: 'For (p ∨ q) the arrows are ¬p → q and ¬q → p.',
    solution: '¬a → ¬b, b → a', wrong: ['a → ¬b, b → ¬a', '¬a → ¬b', 'a → b, ¬b → ¬a'],
    hints: H('If a is false, what must ¬b be?', 'If a is false, ¬b must be true: ¬a → ¬b. The other arrow starts from the negation of ¬b.', '¬a → ¬b and b → a.') });
  const TS = F('(a ∨ ¬b) ∧ (b ∨ c) ∧ (¬c ∨ d) ∧ (¬d ∨ ¬a) ∧ (¬a ∨ ¬c)');
  ex({ id: 'cx-ex-2sat-reach', chapter: CH3, title: 'Where does a lead?', kind: 'string', level: 2,
    text: 'In the implication graph of ψ = ' + show(TS) + ', which literals other than a itself can be reached from a? Write them as a set.',
    accept(w) { return sameSet(litSet(w), ['b', '¬c', '¬d']); }, whyNot: 'Write out the two arrows of every clause, then follow them from a.',
    solution: '{b, ¬c, ¬d}', wrong: ['{¬c, ¬d}', '{b, ¬c, ¬d, ¬a}', '{¬b, c, d}'],
    hints: H('From (¬d ∨ ¬a): a → ¬d. From (¬a ∨ ¬c): a → ¬c.', 'From (¬c ∨ d): ¬d → ¬c. From (b ∨ c): ¬c → b. From (a ∨ ¬b): b → a, back where we started.', '{b, ¬c, ¬d}. Since ¬a is not among them, a = 1 is safe, with b = 1, c = 0, d = 0.') });
  ex({ id: 'cx-ex-2sat-verdict', chapter: CH3, title: 'Read the implication graph', kind: 'choice', level: 2,
    text: 'What does the implication graph of (x ∨ y) ∧ (¬y ∨ w) ∧ (¬w ∨ x) ∧ (¬x ∨ z) ∧ (¬x ∨ ¬z) show?',
    options: ['It is satisfiable', 'It is unsatisfiable: x and ¬x lie on one cycle of implications', 'It is unsatisfiable, because there are more clauses than variables', 'It is satisfiable, and x must be true'], answer: 1,
    why: '¬x → y → w → x, and x → z → ¬x.',
    solution: 1, wrong: [0, 2, 3], hints: H('Follow arrows from ¬x.', '¬x → y (from x ∨ y), y → w, w → x. Now follow arrows from x.', 'x → z and z → ¬x: x and ¬x imply each other, so it is unsatisfiable.') });
  const TS2 = F('(a ∨ b) ∧ (¬a ∨ c) ∧ (¬b ∨ ¬c) ∧ (c ∨ d) ∧ (¬d ∨ e) ∧ (¬e ∨ ¬a) ∧ (b ∨ ¬e)');
  satEx({ id: 'cx-ex-2sat-solve', chapter: CH3, title: 'Solve a 2-SAT formula', kind: 'string', level: 3,
    text: 'Solve ψ = ' + show(TS2) + ' using its implications. Type a satisfying assignment (or unsat).',
    solution: 'a=1 b=0 c=1 d=0 e=0', wrong: ['a=1 b=0 c=1 d=1 e=1', 'unsat', 'a=0 b=1 c=0 d=0 e=0'],
    hints: H('Try a = 1 and follow the arrows from a.', 'a → c (¬a ∨ c), c → ¬b (¬b ∨ ¬c), a → ¬e (¬e ∨ ¬a), ¬e → ¬d (¬d ∨ e).', 'a=1 b=0 c=1 d=0 e=0. The other solution is a=0 b=1 c=0 d=1 e=1.') }, TS2);
  ex({ id: 'cx-ex-phase', chapter: CH3, title: 'Where random 3-SAT is hard', kind: 'choice',
    text: 'For random 3-CNF formulas with n variables and m clauses, at which ratio m/n are the formulas hardest for DPLL on average?',
    options: ['About 1', 'About 2', 'About 4.3', 'About 10', 'There is no such ratio'], answer: 2,
    why: 'Below it almost every formula is satisfiable and easily solved; above it almost every one is unsatisfiable and quickly refuted.',
    solution: 2, wrong: [0, 3, 4], hints: H('Look at the curve in the random 3-SAT topic.', 'The work peaks where the chance of being satisfiable drops from near 1 to near 0.', 'About 4.3.') });

  // =========================================================================================================
  // Chapter 4: reductions
  // =========================================================================================================
  const CH4 = 'cx-ch-red';
  ex({ id: 'cx-ex-red-direction', chapter: CH4, title: 'Which way to reduce', kind: 'choice',
    text: 'You want to show that a new problem X is NP-hard. What do you prove?',
    options: ['3SAT ≤ₚ X', 'X ≤ₚ 3SAT', 'X ∈ P', 'X ∈ NP'], answer: 0,
    why: 'Then every NP problem reduces to 3SAT and on to X.',
    solution: 0, wrong: [1, 3], hints: H('A ≤ₚ B means A is no harder than B.', 'You want X to be at least as hard as something known to be hard.', '3SAT ≤ₚ X.') });
  ex({ id: 'cx-ex-red-meaning', chapter: CH4, title: 'What a reduction gives you', kind: 'choice', level: 2,
    text: 'Suppose A ≤ₚ B. Choose every statement that follows.',
    options: ['If B ∈ P then A ∈ P', 'If A ∈ P then B ∈ P', 'If B ∈ NP then A ∈ NP', 'If A is NP-hard then B is NP-hard', 'If B is NP-hard then A is NP-hard'], answer: [0, 2, 3],
    solution: [0, 2, 3], wrong: [[0, 1, 2, 3], [0, 3], [0, 2, 3, 4]],
    hints: H('A reduction lets you answer A by asking B.', 'Easiness flows from B down to A; hardness flows from A up to B.', 'The first, third and fourth.') });
  ex({ id: 'cx-ex-sat3-count', chapter: CH4, title: 'How long is the chain?', kind: 'number',
    text: 'SAT → 3SAT cuts a clause of 7 literals into a chain of three-literal clauses. How many clauses does the chain have?',
    answer: 5, why: 'k − 2 clauses with k − 3 new variables: 5 clauses and 4 new variables.',
    solution: '5', wrong: ['4', '7', '3'],
    hints: H('The first link holds two literals, the last link two, each middle link one.', '2 + 2 + (number of middle links) = 7.', '3 middle links plus the two ends: 5 clauses.') });
  const LONG = F('(a ∨ ¬b ∨ c ∨ d ∨ ¬e)');
  ex({ id: 'cx-ex-sat3-write', chapter: CH4, title: 'Cut a long clause by hand', kind: 'string', level: 3, placeholder: '(a ∨ ¬b ∨ z1) ∧ …',
    text: 'Write a 3-CNF formula (at most three literals per clause) that is satisfiable exactly when ' + show(LONG) + ' is, for every choice of a … e: whatever a … e are, some values of your new variables make your formula true if and only if the clause is true. Use new variables like z1, z2.',
    accept(w) {
      this.whyNot = '';
      let g;
      try { g = T.sat.parse(w); } catch (e) { this.whyNot = 'The formula cannot be read: ' + e.message + '.'; return false; }
      if (g.clauses.some((c) => !c.length || c.length > 3)) { this.whyNot = 'Every clause needs one to three literals.'; return false; }
      const old = LONG.names.slice(1), fresh = g.names.slice(1).filter((v) => !old.includes(v));
      if (fresh.length > 6) { this.whyNot = 'Two new variables are enough; you used ' + fresh.length + '.'; return false; }
      for (let m = 0; m < 32; m++) {
        const a = [null, ...old.map((v, i) => !!((m >> i) & 1))];
        const want = T.sat.evaluate(LONG, a);
        let can = false;
        for (let e = 0; e < 1 << fresh.length && !can; e++) {
          const b = new Array(g.n + 1).fill(false);
          g.names.forEach((v, i) => { if (i) b[i] = old.includes(v) ? a[1 + old.indexOf(v)] : !!((e >> fresh.indexOf(v)) & 1); });
          can = T.sat.evaluate(g, b);
        }
        if (can !== want) { this.whyNot = 'With ' + old.map((v, i) => v + '=' + (a[i + 1] ? 1 : 0)).join(' ') + ' the clause is ' + (want ? 'true' : 'false') + ', but your formula ' + (can ? 'can' : 'cannot') + ' be made true.'; return false; }
      }
      return true;
    },
    why: 'Each new variable passes the duty of satisfying the clause along the chain.',
    solution: '(a ∨ ¬b ∨ z1) ∧ (¬z1 ∨ c ∨ z2) ∧ (¬z2 ∨ d ∨ ¬e)', wrong: ['(a ∨ ¬b ∨ c) ∧ (d ∨ ¬e)', '(a ∨ ¬b ∨ z1) ∧ (z1 ∨ c ∨ z2) ∧ (¬z2 ∨ d ∨ ¬e)', '(a ∨ ¬b ∨ z1) ∧ (¬z1 ∨ c ∨ d ∨ ¬e)'],
    hints: H('The first clause takes the first two literals and a new variable z1.', 'Each next clause starts with ¬ of the previous new variable.', '(a ∨ ¬b ∨ z1) ∧ (¬z1 ∨ c ∨ z2) ∧ (¬z2 ∨ d ∨ ¬e).') });
  const CQ = F('(p ∨ q ∨ r) ∧ (¬p ∨ ¬q) ∧ (q ∨ ¬r ∨ s) ∧ (¬s)');
  ex({ id: 'cx-ex-clique-size', chapter: CH4, title: 'Size of the CLIQUE instance', kind: 'number',
    text: '3SAT → CLIQUE maps φ = ' + show(CQ) + ' to a graph and a number k. How many vertices does the graph have?',
    answer: 9, why: 'One vertex per literal occurrence: 3 + 2 + 3 + 1 = 9, and k = 4, one per clause.',
    solution: '9', wrong: ['4', '5', '12'],
    hints: H('Vertices are literal occurrences, not variables.', 'Count the literals clause by clause.', '3 + 2 + 3 + 1 = 9.') });
  const RC = F('(a ∨ b) ∧ (¬a ∨ c) ∧ (¬b ∨ ¬c)');
  const RCnames = occNames(RC).join(', ');
  ex({ id: 'cx-ex-clique-edges', chapter: CH4, title: 'Run 3SAT → CLIQUE by hand', kind: 'string', level: 3, placeholder: 'a1-c2, b1-¬a2, …',
    text: 'Map φ = ' + show(RC) + ' to its CLIQUE graph. The vertices are ' + RCnames + ' (the literal and its clause number). List every edge, like a1-c2, separated by commas.',
    accept(w) { this.whyNot = ''; return sameEdges(this, w, RC, T.red.sat3ToClique(RC).graph); },
    why: 'Nine edges: every pair from different clauses except a1–¬a2, b1–¬b3 and c2–¬c3.',
    solution: 'a1-c2, a1-¬b3, a1-¬c3, b1-¬a2, b1-c2, b1-¬c3, ¬a2-¬b3, ¬a2-¬c3, c2-¬b3',
    wrong: ['a1-c2, a1-¬b3, a1-¬c3, b1-¬a2, b1-c2, b1-¬c3, ¬a2-¬b3, ¬a2-¬c3, c2-¬b3, a1-b1', 'a1-c2, a1-¬b3, a1-¬c3, b1-¬a2, b1-c2, b1-¬c3, ¬a2-¬b3, ¬a2-¬c3', 'a1-c2, a1-¬b3, a1-¬c3, b1-¬a2, b1-c2, b1-¬c3, ¬a2-¬b3, ¬a2-¬c3, c2-¬c3'],
    hints: H('Only vertices of different clauses are joined.', 'Of the 12 pairs from different clauses, leave out the three that are a literal and its negation.', 'a1-c2, a1-¬b3, a1-¬c3, b1-¬a2, b1-c2, b1-¬c3, ¬a2-¬b3, ¬a2-¬c3, c2-¬b3.') });
  const RCG = T.red.sat3ToClique(RC).graph, RCN = occNames(RC);
  ex({ id: 'cx-ex-clique-cert', chapter: CH4, title: 'A clique is an assignment', kind: 'string', level: 2,
    text: 'In the CLIQUE graph of φ = ' + show(RC) + ' (vertices ' + RCnames + '), give a clique of size 3. Its literals then form a satisfying assignment.',
    accept(w) { this.whyNot = ''; const v = vertices(w, RCN); if (v.err) { this.whyNot = v.err; return false; } const r = T.cx.verifyClique(RCG, 3, v.S); if (!r.ok) this.whyNot = reason(r, RCN); return r.ok; },
    why: 'Set the chosen literals true: every clause has one, and none contradicts another.',
    solution: 'a1 c2 ¬b3', wrong: ['a1 ¬a2 ¬b3', 'a1 b1 c2', 'b1 c2 ¬c3'],
    hints: H('Take one vertex from each clause.', 'If you pick a1 from clause 1, clause 2 must give c2 (not ¬a2).', 'a1, c2, ¬b3 (a = 1, c = 1, b = 0); b1, ¬a2, ¬c3 also works.') });
  ex({ id: 'cx-ex-is-edges', chapter: CH4, title: 'Run 3SAT → INDEPENDENT SET by hand', kind: 'string', level: 2, placeholder: 'a1-b1, …',
    text: 'Map the same φ = ' + show(RC) + ' to its INDEPENDENT SET graph (vertices ' + RCnames + '). List every edge.',
    accept(w) { this.whyNot = ''; return sameEdges(this, w, RC, T.red.sat3ToIS(RC).graph); },
    why: 'Three clause edges and three conflict edges.',
    solution: 'a1-b1, ¬a2-c2, ¬b3-¬c3, a1-¬a2, b1-¬b3, c2-¬c3', wrong: ['a1-b1, ¬a2-c2, ¬b3-¬c3', 'a1-¬a2, b1-¬b3, c2-¬c3', 'a1-b1, ¬a2-c2, ¬b3-¬c3, a1-¬a2, b1-¬b3, c2-¬c3, a1-c2'],
    hints: H('Two kinds of edges: inside a clause, and between a literal and its negation.', 'Each clause has two literals, so one edge each.', 'a1-b1, ¬a2-c2, ¬b3-¬c3, then a1-¬a2, b1-¬b3, c2-¬c3.') });
  ex({ id: 'cx-ex-is-to-vc', chapter: CH4, title: 'From independent set to cover', kind: 'string',
    text: ['In this graph {a, d, f} is an independent set. Which vertex cover does the reduction INDEPENDENT SET → VERTEX COVER turn it into? Write it as a set.', fig(K.G3, 'A graph on vertices a to h')],
    accept(w) { return sameSet(litSet(w), ['b', 'c', 'e', 'g', 'h']); }, whyNot: 'The cover is everything outside the independent set.',
    solution: '{b, c, e, g, h}', wrong: ['{a, d, f}', '{b, c, e, g}', '{b, c, e, g, h, a}'],
    hints: H('S is independent exactly when V − S is a cover.', 'There are 8 vertices: remove a, d and f.', '{b, c, e, g, h}.') });
  const VCF = F('(a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ c) ∧ (a ∨ ¬c)');
  ex({ id: 'cx-ex-vc-k', chapter: CH4, title: 'The k of 3SAT → VERTEX COVER', kind: 'number', level: 2,
    text: 'The direct reduction 3SAT → VERTEX COVER builds a variable edge for each variable and a clique for each clause. What k does it ask for, for φ = ' + show(VCF) + '?',
    answer: 8, why: 'n + Σ(|c| − 1) = 3 + 2 + 2 + 1 = 8.', solution: '8', wrong: ['3', '6', '11'],
    hints: H('One end of each variable edge: n vertices.', 'Each clause clique of size |c| needs |c| − 1 of its vertices.', '3 + (3 − 1) + (3 − 1) + (2 − 1) = 8.') });
  const SSF = F('(a ∨ b) ∧ (¬b ∨ c ∨ d) ∧ (¬a ∨ ¬d)');
  ex({ id: 'cx-ex-ss-target', chapter: CH4, title: 'The target of SUBSET SUM', kind: 'number',
    text: '3SAT → SUBSET SUM is applied to φ = ' + show(SSF) + ' (variables a, b, c, d in that order, then the clauses). What is the target, as a decimal number?',
    answer: 1111333, solution: '1111333', wrong: ['1111111', '111333', '4444333'],
    hints: H('One digit per variable, then one per clause.', 'Variable digits are 1; clause digits are 3.', '4 variables and 3 clauses: 1111333.') });
  const SSR = F('(p ∨ q ∨ ¬r) ∧ (¬p ∨ ¬q ∨ r)');
  ex({ id: 'cx-ex-ss-row', chapter: CH4, title: 'One row of the table', kind: 'number', level: 2,
    text: 'For φ = ' + show(SSR) + ', the columns are p, q, r, then clause 1, clause 2. What is the number z₁, which stands for "p is false"?',
    answer: 10001, why: 'A 1 in column p, nothing for q and r, 0 for clause 1 and 1 for clause 2, where ¬p occurs: 1 0 0 0 1.', solution: '10001', wrong: ['10010', '11', '10000'],
    hints: H('z₁ has a 1 in p\'s column.', 'In each clause column it counts the occurrences of ¬p.', '¬p occurs only in clause 2: digits 1 0 0 0 1, the number 10001.') });
  const SSRed = T.red.sat3ToSubsetSum(SSR);
  const SSlabels = SSRed.table.rows.map((r) => r.label);
  ex({ id: 'cx-ex-ss-cert', chapter: CH4, title: 'Hit the target', kind: 'string', level: 3, placeholder: 'labels, like y1 z2 g1',
    text: ['3SAT → SUBSET SUM turns φ = ' + show(SSR) + ' into the numbers below (y for true, z for false, g and h are slack) and the target ' + SSRed.target + '. Pick rows that add up to the target; write their labels, like y1 z2.',
      { table: [['label', 'p', 'q', 'r', 'clause 1', 'clause 2']].concat(SSRed.table.rows.map((r) => [r.label].concat(r.digits))).concat([['target'].concat(SSRed.table.targetDigits)]) }],
    accept(w) {
      this.whyNot = '';
      const toks = String(w).split(/[\s,+]+/).filter(Boolean);
      const idx = toks.map((t) => SSlabels.indexOf(t.toLowerCase()));
      if (idx.some((i) => i < 0)) { this.whyNot = 'Use the labels of the table: ' + SSlabels.join(', ') + '.'; return false; }
      const r = T.cx.verifySubsetSum(SSRed.nums, SSRed.target, idx);
      if (!r.ok) this.whyNot = reason(r, []);
      return r.ok;
    },
    why: 'The y and z rows you took are a satisfying assignment.',
    solution: 'y1 z2 z3 g1 g2 h2', wrong: ['y1 z2 z3', 'y1 y2 y3 g1 g2', 'y1 z1 z2 z3 g2 h2'],
    hints: H('Pick an assignment that satisfies φ, say p = 1, q = 0, r = 0: rows y1, z2, z3.', 'Add up the clause columns: clause 1 gets 2 true literals, clause 2 gets 1. Each must reach 3.', 'y1 z2 z3, then g1 for clause 1, and g2 h2 for clause 2.') });
  const CF3 = F('(a ∨ b ∨ ¬c) ∧ (¬a ∨ c) ∧ (b ∨ c ∨ d)');
  ex({ id: 'cx-ex-3col-size', chapter: CH4, title: 'Size of the colouring graph', kind: 'number', level: 2,
    text: 'The 3SAT → 3-COLOUR reduction uses a palette triangle, two vertices per variable, and two OR gadgets of three vertices per clause. How many vertices does it build for φ = ' + show(CF3) + '?',
    answer: 29, why: '3 + 2 · 4 + 6 · 3 = 29.', solution: '29', wrong: ['17', '23', '35'],
    hints: H('The palette: T, F, B.', 'Each variable: x and ¬x. Each clause: two gadgets of u, v, o.', '3 + 8 + 18 = 29.') });
  ex({ id: 'cx-ex-3col-or', chapter: CH4, title: 'Inside an OR gadget', kind: 'choice', level: 2,
    text: 'An OR gadget has inputs x and y, inner vertices u and v joined to each other, u joined to x, v joined to y, and output o joined to u and v. Both inputs are coloured F. What colour can o get?',
    options: ['Only T', 'Only F', 'Only B', 'T or B'], answer: 1,
    why: 'u and v avoid F and each other, so they take T and B; o must differ from both.',
    solution: 1, wrong: [0, 3], hints: H('u is next to x, which is F.', 'u and v both avoid F and differ from each other.', 'They are T and B, so o is F: the output cannot be T when no input is.') });
  const HPF = F('(a ∨ b ∨ ¬c) ∧ (¬a ∨ c)');
  ex({ id: 'cx-ex-ham-size', chapter: CH4, title: 'Size of the HAM-PATH graph', kind: 'number', level: 2,
    text: 'In the 3SAT → HAM-PATH reduction, each variable gets a top vertex, a bottom vertex and a row of 3m + 1 vertices (m = number of clauses), and each clause one vertex. How many vertices for φ = ' + show(HPF) + '?',
    answer: 29, why: 'n(3m + 3) + m = 3 · 9 + 2 = 29.', solution: '29', wrong: ['21', '27', '23'],
    hints: H('Here n = 3 and m = 2.', 'Each variable: 1 + (3 · 2 + 1) + 1 = 9 vertices.', '3 · 9 + 2 = 29.') });
  ex({ id: 'cx-ex-ham-direction', chapter: CH4, title: 'Which way across?', kind: 'choice',
    text: 'In the 3SAT → HAM-PATH graph, what decides the value of a variable in the assignment read off a Hamiltonian path?',
    options: ['The direction in which the path crosses the variable\'s row', 'Whether the path visits the variable\'s row at all', 'How many clause vertices it visits', 'The colour of the row'], answer: 0,
    solution: 0, wrong: [1, 2], hints: H('The path must visit every vertex, so it crosses every row.', 'Each row can be crossed in two directions.', 'Left to right is true, right to left false.') });

  // =========================================================================================================
  // Chapter 5: Cook–Levin
  // =========================================================================================================
  const CH5 = 'cx-ch-cook';
  const GUESS = 'start: g\naccept: yes\ng, 0 -> c0, 0, R\ng, 0 -> c1, 1, R\ng, 1 -> c0, 0, R\ng, 1 -> c1, 1, R\nc0, 0 -> yes, 0, S\nc1, 1 -> yes, 1, S';
  const guessText = { code: GUESS, lang: 'machine' };
  ex({ id: 'cx-ex-cook-table', chapter: CH5, title: 'Count the Cook–Levin formula', kind: 'table', table: 'custom', level: 2,
    text: ['The machine below has tape symbols 0, 1, ⊔ and states g, c0, c1, yes, so with # there are K = 8 symbols. Build the tableau for input w = 010 and time bound t = 3, and count.', guessText, 'A row has W = C + 3 columns with C = max(|w|, t + 1).'],
    rows: ['rows of the tableau', 'columns W', 'cells', 'cell clauses', 'start clauses', 'window positions'], cols: ['how many'], corner: '',
    cells: { 'rows of the tableau|how many': '4', 'columns W|how many': '7', 'cells|how many': '28', 'cell clauses|how many': '812', 'start clauses|how many': '7', 'window positions|how many': '15' },
    solution: { 'rows of the tableau|how many': '4', 'columns W|how many': '7', 'cells|how many': '28', 'cell clauses|how many': '812', 'start clauses|how many': '7', 'window positions|how many': '15' },
    wrong: [{ 'rows of the tableau|how many': '3', 'columns W|how many': '6', 'cells|how many': '18', 'cell clauses|how many': '522', 'start clauses|how many': '6', 'window positions|how many': '12' },
      { 'rows of the tableau|how many': '4', 'columns W|how many': '7', 'cells|how many': '28', 'cell clauses|how many': '784', 'start clauses|how many': '7', 'window positions|how many': '15' }],
    hints: H('Rows: t + 1. C = max(3, 4) = 4, so W = 7.', 'Per cell: 1 + 8 · 7 / 2 = 29 clauses. Start: one per column. Windows: t rows of W − 2 positions.', '4, 7, 28, 28 · 29 = 812, 7, 3 · 5 = 15.') });
  ex({ id: 'cx-ex-cook-cellclauses', chapter: CH5, title: 'Clauses for one cell', kind: 'number', level: 2,
    text: 'A machine\'s tableau uses K = 10 symbols. How many cell clauses does one cell need, to say it holds exactly one symbol?',
    answer: 46, why: '1 + 10 · 9 / 2 = 46.', solution: '46', wrong: ['10', '45', '100'],
    hints: H('One clause says "at least one symbol".', 'One clause per pair of symbols says "not both".', '1 + 45 = 46.') });
  ex({ id: 'cx-ex-cook-accept', chapter: CH5, title: 'The accept clause', kind: 'number', level: 3,
    text: ['For the guessing machine below (one accepting state, yes), input w = 11 and time bound t = 4, the accept clause is one big OR of the variables x(i, j, yes) over all cells. How many literals does it have?', guessText],
    answer: 40, why: 'C = max(2, 5) = 5, W = 8, rows = 5: 5 · 8 = 40 cells, one literal each.', solution: '40', wrong: ['32', '5', '8'],
    hints: H('One literal per cell, for each accepting state.', 'Rows: t + 1 = 5. C = max(|w|, t + 1) = 5, W = C + 3 = 8.', '5 · 8 · 1 = 40.') });
  ex({ id: 'cx-ex-cook-window', chapter: CH5, title: 'Legal windows', kind: 'choice', level: 3,
    text: ['For the guessing machine below, which of these 2 × 3 windows (top row over bottom row) are legal? A state is written just left of the cell the head reads.', guessText],
    options: ['`# g 0` over `# 1 c1`', '`0 1 ⊔` over `0 0 ⊔`', '`1 ⊔ ⊔` over `1 ⊔ ⊔`', '`# g 0` over `# 0 c1`', '`c0 0 ⊔` over `yes 0 ⊔`', '`g 1 ⊔` over `g 1 ⊔`'], answer: [0, 2, 4],
    why: 'A window is legal when one move of the machine (or no change, away from the head) can produce its bottom row from its top row.',
    solution: [0, 2, 4], wrong: [[0, 2], [0, 2, 3, 4], [0, 1, 2, 4]],
    hints: H('Away from the head nothing may change.', 'g reading 0 has two moves: to c0 writing 0, or to c1 writing 1, both moving right.', 'Legal: the first (g, 0 → c1, 1, R), the third (nothing near the head), the fifth (c0, 0 → yes, 0, stay).') });
  ex({ id: 'cx-ex-cook-poly', chapter: CH5, title: 'Why the formula is small', kind: 'choice', level: 2,
    text: 'A machine N decides a language in nondeterministic time nᵏ. Why is the Cook–Levin formula for an input of length n polynomial in n?',
    options: ['The tableau has O(n²ᵏ) cells and each needs a constant number of clauses, because K and the legal windows depend only on N', 'Because SAT is in NP', 'Because the formula only describes one accepting branch, found in advance', 'It is not: the formula is exponential, but that is allowed'], answer: 0,
    solution: 0, wrong: [2, 3], hints: H('The reduction must run in polynomial time, without knowing which branch accepts.', 'Count rows, columns and clauses per cell or window.', '(nᵏ + 1) rows by O(nᵏ) columns, a constant number of clauses each.') });

  // =========================================================================================================
  // Chapter 6: coping, space and the map
  // =========================================================================================================
  const CH6 = 'cx-ch-space';
  ex({ id: 'cx-ex-approx-run', chapter: CH6, title: 'Run the approximation', kind: 'number',
    text: 'The approximation for VERTEX COVER looks at the edges 1-2, 2-3, 3-4, 4-1, 1-5 in this order. Whenever an edge is not yet covered it adds both of its ends. How many vertices does the cover it returns have?',
    answer: 4, why: '1-2 adds {1, 2}; 2-3 is covered; 3-4 adds {3, 4}; 4-1 and 1-5 are covered. The best cover, {1, 3}, has 2.',
    solution: '4', wrong: ['2', '5', '3'],
    hints: H('Start with 1-2: both ends go in.', 'Skip every edge that already has an end in the cover.', '{1, 2, 3, 4}: 4 vertices, exactly twice the best.') });
  ex({ id: 'cx-ex-approx-why', chapter: CH6, title: 'Why within twice the best?', kind: 'choice', level: 2,
    text: 'Why does the edge-picking approximation never return more than twice as many vertices as the smallest vertex cover?',
    options: ['The picked edges share no ends, so any cover needs a different vertex for each of them, while we take two per edge', 'Because it chooses vertices of high degree first', 'Because every graph has a cover of half its vertices', 'It can be worse than twice the best on some graphs'], answer: 0,
    solution: 0, wrong: [1, 3], hints: H('Once an edge is picked, both its ends are in the cover, so no later picked edge touches them.', 'The picked edges form a matching. How many vertices must any cover take from a matching of size m?', 'At least m; we take 2m.') });
  const TREE = { pos: { 0: [150, 25], 1: [70, 95], 2: [150, 95], 3: [230, 95], 4: [30, 170], 5: [110, 170], 6: [230, 170], 7: [190, 245], 8: [270, 245] }, edges: '0-1 0-2 0-3 1-4 1-5 3-6 6-7 6-8' };
  ex({ id: 'cx-ex-tree-vc', chapter: CH6, title: 'Cover a tree', kind: 'number', level: 2,
    text: ['How many vertices does the smallest vertex cover of this tree have?', { svg: K.svg(TREE.pos, TREE.edges, { label: 'A tree with nine vertices' }) }],
    answer: 3, why: '{0, 1, 6} covers every edge, and the three disjoint edges 1-4, 0-2, 6-7 need three different vertices.',
    solution: '3', wrong: ['2', '4', '5'],
    hints: H('A leaf\'s edge is covered best by the leaf\'s parent.', 'Take the parents of leaves: 1 (for 4, 5), 0 (for 2), 6 (for 7, 8).', '{0, 1, 6} covers all eight edges: 3.') });
  ex({ id: 'cx-ex-branch-leaves', chapter: CH6, title: 'How big is the search tree?', kind: 'number',
    text: 'The branching search for VERTEX COVER picks an uncovered edge u-v and branches on putting u or v in the cover. With budget k = 6, at most how many leaves can its tree have?',
    answer: 64, solution: '64', wrong: ['6', '12', '720'],
    hints: H('Every branch spends one unit of the budget.', 'The tree is binary with depth at most k.', '2⁶ = 64.') });
  const QB = (pre, mat) => { const f = F(mat); return T.cx.tqbf(pre.split(' ').map((t) => ({ q: t[0] === '∃' ? 'E' : 'A', v: f.names.indexOf(t.slice(1)) })), f); };
  ex({ id: 'cx-ex-tqbf-1', chapter: CH6, title: 'Who wins this game?', kind: 'choice', level: 2,
    text: 'Is ∀p ∃q ∀r : (p ∨ q ∨ r) ∧ (¬p ∨ ¬q) ∧ (q ∨ ¬r ∨ p) true?',
    options: ['True: for each p the ∃-player has a q that works for both values of r', 'False: the ∀-player wins by choosing p = 0', 'False: the ∀-player wins by choosing r after q'], answer: QB('∀p ∃q ∀r', '(p ∨ q ∨ r) ∧ (¬p ∨ ¬q) ∧ (q ∨ ¬r ∨ p)').value ? 0 : 1,
    why: 'p = 0: take q = 1. p = 1: take q = 0. Either way every clause holds for both values of r.',
    solution: 0, wrong: [1, 2], hints: H('Play both values of p.', 'If p = 0, the first and last clauses need q (r cannot be relied on).', 'q = ¬p wins: true.') });
  const QM = QB('∃a ∀b ∃c', '(¬a ∨ b) ∧ (a ∨ ¬b ∨ c) ∧ (¬c ∨ ¬a)');
  ex({ id: 'cx-ex-tqbf-move', chapter: CH6, title: 'The winning first move', kind: 'string', level: 3,
    text: 'In ∃a ∀b ∃c : (¬a ∨ b) ∧ (a ∨ ¬b ∨ c) ∧ (¬c ∨ ¬a), the ∃-player moves first. Which value of a wins? Write a=0 or a=1.',
    accept(w) { const t = String(w).replace(/\s/g, '').toLowerCase(); const v = /^(a=)?(1|t|true)$/.test(t) || t === 'a' ? 1 : /^(a=)?(0|f|false)$/.test(t) || /^[¬~!-]a$/.test(t) ? 0 : -1; return v === (QM.nodes[0].best ? 1 : 0); },
    whyNot: 'Play it out: after your a, try both values of b.',
    solution: 'a=0', wrong: ['a=1', 'b=0', 'c=1'],
    hints: H('If a = 1, the first clause needs b = 1, and the ∀-player can pick b = 0.', 'With a = 0 the first and last clauses hold; the middle one needs ¬b ∨ c.', 'a = 0, then c = 1 answers either b: a=0.') });
  ex({ id: 'cx-ex-space-facts', chapter: CH6, title: 'Facts about space', kind: 'choice', level: 2,
    text: 'Choose every true statement.',
    options: ['NP ⊆ PSPACE', 'PSPACE = NPSPACE', 'Savitch\'s theorem shows L = NL', 'TQBF is PSPACE-complete', 'A machine that uses space s(n) halts within s(n) steps'], answer: [0, 1, 3],
    solution: [0, 1, 3], wrong: [[0, 1, 2, 3], [0, 3], [0, 1, 3, 4]],
    hints: H('Space can be reused: try every certificate on the same cells.', 'Savitch squares the space, which keeps polynomials polynomial but turns log n into log² n.', 'True: the first, second and fourth. A machine can take far more steps than cells, up to 2^O(s(n)).') });
  ex({ id: 'cx-ex-savitch', chapter: CH6, title: 'Levels of halving', kind: 'number', level: 2,
    text: 'Savitch\'s recursion asks "can u reach v in at most 2ᵏ steps?" at the top, with 2ᵏ at least the number of vertices. For a graph of 30 vertices, what is the smallest such k: how many levels of halving are there?',
    answer: 5, why: '2⁵ = 32 ≥ 30 > 16 = 2⁴.', solution: '5', wrong: ['4', '30', '15'],
    hints: H('A path that repeats no vertex has fewer than 30 steps.', 'You need 2ᵏ ≥ 30.', '2⁴ = 16 is too small, 2⁵ = 32 is enough: k = 5.') });
  ex({ id: 'cx-ex-lnl', chapter: CH6, title: 'What fits in log space', kind: 'choice', level: 2,
    text: 'The NL machine for directed reachability works in O(log n) space. What does it keep on its work tape?',
    options: ['The current vertex and a counter of steps taken', 'The set of vertices visited so far', 'The whole path walked so far', 'A copy of the graph'], answer: 0,
    why: 'Each fits in O(log n) bits. A set of visited vertices could need n bits.',
    solution: 0, wrong: [1, 2], hints: H('How many bits does a vertex name take?', 'log n bits each; a set of vertices may need n bits.', 'The current vertex and a counter.') });
  ex({ id: 'cx-ex-classify', chapter: CH6, title: 'Place the problems on the map', kind: 'table', table: 'custom', level: 2,
    text: 'For each problem, write the class it is complete for or known to lie in: P, NP-complete, PSPACE-complete, or undecidable.',
    rows: ['PATH', '2-SAT', '3-COLOUR', 'SUBSET SUM', 'TQBF', 'HALT (does M halt on w?)', 'TRIANGLE (a clique of exactly 3 vertices)'], cols: ['class'], corner: 'problem',
    cells: { 'PATH|class': 'P', '2-SAT|class': 'P', '3-COLOUR|class': 'NP-complete', 'SUBSET SUM|class': 'NP-complete', 'TQBF|class': 'PSPACE-complete', 'HALT (does M halt on w?)|class': 'undecidable', 'TRIANGLE (a clique of exactly 3 vertices)|class': 'P' },
    solution: { 'PATH|class': 'P', '2-SAT|class': 'P', '3-COLOUR|class': 'NP-complete', 'SUBSET SUM|class': 'NP-complete', 'TQBF|class': 'PSPACE-complete', 'HALT (does M halt on w?)|class': 'undecidable', 'TRIANGLE (a clique of exactly 3 vertices)|class': 'P' },
    wrong: [{ 'PATH|class': 'P', '2-SAT|class': 'NP-complete', '3-COLOUR|class': 'NP-complete', 'SUBSET SUM|class': 'NP-complete', 'TQBF|class': 'PSPACE-complete', 'HALT (does M halt on w?)|class': 'undecidable', 'TRIANGLE (a clique of exactly 3 vertices)|class': 'P' },
      { 'PATH|class': 'P', '2-SAT|class': 'P', '3-COLOUR|class': 'NP-complete', 'SUBSET SUM|class': 'NP-complete', 'TQBF|class': 'NP-complete', 'HALT (does M halt on w?)|class': 'undecidable', 'TRIANGLE (a clique of exactly 3 vertices)|class': 'NP-complete' }],
    hints: H('2-SAT and fixed-size cliques are the easy cousins of NP-complete problems.', 'TQBF is the game version of SAT; HALT has no decider at all.', 'P, P, NP-complete, NP-complete, PSPACE-complete, undecidable, P.') });
  const CLS = ['L', 'NL', 'P', 'NP', 'PSPACE', 'EXPTIME'];
  ex({ id: 'cx-ex-class-order', chapter: CH6, title: 'The chain of classes', kind: 'string', placeholder: 'A ⊆ B ⊆ …',
    text: 'Write the classes P, PSPACE, L, EXPTIME, NL and NP in a chain from smallest to largest, each contained in the next, like A ⊆ B ⊆ ….',
    accept(w) { const got = String(w).toUpperCase().split(/[^A-Z]+/).filter(Boolean); return got.length === CLS.length && got.every((c, i) => c === CLS[i]); },
    whyNot: 'Start with the log-space classes and end with exponential time.',
    solution: 'L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME', wrong: ['NL ⊆ L ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME', 'L ⊆ NL ⊆ P ⊆ PSPACE ⊆ NP ⊆ EXPTIME', 'L ⊆ NL ⊆ P ⊆ NP ⊆ EXPTIME'],
    hints: H('Determinism is a special case of nondeterminism.', 'Log space runs in polynomial time; polynomial space runs in exponential time.', 'L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME.') });
  ex({ id: 'cx-ex-separations', chapter: CH6, title: 'What is actually known?', kind: 'choice', level: 3,
    text: 'Which of these separations have been proved?',
    options: ['P ≠ EXPTIME', 'NL ≠ PSPACE', 'P ≠ NP', 'L ≠ P', 'NP ≠ PSPACE'], answer: [0, 1],
    why: 'Both follow from the hierarchy theorems (with Savitch for NL). The others are open.',
    solution: [0, 1], wrong: [[0, 1, 2], [0], [0, 1, 4]],
    hints: H('The hierarchy theorems separate classes with very different amounts of the same resource.', 'Time n^k against time 2^n; space log² n against polynomial space.', 'Only P ≠ EXPTIME and NL ≠ PSPACE.') });
})();
