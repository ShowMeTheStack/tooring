// Part 7, complexity: chapters, lessons, a guided tour and a course. The exercises are in 71-complexity-ex.js.
// Lessons lean on the topics of src/topics/complexity-*.js, each embedded with an input chosen for the point
// being made.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const K = (T.cxContent = T.cxContent || {});

  // ---- small figures: a graph drawn as an SVG that follows the theme ------------------------------------
  // pos: {name: [x, y]}; edges: 'a-b c>d' (- both ways, > one way); o: {hi: [names], r, label}
  let svgCount = 0;
  K.edgeList = (text) => String(text).trim().split(/[\s,]+/).filter(Boolean).map((e) => { const m = e.match(/^(.+?)(-|>|→)(.+)$/); return { a: m[1], b: m[3], dir: m[2] !== '-' }; });
  K.svg = function (pos, edges, o = {}) {
    const id = 'cxarrow' + ++svgCount, R = o.r || 16, pad = R + 4;
    const P = Object.values(pos), xs = P.map((p) => p[0]), ys = P.map((p) => p[1]);
    const x0 = Math.min(...xs) - pad, y0 = Math.min(...ys) - pad, W = Math.max(...xs) + pad - x0, H = Math.max(...ys) + pad - y0;
    const hi = new Set(o.hi || []), list = K.edgeList(edges);
    let s = `<svg viewBox="${x0} ${y0} ${W} ${H}" width="${W}" height="${H}" role="img" aria-label="${o.label || 'A graph'}" style="font-family: var(--mono); font-size: ${o.fs || 14}px">`;
    if (list.some((e) => e.dir)) s += `<defs><marker id="${id}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" style="fill: var(--edge)"/></marker></defs>`;
    for (const e of list) {
      const [ax, ay] = pos[e.a], [bx, by] = pos[e.b], d = Math.hypot(bx - ax, by - ay) || 1;
      const ux = (bx - ax) / d, uy = (by - ay) / d, end = e.dir ? R + 2 : R;
      s += `<line x1="${ax + ux * R}" y1="${ay + uy * R}" x2="${bx - ux * end}" y2="${by - uy * end}" style="stroke: var(--edge); stroke-width: 1.6"${e.dir ? ` marker-end="url(#${id})"` : ''}/>`;
    }
    for (const [name, [x, y]] of Object.entries(pos)) {
      const on = hi.has(name);
      s += `<circle cx="${x}" cy="${y}" r="${R}" style="fill: var(${on ? '--act-soft' : '--node'}); stroke: var(${on ? '--act' : '--node-line'}); stroke-width: ${on ? 2.4 : 1.6}"/>`;
      s += `<text x="${x}" y="${y + 5}" text-anchor="middle" style="fill: var(--node-text)">${name}</text>`;
    }
    return s + '</svg>';
  };
  /** The graph of a figure as the engines want it: {n, edges, directed, names} */
  K.graph = (pos, edges) => {
    const names = Object.keys(pos), list = K.edgeList(edges);
    return { n: names.length, names, directed: list.some((e) => e.dir), edges: list.map((e) => [names.indexOf(e.a), names.indexOf(e.b)]) };
  };

  // the graphs used by lessons and exercises
  K.G1 = { pos: { a: [200, 190], b: [200, 90], c: [300, 240], d: [200, 20], e: [100, 240], f: [370, 300], g: [30, 300] }, edges: 'a-b a-c a-e b-c b-d b-e c-e c-f d-f e-g f-g d-g' };
  K.G2 = { pos: { a: [30, 40], b: [140, 40], c: [250, 40], d: [30, 140], e: [140, 140], f: [250, 140] }, edges: 'a-b a-d b-c b-e c-f d-e e-f' };
  K.G3 = { pos: { a: [70, 230], b: [70, 40], c: [160, 135], d: [240, 40], e: [300, 150], f: [390, 215], g: [290, 290], h: [20, 300] }, edges: 'a-b b-c c-a c-d d-e e-c e-f f-g g-e g-h h-a b-h' };

  // ---- chapters --------------------------------------------------------------------------------------------
  const P = 'complexity';
  C.chapter({ id: 'cx-ch-time', part: P, n: 1, title: 'Measuring time', blurb: 'Steps on a Turing machine, growth rates and big-O, and why the way an input is written matters.' });
  C.chapter({ id: 'cx-ch-np', part: P, n: 2, title: 'P and NP', blurb: 'Problems solved in polynomial time, answers checked in polynomial time, guessing machines, and the question of whether the two differ.' });
  C.chapter({ id: 'cx-ch-sat', part: P, n: 3, title: 'Satisfiability', blurb: 'Formulas in CNF, the DPLL search with its forced moves, and 2-SAT solved through a graph of implications.' });
  C.chapter({ id: 'cx-ch-red', part: P, n: 4, title: 'Reductions as gadgets', blurb: 'Polynomial reductions, and formulas turned into graphs, numbers, colourings and paths.' });
  C.chapter({ id: 'cx-ch-cook', part: P, n: 5, title: 'The Cook–Levin theorem', blurb: 'Any nondeterministic polynomial-time computation becomes a formula: the tableau, its windows, and the count of clauses.' });
  C.chapter({ id: 'cx-ch-space', part: P, n: 6, title: 'Coping, space and the map', blurb: 'What to do with a hard problem, then space as a resource: PSPACE, TQBF, Savitch, L and NL, and the map of the classes.' });

  const L = (x) => C.lesson(x);

  // =========================================================================================================
  // Chapter 1: measuring time
  // =========================================================================================================
  L({
    id: 'cx-l-steps', chapter: 'cx-ch-time', title: 'Time is a count of steps', minutes: 10,
    summary: 'The running time of a machine is the largest number of steps it takes on any input of length n, written as a function of n.',
    blocks: [
      'Two programs can give the same answers and still be worlds apart: one finishes before you look up, the other is still running when the sun burns out. Computability asked *can it be done at all*. Complexity asks *what does it cost*.',
      'To talk about cost without arguing about which laptop is faster, we count **steps of a Turing machine**. One step is one move: read a cell, write, move the head, change state. The count depends on the input, so we group inputs by their length.',
      { def: 'Running time', text: 'a decider M runs in time t(n) when, for every n, every input of length n makes M halt within t(n) steps. Its exact running time is the **largest** step count over all inputs of length n: the worst case.' },
      { h: 'Watch the steps pile up' },
      { topic: 'cx-steps', input: { m: 'anbn', w: 'aabb', n: 6 }, caption: 'The machine for aⁿbⁿ crosses off one a and one b per pass. Watch the head sweep back and forth on aabb, then look at the bar for each length: the tallest input of each length sets t(n).' },
      { predict: { q: 'On the input ba the same machine rejects after a couple of steps. Does that make its running time for length 2 small?', options: ['Yes: the time for length 2 is the time on ba', 'No: the running time takes the worst input of each length, here ab or aa', 'It depends on the computer'], answer: 1, explain: 'The running time is a promise about every input of a length. One quick rejection does not lower it; the slowest input of length 2 does.' } },
      'Try it yourself. The machine below remembers the first symbol in its state, runs to the end and compares. Count its steps on strings of a few lengths: an accepted input of length n always takes n + 2 steps, and a rejected one never takes more, so its running time is t(n) = n + 2 for n ≥ 1.',
      { sandbox: { kind: 'tm', text: 'start: s\naccept: yes\ns, a -> ra, a, R\ns, b -> rb, b, R\nra, a -> ra, a, R\nra, b -> ra, b, R\nra, _ -> ca, _, L\nrb, a -> rb, a, R\nrb, b -> rb, b, R\nrb, _ -> cb, _, L\nca, a -> yes, a, S\ncb, b -> yes, b, S', input: 'abba' }, caption: 'Run it on abba, then on abab and on a, and compare the step counts with the lengths.' },
      { h: 'A second tape changes the count, but not by much' },
      'Is the count a property of the problem or of the machine? Both. A one-tape machine for palindromes has to shuttle to and fro, about n² steps. With a second tape it copies the input once and compares, about n steps.',
      { topic: 'cx-multitape', input: { w: 'abaaba' }, caption: 'Left: one tape zig-zags. Right: two tapes copy and compare in a single pass. Compare the step counters at the end.' },
      'The gap is never worse than squaring: a one-tape machine can simulate t(n) steps of a many-tape machine in O(t(n)²) steps. Squaring keeps a polynomial a polynomial, which is why the classes that follow do not depend on how many tapes we allow.',
      { warn: 'Running time is a worst case over **all** inputs of a length, not the time on the input you happen to try, and not an average.' },
      { list: ['Time = number of steps, as a function t(n) of the input length n.', 'Worst case over all inputs of that length.', 'Changing the model (more tapes) can change t(n), but at most polynomially.'] },
      { exercise: 'cx-ex-steps-anbn' }, { exercise: 'cx-ex-tm-linear' }, { exercise: 'cx-ex-twotape' },
    ],
  });

  L({
    id: 'cx-l-growth', chapter: 'cx-ch-time', title: 'Growth rates and big-O', minutes: 12,
    summary: 'Big-O keeps the shape of a running time and throws away constants and small terms. The shapes form a ladder: logarithms, polynomials, exponentials, factorials.',
    blocks: [
      'Exact step counts like 3n² + 7n + 2 are fussy and depend on tiny design choices. What matters for large inputs is the **shape** of the curve. Big-O notation keeps the shape and drops the rest.',
      { def: 'Big-O', text: 'f(n) = O(g(n)) when there are constants c > 0 and n₀ such that f(n) ≤ c · g(n) for every n ≥ n₀. In words: from some point on, f is at most a constant multiple of g.' },
      { def: 'Little-o and Θ', text: 'f = o(g) when f(n)/g(n) → 0: f grows strictly slower. f = Θ(g) when f = O(g) and g = O(f): the same rate up to constants.' },
      { h: 'A race between curves' },
      { topic: 'cx-growth', input: { race: 'consts' }, caption: '100·n starts far ahead of n². Watch where n² overtakes it: after that point the constant 100 never helps again.' },
      { predict: { q: 'At n = 10, which is bigger: n³ or 2ⁿ?', options: ['n³ = 1000 is bigger', '2ⁿ = 1024 is bigger', 'They are equal'], answer: 1, explain: '2¹⁰ = 1024 just beats 10³ = 1000, and from n = 10 on, 2ⁿ stays ahead for good. Below that, n³ is ahead (at n = 9: 729 against 512).' } },
      { topic: 'cx-growth', input: { race: 'polyexp' }, caption: 'n³ against 2ⁿ: the exponential looks harmless for small n, then leaves the polynomial behind for ever.' },
      'Here is what the shapes mean in time, at a billion steps a second:',
      { table: [['t(n)', 'n = 10', 'n = 50', 'n = 100'], ['n²', '0.1 µs', '2.5 µs', '10 µs'], ['n³', '1 µs', '125 µs', '1 ms'], ['2ⁿ', '1 µs', '13 days', '40 trillion years'], ['n!', '3.6 ms', 'about 10⁴⁸ years', 'far beyond'], ], caption: 'Polynomials stay reasonable; exponentials do not.' },
      { h: 'Reading big-O off real counts' },
      { topic: 'cx-bigo', input: { m: 'anbn', n: '24' }, caption: 'The measured worst-case steps of the aⁿbⁿ machine, divided by candidate shapes. The shape whose ratio settles to a constant is the machine\'s growth rate.' },
      { tip: 'Constants and lower-order terms disappear: 5n³ + 40n² + 9 = O(n³). The base of a logarithm disappears too, since log₂ n = log₂ 10 · log₁₀ n.' },
      { warn: 'Big-O is only an upper bound. n = O(n²) is true, just not very informative. When you want the exact rate, say Θ.' },
      { list: ['f = O(g): f is eventually at most c · g.', 'The ladder: 1, log n, √n, n, n log n, n², n³, …, 2ⁿ, n!.', 'Any polynomial is o(any exponential cⁿ with c > 1); any power of log n is o(any nᵉ with e > 0).'] },
      { exercise: 'cx-ex-order-1' }, { exercise: 'cx-ex-order-2' }, { exercise: 'cx-ex-bigo-true' }, { exercise: 'cx-ex-bigo-n0' }, { exercise: 'cx-ex-crossover' }, { exercise: 'cx-ex-poly-closure' },
    ],
  });

  L({
    id: 'cx-l-encoding', chapter: 'cx-ch-time', title: 'Encodings: what counts as the input size', minutes: 8,
    summary: 'Running time is measured against the length of the input as written. Write a number in unary and a slow algorithm looks fast; reasonable encodings are all within a polynomial of each other.',
    blocks: [
      'Is a number prime? Try every divisor from 2 up to √N. That is about √N divisions. Is that fast?',
      'It depends on what n is. Time is always measured against the **length of the input**, and a number N written in binary takes only about log₂ N digits. With b digits, √N is about 2^(b/2): exponential in the input length.',
      { topic: 'cx-encoding', input: { N: 65521 }, caption: 'Trial division on a prime of 17 binary digits. Watch the count of divisions against the length of N in binary and in unary.' },
      { predict: { q: 'If N were written in unary (N strokes), would trial division be polynomial in the input length?', options: ['Yes: √N divisions for an input of length N', 'No: it is exponential either way'], answer: 0, explain: 'In unary the input has length N, and √N is less than N. The algorithm did not get faster; the input got exponentially longer.' } },
      { def: 'Reasonable encoding', text: 'a way of writing instances as strings in which any two reasonable choices can be converted into each other in polynomial time. Numbers in binary or decimal, graphs as lists of vertices and edges, or as adjacency matrices, are all reasonable. Numbers in unary are not: they are exponentially longer than needed.' },
      { math: 'length of N in binary = ⌊log₂ N⌋ + 1\nlength of N in unary  = N' },
      { warn: 'An algorithm that is polynomial in the **value** of a number but not in its length is called pseudo-polynomial. Trial division is one; so is the table method for SUBSET SUM that runs in time proportional to the target.' },
      { list: ['Measure time against the length of a reasonable encoding.', 'Binary and decimal are fine; unary is cheating.', 'Pseudo-polynomial means polynomial in the values, exponential in their length.'] },
      { exercise: 'cx-ex-encoding-bits' }, { exercise: 'cx-ex-unary' },
    ],
  });

  // =========================================================================================================
  // Chapter 2: P and NP
  // =========================================================================================================
  L({
    id: 'cx-l-p', chapter: 'cx-ch-np', title: 'The class P', minutes: 12,
    summary: 'P is the set of problems decided in polynomial time. It does not change with the model, it is closed under composition, and it is our working definition of feasible.',
    blocks: [
      { def: 'P', text: 'the class of languages decided by a deterministic one-tape Turing machine in time O(nᵏ) for some constant k. In short, P = TIME(n) ∪ TIME(n²) ∪ TIME(n³) ∪ …' },
      'Why draw the line at polynomials? Not because n¹⁰⁰ is fast. It is because polynomials are **robust**: the class stays the same with many tapes, random-access memory, or any reasonable encoding, since each of those changes the time by at most a polynomial. And a polynomial-time procedure that calls another one a polynomial number of times is still polynomial.',
      { h: 'Reachability: smarter than trying every path' },
      'Is there a path from s to t? Trying every path could take exponentially long. Breadth-first search marks each vertex once and looks at each edge once.',
      { topic: 'cx-path', input: { g: 's>a a>b t>b b>c c>s', s: 's', t: 't' }, caption: 'One-way streets: s can reach a, b and c, but no edge leads into t from them. Watch the marked set stop growing without t in it.' },
      { predict: { q: 'BFS on a graph with m vertices marks each vertex at most once. How many rounds of "mark everything next to a marked vertex" can there be before nothing new is marked?', options: ['At most m', 'At most 2ᵐ', 'At most m!'], answer: 0, explain: 'Each useful round marks at least one new vertex, so there are at most m rounds, each polynomial: PATH is in P.' } },
      { h: 'Euclid: polynomial in the digits' },
      { topic: 'cx-gcd', input: { a: 144, b: 89 }, caption: 'Consecutive Fibonacci numbers are Euclid\'s slowest case. Even here the numbers shrink by at least half every two steps, so the steps grow with the number of digits, not the value.' },
      'Deciding whether two numbers are relatively prime by trying all divisors would be exponential in the number of digits. Euclid\'s algorithm is linear in the number of digits, so RELPRIME is in P.',
      { h: 'Every context-free language is in P' },
      { topic: 'cx-cyk-work', input: { w: 'aabbab' }, caption: 'CYK fills a triangle of about n²/2 cells, and each cell tries fewer than n split points: O(n³) work for a fixed grammar.' },
      { sandbox: { kind: 'grammar', text: 'S → A B | A C | S S\nC → S B\nA → a\nB → b', input: 'aabbab' }, caption: 'The same grammar to test on your own strings: membership is a polynomial-time question.' },
      { list: ['P = polynomial time on a deterministic machine.', 'Robust under the choice of model and encoding.', 'PATH, RELPRIME and every context-free language are in P.'] },
      { exercise: 'cx-ex-bfs-layer' }, { exercise: 'cx-ex-euclid' }, { exercise: 'cx-ex-cyk-splits' }, { exercise: 'cx-ex-in-p' },
    ],
  });

  L({
    id: 'cx-l-verify', chapter: 'cx-ch-np', title: 'NP: answers that are easy to check', minutes: 12,
    summary: 'A problem is in NP when every yes-instance has a short certificate that a polynomial-time verifier can check.',
    blocks: [
      'Finding a group of four people who all know each other in a big friendship graph may take a long search. But if someone hands you four names, checking them is quick: look at the six pairs. That gap between **finding** and **checking** is what NP is about.',
      { def: 'Verifier', text: 'an algorithm V that takes an input w and a certificate c. A language A has a polynomial-time verifier V when w ∈ A exactly if there is some c with V(w, c) = accept, and V runs in time polynomial in |w| (so c can be at most polynomially long).' },
      { def: 'NP', text: 'the class of languages that have polynomial-time verifiers.' },
      { topic: 'cx-verify', input: { problem: 'clique', cert: '0 1 2 3' }, inputs: true, caption: 'The verifier checks a claimed clique pair by pair. Watch it stop at the first pair with no edge: one missing edge is enough to reject this certificate. Then type a certificate of your own.' },
      { predict: { q: 'The verifier rejects the certificate 0 1 2 3. Does that prove the graph has no clique of size 4?', options: ['Yes', 'No: another certificate might pass'], answer: 1, explain: 'A rejected certificate only says this certificate is wrong. The definition needs just one certificate to pass for a yes-instance; a no-instance is one where none passes.' } },
      { topic: 'cx-verify', input: { problem: 'hampath', cert: '0 3 2 1 4 5' }, caption: 'A Hamiltonian path as a certificate: it must list every vertex exactly once, and each step must be an edge.' },
      'Try one by hand. In the graph below, find four vertices that are all joined to each other.',
      { svg: K.svg(K.G1.pos, K.G1.edges, { label: 'A graph with seven vertices a to g' }), caption: 'A graph on a to g. The exercise below checks your clique with the same verifier.' },
      { warn: 'NP stands for *nondeterministic polynomial*, not *not polynomial*. Every problem in P is in NP: the verifier can ignore the certificate and solve the problem itself.' },
      { list: ['NP = problems whose yes-answers have short, quickly checkable certificates.', 'The verifier is polynomial in |w|; the certificate is polynomially long.', 'Only yes-instances need certificates.'] },
      { exercise: 'cx-ex-cert-clique' }, { exercise: 'cx-ex-cert-hampath' }, { exercise: 'cx-ex-cert-subset' }, { exercise: 'cx-ex-cert-colour' }, { exercise: 'cx-ex-cert-is' }, { exercise: 'cx-ex-cert-vc' }, { exercise: 'cx-ex-verifier' },
    ],
  });

  L({
    id: 'cx-l-ntime', chapter: 'cx-ch-np', title: 'Nondeterministic time: a tree of guesses', minutes: 10,
    summary: 'A nondeterministic machine accepts when some branch accepts. NP is exactly what such machines decide in polynomial time: the branch choices are the certificate.',
    blocks: [
      'A nondeterministic machine may have several moves in one configuration. Its computation is a **tree**: every choice opens new branches. It accepts its input when at least one branch reaches the accept state.',
      { def: 'Nondeterministic time', text: 'a nondeterministic decider runs in time t(n) when every branch on every input of length n halts within t(n) steps. NTIME(t(n)) is the class of languages decided by such machines. NP = NTIME(n) ∪ NTIME(n²) ∪ …' },
      { topic: 'cx-ntime', input: { mode: 'sat', f: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z)' }, caption: 'The machine guesses one bit per variable, then checks the formula deterministically on each branch. Watch the tree double at each guess, and look for the leaves that accept.' },
      { predict: { q: 'The tree above guesses 3 bits. How many branches does it have after the guesses?', options: ['3', '6', '8'], answer: 2, explain: 'Each guess doubles the branches: 2 · 2 · 2 = 8 leaves, one for each assignment.' } },
      { h: 'Two definitions, one class' },
      { steps: ['From a verifier to a machine: guess a certificate c of polynomial length, one symbol per step, then run the verifier on (w, c).', 'From a machine to a verifier: the certificate is the list of choices along an accepting branch; the verifier replays the machine following those choices.'] },
      { topic: 'cx-ntime', input: { mode: 'ntm', w: 'cab' }, caption: 'The repeat machine guesses a position and looks for the same letter later. On cab no letter repeats, so every branch rejects: the machine rejects.' },
      { tip: 'A deterministic machine can simulate a nondeterministic one by trying every branch, at the cost of time 2^O(t(n)). Whether the exponential can be avoided is exactly the P versus NP question.' },
      { list: ['A nondeterministic machine accepts when some branch accepts.', 'Its time is the depth of the tree, not the number of branches.', 'NP = nondeterministic polynomial time = polynomially verifiable.'] },
      { exercise: 'cx-ex-ntm-leaves' }, { exercise: 'cx-ex-ntm-sim' },
    ],
  });

  L({
    id: 'cx-l-pvsnp', chapter: 'cx-ch-np', title: 'P versus NP, and co-NP', minutes: 12,
    summary: 'P ⊆ NP, and nobody knows whether the two are equal. co-NP holds the problems whose no-answers have short certificates.',
    blocks: [
      'We know P ⊆ NP. The famous open question is whether the inclusion is strict: is every problem whose answers can be **checked** quickly also one whose answers can be **found** quickly?',
      { topic: 'cx-pvsnp', input: { follow: 'FACTOR' }, caption: 'The two pictures side by side: P = NP, or P strictly inside NP with the NP-complete problems at the top. FACTOR sits in NP, and is not known to be either in P or NP-complete.' },
      { predict: { q: 'Suppose tomorrow someone proves that SAT has no polynomial-time algorithm. Which picture is then the true one?', options: ['P = NP', 'P ≠ NP'], answer: 1, explain: 'SAT is in NP. If it is not in P, then NP has a problem P lacks, so P ≠ NP.' } },
      { h: 'Proving the answer is no' },
      'For SAT, a satisfying assignment is a convincing short proof of *yes*. What would convince you that a formula is **unsatisfiable**? Listing all 2ⁿ rows works, but is not short. No short proof of unsatisfiability is known.',
      { def: 'co-NP', text: 'the class of languages whose complements are in NP. Equivalently: every no-instance has a short certificate checkable in polynomial time.' },
      { topic: 'cx-conp', input: { q: 'taut', f: '(x ∨ ¬y) ∧ (y ∨ z ∨ ¬x)' }, caption: 'TAUT asks whether a formula is true under every assignment. One row that makes it false refutes the claim at once: a short certificate for no.' },
      { table: [['problem', 'short certificate for yes', 'short certificate for no', 'class'], ['SAT', 'a satisfying assignment', 'none known', 'NP'], ['UNSAT', 'none known', 'a satisfying assignment', 'co-NP'], ['TAUT', 'none known', 'a falsifying assignment', 'co-NP'], ['PATH', 'the path', 'not needed: solve it', 'P']] },
      { tip: 'P is closed under complement (swap accept and reject), so P ⊆ NP ∩ co-NP. Whether NP = co-NP is also open; if P = NP then NP = co-NP.' },
      { list: ['P ⊆ NP; whether they are equal is open.', 'co-NP = complements of NP problems: short proofs of no.', 'UNSAT and TAUT are in co-NP.'] },
      { exercise: 'cx-ex-pnp-consequence' }, { exercise: 'cx-ex-conp-which' }, { exercise: 'cx-ex-taut-refute' },
    ],
  });

  // =========================================================================================================
  // Chapter 3: satisfiability
  // =========================================================================================================
  L({
    id: 'cx-l-sat', chapter: 'cx-ch-sat', title: 'Formulas, clauses and assignments', minutes: 9,
    summary: 'SAT asks whether a Boolean formula can be made true. In conjunctive normal form a formula is a list of clauses, and a clause is a list of literals.',
    blocks: [
      { def: 'Literal, clause, CNF', text: 'a literal is a variable x or its negation ¬x. A clause is an OR of literals, like (x ∨ ¬y ∨ z). A formula in CNF is an AND of clauses. A k-CNF formula has at most k literals per clause.' },
      { def: 'SAT', text: 'given a formula φ, is there an assignment of true or false to its variables that makes φ true? Such an assignment is a satisfying assignment. 3SAT is SAT restricted to 3-CNF.' },
      'A clause is true when **at least one** of its literals is true; a CNF formula is true when **every** clause is. So setting a variable can only do two things to a clause: satisfy it for good, or knock out one of its literals.',
      { topic: 'cx-sat-assign', input: { f: '(x ∨ y) ∧ (¬x) ∧ (¬y ∨ z)', v: 'x=1 y=1 z=1' }, inputs: true, caption: 'Values are set one at a time. Watch the clause (¬x) die the moment x is set to 1: no later value can rescue it.' },
      { predict: { q: 'A formula contains the clause () with no literals. Can any assignment satisfy the formula?', options: ['Yes, if all other clauses are true', 'No: an empty clause has no literal that could be true'], answer: 1, explain: 'An OR of nothing is false. The empty clause makes every formula containing it unsatisfiable. In contrast, the formula with no clauses at all is true: an AND of nothing is true.' } },
      { topic: 'cx-sat-assign', input: { f: '(x ∨ y) ∧ () ∧ (¬x)', v: 'x=0' }, caption: 'The empty clause stays false whatever happens.' },
      'The obvious algorithm tries all 2ⁿ assignments. With 60 variables that is about 10¹⁸ rows. The next lesson shows how to cut most of them away, though in the worst case nobody knows how to avoid exponential time.',
      { list: ['A clause needs one true literal; a CNF formula needs every clause true.', 'Empty clause: always false. Empty formula: always true.', 'Checking an assignment is fast, so SAT is in NP.'] },
      { exercise: 'cx-ex-sat-find' }, { exercise: 'cx-ex-sat-choice-1' }, { exercise: 'cx-ex-sat-choice-2' }, { exercise: 'cx-ex-empty' },
    ],
  });

  L({
    id: 'cx-l-dpll', chapter: 'cx-ch-sat', title: 'DPLL: search with forced moves', minutes: 12,
    summary: 'DPLL guesses a value only when it must. Unit clauses force values, pure literals can be set for free, and a conflict sends the search back to the last guess.',
    blocks: [
      'Brute force treats every variable the same. But after a few values are set, many clauses are left with a single unset literal, and then there is no choice at all.',
      { def: 'Unit propagation', text: 'if a clause has all its literals false except one unset literal ℓ, then ℓ must be made true. Repeat until no clause is unit, or until some clause has every literal false (a conflict).' },
      { def: 'Pure literal', text: 'a literal whose negation appears in no remaining clause. Setting it true can only help, so it is set without branching.' },
      { steps: ['Propagate units; if a clause becomes false, report a conflict.', 'Set pure literals true.', 'If every clause is satisfied, report the assignment.', 'Otherwise pick an unset variable, try it true, and if that branch fails, try it false.'] },
      { topic: 'cx-dpll', input: { f: '(x ∨ y ∨ z) ∧ (¬x ∨ y) ∧ (¬y ∨ z) ∧ (¬z ∨ ¬x) ∧ (x ∨ ¬y ∨ ¬z)', pure: 'on' }, caption: 'The search tree. Each guess is a branch; each forced value follows the guess on the same branch. Watch a conflict close a branch and send the search back.' },
      { predict: { q: 'In (a) ∧ (¬a ∨ b) ∧ (¬b ∨ c), how many guesses does DPLL need?', options: ['None: every value is forced', 'One', 'Three'], answer: 0, explain: '(a) is a unit clause, so a = 1. Then (¬a ∨ b) becomes unit: b = 1. Then c = 1. Unit propagation alone solves it.' } },
      { topic: 'cx-dpll', input: { f: '(x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ z) ∧ (¬x ∨ ¬z)', pure: 'on' }, caption: 'An unsatisfiable formula: both values of the first guess end in a conflict, so the whole tree is closed.' },
      { h: 'Where the hard formulas live' },
      { topic: 'cx-phase', input: { n: 20, samples: 16, seed: 7 }, caption: 'Random 3-CNF formulas with more and more clauses per variable. Few clauses: almost all satisfiable and easy. Many clauses: almost all unsatisfiable and quickly refuted. Watch the work peak where the two meet, near 4.3 clauses per variable.' },
      { warn: 'DPLL is still exponential in the worst case. Its tricks prune the tree a great deal in practice, but no known trick makes every formula easy.' },
      { list: ['Unit clauses force values; conflicts send the search back.', 'Pure literals are set for free.', 'Random 3-SAT is hardest near 4.3 clauses per variable.'] },
      { exercise: 'cx-ex-unit-prop' }, { exercise: 'cx-ex-pure' }, { exercise: 'cx-ex-sat-or-unsat-a' }, { exercise: 'cx-ex-sat-or-unsat-b' }, { exercise: 'cx-ex-phase' },
    ],
  });

  L({
    id: 'cx-l-2sat', chapter: 'cx-ch-sat', title: '2-SAT: a graph of implications', minutes: 11,
    summary: 'A clause of two literals is two implications. 2-SAT is unsatisfiable exactly when some variable and its negation imply each other, which a graph search finds in polynomial time.',
    blocks: [
      'The clause (a ∨ b) says: if a is false, then b must be true; and if b is false, a must be true. So it is two implications, ¬a → b and ¬b → a.',
      { def: 'Implication graph', text: 'for a 2-CNF formula, a directed graph with one vertex per literal (x and ¬x for each variable) and, for each clause (a ∨ b), the edges ¬a → b and ¬b → a. A one-literal clause (a) counts as (a ∨ a), giving ¬a → a.' },
      { topic: 'cx-2sat', input: { f: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z) ∧ (y ∨ w)' }, inputs: true, caption: 'Each clause draws two arrows. Then the strongly connected components are found: literals that all imply each other. Watch each component get one value, from the end of the order back to the start.' },
      { predict: { q: 'Suppose there is a path x → … → ¬x and also a path ¬x → … → x. What does that say?', options: ['x must be true', 'x must be false', 'No value of x works: the formula is unsatisfiable'], answer: 2, explain: 'If x were true, the first path forces ¬x; if x were false, the second path forces x. Both values lead to a contradiction.' } },
      { topic: 'cx-2sat', input: { f: '(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)' }, caption: 'Unsatisfiable: x and ¬x land in the same component.' },
      { def: '2-SAT theorem', text: 'a 2-CNF formula is satisfiable exactly when no variable x has x and ¬x in the same strongly connected component. When it is satisfiable, give each component the value true if it comes later in a topological order than its negation\'s component.' },
      { tip: 'Components can be found in time linear in the size of the graph, so 2-SAT is in P. With three literals the trick breaks: (a ∨ b ∨ c) says ¬a → (b ∨ c), an implication to a pair, not to a single literal.' },
      { list: ['Each 2-clause gives two implications.', 'Unsatisfiable exactly when x and ¬x imply each other.', '2-SAT is in P; 3-SAT is NP-complete.'] },
      { exercise: 'cx-ex-2sat-implications' }, { exercise: 'cx-ex-2sat-reach' }, { exercise: 'cx-ex-2sat-verdict' }, { exercise: 'cx-ex-2sat-solve' },
    ],
  });

  // =========================================================================================================
  // Chapter 4: reductions
  // =========================================================================================================
  L({
    id: 'cx-l-reduce', chapter: 'cx-ch-red', title: 'Polynomial reductions, and SAT → 3SAT', minutes: 12,
    summary: 'A polynomial reduction turns instances of one problem into instances of another, keeping yes as yes and no as no. A problem every NP problem reduces to is NP-hard.',
    blocks: [
      { def: 'Polynomial-time reduction', text: 'A ≤ₚ B when there is a function f, computable in polynomial time, with w ∈ A ⟺ f(w) ∈ B for every w.' },
      'Read A ≤ₚ B as "A is no harder than B": to solve A, translate and ask B. If B is in P then so is A, since a polynomial translation followed by a polynomial algorithm is polynomial.',
      { def: 'NP-hard, NP-complete', text: 'B is NP-hard when A ≤ₚ B for every A in NP. B is NP-complete when it is NP-hard and in NP.' },
      'Once one NP-complete problem is known, new ones come cheaply: to show X is NP-hard, reduce a known NP-complete problem **to** X. Reductions compose, so everything in NP then reduces to X.',
      { warn: 'The direction is the most common mistake. Reducing X to 3SAT shows only that X is no harder than 3SAT, which is true of every problem in NP. To show X is hard, reduce 3SAT to X.' },
      { h: 'The first gadget: cutting long clauses' },
      'SAT allows clauses of any length; 3SAT allows at most three literals. A long clause becomes a **chain** of three-literal clauses linked by new variables, each of which says "the job is passed on".',
      { math: '(ℓ₁ ∨ ℓ₂ ∨ ℓ₃ ∨ ℓ₄ ∨ ℓ₅)\n  becomes\n(ℓ₁ ∨ ℓ₂ ∨ z₁) ∧ (¬z₁ ∨ ℓ₃ ∨ z₂) ∧ (¬z₂ ∨ ℓ₄ ∨ ℓ₅)' },
      { topic: 'cx-red-sat3', input: { f: '(a ∨ b ∨ ¬c ∨ d ∨ e) ∧ (¬a ∨ c) ∧ (¬b ∨ ¬d ∨ c)' }, caption: 'The five-literal clause becomes a chain of three; the two-literal clause is padded with a new variable used both ways. Watch how a true literal anywhere in the chain lets the z\'s be set to satisfy every link.' },
      { predict: { q: 'If none of ℓ₁ … ℓ₅ is true, can the z\'s still satisfy the chain?', options: ['Yes, with the right z\'s', 'No: some link is left false'], answer: 1, explain: 'The first link needs z₁ true, which makes the second need z₂ true, and the last link then has ¬z₂ false and both literals false.' } },
      { list: ['A ≤ₚ B: a polynomial translation keeping yes and no.', 'To prove X NP-hard, reduce a known NP-complete problem to X.', 'A clause of k ≥ 4 literals becomes k − 2 clauses with k − 3 new variables.'] },
      { exercise: 'cx-ex-red-direction' }, { exercise: 'cx-ex-red-meaning' }, { exercise: 'cx-ex-sat3-count' }, { exercise: 'cx-ex-sat3-write' },
    ],
  });

  L({
    id: 'cx-l-clique', chapter: 'cx-ch-red', title: '3SAT → CLIQUE and INDEPENDENT SET', minutes: 13,
    summary: 'Make one vertex per literal occurrence. Join compatible literals in different clauses and ask for a clique with one vertex per clause; or join the conflicts and ask for an independent set.',
    blocks: [
      'A satisfying assignment picks, in every clause, at least one true literal. Two picked literals can never be x and ¬x. That is the whole idea: **one pick per clause, no contradictions**.',
      { steps: ['One vertex for every literal in every clause, grouped by clause.', 'Join two vertices when they lie in different clauses and are not a literal and its negation.', 'Ask for a clique of size k = number of clauses.'] },
      { topic: 'cx-red-clique', input: { f: '(p ∨ q ∨ ¬r) ∧ (¬p ∨ r) ∧ (¬q ∨ ¬r ∨ p)', focus: 'all', edges: 'all' }, caption: 'Watch the groups appear, then the compatible edges. A clique of 3 must take one vertex from each group, and its literals can all be made true together.' },
      { predict: { q: 'Can a clique in this graph contain two vertices of the same clause?', options: ['Yes', 'No: vertices of one clause are never joined'], answer: 1, explain: 'Edges only go between different clauses, so a clique has at most one vertex per clause; size k forces exactly one.' } },
      'The two directions of the proof are the two certificate maps. From a satisfying assignment, pick a true literal in each clause: they are pairwise compatible, a clique. From a clique of size k, set its literals true: no conflict, every clause has one.',
      { h: 'The mirror image: independent set' },
      'Flip the edges around: join vertices of the **same** clause (so at most one per clause can be chosen) and join each literal to its negation (so the choices agree). Now we want k vertices with **no** edges among them.',
      { topic: 'cx-red-is', input: { f: '(a ∨ ¬b ∨ c) ∧ (¬a ∨ b ∨ ¬c) ∧ (b ∨ c)', focus: 'all', edges: 'all' }, caption: 'Clause triangles and conflict edges. An independent set of size 3 picks one literal per triangle with no conflicts.' },
      { topic: 'cx-red-is', input: { f: '(p ∨ q) ∧ (¬p ∨ q) ∧ (p ∨ ¬q) ∧ (¬p ∨ ¬q)', focus: 'all', edges: 'all' }, caption: 'An unsatisfiable formula gives a graph with no independent set of size 4.' },
      { tip: 'Name the vertices by literal and clause number, like a1 for the a in clause 1. The exercises use these names.' },
      { list: ['Vertices = literal occurrences; k = number of clauses.', 'CLIQUE: edges between compatible literals of different clauses.', 'INDEPENDENT SET: edges inside clauses and between x and ¬x.'] },
      { exercise: 'cx-ex-clique-size' }, { exercise: 'cx-ex-clique-edges' }, { exercise: 'cx-ex-clique-cert' }, { exercise: 'cx-ex-is-edges' },
    ],
  });

  L({
    id: 'cx-l-cover', chapter: 'cx-ch-red', title: 'One problem in three coats: IS, VC, CLIQUE', minutes: 11,
    summary: 'A set is independent exactly when the rest is a vertex cover, and exactly when it is a clique in the complement graph. So the three problems reduce to each other with almost no work.',
    blocks: [
      { def: 'Vertex cover', text: 'a set C of vertices such that every edge has at least one end in C. VERTEX COVER asks for one of size at most k.' },
      'Take an independent set S. No edge has both ends in S, so every edge has an end **outside** S: the rest of the vertices form a cover. The argument runs backwards too.',
      { math: 'S independent in G   ⟺   V − S is a vertex cover of G\nS independent in G   ⟺   S is a clique in the complement of G' },
      { topic: 'cx-red-complement', input: { g: 'a-b, b-c, c-d, d-e, e-a, a-f, c-f', k: 3 }, caption: 'The same set three ways: independent in G, its complement covering every edge, and a clique once edges and non-edges swap.' },
      { predict: { q: 'A graph has 9 vertices and its largest independent set has 4. What is its smallest vertex cover?', options: ['4', '5', '9'], answer: 1, explain: 'The complement of a largest independent set is a smallest cover: 9 − 4 = 5.' } },
      { h: '3SAT → VERTEX COVER directly' },
      'There is also a gadget straight from formulas. Each variable is an edge x — ¬x, so a cover takes one end of it: that end is the true literal. Each clause is a clique of its occurrences, so a cover takes all but one of them. Each occurrence is linked to its literal, and the one left out of the cover needs its literal in the cover: true.',
      { topic: 'cx-red-vc', input: { f: '(a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ c) ∧ (a ∨ ¬c)', focus: 'all', edges: 'all' }, caption: 'Variable edges at the top, clause cliques below, links between. k = n + Σ(|clause| − 1); here 3 + 2 + 2 + 1 = 8.' },
      { list: ['IS ↔ VC: take the complement set, k becomes n − k.', 'IS ↔ CLIQUE: take the complement graph, k stays.', '3SAT → VC: variable edges, clause cliques, links; k = n + Σ(|c| − 1).'] },
      { exercise: 'cx-ex-is-to-vc' }, { exercise: 'cx-ex-vc-k' },
    ],
  });

  L({
    id: 'cx-l-subsetsum', chapter: 'cx-ch-red', title: 'From formulas to numbers: SUBSET SUM', minutes: 12,
    summary: 'Write numbers in decimal with one column per variable and one per clause. The target forces one value per variable and at least one true literal per clause, and no column ever carries.',
    blocks: [
      { def: 'SUBSET SUM', text: 'given numbers and a target t, is there a selection of the numbers (each used at most once) that adds up to exactly t?' },
      'It looks like arithmetic has nothing to do with logic. The trick is to use **digits as switches**: if no column can ever add up to 10 or more, the columns never interact, and each one can enforce its own rule.',
      { steps: ['Columns: one per variable, then one per clause.', 'For each variable x, two numbers: y (x true) and z (x false). Both have 1 in x\'s column; in each clause column, y has the number of times x occurs there, z the number of times ¬x does.', 'For each clause, two slack numbers with a 1 in its column.', 'Target: 1 in every variable column, 3 in every clause column.'] },
      { topic: 'cx-red-subsetsum', input: { f: '(x ∨ y ∨ ¬z) ∧ (¬x ∨ ¬y ∨ z)' }, caption: 'Read the table column by column. A variable column says: take exactly one of y and z. A clause column says: the true literals plus at most two slacks make 3, so at least one literal is true.' },
      { predict: { q: 'A clause column has 0 true literals. Can the two slack numbers make it reach 3?', options: ['Yes', 'No: the slacks give at most 2'], answer: 1, explain: 'Without a true literal the column reaches at most 2, short of the target 3. That is how the target enforces the clause.' } },
      { warn: 'The numbers here have n + m digits, so they are exponentially large in value. That is fine: the reduction writes them in decimal, polynomially many digits, and SUBSET SUM is NP-complete for numbers written that way. In unary it would be easy.' },
      { list: ['Digit columns act as independent constraints because nothing carries.', 'Variable columns: exactly one of y, z.', 'Clause columns: target 3, at most 2 from slack.'] },
      { exercise: 'cx-ex-ss-target' }, { exercise: 'cx-ex-ss-row' }, { exercise: 'cx-ex-ss-cert' },
    ],
  });

  L({
    id: 'cx-l-colour-path', chapter: 'cx-ch-red', title: 'Colours and paths', minutes: 14,
    summary: '3-COLOUR uses a palette triangle and small OR gadgets; HAM-PATH uses rows that can be crossed in two directions and clause vertices reached by detours.',
    blocks: [
      { h: '3SAT → 3-COLOUR' },
      'In a 3-colouring, neighbours get different colours. Start with a triangle T, F, B: its three colours are now names for **true**, **false** and **base**. Join x and ¬x to each other and to B: one of them is coloured T and the other F.',
      'For each clause, an OR gadget takes two inputs and has an output that can be coloured T only if an input is T. Chain two of them for a three-literal clause, and join the last output to F and B, which forces it to T.',
      { topic: 'cx-red-3col', input: { f: '(x ∨ ¬y ∨ z) ∧ (¬x ∨ y)', focus: 'all', edges: 'all' }, frame: 19, caption: 'Look at clause 1. Follow the colouring through its two OR gadgets: the final output is forced to T, so some literal of the clause must be T.' },
      { predict: { q: 'In an OR gadget (inputs x, y; inner u, v joined to each other; u joined to x, v to y; output o joined to u and v) both inputs are F. What colour must o get?', options: ['T', 'F', 'B', 'Any of the three'], answer: 1, explain: 'u and v avoid F (their inputs) and each other, so they are T and B in some order. Then o avoids both: o is F.' } },
      { h: '3SAT → HAM-PATH' },
      'For each variable, a row of vertices that can be crossed left to right (true) or right to left (false). Rows are chained top to bottom, so a Hamiltonian path crosses each row once. Each clause is one extra vertex, reached by a detour from a row, and the detour only fits the direction that makes the literal true.',
      { topic: 'cx-red-hampath', input: { f: '(x ∨ ¬y) ∧ (¬x ∨ y)' }, caption: 'Two variables, two clauses. Watch the path cross each row in the direction of its value and pick up each clause vertex on the way.' },
      { tip: 'Row i has 3m + 1 vertices for m clauses, plus a top and a bottom; with one vertex per clause the graph has n(3m + 3) + m vertices.' },
      { list: ['3-COLOUR: palette triangle, literal pairs on B, two OR gadgets per clause.', 'HAM-PATH: one two-way row per variable, one detour vertex per clause.', 'Both are polynomial in the size of the formula.'] },
      { exercise: 'cx-ex-3col-size' }, { exercise: 'cx-ex-3col-or' }, { exercise: 'cx-ex-ham-size' }, { exercise: 'cx-ex-ham-direction' },
    ],
  });

  // =========================================================================================================
  // Chapter 5: Cook–Levin
  // =========================================================================================================
  L({
    id: 'cx-l-tableau', chapter: 'cx-ch-cook', title: 'Cook–Levin I: a run becomes a tableau', minutes: 13,
    summary: 'SAT is NP-complete. Any accepting run of a nondeterministic polynomial-time machine can be written as a table of configurations, and the table can be checked locally, window by window.',
    blocks: [
      'Every reduction so far started from 3SAT. Something has to start the chain: a direct proof that **every** problem in NP reduces to SAT. The idea is to turn a machine\'s computation into a formula.',
      { def: 'Tableau', text: 'for a nondeterministic machine N, an input w and a time bound t, a table with t + 1 rows, one configuration per time step. Each row is written # u q v #, where q is the state just left of the cell the head reads. Row 0 is the start configuration.' },
      { topic: 'cx-cook-tableau', input: { w: '01', t: 3 }, caption: 'The machine guesses a bit and checks it against the input. Watch each row follow from the one above by one move; where there is a choice, the tableau records the branch that accepts.' },
      { predict: { q: 'The machine accepts after two steps but the bound is t = 4. What goes in the remaining rows?', options: ['Blanks', 'The last configuration again', 'Nothing: the tableau is shorter'], answer: 1, explain: 'A halting row repeats unchanged, so every tableau has exactly t + 1 rows and the formula does not need to know when the machine halts.' } },
      { h: 'Checking locally' },
      'How do we know each row really follows from the previous one? Look through a **window** of 2 rows by 3 columns. A move changes only the cells next to the head, so the whole tableau is legal exactly when every window is one of a fixed finite list of legal windows.',
      { topic: 'cx-cook-windows', input: { w: '01', t: 3, fault: 'far' }, caption: 'A symbol has been changed far from the head. Watch the window sweep: the window over that cell is not on the legal list, and the tableau is rejected.' },
      { topic: 'cx-cook-windows', input: { w: '11', t: 2, fault: 'two' }, caption: 'A second state has appeared in a row. Again some window catches it.' },
      { list: ['A run of N on w within t steps is a (t + 1)-row tableau.', 'Halting rows repeat, so the tableau always has t + 1 rows.', 'Legal = every 2 × 3 window is legal: a local check.'] },
      { exercise: 'cx-ex-cook-window' },
    ],
  });

  L({
    id: 'cx-l-clauses', chapter: 'cx-ch-cook', title: 'Cook–Levin II: the formula and its size', minutes: 13,
    summary: 'Variables say which symbol is in which cell. Four groups of clauses say: one symbol per cell, row 0 is the start, some cell is accepting, every window is legal. The total is polynomial.',
    blocks: [
      { def: 'Cell variables', text: 'x(i, j, s) is true when cell (i, j) of the tableau holds symbol s, where s ranges over #, the tape symbols and the states: K symbols in all.' },
      { table: [['group', 'says', 'how many clauses'], ['cell', 'each cell holds exactly one symbol', 'per cell: 1 "at least one" + K(K − 1)/2 "not two"'], ['start', 'row 0 is # q₀ w ⊔ … ⊔ #', 'one per column: W'], ['accept', 'an accepting state appears somewhere', '1 (a big OR)'], ['move', 'every 2 × 3 window is legal', 'per window position, a fixed number']] },
      'A row has W = C + 3 columns: C tape cells, where C = max(|w|, t + 1) because the head cannot get further in t steps, two # marks and one state. There are t + 1 rows and t · (W − 2) window positions.',
      { topic: 'cx-cook-count', input: { mc: 'guess', w: '01', tmax: 5 }, caption: 'The four groups counted for t = 1 to 5. Watch the cell clauses dominate and every count grow like a polynomial in t.' },
      { predict: { q: 'With K = 8 symbols, how many cell clauses does one cell need?', options: ['8', '29', '64'], answer: 1, explain: 'One clause says some symbol is there, and one clause for each of the 8 · 7 / 2 = 28 pairs says not both: 29.' } },
      'The formula is satisfiable exactly when an accepting tableau exists, that is, when N accepts w within t steps. For a polynomial bound t = nᵏ the tableau has O(n²ᵏ) cells, K is a constant for the fixed machine, and so the whole formula is polynomial in n. Every NP problem therefore reduces to SAT.',
      { topic: 'cx-cook-assign', input: { w: '01', t: 3 }, caption: 'From a tableau to an assignment and back: the true cell variables spell out the tableau, row by row.' },
      { tip: 'The move clauses here use one selector variable per legal window, saying "this window is the one used here". Other ways of writing the same condition as CNF exist; all are polynomial because the list of legal windows depends only on N.' },
      { list: ['Variables x(i, j, s): which symbol is in which cell.', 'Cell, start, accept and move clauses.', 'Polynomial size: SAT is NP-complete, and with the chain gadget, so is 3SAT.'] },
      { exercise: 'cx-ex-cook-table' }, { exercise: 'cx-ex-cook-cellclauses' }, { exercise: 'cx-ex-cook-accept' }, { exercise: 'cx-ex-cook-poly' },
    ],
  });

  // =========================================================================================================
  // Chapter 6: coping, space and the map
  // =========================================================================================================
  L({
    id: 'cx-l-coping', chapter: 'cx-ch-space', title: 'Coping with NP-completeness', minutes: 12,
    summary: 'NP-complete does not mean hopeless. Search cleverly, settle for a provably good answer, or notice that your inputs belong to an easy special case.',
    blocks: [
      'Your boss asks for the smallest vertex cover of a network, and you have just proved the problem NP-complete. Three honest replies remain.',
      { h: '1. Search, but prune' },
      'For VERTEX COVER with budget k: pick any uncovered edge u — v. One of u and v must be in the cover, so branch on the two. Each branch spends one unit of budget, so the tree has depth at most k and at most 2ᵏ leaves, however large the graph.',
      { topic: 'cx-backtrack', input: { g: '0-1 1-2 2-3 3-4 4-5 5-0', k: 2 }, caption: 'A six-cycle with budget 2: every branch runs out of budget with edges left over. Watch the tree stay small because each branch is cut when the budget is spent.' },
      { h: '2. Approximate, with a guarantee' },
      { topic: 'cx-approx-vc', input: { g: '0-1 1-2 2-3' }, caption: 'Take any uncovered edge, put both ends in the cover, repeat. On this path it takes 4 vertices where 2 suffice: exactly twice the best.' },
      { predict: { q: 'Why is the result never more than twice the best cover?', options: ['Because the graph is small', 'The picked edges share no ends, and any cover needs a different vertex for each of them', 'Because it picks high-degree vertices first'], answer: 1, explain: 'The picked edges form a matching. The best cover must contain an end of each, all different, so best ≥ (number picked) and ours = 2 · (number picked).' } },
      { h: '3. Use the structure you have' },
      { topic: 'cx-tree-dp', input: { g: '0-1 0-2 1-3 1-4 2-5 2-6' }, caption: 'On a tree, solve each subtree twice, once with its root in the cover and once without, from the leaves up. Linear time.' },
      { list: ['Branching with a budget: 2ᵏ · poly(n), fine when k is small.', 'Approximation: within a factor 2 for vertex cover.', 'Special cases: trees, 2-SAT, small treewidth are easy.'] },
      { exercise: 'cx-ex-approx-run' }, { exercise: 'cx-ex-approx-why' }, { exercise: 'cx-ex-tree-vc' }, { exercise: 'cx-ex-branch-leaves' },
    ],
  });

  L({
    id: 'cx-l-pspace', chapter: 'cx-ch-space', title: 'Space, PSPACE and TQBF', minutes: 12,
    summary: 'Space counts tape cells used, and space can be reused. PSPACE contains NP, and TQBF, the game version of SAT, is complete for it.',
    blocks: [
      { def: 'Space', text: 'a machine runs in space s(n) when on every input of length n it uses at most s(n) tape cells. PSPACE is the class of languages decided in polynomial space; NPSPACE allows nondeterminism.' },
      'Space is a gentler resource than time, because it can be **reused**. To decide SAT in linear space, try each assignment in turn on the same stretch of tape, erasing as you go. So NP ⊆ PSPACE.',
      { def: 'TQBF', text: 'given a fully quantified Boolean formula like ∃x ∀y ∃z φ, is it true? It is a game: the ∃-player picks values trying to make φ true, the ∀-player trying to make it false, in the order of the quantifiers.' },
      { topic: 'cx-tqbf', input: { q: '∃x ∀y ∃z : (x ∨ y) ∧ (¬y ∨ z) ∧ (y ∨ ¬z)' }, inputs: true, caption: 'The game tree, evaluated depth first. At ∃ nodes one winning child suffices; at ∀ nodes every child must win. Only one path of the tree is kept in memory at a time.' },
      { predict: { q: 'A formula has only ∃ quantifiers. What problem is TQBF then?', options: ['SAT', 'TAUT', '2-SAT'], answer: 0, explain: 'With only ∃ the question is whether some assignment makes φ true: SAT. With only ∀ it is TAUT.' } },
      { topic: 'cx-tqbf', input: { q: '∃x ∀y : (x ∨ y) ∧ (¬x ∨ ¬y)' }, caption: 'Whatever the ∃-player picks for x, the ∀-player picks y = x and one clause fails. False.' },
      'The recursion keeps one value per variable on the current path: linear space. TQBF is **PSPACE-complete**: every polynomial-space problem reduces to it. Many two-player games on growing boards are PSPACE-complete for the same reason.',
      { list: ['Space can be reused; time cannot.', 'P ⊆ NP ⊆ PSPACE.', 'TQBF, a game of alternating choices, is PSPACE-complete.'] },
      { exercise: 'cx-ex-tqbf-1' }, { exercise: 'cx-ex-tqbf-move' }, { exercise: 'cx-ex-space-facts' },
    ],
  });

  L({
    id: 'cx-l-savitch', chapter: 'cx-ch-space', title: 'Savitch\'s theorem, L and NL', minutes: 13,
    summary: 'Reachability can be decided by halving: can u reach v in 2ⁱ steps through some midpoint? That puts nondeterministic space s inside deterministic space s². Below that, L and NL use only logarithmic space.',
    blocks: [
      'A nondeterministic machine in space s(n) has at most 2^O(s(n)) configurations. It accepts when the accepting configuration is reachable from the start in its configuration graph. So the whole question is **reachability**, and we want to answer it using little space.',
      { def: 'Savitch\'s recursion', text: 'CAN(u, v, i): can u reach v in at most 2ⁱ steps? For i = 0, check u = v or an edge u → v. Otherwise try every midpoint m and ask CAN(u, m, i − 1) and CAN(m, v, i − 1), reusing the space for each try.' },
      { topic: 'cx-savitch', input: { g: 'a→b, b→c, c→d, b→e, e→a', s: 'a', t: 'd' }, caption: 'Each question splits into two half-size questions. Watch the stack of open questions: it never gets deeper than log₂ of the number of vertices.' },
      { predict: { q: 'The recursion has depth log₂ N and each level stores a few vertex names of log₂ N bits. How much space in all?', options: ['O(log N)', 'O(log² N)', 'O(N)'], answer: 1, explain: 'log N levels times O(log N) bits each. With N = 2^O(s(n)) configurations this is O(s(n)²): NSPACE(s) ⊆ SPACE(s²), and so NPSPACE = PSPACE.' } },
      { h: 'Logarithmic space' },
      { def: 'L and NL', text: 'with a read-only input tape and a separate work tape, L is the class decided in O(log n) work space deterministically, NL nondeterministically. Log space is just enough for a constant number of pointers into the input and counters up to n.' },
      { topic: 'cx-lnl', input: { g: 'a→b, b→c, c→a, c→d, a→e, e→a', s: 'a', t: 'd' }, caption: 'The NL machine keeps only the current vertex and a step counter, and guesses the next vertex each time. The counter stops walks that circle for ever.' },
      'Directed reachability is **NL-complete**. Savitch puts NL inside SPACE(log² n), and every log-space machine runs in polynomial time, so L ⊆ NL ⊆ P. It is also known that NL = co-NL; whether L = NL is open.',
      { list: ['Savitch: NSPACE(s) ⊆ SPACE(s²); hence NPSPACE = PSPACE.', 'L ⊆ NL ⊆ P; PATH is NL-complete.', 'A log-space machine stores a constant number of pointers and counters.'] },
      { exercise: 'cx-ex-savitch' }, { exercise: 'cx-ex-lnl' },
    ],
  });

  L({
    id: 'cx-l-map', chapter: 'cx-ch-space', title: 'The map of the classes', minutes: 9,
    summary: 'L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME. The hierarchy theorems separate the ends; almost every step in between is open.',
    blocks: [
      'Put everything together and the classes form a chain:',
      { math: 'L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE = NPSPACE ⊆ EXPTIME' },
      'The **hierarchy theorems** say that more of the same resource buys strictly more: with much more time (or space) a machine can diagonalise against every faster one. So P ≠ EXPTIME and NL ≠ PSPACE. Since the chain cannot be equal all the way, at least one of the inclusions between P and EXPTIME is strict, but nobody knows which.',
      { topic: 'cx-classmap', input: { world: 'known' }, caption: 'The classes as nested regions, with example problems placed in each. Step through to see which inclusions are known to be strict.' },
      { predict: { q: 'If P = NP were proved, what would happen to NP and co-NP?', options: ['They would be equal', 'They would still possibly differ', 'NP would equal PSPACE'], answer: 0, explain: 'P is closed under complement, so P = NP gives co-NP = co-P = P = NP.' } },
      { topic: 'cx-classmap', input: { world: 'pnp' }, caption: 'The picture if P = NP: the middle collapses, but EXPTIME stays strictly bigger.' },
      { list: ['L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME.', 'Known strict: P ⊊ EXPTIME, NL ⊊ PSPACE.', 'Open: L vs NL, P vs NP, NP vs PSPACE, and more.'] },
      { exercise: 'cx-ex-classify' }, { exercise: 'cx-ex-class-order' }, { exercise: 'cx-ex-separations' },
    ],
  });

  // ---- a guided tour and a course ---------------------------------------------------------------------------
  C.tour({
    id: 'cx-tour', title: 'Tour: complexity', blurb: 'Certificates, a SAT solver, a reduction and the map of the classes.',
    steps: [
      { route: 'topic=cx-verify', target: '#stageWrap', text: 'Complexity starts with checking. Here a verifier checks a certificate for CLIQUE, one pair of vertices at a time.' },
      { target: '#inputs', text: 'Type your own certificate here, or pick one of the examples, and the check runs again.' },
      { target: '#btnPlay', text: 'Play runs the check step by step; each step names the pair it looked at.' },
      { route: 'topic=cx-dpll', target: '#stageWrap', text: 'DPLL searches for a satisfying assignment as a tree: guesses branch, forced values follow, conflicts close branches.' },
      { target: '#say', text: 'Every step says which clause forced which value, with the actual literals.' },
      { route: 'topic=cx-red-clique', target: '#stageWrap', text: 'A reduction drawn as a gadget: a formula becomes a graph whose cliques are its satisfying assignments.' },
      { route: 'topic=cx-cook-tableau', target: '#stageWrap', text: 'Cook–Levin: a nondeterministic run written as a tableau, the first step to turning any NP problem into a formula.' },
      { route: 'topic=cx-classmap', target: '#stageWrap', text: 'And the map of the classes, from log space to exponential time, with what is known and what is open.' },
      { route: 'learn', target: '[data-chapter="cx-ch-time"]', text: 'The lessons and exercises of this part start here, with time measured in steps.' },
    ],
  });

  C.course({
    id: 'cx-course', title: 'Complexity, start to finish', blurb: 'From counting steps to the map of the classes: every complexity topic in teaching order, with lessons and exercises along the way.',
    steps: [
      { topic: 'cx-steps', note: 'The tallest bar of each length is the running time: the worst case.' },
      { topic: 'cx-multitape', note: 'Compare the counters: a second tape saves a factor of n, never more than squaring.' },
      { topic: 'cx-growth', note: 'Watch where the exponential overtakes every polynomial for good.' },
      { topic: 'cx-bigo', note: 'The shape whose ratio settles to a constant is the big-O.' },
      { topic: 'cx-encoding', note: 'The same divisions, counted against binary and against unary length.' },
      { exercise: 'cx-ex-order-1', note: 'Put the growth rates in order.' },
      { topic: 'cx-path', note: 'Each vertex is marked once: PATH is in P.' },
      { topic: 'cx-gcd', note: 'The numbers halve every two steps: time grows with the digits.' },
      { topic: 'cx-cyk-work', note: 'n² cells, n splits each: membership in a CFL is polynomial.' },
      { topic: 'cx-verify', note: 'The verifier stops at the first failed check.' },
      { exercise: 'cx-ex-cert-clique', note: 'Hand the verifier your own certificate.' },
      { topic: 'cx-ntime', note: 'The tree doubles at each guess; one accepting leaf is enough.' },
      { topic: 'cx-pvsnp', note: 'Two possible worlds; nobody knows which one we live in.' },
      { topic: 'cx-conp', note: 'One falsifying row refutes a tautology claim.' },
      { topic: 'cx-sat-assign', note: 'A clause dies when its last literal is knocked out.' },
      { topic: 'cx-dpll', note: 'Guesses branch; units follow without choice.' },
      { topic: 'cx-2sat', note: 'x and ¬x in one component means unsatisfiable.' },
      { topic: 'cx-phase', note: 'The hardest formulas sit where satisfiable turns unsatisfiable.' },
      { lesson: 'cx-l-reduce', note: 'Which way a reduction goes, and why it matters.' },
      { topic: 'cx-red-sat3', note: 'A long clause becomes a chain linked by new variables.' },
      { topic: 'cx-red-clique', note: 'One vertex per clause, no contradictions.' },
      { topic: 'cx-red-is', note: 'Clause triangles and conflict edges.' },
      { topic: 'cx-red-complement', note: 'The same set as independent set, cover and clique.' },
      { topic: 'cx-red-vc', note: 'Variable edges, clause cliques and the links between.' },
      { topic: 'cx-red-subsetsum', note: 'Each column is its own rule because nothing carries.' },
      { topic: 'cx-red-3col', note: 'The forced output needs a true literal.' },
      { topic: 'cx-red-hampath', note: 'The direction of each crossing is the value of a variable.' },
      { exercise: 'cx-ex-clique-edges', note: 'Run a reduction by hand.' },
      { topic: 'cx-cook-tableau', note: 'One row per step; halting rows repeat.' },
      { topic: 'cx-cook-windows', note: 'A tampered cell shows up in some window.' },
      { topic: 'cx-cook-count', note: 'Every group of clauses grows polynomially.' },
      { topic: 'cx-cook-assign', note: 'The true variables spell out the tableau.' },
      { topic: 'cx-backtrack', note: 'The budget bounds the depth of the tree.' },
      { topic: 'cx-approx-vc', note: 'Both ends of each picked edge: at most twice the best.' },
      { topic: 'cx-tree-dp', note: 'With or without the root, from the leaves up.' },
      { topic: 'cx-tqbf', note: '∃ needs one winning child, ∀ needs all.' },
      { topic: 'cx-savitch', note: 'The stack of open questions stays log-deep.' },
      { topic: 'cx-lnl', note: 'Only a vertex and a counter are remembered.' },
      { topic: 'cx-classmap', note: 'The chain of classes, and the few separations we know.' },
      { exercise: 'cx-ex-classify', note: 'Place each problem on the map.' },
    ],
  });
})();
