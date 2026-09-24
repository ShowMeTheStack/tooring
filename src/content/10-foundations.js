// Part 1, Foundations: sets, relations and functions; closures and equivalence relations; countable and
// uncountable sets; induction, pigeonhole and diagonalisation; strings and languages; and why most
// languages have no finite description. Six chapters, thirteen lessons, a tour and a course.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const H = (a, b, c) => [a, b, c];
  const ex = (x) => C.exercise(Object.assign({ level: 1 }, x));

  // ---- answer readers for the string kind -------------------------------------------------------------
  // The string checker hands accept() the trimmed text (ε alone becomes ''). These read sets of strings,
  // sets of pairs, partitions and lists of numbers, so the order and spacing a student uses never matter.
  const EPS = /^(ε|eps|epsilon|λ)$/i;
  const words = (t) => String(t).replace(/[{}]/g, ' ').split(/[\s,]+/).filter(Boolean).filter((v) => v !== '∅').map((v) => (EPS.test(v) ? '' : v));
  const sameSet = (a, b) => { const A = new Set(a), B = new Set(b); return A.size === B.size && [...A].every((v) => B.has(v)); };
  /** A set of strings, written {a, ab} or a, ab; repeats are harmless, as they are in a set */
  const setOf = (want) => (t) => sameSet(words(t), want);
  /** A set of ordered pairs, written (1, 2), (2, 3) or 1-2, 2-3; anything else in the text fails */
  const pairs = (t) => {
    const s = String(t);
    const out = [];
    let rest = s.replace(/\(\s*([^\s(),]+)\s*,\s*([^\s(),]+)\s*\)/g, (m, x, y) => { out.push(x + '-' + y); return ' '; });
    rest = rest.replace(/(?:^|[\s,{])([^\s(),{}-]+)\s*-\s*([^\s(),{}-]+)(?=$|[\s,}])/g, (m, x, y) => { out.push(x + '-' + y); return ' '; });
    return /^[\s,{}∅]*$/.test(rest) ? out : null;
  };
  const pairSet = (want) => (t) => { const p = pairs(t); return !!p && sameSet(p, want.split(/\s*,\s*/).filter(Boolean)); };
  /** A partition, written {1, 4}, {2}: blocks in braces, compared as a set of sets */
  const partition = (want) => (t) => {
    const blocks = String(t).match(/\{[^{}]*\}/g);
    if (!blocks) return false;
    if (String(t).replace(/\{[^{}]*\}/g, '').replace(/[\s,]/g, '') !== '') return false;
    const key = (b) => words(b).map((w) => (w === '' ? 'ε' : w)).sort().join(' ');
    const got = blocks.map(key), exp = want.map((b) => b.map((w) => (w === '' ? 'ε' : w)).sort().join(' '));
    return got.every((b) => b !== '') && got.length === exp.length && sameSet(got, exp);
  };
  /** A list of numbers in order, written 1, 5, 5, 6 or 1 5 5 6 */
  const numbers = (want) => (t) => { const v = String(t).split(/[\s,]+/).filter(Boolean); return v.length === want.length && v.every((x, i) => Number(x) === want[i]); };

  // ---- chapters ---------------------------------------------------------------------------------------
  C.chapter({ id: 'found-sets', part: 'foundations', n: 1, title: 'Sets, relations and functions', blurb: 'The vocabulary everything else is written in: sets and their operations, pairs and products, relations and their properties, and the kinds of function.' });
  C.chapter({ id: 'found-closures', part: 'foundations', n: 2, title: 'Closures and equivalence', blurb: 'Adding the fewest pairs to get a property you want, and the relations that cut a set into classes.' });
  C.chapter({ id: 'found-infinite', part: 'foundations', n: 3, title: 'Countable and uncountable', blurb: 'Which infinite sets can be listed one after another, and the diagonal trick that shows some cannot.' });
  C.chapter({ id: 'found-proofs', part: 'foundations', n: 4, title: 'Three ways to prove things', blurb: 'Induction, the pigeonhole principle and diagonalisation: the three arguments the rest of the course leans on.' });
  C.chapter({ id: 'found-strings', part: 'foundations', n: 5, title: 'Strings and languages', blurb: 'Alphabets, strings and their operations; languages as sets of strings, and how to combine them.' });
  C.chapter({ id: 'found-descriptions', part: 'foundations', n: 6, title: 'Finite descriptions', blurb: 'Every machine, grammar and expression is a finite string, so there are only countably many of them; there are far more languages.' });

  // =======================================================================================================
  // Chapter 1: sets, relations and functions
  // =======================================================================================================
  C.lesson({
    id: 'found-l-sets', chapter: 'found-sets', title: 'Sets and what you can do with them', minutes: 10,
    summary: 'A set is a collection where only membership matters. Union, intersection, difference and complement are regions of a Venn picture, and the power set collects every subset.',
    blocks: [
      'Almost every object in this course is a set in disguise. A machine has a *set* of states; a language is a *set* of strings; a problem is a *set* of yes-instances. So we start by making the word exact.',
      { def: 'Set', text: 'a collection of things, its **elements**. We write x ∈ A when x is an element of A. Two sets are equal when they have exactly the same elements, so order and repetition do not matter: {1, 2, 2} = {2, 1}.' },
      'The **empty set** ∅ has no elements at all. It is not "nothing": it is a perfectly good set, just one you cannot take anything out of. A is a **subset** of B, written A ⊆ B, when every element of A is also in B. In particular ∅ ⊆ B for every B, because ∅ has no element that could break the rule.',
      { h: 'Four ways to make new sets' },
      { math: 'A ∪ B = { x : x ∈ A or x ∈ B }        union\nA ∩ B = { x : x ∈ A and x ∈ B }       intersection\nA − B = { x : x ∈ A and x ∉ B }       difference\nAᶜ    = U − A                          complement (inside a universe U)' },
      'Each operation picks out some **regions** of a Venn picture. Watch the elements fall into their regions, then the regions of the answer light up.',
      { topic: 'set-ops', input: { U: ['1', '2', '3', '4', '5', '6', '7', '8', '9'], A: ['1', '2', '3', '4', '5'], B: ['4', '5', '6', '7'], op: 'sym' }, caption: 'A △ B, the elements in exactly one of A and B. Watch the middle region stay dark: 4 and 5 are in both, so they are out.' },
      { predict: { q: 'A = {1, 2, 3} and B = {3, 4}. How many elements does A − B have?', options: ['1', '2', '3', '5'], answer: 1, explain: 'A − B keeps the elements of A that are not in B: 1 and 2. The 4 never mattered, since it was not in A to begin with.' } },
      { warn: 'A − B and B − A are different sets. Difference, like subtraction of numbers, is not symmetric; only union, intersection and △ are.' },
      { h: 'De Morgan\'s laws' },
      'Being outside A ∪ B means being outside A *and* outside B. Being outside A ∩ B means being outside A *or* outside B. In symbols, (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ and (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ. Try the two De Morgan examples in the player\'s presets and check that both light the same region.',
      { h: 'The power set' },
      { def: 'Power set', text: 'P(S) is the set of all subsets of S, including ∅ and S itself. If S has n elements, P(S) has 2ⁿ.' },
      'Why 2ⁿ? Each subset is a sequence of n yes-or-no choices, one per element: is it in, or out? That is exactly an n-bit binary number, so counting the subsets is counting from 0 to 2ⁿ − 1.',
      { topic: 'set-powerset', input: { S: ['p', 'q', 'r'] }, caption: 'Each row is a binary number: a 1 under an element puts it in the subset. Watch 000 give ∅ and 111 give the whole set.' },
      { predict: { q: 'How many elements does P(∅) have?', options: ['0: the empty set has no subsets', '1: the empty set is a subset of itself', '2'], answer: 1, explain: 'P(∅) = {∅}. It has one element, the empty set. 2⁰ = 1 agrees.' } },
      { list: ['Only membership matters in a set: no order, no repeats.', '∪, ∩, − and complement each pick regions of the Venn picture.', 'A − B ≠ B − A in general.', '|P(S)| = 2^|S|, one bit per element; P(∅) = {∅}.'] },
      { exercise: 'found-ex-set-diff' }, { exercise: 'found-ex-set-sym' }, { exercise: 'found-ex-set-demorgan' }, { exercise: 'found-ex-powerset-size' }, { exercise: 'found-ex-powerset-empty' },
    ],
  });

  C.lesson({
    id: 'found-l-relations', chapter: 'found-sets', title: 'Pairs, products and relations', minutes: 12,
    summary: 'Ordered pairs make the Cartesian product; any set of pairs is a relation. Reflexive, symmetric, transitive and antisymmetric are the properties we check again and again.',
    blocks: [
      'Sets ignore order, but often order is the whole point: "3 is less than 5" is not the same statement as "5 is less than 3". For that we need **ordered pairs**.',
      { def: 'Ordered pair and product', text: '(x, y) is an ordered pair: (x, y) = (u, v) exactly when x = u and y = v. The Cartesian product A × B is the set of all pairs (x, y) with x ∈ A and y ∈ B. |A × B| = |A| · |B|.' },
      { topic: 'set-product', input: { A: ['p', 'q', 'r'], B: ['0', '1'], rel: 'none' }, caption: 'A × B as a grid: one cell per pair, rows from A and columns from B. Watch the count reach 3 · 2 = 6.' },
      { predict: { q: 'Is A × B the same set as B × A?', options: ['Always', 'Only when A = B, or when one of them is empty', 'Never'], answer: 1, explain: '(p, 0) is in {p} × {0} but not in {0} × {p}, whose only pair is (0, p). They agree only when A = B, or when either is empty, so both products are ∅.' } },
      { h: 'A relation is just a set of pairs' },
      { def: 'Relation', text: 'a relation on a set D is any subset R ⊆ D × D. We write x R y, or (x, y) ∈ R, when x is related to y.' },
      'That is the whole definition. "Less than" on {1, 2, 3} is the set {(1, 2), (1, 3), (2, 3)}.\nA relation can be drawn as arrows between the elements, a loop for each pair (x, x), or as a table with a mark in row x, column y for each pair (x, y).',
      { h: 'Four properties' },
      { table: [['property', 'it means', 'in the picture'], ['reflexive', '(x, x) ∈ R for every x ∈ D', 'a loop on every element'], ['symmetric', 'x R y implies y R x', 'every arrow has a partner coming back'], ['transitive', 'x R y and y R z imply x R z', 'every two-step path has a shortcut'], ['antisymmetric', 'x R y and y R x imply x = y', 'no two-way arrows between different elements']], caption: 'The properties of a relation R on D.' },
      { topic: 'rel-props', input: { D: ['a', 'b', 'c', 'd'], R: 'a-a, b-b, c-c, d-d, a-b, b-a, c-d' }, caption: 'Watch each property being tested. When one fails, the pairs that break it are lit: here c → d has no arrow back.' },
      { predict: { q: 'Is the empty relation on {1, 2, 3} transitive?', options: ['No, it has no pairs at all', 'Yes', 'It depends on the set'], answer: 1, explain: 'Transitivity says "whenever x R y and y R z, then ...". With no pairs, the "whenever" never happens, so nothing can break the rule. It is symmetric too, but not reflexive: the loops are missing.' } },
      { relation: { domain: 'p q r', pairs: '(p, p), (q, q), (r, r), (p, q), (q, p)', props: ['reflexive', 'symmetric', 'antisymmetric', 'transitive', 'equivalence'] }, caption: 'Loops on all three, and p and q paired both ways: every property but antisymmetry holds. Add (q, r) to the pairs. Which properties break, and which pairs would you have to add to mend them?' },
      { tip: 'Symmetric and antisymmetric are not opposites. A relation made only of loops, like {(a, a), (c, c)}, is both. A relation with (a, b), (b, a) and (b, c) is neither.' },
      { list: ['A × B holds every ordered pair; |A × B| = |A| · |B|.', 'A relation on D is any subset of D × D.', 'Check each property against its exact definition: empty cases pass the "whenever" rules.', 'Symmetric and antisymmetric can both hold, or neither.'] },
      { exercise: 'found-ex-product-list' }, { exercise: 'found-ex-product-size' }, { exercise: 'found-ex-rel-table' }, { exercise: 'found-ex-rel-fails' },
    ],
  });

  C.lesson({
    id: 'found-l-functions', chapter: 'found-sets', title: 'Functions: one-to-one, onto and both', minutes: 10,
    summary: 'A function is a relation with exactly one arrow out of each element. One-to-one means no two arrows meet; onto means every target is hit; both together is a bijection, which can be turned round.',
    blocks: [
      'A machine\'s transition function, a numbering of all strings, a reduction from one problem to another: all are functions. Two questions about functions come up constantly: does it lose information, and does it reach everything?',
      { def: 'Function', text: 'f : A → B is a relation from A to B in which every x ∈ A has **exactly one** y ∈ B with (x, y) ∈ f. We write f(x) = y. A is the domain, B the codomain.' },
      { warn: 'Both halves of "exactly one" matter. An element of A with no arrow out, or with two arrows out, means the relation is not a function at all.' },
      { def: 'One-to-one, onto, bijection', text: 'f is **one-to-one** (injective) when f(x) = f(x′) implies x = x′: no two arrows land on the same target. f is **onto** (surjective) when every y ∈ B is f(x) for some x. A **bijection** is both, and then it has an inverse f⁻¹ : B → A.' },
      { topic: 'fn-kinds', input: { A: ['1', '2', '3', '4'], B: ['p', 'q', 'r', 's', 't'], f: '1-q, 2-s, 3-p, 4-t' }, caption: 'Four arrows into five targets: watch the one-to-one test pass and the onto test find r with nothing pointing at it.' },
      { predict: { q: 'A has 5 elements and B has 3. Can some f : A → B be one-to-one?', options: ['Yes, if chosen carefully', 'No: two arrows must share a target'], answer: 1, explain: 'Five arrows, three targets: two arrows must land together. This is the pigeonhole principle, which gets a lesson of its own.' } },
      'For finite sets, the kinds of function compare sizes: a one-to-one f : A → B shows |A| ≤ |B|, an onto one shows |A| ≥ |B|, and a bijection shows |A| = |B|. For infinite sets we will **define** "the same size" by bijections, and the next chapter shows how strange that gets.',
      { h: 'Counting functions' },
      'A function from A to B makes one free choice in B for each element of A, so there are |B|^|A| of them. A one-to-one function must choose a new target each time: |B| · (|B| − 1) · … for |A| factors.',
      { list: ['A function has exactly one arrow out of each element.', 'One-to-one: no two arrows meet. Onto: every target is hit.', 'Bijection = both, and it can be turned round.', 'There are |B|^|A| functions from A to B.'] },
      { exercise: 'found-ex-fn-which' }, { exercise: 'found-ex-fn-kind' }, { exercise: 'found-ex-fn-count' }, { exercise: 'found-ex-fn-inj-count' },
    ],
  });

  // =======================================================================================================
  // Chapter 2: closures and equivalence
  // =======================================================================================================
  C.lesson({
    id: 'found-l-closures', chapter: 'found-closures', title: 'Closures: adding just enough', minutes: 12,
    summary: 'The closure of R under a property is the smallest relation that contains R and has the property. Reflexive and symmetric closures add loops and mirrors; Warshall\'s algorithm finds the transitive closure.',
    blocks: [
      'A relation says who can move to whom in **one step**: a machine moves from state to state, a grammar rewrites one string into another. The question we really care about is usually about **any number of steps**: can this state ever be reached? Can this string ever be derived? Closures turn the first kind of relation into the second.',
      { def: 'Closure', text: 'the closure of R under a property is the **smallest** relation that contains R and has the property. "Smallest" means it is a subset of every other relation that contains R and has the property.' },
      { list: ['**Reflexive closure**: add (x, x) for every x in D.', '**Symmetric closure**: add (y, x) for every (x, y) in R.', '**Transitive closure** R⁺: add (x, z) whenever z can be reached from x by one or more steps of R.', '**Reflexive-transitive closure** R*: zero or more steps, so the loops come too.'] },
      { h: 'Warshall\'s algorithm' },
      'Adding shortcuts one at a time can take many passes, because a new shortcut can make another two-step path. Warshall\'s idea is to take the elements one by one as **stepping stones**. In the round for k, add (i, j) whenever (i, k) and (k, j) are already there. After the round for k, every path whose middle points are among the stones used so far has its shortcut. One round per element is enough.',
      { topic: 'closure-warshall', input: { D: ['1', '2', '3', '4', '5'], R: '1-2, 2-3, 3-1, 4-5' }, caption: 'A triangle 1 → 2 → 3 → 1 and a separate 4 → 5. Watch the loops (1, 1), (2, 2), (3, 3) appear: going round the triangle brings you back. Nothing ever joins the two pieces.' },
      { predict: { q: 'R = {(a, b), (b, a)} on {a, b}. Is (a, a) in the transitive closure?', options: ['No: the closure only adds pairs between different elements', 'Yes: a → b → a is a path of two steps'], answer: 1, explain: 'The transitive closure adds (x, z) for every path, and nothing stops z from being x. Forgetting these loops is the most common closure mistake.' } },
      { warn: 'The transitive closure is not reflexive in general. An element on no cycle gets no loop: in the topic above, 4 and 5 stay without loops. Only R* adds every loop.' },
      { predict: { q: 'R is the chain 1 → 2 → 3 → 4. How many pairs are in its transitive closure?', options: ['3', '6', '10', '16'], answer: 1, explain: 'Every (i, j) with i < j: 3 + 2 + 1 = 6. No loops, since the chain has no cycle.' } },
      { list: ['Closure = the smallest superset with the property.', 'Reflexive: add loops. Symmetric: add mirrors.', 'Transitive: add a shortcut for every path; cycles bring loops.', 'Warshall: one round per element, used as a stepping stone.'] },
      { exercise: 'found-ex-trans-closure' }, { exercise: 'found-ex-refl-closure' }, { exercise: 'found-ex-sym-closure' }, { exercise: 'found-ex-chain-closure' }, { exercise: 'found-ex-rt-closure' },
    ],
  });

  C.lesson({
    id: 'found-l-equivalence', chapter: 'found-closures', title: 'Equivalence relations and partitions', minutes: 12,
    summary: 'A relation that is reflexive, symmetric and transitive cuts its set into classes that do not overlap. Every partition comes from exactly one equivalence relation, and back.',
    blocks: [
      'Often we want to say that two things are "the same for our purposes": two numbers with the same remainder, two strings of the same length, and later two strings that no automaton can tell apart. Equivalence relations make this exact, and they are behind one of the deepest results about automata.',
      { def: 'Equivalence relation', text: 'a relation on D that is reflexive, symmetric and transitive. The **class** of x is [x] = { y : y ~ x }.' },
      { def: 'Partition', text: 'a partition of D is a set of non-empty **blocks**, subsets of D, such that every element of D is in exactly one block.' },
      'The two ideas are one idea. The classes of an equivalence relation always form a partition: every x is in [x] (reflexive), and two classes that share one element are equal (symmetric and transitive). The other way round, any partition gives the equivalence "in the same block".',
      { topic: 'equiv-classes', input: { items: ['', 'a', 'b', 'aa', 'ab', 'ba', 'bb', 'aab'], rule: 'first' }, caption: 'Strings grouped by their first symbol. Watch ε go into a class of its own: it has no first symbol to share.' },
      { predict: { q: 'On the numbers 0 to 9, "x and y have the same remainder mod 4". How many classes?', options: ['3', '4', '10'], answer: 1, explain: 'One class per remainder: {0, 4, 8}, {1, 5, 9}, {2, 6}, {3, 7}. The classes need not be the same size.' } },
      { h: 'The smallest equivalence containing R' },
      'Given any relation R, we can close it under all three properties at once: add loops, mirror every pair, then take the transitive closure. The result is the smallest equivalence containing R, and its classes are the **connected pieces** of R\'s picture, arrow directions ignored.',
      { topic: 'closure-equivalence', input: { D: ['1', '2', '3', '4', '5', '6'], R: '1-3, 5-3, 2-6' }, caption: 'Watch 1, 3 and 5 merge into one class through 3, while 4 is left alone in a class of its own.' },
      { predict: { q: 'How many equivalence relations are there on {1, 2}?', options: ['1', '2', '4'], answer: 1, explain: 'One for each partition: {1}, {2} (equality) or {1, 2} (everything related).' } },
      { warn: 'A relation can be reflexive and symmetric yet not transitive: "x and y differ by at most 1" relates 1 to 2 and 2 to 3 but not 1 to 3. Its "classes" would overlap, which a partition never allows.' },
      { list: ['Equivalence = reflexive + symmetric + transitive.', 'Its classes form a partition, and every partition comes from one.', 'The smallest equivalence containing R groups the connected pieces of R.', 'An element related only to itself is a class of its own.'] },
      { exercise: 'found-ex-equiv-which' }, { exercise: 'found-ex-equiv-classes' }, { exercise: 'found-ex-equiv-closure' }, { exercise: 'found-ex-equiv-count' }, { exercise: 'found-ex-equiv-pairs' },
    ],
  });

  // =======================================================================================================
  // Chapter 3: countable and uncountable
  // =======================================================================================================
  C.lesson({
    id: 'found-l-countable', chapter: 'found-infinite', title: 'Counting infinite sets', minutes: 12,
    summary: 'A set is countable when its elements can be listed first, second, third, … with none left out. The integers, the pairs of numbers, the fractions and the finite strings are all countable.',
    blocks: [
      'Two finite sets have the same size when they can be paired off one to one. We keep that definition for infinite sets, and see where it takes us. It will take us somewhere surprising: a part can be as big as the whole.',
      { def: 'Countable', text: 'a set S is **countable** when it is finite or there is a bijection between ℕ = {0, 1, 2, …} and S. Equivalently, S can be listed s₀, s₁, s₂, … so that every element appears at some finite position.' },
      { topic: 'hilbert-hotel', input: { scen: 'bus' }, caption: 'Every room is taken, and infinitely many new guests arrive. Watch everyone move from room n to room 2n, freeing all the odd rooms.' },
      { predict: { q: 'With the rule n → 2n, which room does the guest from room 9 move to?', options: ['10', '18', '19'], answer: 1, explain: 'Doubling: 9 → 18. All the even rooms fill up and every odd room is free for the bus.' } },
      { h: 'Listing a grid' },
      'ℕ × ℕ, all pairs (i, j), looks much bigger than ℕ. But the listing only has to reach each pair at **some** finite step. Going row by row fails: the first row never ends, so (1, 0) is never reached. Going diagonal by diagonal works: diagonal d holds the d + 1 pairs with i + j = d, and each diagonal is finite.',
      { topic: 'count-pairs', input: { steps: 21, walk: 'zig' }, caption: 'Twenty-one steps finish diagonals 0 to 5. Watch the walk turn at the edge of each diagonal: every pair gets its number after finitely many steps.' },
      { predict: { q: 'Diagonal d has d + 1 pairs. How many steps finish diagonals 0 to 9?', options: ['45', '55', '100'], answer: 1, explain: '1 + 2 + … + 10 = 55.' } },
      'The positive fractions are pairs too, numerator and denominator, so they are countable as well; the walk just skips a fraction like 2/4 that was already counted as 1/2.',
      { topic: 'count-rationals', input: { steps: 20 }, caption: 'Watch the walk skip 2/2, 4/2, 3/3 and 2/4: each was already counted under a simpler name.' },
      { h: 'Strings are countable' },
      'All the finite strings over a finite alphabet can be listed in **shortlex order**: shorter strings first, and strings of the same length in dictionary order. Over {a, b}: ε, a, b, aa, ab, ba, bb, aaa, … There are finitely many strings of each length, so every string gets a position. This little fact will matter a great deal: programs, machines and grammars are all finite strings.',
      { list: ['Countable = can be listed with every element at a finite position.', 'An infinite set can be the same size as a part of itself.', 'Walk a grid by diagonals, not by rows.', 'ℤ, ℕ × ℕ, the fractions and Σ* are all countable.'] },
      { exercise: 'found-ex-hotel-room' }, { exercise: 'found-ex-diagonals' }, { exercise: 'found-ex-integer-list' }, { exercise: 'found-ex-shortlex-index' }, { exercise: 'found-ex-countable-which' },
    ],
  });

  C.lesson({
    id: 'found-l-uncountable', chapter: 'found-infinite', title: 'The diagonal argument: some sets are too big', minutes: 14,
    summary: 'No list of infinite 0/1 sequences can contain them all: flip the diagonal and you get a sequence the list missed. In the same way, no set is as big as its power set.',
    blocks: [
      'So far every infinite set we tried could be listed. Is every infinite set countable? No, and the proof is one of the most reused ideas in all of computer science. You will meet it again in the halting problem.',
      { h: 'Beat any list' },
      'Suppose someone hands you a list of infinite 0/1 sequences and claims it contains every one. Build a new sequence d: at place i, write the **opposite** of row i\'s digit at place i. Then d differs from row 0 at place 0, from row 1 at place 1, and in general from row i at place i. So d is in no row, and the list was not complete.',
      { topic: 'cantor-diagonal', input: { rows: ['1101001', '0010110', '1111000', '0100111', '1010101', '0001100'] }, caption: 'Six rows of a list. Watch the diagonal cells light one by one, each flipped into the new sequence d: it disagrees with every row somewhere.' },
      { predict: { q: 'The new sequence differs from row 4. Where is it guaranteed to differ?', options: ['At place 0', 'At place 4', 'At the last place', 'Nowhere in particular'], answer: 1, explain: 'Place 4 was built from row 4\'s own digit at place 4, flipped. Other places may agree or not; place 4 never does.' } },
      { def: 'Uncountable', text: 'a set that is not countable. The set of infinite 0/1 sequences is uncountable, and so are the real numbers.' },
      { tip: 'The argument works against **any** list, not just a badly chosen one. That is what makes it a proof: whoever builds the list, we can always build a sequence it misses.' },
      { h: 'Sets and their power sets' },
      'The same idea works with no digits at all. Take any function f : A → P(A), giving each element x a subset f(x). Let D = { x ∈ A : x ∉ f(x) }. If D were f(y) for some y, ask whether y ∈ D: by the definition of D, y ∈ D exactly when y ∉ f(y) = D. That is a contradiction, so D is no f(y), and f is not onto.',
      { topic: 'cantor-powerset', input: { A: ['p', 'q', 'r', 's'], f: ['pq', 'r', '-', 'qrs'] }, caption: 'For each x, ask whether x ∈ f(x). Watch D collect exactly the x that are not in their own f(x): here q and r.' },
      { predict: { q: 'Why does D differ from f(p) in the topic above?', options: ['Because p ∈ f(p) and p ∉ D', 'Because f(p) has two elements', 'Because D has more elements'], answer: 0, explain: 'D was built to disagree with f(x) on x itself. p is in f(p) = {p, q}, so p was left out of D.' } },
      'So for every set A, even an infinite one, P(A) is strictly bigger than A. In particular P(ℕ) is uncountable, and there is no largest infinity: P(ℕ), P(P(ℕ)), … each strictly bigger than the last.',
      { list: ['Flip the diagonal: the new row differs from row i at place i.', 'Infinite 0/1 sequences, the reals and P(ℕ) are uncountable.', 'D = { x : x ∉ f(x) } is no f(y): no set is as big as its power set.', 'The argument beats every list, not one particular list.'] },
      { exercise: 'found-ex-diag-bits' }, { exercise: 'found-ex-cantor-d' }, { exercise: 'found-ex-diag-why' }, { exercise: 'found-ex-decimals' },
    ],
  });

  // =======================================================================================================
  // Chapter 4: three proof techniques
  // =======================================================================================================
  C.lesson({
    id: 'found-l-induction', chapter: 'found-proofs', title: 'Induction: one step at a time', minutes: 12,
    summary: 'To prove P(n) for every n ≥ n₀, prove P(n₀), then prove that P(n) implies P(n + 1). Both halves are needed, and many checked cases are no proof at all.',
    blocks: [
      'We constantly prove things about every string, every derivation, every run of a machine. These are infinitely many cases, so we cannot check them one by one. Induction proves infinitely many cases with two finite arguments.',
      { def: 'Induction', text: 'to prove P(n) for every n ≥ n₀: prove the **base case** P(n₀), and prove the **step**: for every n ≥ n₀, if P(n) then P(n + 1). The assumption P(n) inside the step is the **induction hypothesis**.' },
      'Think of a row of dominoes. The base case knocks over the first. The step says each domino knocks over the next. Then every domino falls, and none needs to be pushed by hand.',
      { topic: 'induction-dominoes', input: { claim: 'odd', from: 1 }, caption: 'Watch the base case tip the first domino, then the step carry it along: adding the next odd number 2n + 1 to n² gives (n + 1)².' },
      { predict: { q: 'A claim is checked by computer for n = 1 to 1000 and holds every time. Is it proved for all n ≥ 1?', options: ['Yes, that is a lot of cases', 'No'], answer: 1, explain: 'Try the preset "n² + n + 11 is prime": it holds for many n in a row, then fails at n = 10, where 121 = 11 · 11. Cases are evidence, not proof.' } },
      { h: 'When one half is missing' },
      { topic: 'induction-dominoes', input: { claim: 'pow', from: 1 }, caption: '2ⁿ > n² starting at n = 1. Watch the chain break: the claim is false at n = 2, 3 and 4, so the step cannot carry it from 1. Started at n = 5 it works.' },
      'The opposite mistake is a good step with a false base. "n² + n is odd" has a step that works: if n² + n is odd, then (n + 1)² + (n + 1) = (n² + n) + 2(n + 1) is odd too. But the base fails, 1² + 1 = 2, and in fact the claim is false for every n.',
      { h: 'Strong induction' },
      'Sometimes P(n + 1) needs an earlier case, not just P(n). **Strong induction** lets the step assume P(k) for **all** k from n₀ to n. For example, every amount from 8 up can be paid with 3s and 5s: once 8, 9 and 10 are done, each later amount is three more than one already paid.',
      { topic: 'induction-dominoes', input: { claim: 'stamps', from: 8 }, caption: 'Watch three base cases fall by hand, then each new domino pushed by the one three places back.' },
      { list: ['Base case and step: both are needed.', 'The step proves "P(n) ⇒ P(n + 1)" for every n, not P(n + 1) itself.', 'Many checked cases prove nothing.', 'Strong induction may lean on any earlier case; give enough base cases.'] },
      { exercise: 'found-ex-ind-parts' }, { exercise: 'found-ex-ind-threshold' }, { exercise: 'found-ex-ind-flaw' }, { exercise: 'found-ex-coins' },
    ],
  });

  C.lesson({
    id: 'found-l-pigeonhole', chapter: 'found-proofs', title: 'The pigeonhole principle', minutes: 10,
    summary: 'Put more than k things into k holes and some hole holds two. With n things, some hole holds at least ⌈n / k⌉. This is why a machine with finitely many states must repeat a state on a long input.',
    blocks: [
      'Some facts are true for the plainest reason: there is not enough room. The pigeonhole principle makes "not enough room" into a proof.',
      { def: 'Pigeonhole principle', text: 'if n things are placed into k holes and n > k, some hole holds at least two. More generally, some hole holds at least ⌈n / k⌉ things.' },
      'The hard part is never the principle itself; it is choosing the holes. The holes should be the thing you want two items to share: a remainder, a birth month, a state of a machine.',
      { topic: 'pigeonhole', input: { scen: 'mod', items: ['23', '8', '15', '42', '31', '7'], k: 5 }, caption: 'Six numbers into five holes, one per remainder mod 5. Watch 8 land in the hole 23 already holds: both leave remainder 3, so their difference is a multiple of 5.' },
      { predict: { q: 'Four numbers into holes mod 4. Must two share a hole?', options: ['Yes', 'No: four things fit into four holes one each'], answer: 1, explain: 'n > k is needed. With four numbers like 8, 13, 6, 3 every remainder is used once. The preset "4 numbers mod 4" shows it.' } },
      { topic: 'pigeonhole', input: { scen: 'pairs', items: ['1', '4', '7', '10', '6', '3'], k: 5 }, caption: 'Six numbers from 1 to 10. The holes are the pairs {1, 2}, {3, 4}, …, {9, 10}. Watch two numbers fall into one pair: they are neighbours.' },
      { h: 'Why automata care' },
      'A machine with k states that reads a string of length k visits k + 1 states, counting the start. Those are k + 1 pigeons in k holes: some state is visited twice, so the run has a loop. That loop is the heart of the pumping lemma in the next part.',
      { predict: { q: 'A DFA has 4 states. What is the longest input it can read without visiting any state twice?', options: ['3', '4', '5'], answer: 0, explain: 'Reading 3 symbols visits 4 states, which can all be different. Reading 4 visits 5, and five pigeons do not fit into four holes.' } },
      { list: ['More than k things in k holes: some hole holds two.', 'n things in k holes: some hole holds at least ⌈n / k⌉.', 'The skill is choosing the holes.', 'A long enough run must repeat a state.'] },
      { exercise: 'found-ex-pigeon-week' }, { exercise: 'found-ex-pigeon-dfa' }, { exercise: 'found-ex-pigeon-sum' },
    ],
  });

  C.lesson({
    id: 'found-l-diagonalisation', chapter: 'found-proofs', title: 'Diagonalisation as a technique', minutes: 10,
    summary: 'Given any list of objects, build a new one that differs from the i-th object at the i-th place. It proves a list is incomplete, and later that some problems cannot be solved.',
    blocks: [
      'We met diagonalisation as Cantor\'s argument. Here it is as a general recipe, because you will use it to prove things nobody can compute.',
      { steps: ['Suppose a list f₀, f₁, f₂, … of objects of some kind.', 'Build a new object g by changing the diagonal: g(n) is made different from fₙ(n).', 'Then g ≠ fₙ for every n, since they disagree at n.', 'So the list is not complete; if it was claimed to be, that claim is false.'] },
      { topic: 'diagonal-functions', input: { fs: ['tri', 'seven', 'dbl', 'sq', 'inc'], change: 'plus' }, caption: 'Five functions from ℕ to ℕ, and g(n) = fₙ(n) + 1. Watch each diagonal value grow by one: g differs from every row where its row meets the diagonal.' },
      { predict: { q: 'Could g be on the list after all, say at row 1000?', options: ['Yes, if the list is long enough', 'No: g(1000) = f₁₀₀₀(1000) + 1, so g ≠ f₁₀₀₀'], answer: 1, explain: 'Whatever row you name, g was built to disagree with it on that row\'s own index.' } },
      { h: 'The change must always change' },
      'The only rule is that the new value must differ from the old one **every time**. "Add 1" always does. "Double" does not: when fₙ(n) = 0, doubling gives 0 again, and g may agree with fₙ.',
      { topic: 'diagonal-functions', input: { fs: ['inc', 'zero', 'sq', 'pow'], change: 'times' }, caption: 'The broken recipe. Watch row 1, the zero function: its diagonal value 0 doubles to 0, so nothing proves g differs from it.' },
      { warn: 'A diagonal proof needs a change that never leaves a value as it was. Check the edge case: 0 for doubling, 5 ↔ 4 rather than 0 ↔ 9 for decimals.' },
      { list: ['List, go down the diagonal, change each value, conclude.', 'g differs from row n at place n.', 'The change must always change the value.', 'The halting problem is this argument, with programs as the rows.'] },
      { exercise: 'found-ex-diag-fns' }, { exercise: 'found-ex-diag-double' },
    ],
  });

  // =======================================================================================================
  // Chapter 5: strings and languages
  // =======================================================================================================
  C.lesson({
    id: 'found-l-strings', chapter: 'found-strings', title: 'Alphabets and strings', minutes: 10,
    summary: 'An alphabet is a finite set of symbols, a string a finite sequence of them. Concatenation, reversal, prefixes and suffixes, and Σ*, the set of all strings, listed in shortlex order.',
    blocks: [
      'Everything a computer reads is a string: a program, a file, a number in binary. Theory of computation describes problems as questions about strings, so strings are our raw material.',
      { def: 'Alphabet and string', text: 'an **alphabet** Σ is a finite, non-empty set of symbols. A **string** over Σ is a finite sequence of symbols from Σ. Its **length** |w| is the number of symbols. The **empty string** ε has length 0.' },
      { warn: 'ε is a string, not a symbol, and never part of the alphabet. It is not the empty set either: ∅ is a set with no strings, while ε is one string with no symbols.' },
      { h: 'Operations on strings' },
      { math: 'uv            concatenation: u followed by v, |uv| = |u| + |v|\nwᴿ            reversal: w backwards\nwⁿ            w repeated n times; w⁰ = ε\nprefix of w   any u with w = uv; suffix: any v with w = uv' },
      { topic: 'string-ops', input: { u: 'ba', v: 'cca', op: 'revcat' }, caption: 'Reverse uv and it equals vᴿ uᴿ, not uᴿ vᴿ. Watch the two pieces swap places as well as turning round.' },
      { predict: { q: 'How many prefixes does a string of length 5 have?', options: ['4', '5', '6'], answer: 2, explain: 'One of each length from 0 to 5: ε, the first symbol, …, the whole string. 6 in all.' } },
      { tip: 'εw = wε = w for every string w: ε is the identity for concatenation, as 0 is for addition.' },
      { h: 'Σ*: all strings' },
      { def: 'Σ*', text: 'the set of all strings over Σ, including ε. Σⁿ is the set of strings of length exactly n, and |Σⁿ| = |Σ|ⁿ.' },
      { topic: 'sigma-star', input: { sigma: ['x', 'y', 'z'], n: 2 }, caption: 'Σ = {x, y, z}: 1 string of length 0, 3 of length 1, 9 of length 2. Watch the shortlex order: by length first, then like a dictionary.' },
      'Σ* is infinite, yet every one of its strings is finite. Do not confuse "infinitely many strings" with "an infinitely long string": Σ* contains no infinite string.',
      { h: 'Try it' },
      { sandbox: { kind: 'regex', text: '(a|b)(a|b)(a|b)', input: 'bab' }, caption: 'This expression matches Σ³ for Σ = {a, b}. Try strings of other lengths: only the 8 strings of length 3 are accepted.' },
      { list: ['An alphabet is finite; strings over it are finite sequences.', 'ε is the string of length 0, not a symbol and not ∅.', '(uv)ᴿ = vᴿuᴿ.', '|Σⁿ| = |Σ|ⁿ, and Σ* lists in shortlex order.'] },
      { exercise: 'found-ex-rev-cat' }, { exercise: 'found-ex-substrings' }, { exercise: 'found-ex-sigma-count' },
    ],
  });

  C.lesson({
    id: 'found-l-languages', chapter: 'found-strings', title: 'Languages and their operations', minutes: 14,
    summary: 'A language is any set of strings. Besides the set operations, languages concatenate and take powers and the star. ∅ and {ε} behave very differently, and the star always contains ε.',
    blocks: [
      'A **language** over Σ is any subset of Σ*: finite or infinite, simple or wild. "Binary numbers divisible by 3", "balanced brackets" and "programs that halt" are all languages. Every question the course asks is about some language.',
      { h: 'Set operations and concatenation' },
      'Since languages are sets, union, intersection, difference and complement (with Σ* as the universe) all apply. And because their elements are strings, there is one more operation.',
      { def: 'Concatenation of languages', text: 'AB = { uv : u ∈ A and v ∈ B }: one piece from A followed by one from B. Powers: A⁰ = {ε}, Aⁿ⁺¹ = AⁿA.' },
      { topic: 'lang-ops', input: { A: ['b', 'bb'], B: ['', 'b'], op: 'concat' }, caption: '{b, bb} · {ε, b}. Four pairs, but watch two of them glue into the same string bb: the result has only three strings.' },
      { predict: { q: 'What is {a, b} · ∅?', options: ['{a, b}', '∅', '{ε}'], answer: 1, explain: 'A string of A∅ needs a piece from ∅, and there is none. ∅ behaves like 0 in multiplication, while {ε} behaves like 1.' } },
      { table: [['', 'behaves like', 'example'], ['∅', '0: L∅ = ∅L = ∅', '{a} · ∅ = ∅'], ['{ε}', '1: L{ε} = {ε}L = L', '{a} · {ε} = {a}']], caption: 'The two smallest languages.' },
      { h: 'The star' },
      { def: 'Kleene star', text: 'A* = A⁰ ∪ A¹ ∪ A² ∪ …: all strings made by gluing together **zero or more** pieces from A. A⁺ = AA* asks for at least one piece.' },
      { topic: 'lang-star', input: { A: ['b', 'aba'], n: 5 }, caption: 'The star of {b, aba}, level by level: zero pieces, one piece, two, …. Watch ε arrive at level 0, and every string keep its a\'s in pairs inside aba blocks.' },
      { predict: { q: 'What is ∅*?', options: ['∅', '{ε}', 'Σ*'], answer: 1, explain: 'Zero pieces are always allowed, giving ε; there is nothing else to glue. So ∅* = {ε}, not ∅.' } },
      { warn: 'A* always contains ε, whatever A is. And A⁺ contains ε only when ε ∈ A.' },
      { h: 'Try it' },
      'Regular expressions, the subject of the next part, write these operations down: | for union, juxtaposition for concatenation, * for the star. Here is (b|aba)*, the language above. Add and remove test lines to see which strings belong.',
      { editor: { kind: 'regex', text: '(b|aba)*', tests: 'ε\nb\naba\nbabab\nabaaba\n-a\n-ab\n-abab' }, caption: 'Press Test. Lines starting with − should be rejected; can you see why abab is out?' },
      { list: ['A language is any set of strings.', 'AB glues one piece from A to one from B; repeats collapse.', '∅ is like 0, {ε} is like 1.', 'A* = zero or more pieces, so ε ∈ A* always; ∅* = {ε}.'] },
      { exercise: 'found-ex-concat-set' }, { exercise: 'found-ex-lang-table' }, { exercise: 'found-ex-empty-eps' }, { exercise: 'found-ex-star-member' }, { exercise: 'found-ex-star-regex' }, { exercise: 'found-ex-both-ends' }, { exercise: 'found-ex-reverse-lang' },
    ],
  });

  // =======================================================================================================
  // Chapter 6: finite descriptions
  // =======================================================================================================
  C.lesson({
    id: 'found-l-descriptions', chapter: 'found-descriptions', title: 'Why most languages have no description', minutes: 12,
    summary: 'Every expression, grammar, machine or program is a finite string, so there are countably many. The languages over {a} alone are uncountable. So almost every language has no finite description at all.',
    blocks: [
      'The rest of the course studies ways to describe languages: regular expressions, grammars, automata, Turing machines. Before we start, a sobering fact: whatever kind of description we choose, it misses almost every language. The proof needs nothing but the two halves of the last chapter.',
      { h: 'Descriptions are countable' },
      'A regular expression is a finite string over a finite alphabet of symbols and operators. So is a grammar, a machine table and a program. Σ* of any finite alphabet is countable, so the set of all descriptions of any one kind is countable: list them in shortlex order and skip the ones that do not parse.',
      { h: 'Languages are not' },
      'A language over {a} is any subset of {ε, a, aa, aaa, …}. Write it as an infinite 0/1 sequence: the n-th bit says whether aⁿ is in. Every 0/1 sequence is some language and the other way round, so the languages over {a} are as many as the infinite 0/1 sequences: uncountably many.',
      { topic: 'counting-languages', input: { ds: ['a*', '(aa)*', 'ε|b', 'b*a', '∅', 'ab*'] }, caption: 'Six descriptions, each a row of bits for ε, a, b, aa, …. Watch the diagonal produce a language that disagrees with every one of them.' },
      { predict: { q: 'The topic shows six descriptions. Would it help to list a million, or every regular expression there is?', options: ['Yes, eventually the list would cover every language', 'No: any list, even an infinite one, is beaten by its diagonal'], answer: 1, explain: 'The diagonal language differs from the n-th listed language on the n-th string. However long the list, the diagonal is not on it.' } },
      'Putting the two together: countably many descriptions, uncountably many languages. A description describes one language, so most languages are described by none. Not just a few: "most" in the strong sense that the describable ones form a countable sliver of an uncountable set.',
      { tip: 'This holds for every kind of finite description at once, including programs in any programming language. So there are languages that no program can recognise. Later parts will find specific ones, starting with the halting problem.' },
      { h: 'Try it' },
      { sandbox: { kind: 'regex', text: 'a(aa)*', input: 'aaa' }, caption: 'One description, one language: the odd-length runs of a. Its bits for ε, a, aa, aaa, … are 0101…. Change the expression and see which bits change.' },
      { list: ['Every description is a finite string, so there are countably many.', 'Languages over even one symbol are uncountable: one bit per string.', 'So almost every language has no finite description.', 'The diagonal language beats any list of described languages.'] },
      { exercise: 'found-ex-desc-count' }, { exercise: 'found-ex-uncountable-which' }, { exercise: 'found-ex-char-bits' }, { exercise: 'found-ex-diag-lang' }, { exercise: 'found-ex-most-why' },
    ],
  });

  // =======================================================================================================
  // Exercises
  // =======================================================================================================
  // ---- chapter 1 -----------------------------------------------------------------------------------------
  ex({ id: 'found-ex-set-diff', chapter: 'found-sets', title: 'A difference of sets', kind: 'string', accept: setOf(['2', '11']),
    text: 'A = {2, 3, 5, 7, 11} and B = {1, 3, 5, 7, 9}. Write A − B as a set, like {x, y}.',
    solution: '{2, 11}', wrong: ['{1, 9}', '{3, 5, 7}', '{1, 2, 9, 11}'],
    hints: H('A − B keeps what is in A and not in B.', 'Go through A: 3, 5 and 7 are also in B, so they go.', '{2, 11}') });
  ex({ id: 'found-ex-set-sym', chapter: 'found-sets', title: 'In exactly one of them', kind: 'string', accept: setOf(['1', '2', '9', '11']),
    text: 'With the same A = {2, 3, 5, 7, 11} and B = {1, 3, 5, 7, 9}, write A △ B, the elements in exactly one of the two sets.',
    solution: '{1, 2, 9, 11}', wrong: ['{2, 11}', '{3, 5, 7}', '{1, 2, 3, 5, 7, 9, 11}'],
    hints: H('A △ B = (A − B) ∪ (B − A).', 'A − B = {2, 11}; B − A = {1, 9}.', '{1, 2, 9, 11}') });
  ex({ id: 'found-ex-set-demorgan', chapter: 'found-sets', title: 'Outside the overlap', kind: 'string', level: 2, accept: setOf(['1', '2', '4', '5', '6', '7', '8']),
    text: 'In the universe U = {1, 2, …, 8}, A = {1, 2, 3} and B = {3, 4, 5}. Write Aᶜ ∪ Bᶜ as a set.',
    solution: '{1, 2, 4, 5, 6, 7, 8}', wrong: ['{6, 7, 8}', '{1, 2, 4, 5}', '{3}'],
    hints: H('By De Morgan, Aᶜ ∪ Bᶜ = (A ∩ B)ᶜ.', 'A ∩ B = {3}.', 'Everything in U but 3: {1, 2, 4, 5, 6, 7, 8}.') });
  ex({ id: 'found-ex-powerset-size', chapter: 'found-sets', title: 'Counting subsets', kind: 'number', answer: 32,
    text: 'How many elements does the power set of {p, q, r, s, t} have?',
    solution: '32', wrong: ['25', '10', '31'],
    hints: H('Each subset is one in-or-out choice per element.', 'Five elements, two choices each.', '2⁵ = 32, counting ∅ and the whole set.') });
  ex({ id: 'found-ex-powerset-empty', chapter: 'found-sets', title: 'The power set of nothing', kind: 'choice',
    text: 'Which set is P(∅), the power set of the empty set?',
    options: ['∅', '{∅}', '{ε}', '{∅, {∅}}'], answer: 1, why: 'The only subset of ∅ is ∅ itself, so P(∅) has exactly one element.',
    whyNot: { 0: 'P(∅) is not empty: ∅ is a subset of itself.', 2: 'ε is the empty string, not the empty set.', 3: '{∅} is not a subset of ∅, since ∅ has no elements.' },
    solution: 1, wrong: [0, 2, 3],
    hints: H('List the subsets of ∅. Is ∅ a subset of ∅?', 'Yes, and it is the only one: 2⁰ = 1.', '{∅}') });
  ex({ id: 'found-ex-product-list', chapter: 'found-sets', title: 'Write out a product', kind: 'string', accept: pairSet('u-0, u-1, v-0, v-1'),
    text: 'Write out {u, v} × {0, 1}, every ordered pair, like (u, 0), (u, 1), ….',
    solution: '(u, 0), (u, 1), (v, 0), (v, 1)', wrong: ['(0, u), (1, u), (0, v), (1, v)', '(u, 0), (v, 1)', '(u, 0), (u, 1), (v, 0), (v, 1), (u, v)'],
    hints: H('The first coordinate comes from the first set.', 'Two choices first, two choices second: four pairs.', '(u, 0), (u, 1), (v, 0), (v, 1)') });
  ex({ id: 'found-ex-product-size', chapter: 'found-sets', title: 'The size of a triple product', kind: 'number', answer: 12,
    text: 'A = {x, y, z} and B = {0, 1}. How many elements does A × B × B have? (Its elements are triples like (x, 0, 1).)',
    solution: '12', wrong: ['7', '9', '6'],
    hints: H('Sizes multiply, they do not add.', '|A| · |B| · |B|.', '3 · 2 · 2 = 12.') });
  ex({ id: 'found-ex-rel-table', chapter: 'found-sets', title: 'Which properties hold?', kind: 'table', table: 'custom', level: 2,
    text: 'Five relations on D = {1, 2, 3}. R1 = {(1,1), (2,2), (3,3), (1,2)}; R2 = {(1,2), (2,1)}; R3 = {(1,1), (2,2), (3,3), (1,3), (3,1)}; R4 = ∅; R5 = {(1,2), (2,3), (1,3)}. For each, write yes or no under reflexive, symmetric and transitive.',
    rows: ['R1', 'R2', 'R3', 'R4', 'R5'], cols: ['reflexive', 'symmetric', 'transitive'],
    cells: { 'R1|reflexive': 'yes', 'R1|symmetric': 'no', 'R1|transitive': 'yes', 'R2|reflexive': 'no', 'R2|symmetric': 'yes', 'R2|transitive': 'no', 'R3|reflexive': 'yes', 'R3|symmetric': 'yes', 'R3|transitive': 'yes', 'R4|reflexive': 'no', 'R4|symmetric': 'yes', 'R4|transitive': 'yes', 'R5|reflexive': 'no', 'R5|symmetric': 'no', 'R5|transitive': 'yes' },
    solution: { 'R1|reflexive': 'yes', 'R1|symmetric': 'no', 'R1|transitive': 'yes', 'R2|reflexive': 'no', 'R2|symmetric': 'yes', 'R2|transitive': 'no', 'R3|reflexive': 'yes', 'R3|symmetric': 'yes', 'R3|transitive': 'yes', 'R4|reflexive': 'no', 'R4|symmetric': 'yes', 'R4|transitive': 'yes', 'R5|reflexive': 'no', 'R5|symmetric': 'no', 'R5|transitive': 'yes' },
    wrong: [
      { 'R1|reflexive': 'yes', 'R1|symmetric': 'no', 'R1|transitive': 'yes', 'R2|reflexive': 'no', 'R2|symmetric': 'yes', 'R2|transitive': 'no', 'R3|reflexive': 'yes', 'R3|symmetric': 'yes', 'R3|transitive': 'yes', 'R4|reflexive': 'no', 'R4|symmetric': 'no', 'R4|transitive': 'no', 'R5|reflexive': 'no', 'R5|symmetric': 'no', 'R5|transitive': 'yes' },
      { 'R1|reflexive': 'yes', 'R1|symmetric': 'no', 'R1|transitive': 'yes', 'R2|reflexive': 'no', 'R2|symmetric': 'yes', 'R2|transitive': 'yes', 'R3|reflexive': 'yes', 'R3|symmetric': 'yes', 'R3|transitive': 'yes', 'R4|reflexive': 'no', 'R4|symmetric': 'yes', 'R4|transitive': 'yes', 'R5|reflexive': 'no', 'R5|symmetric': 'no', 'R5|transitive': 'yes' },
    ],
    hints: H('Reflexive needs all three loops; symmetric needs every arrow mirrored; transitive needs a shortcut for every two-step path.', 'In R2, (1, 2) and (2, 1) make a path from 1 to 1, so (1, 1) would be needed. The empty relation R4 breaks no "whenever" rule.', 'R1: yes no yes. R2: no yes no. R3: yes yes yes. R4: no yes yes. R5: no no yes.') });
  ex({ id: 'found-ex-rel-fails', chapter: 'found-sets', title: 'What goes wrong?', kind: 'choice', level: 2,
    text: 'R = {(a,a), (b,b), (c,c), (a,b), (b,c)} on D = {a, b, c}. Which properties does R **fail** to have? Choose all that fail.',
    options: ['reflexive', 'symmetric', 'transitive', 'antisymmetric'], answer: [1, 2], why: '(a, b) has no mirror, and a → b → c has no shortcut (a, c). It is antisymmetric: no two-way arrows between different elements.',
    solution: [1, 2], wrong: [[2], [1, 2, 3], [0, 1, 2]],
    hints: H('Check each definition separately.', 'Is (b, a) there? Is (a, c) there?', 'It fails symmetric and transitive; it is reflexive and antisymmetric.') });
  ex({ id: 'found-ex-fn-which', chapter: 'found-sets', title: 'Is it a function?', kind: 'choice',
    text: 'Which of these sets of arrows are functions from {1, 2, 3} to {a, b}? Choose all that are.',
    options: ['1 → a, 2 → a, 3 → a', '1 → a, 2 → b', '1 → a, 1 → b, 2 → a, 3 → b', '1 → b, 2 → a, 3 → b'], answer: [0, 3], why: 'Each needs exactly one arrow out of every element of the domain. Sharing targets is fine.',
    solution: [0, 3], wrong: [[3], [0, 1, 3], [0, 2, 3]],
    hints: H('Count the arrows leaving each of 1, 2 and 3.', 'The second leaves 3 with no arrow; the third gives 1 two arrows.', 'The first and the last.') });
  ex({ id: 'found-ex-fn-kind', chapter: 'found-sets', title: 'Adding two', kind: 'choice', level: 2,
    text: 'f : ℕ → ℕ with f(n) = n + 2, where ℕ = {0, 1, 2, …}. What kind of function is it?',
    options: ['one-to-one, not onto', 'onto, not one-to-one', 'a bijection', 'neither'], answer: 0, why: 'Different n give different n + 2, but 0 and 1 are never hit.',
    whyNot: { 2: 'Which n has f(n) = 0?', 1: 'Can two different n give the same n + 2?' },
    solution: 0, wrong: [1, 2, 3],
    hints: H('One-to-one: can f(n) = f(m) with n ≠ m?', 'Onto: is every number in ℕ some n + 2?', 'One-to-one but not onto: 0 and 1 are missed.') });
  ex({ id: 'found-ex-fn-count', chapter: 'found-sets', title: 'How many functions?', kind: 'number', level: 2, answer: 8,
    text: 'How many functions are there from {1, 2, 3} to {a, b}?',
    solution: '8', wrong: ['6', '9', '5'],
    hints: H('Each of 1, 2, 3 picks one target, independently.', 'Two choices, three times.', '2³ = 8.') });
  ex({ id: 'found-ex-fn-inj-count', chapter: 'found-sets', title: 'How many one-to-one functions?', kind: 'number', level: 2, answer: 12,
    text: 'How many one-to-one functions are there from {1, 2} to {a, b, c, d}?',
    solution: '12', wrong: ['16', '6', '8'],
    hints: H('1 picks any target; then 2 must pick a different one.', '4 choices, then 3.', '4 · 3 = 12.') });

  // ---- chapter 2 -----------------------------------------------------------------------------------------
  ex({ id: 'found-ex-trans-closure', chapter: 'found-closures', title: 'A transitive closure', kind: 'string', level: 2, accept: pairSet('a-b, a-c, b-b, b-c, c-b, c-c, d-a, d-b, d-c'),
    text: 'R = {(a,b), (b,c), (c,b), (d,a)} on {a, b, c, d}. List every pair of its transitive closure R⁺, like a-b, a-c, ….',
    solution: 'a-b, a-c, b-b, b-c, c-b, c-c, d-a, d-b, d-c',
    wrong: ['a-b, a-c, b-c, c-b, d-a, d-b, d-c', 'a-a, b-b, c-c, d-d, a-b, a-c, b-c, c-b, d-a, d-b, d-c', 'a-b, b-c, c-b, d-a, a-c, d-b'],
    hints: H('For each element, list everything reachable in one or more steps.', 'b → c → b is a cycle, so b reaches b and c reaches c.', 'a: b, c; b: b, c; c: b, c; d: a, b, c. Nine pairs.') });
  ex({ id: 'found-ex-refl-closure', chapter: 'found-closures', title: 'Adding the loops', kind: 'number', answer: 7,
    text: 'R = {(1,1), (1,2), (3,4)} on D = {1, 2, 3, 4, 5}. How many pairs does the reflexive closure of R have?',
    solution: '7', wrong: ['8', '5', '3'],
    hints: H('Add (x, x) for every x in D that does not have it yet.', '(1, 1) is already there; four loops are missing.', '3 + 4 = 7.') });
  ex({ id: 'found-ex-sym-closure', chapter: 'found-closures', title: 'Adding the mirrors', kind: 'string', accept: pairSet('p-q, q-p, q-r, r-q, r-r'),
    text: 'R = {(p,q), (q,r), (r,r)} on {p, q, r}. List every pair of the symmetric closure of R.',
    solution: '(p, q), (q, p), (q, r), (r, q), (r, r)', wrong: ['p-q, q-p, q-r, r-q', 'p-q, q-p, q-r, r-q, r-r, p-r, r-p', 'p-p, q-q, r-r, p-q, q-p, q-r, r-q'],
    hints: H('Keep R and add the reverse of every pair.', 'A loop is its own mirror.', '(p, q), (q, p), (q, r), (r, q), (r, r)') });
  ex({ id: 'found-ex-chain-closure', chapter: 'found-closures', title: 'Closing a long chain', kind: 'number', level: 2, answer: 15,
    text: 'R is the chain 1 → 2 → 3 → 4 → 5 → 6 on {1, …, 6}. How many pairs are in its transitive closure?',
    solution: '15', wrong: ['5', '21', '36'],
    hints: H('The closure holds (i, j) when j can be reached from i.', 'Exactly the pairs with i < j; with no cycle there are no loops.', '5 + 4 + 3 + 2 + 1 = 15.') });
  ex({ id: 'found-ex-rt-closure', chapter: 'found-closures', title: 'Zero or more steps', kind: 'string', level: 2, accept: pairSet('p-p, q-q, r-r, p-q, q-r, p-r'),
    text: 'R = {(p,q), (q,r)} on {p, q, r}. List every pair of R*, the reflexive-transitive closure.',
    solution: 'p-p, q-q, r-r, p-q, q-r, p-r', wrong: ['p-q, q-r, p-r', 'p-p, q-q, r-r, p-q, q-r', 'p-p, q-q, r-r, p-q, q-p, q-r, r-q, p-r, r-p'],
    hints: H('R* relates x to y when y can be reached in zero or more steps.', 'Zero steps gives every loop; two steps gives p → r.', 'p-p, q-q, r-r, p-q, q-r, p-r') });
  ex({ id: 'found-ex-equiv-which', chapter: 'found-closures', title: 'Spot the equivalences', kind: 'choice',
    text: 'Which of these relations on the strings over {a, b} are equivalence relations? Choose all that are.',
    options: ['u and v have the same length', 'u is a prefix of v', 'u and v end in the same symbol, or are both ε', 'their lengths differ by at most 1', 'they have the same number of b\'s, mod 2'], answer: [0, 2, 4],
    why: 'Each of the three is "same value of some function", which is always an equivalence.',
    solution: [0, 2, 4], wrong: [[0, 2], [0, 1, 2, 4], [0, 2, 3, 4]],
    hints: H('Test each for reflexive, symmetric and transitive.', 'Prefix is not symmetric; "differ by at most 1" is not transitive (lengths 1, 2, 3).', 'Same length, same last symbol, and same parity of b\'s.') });
  ex({ id: 'found-ex-equiv-classes', chapter: 'found-closures', title: 'Classes of strings', kind: 'string', level: 2, accept: partition([['', 'a', 'aa'], ['b', 'ab', 'ba'], ['bb']]),
    text: 'Take the strings over {a, b} of length at most 2, and relate two when they have the same number of b\'s. Write the classes, each in braces, like {x, y}, {z}. Write the empty string as ε.',
    solution: '{ε, a, aa}, {b, ab, ba}, {bb}', wrong: ['{a, aa}, {b, ab, ba}, {bb}', '{ε, a, aa}, {b, ab, ba, bb}', '{ε}, {a, aa}, {b, ab, ba}, {bb}'],
    hints: H('There are 7 strings: ε, a, b, aa, ab, ba, bb.', 'Group by the count of b: 0, 1 or 2. ε has zero b\'s.', '{ε, a, aa}, {b, ab, ba}, {bb}') });
  ex({ id: 'found-ex-equiv-closure', chapter: 'found-closures', title: 'The smallest equivalence', kind: 'set', level: 2, answer: '{{1, 4, 6}, {2, 5}, {3}}',
    text: 'R = {(1,4), (2,5), (4,6)} on {1, 2, 3, 4, 5, 6}. Write the classes of the smallest equivalence relation containing R, each in braces.',
    solution: '{1, 4, 6}, {2, 5}, {3}', wrong: ['{1, 4, 6}, {2, 5}', '{1, 4}, {4, 6}, {2, 5}, {3}', '{1, 4, 6}, {2, 3, 5}'],
    hints: H('The classes are the connected pieces of R, ignoring directions.', '1–4–6 is one piece, 2–5 another. Do not forget elements R never mentions.', '{1, 4, 6}, {2, 5}, {3}') });
  ex({ id: 'found-ex-equiv-count', chapter: 'found-closures', title: 'How many equivalences?', kind: 'number', level: 2, answer: 5,
    text: 'How many different equivalence relations are there on the set {1, 2, 3}?',
    solution: '5', wrong: ['3', '8', '4'],
    hints: H('Equivalence relations match partitions one to one.', 'All apart; all together; or one pair together and the third alone, in three ways.', '1 + 1 + 3 = 5.') });
  ex({ id: 'found-ex-equiv-pairs', chapter: 'found-closures', title: 'Pairs in an equivalence', kind: 'number', level: 2, answer: 18,
    text: 'On {1, 2, 3, 4, 5, 6}, relate x and y when they are both even or both odd. How many pairs (x, y) are in the relation, loops included?',
    solution: '18', wrong: ['9', '6', '15'],
    hints: H('Inside one class every element is related to every element, itself included.', 'Two classes of 3 elements each; a class of size k gives k² pairs.', '9 + 9 = 18.') });

  // ---- chapter 3 -----------------------------------------------------------------------------------------
  ex({ id: 'found-ex-hotel-room', chapter: 'found-infinite', title: 'A room for the bus', kind: 'number', answer: 11,
    text: 'The hotel has rooms 1, 2, 3, … all full. Everyone moves from room n to room 2n, and the k-th passenger of an infinite bus takes room 2k − 1. Which room does passenger 6 get?',
    solution: '11', wrong: ['12', '6', '13'],
    hints: H('The bus fills the odd rooms.', 'Passenger k gets 2k − 1.', '2 · 6 − 1 = 11.') });
  ex({ id: 'found-ex-diagonals', chapter: 'found-infinite', title: 'Before the seventh diagonal', kind: 'number', level: 2, answer: 28,
    text: 'The pairs (i, j) of ℕ × ℕ are listed diagonal by diagonal, diagonal d holding the pairs with i + j = d. The pair (3, 4) is on diagonal 7. How many pairs are listed before diagonal 7 begins?',
    solution: '28', wrong: ['21', '36', '7'],
    hints: H('Diagonal d has d + 1 pairs.', 'Diagonals 0 to 6 hold 1 + 2 + … + 7 pairs.', '28.') });
  ex({ id: 'found-ex-integer-list', chapter: 'found-infinite', title: 'Listing the integers', kind: 'number', answer: 8,
    text: 'The integers are listed as 0, 1, −1, 2, −2, 3, −3, …, at positions 0, 1, 2, …. At which position is −4?',
    solution: '8', wrong: ['4', '7', '9'],
    hints: H('Write out the list with positions.', 'n > 0 is at position 2n − 1, and −n at 2n.', '−4 is at position 8.') });
  ex({ id: 'found-ex-shortlex-index', chapter: 'found-infinite', title: 'Where is bab?', kind: 'number', level: 2, answer: 12,
    text: 'The strings over {a, b} are listed in shortlex order (shorter first, then a before b), with ε at position 0. At which position is bab?',
    solution: '12', wrong: ['5', '11', '13'],
    hints: H('ε, then 2 strings of length 1, then 4 of length 2: those fill positions 0 to 6.', 'Length 3 starts at position 7 with aaa; bab is the sixth string of length 3.', '7 + 5 = 12.') });
  ex({ id: 'found-ex-countable-which', chapter: 'found-infinite', title: 'Countable or not?', kind: 'choice', level: 2,
    text: 'Which of these sets are countable? Choose all that are.',
    options: ['the integers ℤ', 'all pairs (i, j) of natural numbers', 'all finite strings over {a, b}', 'all infinite 0/1 sequences', 'all positive fractions', 'all subsets of ℕ', 'all languages over {a}'], answer: [0, 1, 2, 4],
    why: 'The last three are each in one-to-one correspondence with the infinite 0/1 sequences, which the diagonal argument beats.',
    solution: [0, 1, 2, 4], wrong: [[0, 1, 2], [0, 1, 2, 4, 6], [0, 1, 2, 3, 4]],
    hints: H('Can you write a list that reaches each element at a finite position?', 'Finite objects from a finite alphabet can be listed; infinite sequences cannot.', 'ℤ, the pairs, the finite strings and the fractions.') });
  ex({ id: 'found-ex-diag-bits', chapter: 'found-infinite', title: 'Flip the diagonal', kind: 'string',
    answer: '01110',
    text: 'A list of infinite 0/1 sequences begins row 0 = 10110…, row 1 = 00101…, row 2 = 11011…, row 3 = 01100…, row 4 = 10011…. Write the first five digits of the diagonal sequence, flipping 0 ↔ 1.',
    solution: '01110', wrong: ['10001', '01111', '10110'],
    hints: H('Row i contributes its digit at place i, counting from 0.', 'The diagonal reads 1, 0, 0, 0, 1.', 'Flipped: 01110.') });
  ex({ id: 'found-ex-cantor-d', chapter: 'found-infinite', title: 'The set nobody maps to', kind: 'string', level: 2, accept: setOf(['a', 'c']),
    text: 'A = {a, b, c, d}, and f : A → P(A) has f(a) = {b, c}, f(b) = {a, b, c}, f(c) = ∅, f(d) = {a, d}. Write D = { x ∈ A : x ∉ f(x) }.',
    solution: '{a, c}', wrong: ['{b, d}', '{c}', '{a, b, c, d}'],
    hints: H('For each x, ask: is x in its own f(x)?', 'a ∉ {b, c}; b ∈ {a, b, c}; c ∉ ∅; d ∈ {a, d}.', '{a, c}') });
  ex({ id: 'found-ex-diag-why', chapter: 'found-infinite', title: 'Where they differ', kind: 'choice',
    text: 'The diagonal sequence d is built from a list of rows r₀, r₁, r₂, … by flipping. Where is d guaranteed to differ from r₇?',
    options: ['At place 7', 'At place 0', 'Somewhere, but we cannot say where', 'Nowhere, if r₇ is all 1s'], answer: 0, why: 'd at place 7 is r₇\'s digit at place 7, flipped.',
    solution: 0, wrong: [1, 2, 3],
    hints: H('How was d\'s digit at place 7 chosen?', 'From row 7, at place 7.', 'At place 7.') });
  ex({ id: 'found-ex-decimals', chapter: 'found-infinite', title: 'Why 5 and 4?', kind: 'choice', level: 3,
    text: 'To show the reals in [0, 1] are uncountable with decimal expansions, the diagonal digit is changed 5 → 4 and anything else → 5. Why not change 0 → 9 and anything else → 0?',
    options: ['Some numbers have two expansions, like 0.1999… = 0.2000…, so a sequence of 0s and 9s might be a listed number in disguise', '9 is not a digit', 'It would change too many digits', 'There is no reason; both work'], answer: 0,
    why: 'Using only the digits 4 and 5 builds a number whose expansion is unique, so differing in a digit really means being a different number.',
    solution: 0, wrong: [1, 2, 3],
    hints: H('Is a real number the same thing as its decimal expansion?', 'Expansions ending in all 0s or all 9s can name the same number.', 'Two expansions of one number: avoid 0 and 9.') });

  // ---- chapter 4 -----------------------------------------------------------------------------------------
  ex({ id: 'found-ex-ind-parts', chapter: 'found-proofs', title: 'What the step proves', kind: 'choice',
    text: 'To prove P(n) for every n ≥ 0 by induction, what exactly must the inductive step show?',
    options: ['P(n + 1) for some n', 'P(0)', 'For every n ≥ 0, if P(n) then P(n + 1)', 'P(n) for every n up to some large number'], answer: 2, why: 'The step is an implication, proved for every n at once.',
    solution: 2, wrong: [0, 1, 3],
    hints: H('One of these is the base case.', 'The step links each case to the next.', 'For every n ≥ 0, P(n) implies P(n + 1).') });
  ex({ id: 'found-ex-ind-threshold', chapter: 'found-proofs', title: 'Where does it start?', kind: 'number', level: 2, answer: 4,
    text: 'What is the smallest n₀ such that 3ⁿ > n³ for every n ≥ n₀?',
    solution: '4', wrong: ['0', '3', '5'],
    hints: H('Compute both sides for n = 0, 1, 2, 3, 4, 5.', '3³ = 27 = 3³: equal is not greater.', 'It fails at n = 3 and holds from n = 4 on, so n₀ = 4.') });
  ex({ id: 'found-ex-ind-flaw', chapter: 'found-proofs', title: 'Find the broken step', kind: 'choice', level: 2,
    text: '"Claim: in every non-empty finite set of strings, all strings have the same length. Base: a set with one string. Step: take a set of n + 1 strings; leave out one string, and by the hypothesis the other n have equal length; leave out a different one, and those n have equal length; the two groups overlap, so all n + 1 agree." Where does this fail?',
    options: ['The base case is false', 'Going from 1 to 2: two groups of one string each do not overlap', 'Only for very large sets', 'Nowhere: the claim is true'], answer: 1,
    why: 'The overlap argument needs a string in both groups. With n + 1 = 2, each group has one string and they share none.',
    solution: 1, wrong: [0, 2, 3],
    hints: H('Try the step with small n.', 'With n + 1 = 2, what do the two groups have in common?', 'The step fails from 1 to 2.') });
  ex({ id: 'found-ex-coins', chapter: 'found-proofs', title: 'Coins of 4 and 7', kind: 'number', level: 2, answer: 17,
    text: 'With unlimited coins worth 4 and 7, which is the largest amount that cannot be paid exactly? (Strong induction shows every amount above it can.)',
    solution: '17', wrong: ['3', '13', '28'],
    hints: H('Try amounts upward and look for four payable in a row.', '18 = 4 + 7 + 7, 19 = 4 + 4 + 4 + 7, 20 = 5 · 4, 21 = 3 · 7; then add 4s.', '17 cannot be paid: 17, 10 and 3 are not multiples of 4.') });
  ex({ id: 'found-ex-pigeon-week', chapter: 'found-proofs', title: 'Three on one weekday', kind: 'number', answer: 15,
    text: 'How many people must be in a room to be sure that at least three of them were born on the same day of the week?',
    solution: '15', wrong: ['8', '14', '21'],
    hints: H('Seven holes, one per weekday.', '14 people can fill each day exactly twice.', '2 · 7 + 1 = 15.') });
  ex({ id: 'found-ex-pigeon-dfa', chapter: 'found-proofs', title: 'A state must repeat', kind: 'number', level: 2, answer: 6,
    text: 'A DFA has 6 states. What is the shortest input length that guarantees the run visits some state twice (counting the start state as visited)?',
    solution: '6', wrong: ['5', '7', '12'],
    hints: H('Reading m symbols visits m + 1 states.', 'Seven visits into six states must collide.', 'm + 1 > 6, so m = 6.') });
  ex({ id: 'found-ex-pigeon-sum', chapter: 'found-proofs', title: 'Two that add to 13', kind: 'number', level: 2, answer: 7,
    text: 'How many different numbers must you pick from {1, 2, …, 12} to be sure that two of them add up to 13?',
    solution: '7', wrong: ['6', '12', '13'],
    hints: H('Make the holes the pairs that add to 13.', '{1, 12}, {2, 11}, …, {6, 7}: six holes, and you can pick one from each.', '6 + 1 = 7.') });
  ex({ id: 'found-ex-diag-fns', chapter: 'found-proofs', title: 'Build the diagonal function', kind: 'string', level: 2, accept: numbers([1, 5, 5, 6]),
    text: 'A list of functions ℕ → ℕ begins f₀(n) = n², f₁(n) = n + 3, f₂(n) = 2ⁿ, f₃(n) = 5. With g(n) = fₙ(n) + 1, write g(0), g(1), g(2), g(3), separated by commas.',
    solution: '1, 5, 5, 6', wrong: ['0, 4, 4, 5', '1, 4, 5, 6', '2, 5, 5, 6'],
    hints: H('Use row n at input n.', 'f₀(0) = 0, f₁(1) = 4, f₂(2) = 4, f₃(3) = 5.', 'Add 1 to each: 1, 5, 5, 6.') });
  ex({ id: 'found-ex-diag-double', chapter: 'found-proofs', title: 'When doubling fails', kind: 'choice', level: 2,
    text: 'Someone builds g(n) = 2 · fₙ(n) instead of fₙ(n) + 1. On which kind of list can the argument fail?',
    options: ['A list where fₙ(n) = 0 for some n', 'A list of fast-growing functions', 'A list of exactly four functions', 'A list where every fₙ(n) is odd'], answer: 0,
    why: 'Doubling 0 gives 0, so g(n) may equal fₙ(n) and nothing proves g ≠ fₙ.',
    solution: 0, wrong: [1, 2, 3],
    hints: H('The change must always change the value.', 'Which number is its own double?', 'A list with fₙ(n) = 0 somewhere.') });

  // ---- chapter 5 -----------------------------------------------------------------------------------------
  ex({ id: 'found-ex-rev-cat', chapter: 'found-strings', title: 'Reverse a concatenation', kind: 'string', answer: 'bcbaa',
    text: 'u = aab and v = cb. Write (uv)ᴿ.',
    solution: 'bcbaa', wrong: ['baabc', 'aabcb', 'bcaab'],
    hints: H('First glue: uv = aabcb.', 'Then read it backwards. Note (uv)ᴿ = vᴿuᴿ, not uᴿvᴿ.', 'bcbaa') });
  ex({ id: 'found-ex-substrings', chapter: 'found-strings', title: 'Different substrings', kind: 'number', level: 2, answer: 8,
    text: 'How many **different** substrings (contiguous pieces) does abab have, counting ε and abab itself?',
    solution: '8', wrong: ['11', '7', '10'],
    hints: H('List them by length; repeats count once.', 'Length 1: a, b. Length 2: ab, ba. Length 3: aba, bab.', 'ε, a, b, ab, ba, aba, bab, abab: 8.') });
  ex({ id: 'found-ex-sigma-count', chapter: 'found-strings', title: 'Short strings over three symbols', kind: 'number', answer: 40,
    text: 'Σ = {0, 1, 2}. How many strings over Σ have length at most 3 (ε included)?',
    solution: '40', wrong: ['27', '39', '13'],
    hints: H('|Σⁿ| = 3ⁿ.', 'Add up lengths 0, 1, 2 and 3.', '1 + 3 + 9 + 27 = 40.') });
  ex({ id: 'found-ex-concat-set', chapter: 'found-strings', title: 'Concatenate two languages', kind: 'string', accept: setOf(['ab', 'abb', 'abbb']),
    text: 'Write {a, ab} · {b, bb} as a set.',
    solution: '{ab, abb, abbb}', wrong: ['{ab, bb, abb}', '{ab, abbb}', '{ab, abb, ba, abbb}'],
    hints: H('Every string of A followed by every string of B: four pairs.', 'a · bb and ab · b both give abb.', '{ab, abb, abbb}') });
  ex({ id: 'found-ex-lang-table', chapter: 'found-strings', title: 'Six operations, one table', kind: 'table', table: 'custom', cellKind: 'set', level: 2,
    text: 'A = {ε, b} and B = {b, bb}. Fill in each language. Write a set as b, bb (ε for the empty string); leave a cell empty for ∅.',
    rows: ['A ∪ B', 'A ∩ B', 'A − B', 'B − A', 'AB', 'BA'], cols: ['the language'],
    cells: { 'A ∪ B|the language': 'ε, b, bb', 'A ∩ B|the language': 'b', 'A − B|the language': 'ε', 'B − A|the language': 'bb', 'AB|the language': 'b, bb, bbb', 'BA|the language': 'b, bb, bbb' },
    solution: { 'A ∪ B|the language': 'ε, b, bb', 'A ∩ B|the language': 'b', 'A − B|the language': 'ε', 'B − A|the language': 'bb', 'AB|the language': 'b, bb, bbb', 'BA|the language': 'bb, b, bbb' },
    wrong: [
      { 'A ∪ B|the language': 'ε, b, bb', 'A ∩ B|the language': 'b', 'A − B|the language': '', 'B − A|the language': 'bb', 'AB|the language': 'b, bb, bbb', 'BA|the language': 'b, bb, bbb' },
      { 'A ∪ B|the language': 'ε, b, bb', 'A ∩ B|the language': 'b', 'A − B|the language': 'ε', 'B − A|the language': 'bb', 'AB|the language': 'ε, b, bb, bbb', 'BA|the language': 'b, bb, bbb' },
    ],
    hints: H('ε is a string like any other: it can be in a set, and A − B keeps it.', 'AB: ε·b = b, ε·bb = bb, b·b = bb, b·bb = bbb.', 'ε, b, bb | b | ε | bb | b, bb, bbb | b, bb, bbb') });
  ex({ id: 'found-ex-empty-eps', chapter: 'found-strings', title: '∅ and {ε}', kind: 'choice', level: 2,
    text: 'Which of these hold for **every** language L? Choose all that do.',
    options: ['L∅ = ∅', 'L{ε} = L', 'L∅ = L', '∅* = ∅', '{ε}* = {ε}', 'L ∪ {ε} = L'], answer: [0, 1, 4],
    why: '∅ acts like 0 and {ε} like 1; and the star of either is {ε}.',
    solution: [0, 1, 4], wrong: [[0, 1], [0, 1, 3, 4], [1, 2, 4]],
    hints: H('A string of L∅ would need a piece from ∅.', 'Zero pieces always give ε, so ∅* contains ε.', 'L∅ = ∅, L{ε} = L and {ε}* = {ε}.') });
  ex({ id: 'found-ex-star-member', chapter: 'found-strings', title: 'In the star or not?', kind: 'choice',
    text: 'Which of these strings are in {ab, b}*? Choose all that are.',
    options: ['ε', 'abb', 'ba', 'bab', 'aab'], answer: [0, 1, 3], why: 'ε is zero pieces, abb = ab · b and bab = b · ab. Every a must be followed by b.',
    solution: [0, 1, 3], wrong: [[1, 3], [0, 1, 2, 3], [0, 1, 3, 4]],
    hints: H('Try to cut the string into pieces ab and b.', 'Every a must be immediately followed by a b.', 'ε, abb and bab.') });
  ex({ id: 'found-ex-star-regex', chapter: 'found-strings', title: 'The star of {aa, aaaaa}', kind: 'regex', alphabet: 'a', level: 2,
    text: 'Write a regular expression over {a} for {aa, aaaaa}*. (| is union, * is the star, ε is the empty string.)',
    ref: { member: (w) => w.length !== 1 && w.length !== 3 },
    solution: '(aa|aaaaa)*', wrong: ['a*', '(aa)*', 'ε|aa(a)*', '(aa)*|aaaaa'],
    hints: H('Which lengths can be made from 2s and 5s?', 'Every length except 1 and 3: 0, 2, 4, 5, 6, 7, ….', '(aa|aaaaa)*, or ε|aa|aaaa(a)*') });
  ex({ id: 'found-ex-both-ends', chapter: 'found-strings', title: 'Starts with a and ends with b', kind: 'regex', alphabet: 'ab', level: 2,
    text: 'L₁ is the strings over {a, b} that start with a, and L₂ those that end with b. Write a regular expression for L₁ ∩ L₂.',
    ref: { member: (w) => w[0] === 'a' && w[w.length - 1] === 'b' },
    solution: 'a(a|b)*b', wrong: ['a(a|b)*|(a|b)*b', 'a(a|b)*b|a', 'ab'],
    hints: H('Intersection: both conditions at once.', 'The first symbol is a, the last is b, and they are different symbols, so the string has length at least 2.', 'a(a|b)*b') });
  ex({ id: 'found-ex-reverse-lang', chapter: 'found-strings', title: 'Reverse a language', kind: 'string', accept: setOf(['ba', 'baa', 'abb']),
    text: 'The reversal of a language is Lᴿ = { wᴿ : w ∈ L }. Write {ab, aab, bba}ᴿ as a set.',
    solution: '{ba, baa, abb}', wrong: ['{ab, aab, bba}', '{ba, aba, abb}', '{bba, aab, ab}'],
    hints: H('Reverse each string on its own.', 'ab → ba, aab → baa.', '{ba, baa, abb}') });

  // ---- chapter 6 -----------------------------------------------------------------------------------------
  ex({ id: 'found-ex-desc-count', chapter: 'found-descriptions', title: 'Counting descriptions', kind: 'number', answer: 110,
    text: 'Descriptions are written with an alphabet of 10 symbols. How many descriptions of length 1 or 2 are there (whether or not they make sense)?',
    solution: '110', wrong: ['100', '20', '111'],
    hints: H('Count strings of length 1 and length 2 separately.', '10 of length 1 and 10² of length 2.', '10 + 100 = 110.') });
  ex({ id: 'found-ex-uncountable-which', chapter: 'found-descriptions', title: 'The one that is too big', kind: 'choice',
    text: 'Which of these sets is uncountable?',
    options: ['all regular expressions over {a, b}', 'all languages over {a}', 'all DFAs with input alphabet {a, b}', 'all finite languages over {a, b}'], answer: 1,
    why: 'A language over {a} is an infinite 0/1 sequence. The others are all made of finite objects written with finitely many symbols.',
    solution: 1, wrong: [0, 2, 3],
    hints: H('Which of these can be written down as a single finite string?', 'A finite language is a finite list of strings, so it can be written down too.', 'All languages over {a}.') });
  ex({ id: 'found-ex-char-bits', chapter: 'found-descriptions', title: 'A language as bits', kind: 'string', answer: '1001001',
    text: 'L = { aⁿ : n is a multiple of 3 } over {a}. Write its bits for ε, a, aa, aaa, aaaa, aaaaa, aaaaaa (1 for in, 0 for out), as one string of 7 digits.',
    solution: '1001001', wrong: ['0010010', '1001', '0110110'],
    hints: H('Bit n says whether aⁿ ∈ L.', '0 is a multiple of 3, so ε is in.', 'n = 0, 3, 6 are in: 1001001.') });
  ex({ id: 'found-ex-diag-lang', chapter: 'found-descriptions', title: 'A language no one listed', kind: 'string', level: 2, answer: '0100',
    text: 'Four languages over {a} are listed: L₀ = all strings, L₁ = ∅, L₂ = the strings of even length, L₃ = {a, aaa}. The diagonal language D contains aⁿ exactly when aⁿ ∉ Lₙ. Write D\'s bits for ε, a, aa, aaa as one string of 4 digits.',
    solution: '0100', wrong: ['1011', '0101', '1100'],
    hints: H('Bit n of D is the opposite of bit n of Lₙ.', 'ε ∈ L₀, a ∉ L₁, aa ∈ L₂, aaa ∈ L₃.', 'Flip 1, 0, 1, 1 to get 0100.') });
  ex({ id: 'found-ex-most-why', chapter: 'found-descriptions', title: 'The counting argument', kind: 'choice', level: 2,
    text: 'Which sentence gives the reason that some language over {a} has no regular expression, no grammar and no program?',
    options: ['Descriptions are finite strings, so there are countably many; languages over {a} are uncountably many', 'Some languages are infinite, and descriptions are finite', 'Regular expressions cannot count', 'Programs can run forever'], answer: 0,
    whyNot: { 1: 'a* is infinite and has a short description, so being infinite is not the problem.' },
    why: 'Countably many descriptions cannot cover uncountably many languages.',
    solution: 0, wrong: [1, 2, 3],
    hints: H('Compare the sizes of two sets.', 'One set is countable, the other is not.', 'Countably many descriptions, uncountably many languages.') });

  // =======================================================================================================
  // Tour and course
  // =======================================================================================================
  C.tour({
    id: 'found-tour', title: 'Foundations: a first look round', blurb: 'Where the foundations topics, lessons and exercises are, and how a topic page works.',
    steps: [
      { route: 'learn', target: '[data-chapter="found-sets"]', text: 'Part 1 has six chapters of lessons and exercises. The lessons explain each idea with live players built in; the exercises are checked the moment you answer.' },
      { route: '', target: '#part-foundations', text: 'The topics of Part 1 live in the catalogue: sets, relations, infinity, proofs, strings and languages. Every card is a picture you can run with your own input.' },
      { route: 'topic=set-ops', target: '#inputs', text: 'Each topic starts from an input you can change. Type your own sets here, or pick one of the examples.' },
      { target: '#stageWrap', text: 'The stage draws what is happening. Here the elements fall into the regions of a Venn picture.' },
      { target: '#btnPlay', text: 'Play runs the steps one after another; Space does the same. The arrow keys step back and forth.' },
      { target: '#say', text: 'Each step is told in words, with the actual elements.' },
      { route: 'topic=closure-warshall', target: '#stageWrap', text: 'A relation is drawn as arrows. Warshall\'s algorithm adds shortcut arrows, one round per element.' },
      { target: '#btnQuiz', text: 'Every topic ends with a short quiz to check you caught the idea.' },
      { route: 'exercise=found-ex-trans-closure', target: '#btnHint', text: 'Stuck on an exercise? Hints come one at a time; the last one is a worked answer.' },
    ],
  });

  C.course({
    id: 'found-course', title: 'Foundations in order', blurb: 'From sets to the counting argument: every foundations topic in teaching order, with a lesson and an exercise at the key points.',
    steps: [
      { topic: 'set-ops', note: 'Watch which Venn regions light: each operation is a choice of regions.' },
      { topic: 'set-powerset', note: 'One bit per element: count in binary and every subset appears once.' },
      { topic: 'set-product', note: 'A × B is a grid; a relation is a set of its cells.' },
      { topic: 'rel-props', note: 'When a property fails, look at the lit pairs that break it.' },
      { topic: 'fn-kinds', note: 'Two arrows meeting break one-to-one; a target left alone breaks onto.' },
      { exercise: 'found-ex-rel-table', note: 'Check five relations against the exact definitions.' },
      { topic: 'closure-warshall', note: 'Each round uses one element as a stepping stone; cycles bring loops.' },
      { topic: 'closure-equivalence', note: 'The classes are the connected pieces, directions ignored.' },
      { topic: 'equiv-classes', note: 'Every element lands in exactly one class.' },
      { lesson: 'found-l-equivalence', note: 'Why equivalences and partitions are the same thing.' },
      { topic: 'hilbert-hotel', note: 'A full infinite hotel still makes room: n → 2n frees every odd room.' },
      { topic: 'count-pairs', note: 'Row by row gets stuck; diagonal by diagonal reaches everything.' },
      { topic: 'count-rationals', note: 'Skip the fractions already counted under a simpler name.' },
      { topic: 'cantor-diagonal', note: 'The flipped diagonal differs from row i at place i.' },
      { topic: 'cantor-powerset', note: 'D collects the x that are not in their own f(x), so D is no f(x).' },
      { exercise: 'found-ex-cantor-d', note: 'Build D yourself.' },
      { topic: 'induction-dominoes', note: 'Base case and step: try the presets where one of them fails.' },
      { topic: 'pigeonhole', note: 'Choose the holes well and the collision is forced.' },
      { topic: 'diagonal-functions', note: 'The change must always change: watch doubling fail on 0.' },
      { topic: 'string-ops', note: '(uv)ᴿ = vᴿuᴿ: the pieces swap as well as turn round.' },
      { topic: 'sigma-star', note: 'Shortlex order lists every string at a finite position.' },
      { topic: 'lang-ops', note: 'Two pairs can glue into the same string; ∅ wipes everything out.' },
      { topic: 'lang-star', note: 'Level 0 is always {ε}, so ε ∈ A* for every A.' },
      { topic: 'counting-languages', note: 'The diagonal language is described by none of the listed expressions.' },
      { lesson: 'found-l-descriptions', note: 'Countably many descriptions, uncountably many languages.' },
    ],
  });
})();
