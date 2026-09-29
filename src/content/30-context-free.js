// Part 3, context-free languages: grammars and parse trees, ambiguity, cleanup and normal forms,
// pushdown automata, and the limits of the class (the pumping game, closure and non-closure).
// Chapters cf-*, lessons cf-l-*, exercises cf-x-*, one tour and one course.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const K = (T.Check = T.Check || {});

  // form ('gnf', 'noleftrec', 'noeps', 'right-linear', 'unambiguous' with ambLen) on grammar exercises and
  // acceptBy ('empty' | 'final') on PDA exercises are checked by src/app/check-lang.js and check-machine.js.
  /** A string answer that must be a word with at least two parse trees in the grammar */
  const twoTrees = (text) => { let G = null; return (w) => { G = G || T.grammar.parse(text); return T.grammar.parseTrees(G, [...w], 2).length >= 2; }; };
  const blocks = (w, letters) => { const out = []; let i = 0; for (const L of letters) { let k = 0; while (w[i] === L) { k++; i++; } out.push(k); } return i === w.length ? out : null; };
  const count = (w, c) => [...w].filter((s) => s === c).length;
  const rev = (w) => [...w].reverse().join('');
  const H = (a, b, c) => [a, b, c];
  const ex = (x) => C.exercise(Object.assign({ level: 1 }, x));

  // ---- chapters ----------------------------------------------------------------------------------------------
  C.chapter({ id: 'cf-grammars', part: 'context-free', n: 1, title: 'Grammars and parse trees', blurb: 'Rules that rewrite one nonterminal at a time, the trees they grow, and how to design a grammar for a language.' });
  C.chapter({ id: 'cf-ambiguity', part: 'context-free', n: 2, title: 'Ambiguity', blurb: 'One word, two trees: finding them, rewriting a grammar to avoid them, and languages where no grammar can.' });
  C.chapter({ id: 'cf-normal', part: 'context-free', n: 3, title: 'Cleanup and normal forms', blurb: 'Useless symbols, ε-rules and unit rules removed; Chomsky and Greibach normal forms; left recursion turned around.' });
  C.chapter({ id: 'cf-pda', part: 'context-free', n: 4, title: 'Pushdown automata', blurb: 'A finite control with a stack, two ways to accept, the bridge to grammars both ways, and determinism.' });
  C.chapter({ id: 'cf-limits', part: 'context-free', n: 5, title: 'Limits and closure', blurb: 'The context-free pumping lemma as a tree and as a game, and the operations that keep a language context-free.' });

  // =============================================================================================================
  // Chapter 1: grammars and parse trees
  // =============================================================================================================
  C.lesson({
    id: 'cf-l-rules', chapter: 'cf-grammars', title: 'Rules that rewrite', minutes: 10,
    summary: 'A context-free grammar starts from one symbol and rewrites nonterminals, one at a time, until only letters are left.',
    blocks: [
      "Finite automata cannot count: no DFA checks that a string has as many a's as b's in two blocks, or that every bracket is closed. Yet these are exactly the shapes that programs, formulas and sentences are made of. We need a way to describe *nesting*.",
      "A grammar describes a language by **building** its words instead of checking them. You start with one symbol and keep replacing a placeholder by one of the pieces a rule allows, until no placeholder is left. The rule S → a S b says: wherever you see S, you may write a S b instead. Each use wraps one more a and b around the middle, so the a's and b's always match.",
      { def: 'Context-free grammar', text: 'a 4-tuple (V, Σ, R, S): V is a finite set of nonterminals, Σ a finite set of terminals disjoint from V, R a finite set of rules A → α with A in V and α a string over V ∪ Σ (possibly ε), and S in V the start symbol.' },
      { def: 'Derivation', text: 'a sequence of sentential forms α₀ ⇒ α₁ ⇒ … ⇒ αₙ, where α₀ = S and each step replaces one nonterminal A by α for some rule A → α. The language L(G) is the set of terminal strings w with S ⇒* w.' },
      "*Context-free* means the left side is a single nonterminal: whatever surrounds an A, the same rules apply to it. That is the one restriction, and it is exactly what makes nesting possible but crossing patterns hard, as we will see at the end of this part.",
      { h: 'Watch a derivation' },
      { topic: 'cfg-derive', input: { g: 'S → A B\nA → a A | a\nB → b B | b', w: 'aabb', order: 'both' }, caption: 'Two derivations of aabb side by side. Watch which nonterminal is replaced at each step: the leftmost one on the left, the rightmost one on the right. They use the same rules, in a different order.' },
      { predict: { q: 'With S → a S b | ε, how many steps does the derivation of aaabbb take?', options: ['3', '4', '6'], answer: 1, explain: 'Three steps with S → a S b, each adding one a and one b, and a fourth with S → ε to remove the last S: S ⇒ aSb ⇒ aaSbb ⇒ aaaSbbb ⇒ aaabbb.' } },
      "Two honest edge cases. First, ε is a perfectly good word: S → a S b | ε generates it in one step. Second, a grammar may generate nothing at all: with only S → a S, every form still contains S, so no derivation ever finishes and L(G) = ∅.",
      { warn: 'Rules are permissions, not instructions. You do not have to use every rule, and a nonterminal may be rewritten by any of its alternatives at any time. A word is in the language if *some* derivation reaches it.' },
      { h: 'Try it yourself' },
      { sandbox: { kind: 'grammar', text: 'S → a S b | ε', input: 'aaabbb' }, caption: 'Run the grammar on words of your own. Try ε, abab and aabbb: which ones are generated?' },
      { list: ['A grammar builds words; an automaton checks them.', 'One nonterminal on the left of every rule: that is what context-free means.', 'A derivation rewrites one nonterminal per step; the words are the forms with no nonterminal left.', 'ε can be a word, and ∅ can be the language.'] },
      { exercise: 'cf-x-steps' },
      { exercise: 'cf-x-form' },
      { exercise: 'cf-x-gr-onemore' },
    ],
  });

  C.lesson({
    id: 'cf-l-trees', chapter: 'cf-grammars', title: 'Parse trees and the order of steps', minutes: 9,
    summary: 'A parse tree records which rule built which part of the word, and forgets the order of the steps.',
    blocks: [
      "A derivation is a list of steps, but most of the order is accidental. In S ⇒ A B, it makes no difference to the result whether A or B is expanded first. A **parse tree** keeps what matters (which rule was applied to which nonterminal) and drops the order.",
      { def: 'Parse tree', text: 'a tree whose root is the start symbol, whose inner nodes are nonterminals, and where the children of a node A, read left to right, are the right side of a rule A → α (a single leaf ε for A → ε). Its yield is the string of leaves read left to right.' },
      { topic: 'cfg-tree', input: { g: 'E → E + T | T\nT → T * F | F\nF → ( E ) | x', w: 'x+x*x', order: 'breadth' }, caption: 'The tree for x+x*x grows level by level. Watch the yield along the bottom: it is the word only once every leaf is a terminal.' },
      "Every derivation gives one tree, but one tree comes from many derivations. To talk about a single derivation per tree, fix the order: a **leftmost derivation** always rewrites the leftmost nonterminal, a **rightmost derivation** the rightmost one. Each tree has exactly one of each.",
      { topic: 'cfg-orders', input: { g: 'S → A B\nA → a A | a\nB → b B | b', w: 'aabb' }, caption: 'The same tree is walked in two orders. The nodes light up in the order each derivation expands them; the tree itself never changes.' },
      { predict: { q: 'A parse tree has 6 inner nodes (6 nonterminals that were expanded). How many steps does each of its derivations have?', options: ['It depends on the order', '6, whatever the order', '5, one fewer than the nodes'], answer: 1, explain: 'Each step expands exactly one nonterminal, and each inner node is expanded exactly once, so every derivation of that tree has 6 steps.' } },
      { tip: 'The number of steps of a derivation equals the number of inner nodes of its tree. That is a quick sanity check when you write derivations by hand.' },
      { editor: { kind: 'grammar', text: 'S → L , S | L\nL → p | q', tests: 'p\np,q\nq,q,p\n-p,\n-,p\n-ε' }, caption: 'A grammar for comma-separated lists. Run the tests, then change it so the empty list ε is also allowed (mark ε as accepted in the tests).' },
      { list: ['A parse tree shows which rule built which piece.', 'Leftmost and rightmost derivations are one per tree.', 'Steps of a derivation = inner nodes of the tree.'] },
      { exercise: 'cf-x-leftmost' },
      { exercise: 'cf-x-steps' },
    ],
  });

  C.lesson({
    id: 'cf-l-design', chapter: 'cf-grammars', title: 'Designing a grammar', minutes: 14,
    summary: 'Four moves cover most grammars: match from the outside in, glue pieces side by side, offer a choice, and repeat.',
    blocks: [
      "Writing a grammar is a design task, not a calculation. The trick is to see the word as built from parts, and give each part its own nonterminal. Four moves go a long way.",
      { steps: ['**Match from the outside in.** Two things that must agree in number and sit at the two ends: X → a X b. Each rule use adds one of each.', '**Glue side by side.** A word made of independent pieces: S → A B, with A and B designed separately.', '**Offer a choice.** A union of two languages: S → A | B.', '**Repeat.** Any number of a piece: R → P R | ε.'] },
      "Take aⁱbʲcᵏ with j = i + k. Split the b's into the ones matching the a's and the ones matching the c's: it is aⁱbⁱ followed by bᵏcᵏ. Glue two matching pieces: S → A B, A → a A b | ε, B → b B c | ε. Seeing the hidden split is the whole design.",
      { topic: 'cfg-design', input: { lang: 'brackets', g: 'S → ( S ) | ε', n: 6 }, caption: 'This grammar for balanced brackets is too small: it only nests. The green words are right, the red ones are missing. Which bracket strings never appear?' },
      { predict: { q: 'Which rule should be added to S → ( S ) | ε so that it generates every balanced bracket string?', options: ['S → ( ) S', 'S → S S', 'S → ( S S )'], answer: 1, explain: 'A balanced string is either empty, or a bracketed balanced string, or two balanced strings side by side. ()() needs the side-by-side case, which S → S S provides. (S → ( S ) S does the same job in one rule, without ambiguity.)' } },
      { h: 'Test as you design' },
      "A grammar is right when it generates every word of the language and nothing else. Test both sides: words that must be generated, and near misses that must not.",
      { editor: { kind: 'grammar', text: 'S → A B\nA → a A b | ε\nB → b B c | ε', tests: 'ε\nab\nbc\nabbc\naabbbc\n-abc\n-aabbc\n-ba' }, caption: 'aⁱbⁱ⁺ᵏcᵏ, built from two matching pieces. Every test passes; now break the grammar on purpose and see which tests catch it.' },
      { warn: 'The most common mistakes: forgetting ε (or small cases like n = 0), and a rule that is too generous, such as S → a S | S b | ε for "as many b as a", which lets the counts drift apart.' },
      { list: ['Find the hidden structure first: which symbols must match which?', 'Matching pairs → wrap from the outside in.', 'Independent pieces → glue; alternatives → choose; repetition → recurse with ε.', 'Test the near misses, not only the words.'] },
      { exercise: 'cf-x-gr-middle' },
      { exercise: 'cf-x-gr-split' },
      { exercise: 'cf-x-gr-xyx' },
      { exercise: 'cf-x-gr-unequal' },
      { exercise: 'cf-x-gr-eqab' },
      { exercise: 'cf-x-gr-double' },
      { exercise: 'cf-x-gr-brackets2' },
      { exercise: 'cf-x-gr-nonpal' },
    ],
  });

  C.lesson({
    id: 'cf-l-hierarchy', chapter: 'cf-grammars', title: 'Where context-free grammars sit', minutes: 7,
    summary: 'Restrict the shape of the rules and you get the regular languages; relax it and you get much more.',
    blocks: [
      "Grammars come in four families, set by the shape of their rules. The tighter the shape, the smaller the family of languages, and the simpler the machine that recognises it.",
      { table: [['type', 'rules look like', 'machine'], ['3, regular', 'A → w B or A → w (right-linear)', 'finite automaton'], ['2, context-free', 'A → α', 'pushdown automaton'], ['1, context-sensitive', 'α → β with |α| ≤ |β|', 'linear-bounded automaton'], ['0, unrestricted', 'any α → β', 'Turing machine']], caption: 'The Chomsky hierarchy of grammars.' },
      "A right-linear grammar is a finite automaton in disguise: the nonterminal is the state, and A → a B is a move from A to B on a. A → ε marks an accepting state. So every regular language is context-free.",
      { topic: 'cfg-hierarchy', input: { g: 'S → a S | b A\nA → a A | ε' }, caption: 'Each rule is checked in turn. All of them have at most one nonterminal, at the right end, so the grammar is right-linear: type 3.' },
      { predict: { q: 'S → a S b | ε is linear (one nonterminal per right side). Is it regular?', options: ['Yes, linear grammars are regular', 'No: the nonterminal sits in the middle, and the language aⁿbⁿ is not regular'], answer: 1, explain: 'Regular needs every rule linear on the same side. A nonterminal in the middle can match symbols on both sides of it, which no finite automaton can do.' } },
      { sandbox: { kind: 'grammar', text: 'S → a S | b A\nA → a A | ε', input: 'aaba' }, caption: 'Strings with exactly one b. Read the grammar as a machine: two states, S before the b and A after it.' },
      { list: ['Type 3 ⊂ type 2 ⊂ type 1 ⊂ type 0.', 'Right-linear grammars are finite automata written as rules.', 'Linear is not enough for regular: the nonterminal must be at one end, the same end in every rule.'] },
      { exercise: 'cf-x-hierarchy' },
      { exercise: 'cf-x-gr-rl-evena' },
    ],
  });

  // ---- chapter 1 exercises ------------------------------------------------------------------------------------
  ex({ id: 'cf-x-steps', chapter: 'cf-grammars', title: 'Counting derivation steps', kind: 'number',
    text: 'In the grammar S → A B, A → a A | a, B → b B | b, how many steps does a derivation of aabbb take (any order)?',
    answer: 6, solution: '6', wrong: ['5', '7', '3'], why: 'The tree has six inner nodes: S, two A and three B.',
    hints: H('Count the rule uses: each step uses one rule once.', 'One for S, one for each a (A → a A then A → a), one for each b.', '1 + 2 + 3 = 6.') });
  ex({ id: 'cf-x-form', chapter: 'cf-grammars', title: 'Two leftmost steps', kind: 'string',
    text: 'The grammar S → L , S | L and L → p | q generates comma-separated lists. In the leftmost derivation of p,q, what is the sentential form after exactly two steps? Write it without spaces.',
    answer: ['p,S'], solution: 'p,S', wrong: ['L,S', 'p,q', 'L,L'],
    hints: H('The first step must create the comma.', 'S ⇒ L,S. Now the leftmost nonterminal is L.', 'S ⇒ L,S ⇒ p,S.') });
  ex({ id: 'cf-x-leftmost', chapter: 'cf-grammars', title: 'Which derivation is leftmost?', kind: 'choice',
    text: 'Grammar: S → A B, A → a, B → b B | b. Which of these is a leftmost derivation of abb?',
    options: ['S ⇒ A B ⇒ A b B ⇒ a b B ⇒ a b b', 'S ⇒ A B ⇒ a B ⇒ a b B ⇒ a b b', 'S ⇒ A B ⇒ A b B ⇒ A b b ⇒ a b b', 'S ⇒ a B ⇒ a b B ⇒ a b b'],
    answer: 1, whyNot: { 0: 'The second step rewrites B while A is still to its left.', 2: 'That one is rightmost: it always rewrites the rightmost nonterminal.', 3: 'There is no rule S → a B; the first step must be S → A B.' },
    solution: 1, wrong: [0, 2, 3], why: 'Every step rewrites the leftmost nonterminal: A first, then B twice.',
    hints: H('In each form, find the leftmost nonterminal; that is the one that must change.', 'After S ⇒ A B, the leftmost nonterminal is A.', 'S ⇒ A B ⇒ a B ⇒ a b B ⇒ a b b.') });
  ex({ id: 'cf-x-hierarchy', chapter: 'cf-grammars', title: 'Which type?', kind: 'choice',
    text: 'Which is the smallest family in the Chomsky hierarchy whose rule shapes fit the grammar S → a A | b, A → S b?',
    options: ['Type 3, right-linear', 'Type 2, context-free but not right- or left-linear', 'Type 1, context-sensitive', 'Type 0, unrestricted'],
    answer: 1, whyNot: { 0: 'A → S b has its nonterminal on the left end, while S → a A has it on the right: the sides are mixed.' },
    solution: 1, wrong: [0, 2], why: 'One nonterminal on every left side, but the rules mix right-linear and left-linear shapes. (The language, aⁿ b bⁿ, is indeed not regular.)',
    hints: H('Look at where the nonterminal sits in each right side.', 'S → a A has it at the right end, A → S b at the left end.', 'Mixed sides: context-free, type 2, and not regular as written.') });
  ex({ id: 'cf-x-gr-onemore', chapter: 'cf-grammars', title: 'One b more', kind: 'grammar', alphabet: 'ab',
    text: 'Write a grammar for aⁿbⁿ⁺¹ with n ≥ 0: some a\'s, then exactly one more b than there were a\'s.',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && b[1] === b[0] + 1; },
    solution: 'S -> a S b | b', wrong: ['S -> a S b | ε', 'S -> a S b | b | ε', 'S -> a S b b | b'],
    hints: H('Wrap matching a…b pairs from the outside in, as for aⁿbⁿ.', 'What is left in the middle when the pairs run out? Not ε this time.', 'S → a S b | b') });
  ex({ id: 'cf-x-gr-middle', chapter: 'cf-grammars', title: 'b in the middle', kind: 'grammar', alphabet: 'ab',
    text: 'Write a grammar for the strings over {a, b} of odd length whose middle symbol is b.',
    member: (w) => w.length % 2 === 1 && w[(w.length - 1) / 2] === 'b',
    solution: 'S -> X S X | b\nX -> a | b', wrong: ['S -> a S a | b S b | b', 'S -> X S X | b | ε\nX -> a | b', 'S -> X S | b\nX -> a | b'],
    hints: H('The two sides of the middle need not match each other, only have the same length.', 'Add one arbitrary symbol on each side at a time.', 'S → X S X | b, X → a | b') });
  ex({ id: 'cf-x-gr-split', chapter: 'cf-grammars', title: 'The b\'s are shared', kind: 'grammar', alphabet: 'abc', level: 2,
    text: 'Write a grammar for aⁱbʲcᵏ with j = i + k (i, k ≥ 0): the number of b\'s is the number of a\'s plus the number of c\'s.',
    member: (w) => { const b = blocks(w, 'abc'); return !!b && b[1] === b[0] + b[2]; },
    solution: 'S -> A B\nA -> a A b | ε\nB -> b B c | ε', wrong: ['S -> a S c | B\nB -> b B | ε', 'S -> a S b | B\nB -> b B c | ε\nS -> S c', 'S -> A B\nA -> a A b | ε\nB -> b B c | c'],
    hints: H('Split the b block into two parts. Which part matches the a\'s, which the c\'s?', 'The word is aⁱbⁱ followed by bᵏcᵏ.', 'S → A B, A → a A b | ε, B → b B c | ε') });
  ex({ id: 'cf-x-gr-xyx', chapter: 'cf-grammars', title: 'Same on both ends', kind: 'grammar', alphabet: 'xy',
    text: 'Write a grammar for xⁿyᵐxⁿ with n, m ≥ 0: a block of x\'s, any number of y\'s, and as many x\'s again.',
    member: (w) => { const m = /^(x*)(y*)(x*)$/.exec(w); return !!m && (m[2] ? m[1].length === m[3].length : w.length % 2 === 0); },
    solution: 'S -> x S x | Y\nY -> y Y | ε', wrong: ['S -> x S x | y', 'S -> x S x | Y\nY -> y Y | x | ε', 'S -> x S | S x | Y\nY -> y Y | ε'],
    hints: H('The x blocks match from the outside in.', 'In the middle, any number of y\'s, including none.', 'S → x S x | Y, Y → y Y | ε') });
  ex({ id: 'cf-x-gr-unequal', chapter: 'cf-grammars', title: 'Unequal blocks', kind: 'grammar', alphabet: 'ab', level: 2,
    text: 'Write a grammar for aⁱbʲ with i ≠ j.',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] !== b[1]; },
    solution: 'S -> a S b | A | B\nA -> a A | a\nB -> b B | b', wrong: ['S -> a S b | a | b', 'S -> a S b | A | B\nA -> a A | ε\nB -> b B | ε', 'S -> A B\nA -> a A | a\nB -> b B | b'],
    hints: H('Match a\'s with b\'s from the outside in, as long as you like.', 'Then one side must have a surplus: at least one extra a, or at least one extra b.', 'S → a S b | A | B, A → a A | a, B → b B | b') });
  ex({ id: 'cf-x-gr-eqab', chapter: 'cf-grammars', title: 'As many a as b, in any order', kind: 'grammar', alphabet: 'ab', level: 2,
    text: 'Write a grammar for the strings over {a, b} with as many a\'s as b\'s, in any order (abba and baab included).',
    member: (w) => count(w, 'a') === count(w, 'b'),
    solution: 'S -> a S b S | b S a S | ε', wrong: ['S -> a S b | b S a | ε', 'S -> a b S | b a S | ε', 'S -> a S b | S S | ε'],
    hints: H('Look at the first symbol of a nonempty word, say a. Somewhere later is the b that brings the count back to zero for the first time.', 'Between them is a balanced word, and after that b another balanced word.', 'S → a S b S | b S a S | ε') });
  ex({ id: 'cf-x-gr-double', chapter: 'cf-grammars', title: 'Once or twice as many', kind: 'grammar', alphabet: 'ab', level: 3,
    text: 'Write a grammar for aⁿbᵐ where m = n or m = 2n (n ≥ 0).',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && (b[1] === b[0] || b[1] === 2 * b[0]); },
    solution: 'S -> A | B\nA -> a A b | ε\nB -> a B b b | ε', wrong: ['S -> a S b | a S b b | ε', 'S -> a S b | ε', 'S -> A | B\nA -> a A b | ε\nB -> a B b b | b'],
    hints: H('This is a union of two languages; design each part on its own.', 'One part wraps a…b, the other wraps a…bb. Mixing the two in one nonterminal lets a word use both kinds of steps.', 'S → A | B, A → a A b | ε, B → a B b b | ε') });
  ex({ id: 'cf-x-gr-brackets2', chapter: 'cf-grammars', title: 'Two kinds of brackets', kind: 'grammar', alphabet: '()[]', level: 2, maxLen: 6,
    text: 'Write a grammar for the balanced strings over ( ) [ ]: every bracket is closed by one of its own kind, properly nested, as in ([])() but not ([)].',
    member: (w) => { const st = []; for (const c of w) { if (c === '(' || c === '[') st.push(c); else { const o = st.pop(); if ((c === ')' && o !== '(') || (c === ']' && o !== '[')) return false; } } return !st.length; },
    solution: 'S -> ( S ) S | [ S ] S | ε', wrong: ['S -> ( S ) | [ S ] | ε', 'S -> ( S ) S | [ S ) S | ε', 'S -> ( S ) S | [ S ] S'],
    hints: H('A nonempty balanced string starts with an opening bracket. Where is its partner?', 'Inside the pair is a balanced string, and after it another one.', 'S → ( S ) S | [ S ] S | ε') });
  ex({ id: 'cf-x-gr-nonpal', chapter: 'cf-grammars', title: 'Not a palindrome', kind: 'grammar', alphabet: 'ab', level: 3,
    text: 'Write a grammar for the strings over {a, b} that are not palindromes.',
    member: (w) => w !== rev(w),
    solution: 'S -> a S a | b S b | a X b | b X a\nX -> a X | b X | ε', wrong: ['S -> a S b | b S a | ε', 'S -> a S a | b S b | a X b | b X a\nX -> a | b | ε', 'S -> a X b | b X a\nX -> a X | b X | ε'],
    hints: H('Compare the word from both ends inwards. Somewhere the two ends differ for the first time.', 'Outside that point the ends match (like a palindrome); at that point a meets b; inside, anything goes.', 'S → a S a | b S b | a X b | b X a, X → a X | b X | ε') });
  ex({ id: 'cf-x-gr-rl-evena', chapter: 'cf-grammars', title: 'A right-linear grammar', kind: 'grammar', form: 'right-linear', alphabet: 'ab', level: 2,
    text: 'Write a right-linear grammar (every rule A → w B or A → w) for the strings over {a, b} with an even number of a\'s.',
    member: (w) => count(w, 'a') % 2 === 0,
    solution: 'S -> a A | b S | ε\nA -> a S | b A', wrong: ['S -> a S a | b S | ε', 'S -> a A | b S | ε\nA -> a S | b A | ε', 'S -> a a S | b S | ε'],
    hints: H('Think of a two-state automaton: even so far, odd so far.', 'Each nonterminal is a state; a moves between them, b stays.', 'S → a A | b S | ε, A → a S | b A') });

  // =============================================================================================================
  // Chapter 2: ambiguity
  // =============================================================================================================
  C.lesson({
    id: 'cf-l-ambiguous', chapter: 'cf-ambiguity', title: 'One word, two trees', minutes: 9,
    summary: 'A grammar is ambiguous when some word has two different parse trees; to prove it, one witness is enough.',
    blocks: [
      "A parse tree is the *meaning* a grammar gives a word: a compiler evaluates the tree, not the string. So it matters when one word has two trees. In E → E + E | E * E | x, the word x+x*x can be read as x+(x*x) or as (x+x)*x.",
      { def: 'Ambiguous grammar', text: 'a grammar in which some word has two different parse trees (equivalently, two different leftmost derivations).' },
      { topic: 'amb-find', input: { g: 'E → E + E | E * E | x', n: 5 }, caption: 'The finder tries the words in order of length. Short words have one tree each; watch for the first word that has two, and compare the two trees it draws.' },
      "Two leftmost derivations, not just two derivations: every tree with two or more inner nodes has several derivations, which is harmless. Ambiguity is about different *trees*.",
      { predict: { q: 'Is S → a S | S a | a ambiguous?', options: ['No: every word is just a⁺', 'Yes: aa already has two trees', 'Only for words of length 3 or more'], answer: 1, explain: 'aa can be built as a S with S → a, or as S a with S → a: two different trees for the same word, so the grammar is ambiguous even though the language a⁺ is simple.' } },
      { topic: 'amb-find', input: { g: 'S → i S | i S e S | o', n: 5 }, caption: 'A branch with an optional else: in iioeo, which i does the e belong to? Each tree gives a different answer.' },
      { warn: 'To show a grammar is ambiguous you need one word with two trees. To show it is unambiguous you need an argument about every word: no search can do that, because the question is undecidable in general.' },
      { sandbox: { kind: 'grammar', text: 'S → S S | ( S ) | ε', input: '()()' }, caption: 'With S → S S and ε together, even ε has infinitely many trees: S ⇒ S S ⇒ S ⇒ ε, and so on.' },
      { list: ['Ambiguity is about trees (or leftmost derivations), not derivations.', 'One witness word proves ambiguity.', 'Simple languages can have ambiguous grammars; that is a property of the grammar.'] },
      { exercise: 'cf-x-amb-sas' },
      { exercise: 'cf-x-amb-if' },
      { exercise: 'cf-x-amb-split' },
      { exercise: 'cf-x-amb-which' },
      { exercise: 'cf-x-amb-count' },
    ],
  });

  C.lesson({
    id: 'cf-l-unambiguous', chapter: 'cf-ambiguity', title: 'Layers fix precedence and associativity', minutes: 10,
    summary: 'An expression grammar becomes unambiguous with one nonterminal per level of binding, and recursion on the side the operator groups to.',
    blocks: [
      "Ambiguity is usually a property of the grammar, not of the language. The fix for expressions is to give each level of binding its own nonterminal, so the grammar decides for you which operator sits higher in the tree.",
      { math: 'E → E + T | E - T | T        sums: the loosest level\nT → T * F | F                products\nF → ( E ) | number           atoms' },
      "**Precedence**: a + can only appear at the E level, above every *. So in 2+3*4 the * is buried in a T, below the +: it is evaluated first. **Associativity**: E → E - T recurses on the left, so 8-4-2 groups as (8-4)-2.",
      { topic: 'amb-fix', input: { e: '8-4-2' }, caption: 'The ambiguous grammar gives two trees with different values. The layered grammar gives one tree, grouped to the left. Watch the value under each tree.' },
      { predict: { q: 'In the layered grammar, which operator is at the root of the tree for 2*3+4?', options: ['The *', 'The +', 'It depends on the derivation'], answer: 1, explain: 'A + appears only through E → E + T, at the top level. The 2*3 is the left E, then a T. The tree is unique, so there is no choice: + is the root.' } },
      { topic: 'amb-fix', input: { e: '2+3*4' }, caption: 'Precedence: the ambiguous grammar allows (2+3)*4 = 20 too; the layered one only 2+(3*4) = 14.' },
      { editor: { kind: 'grammar', text: 'E → E + T | T\nT → T * F | F\nF → ( E ) | x', tests: 'x\nx+x*x\n(x+x)*x\nx*x*x\n-x+\n-()\n-x x' }, caption: 'The layered grammar for x, + and *. It generates the same words as E → E + E | E * E | ( E ) | x, with one tree each.' },
      { tip: 'Right-recursive rules (E → T + E) give right associativity, which is what you want for powers: 2^3^2 is 2^(3^2).' },
      { list: ['One nonterminal per precedence level, loosest at the top.', 'Left recursion groups to the left; right recursion to the right.', 'Brackets reset to the top level inside F → ( E ).'] },
      { exercise: 'cf-x-unamb-plus' },
      { exercise: 'cf-x-unamb-expr' },
      { exercise: 'cf-x-unamb-brackets' },
      { exercise: 'cf-x-fix-root' },
    ],
  });

  C.lesson({
    id: 'cf-l-inherent', chapter: 'cf-ambiguity', title: 'Inherent ambiguity', minutes: 7,
    summary: 'Some context-free languages have no unambiguous grammar at all: every grammar for them is ambiguous.',
    blocks: [
      "Layering fixes expression grammars, but not every language can be fixed. Take the words aⁱbʲcᵏ where i = j **or** j = k. It is context-free: a union of two easy languages.",
      { math: 'S → X C | A Y\nX → a X b | ε     C → c C | ε      (i = j)\nA → a A | ε       Y → b Y c | ε    (j = k)' },
      "A word like aabbcc belongs to both halves, so it gets one tree from each. You might hope a cleverer grammar avoids that. It cannot: any grammar for this language must, for words aⁿbⁿcⁿ with n large enough, count the a's against the b's and also the b's against the c's, and the two countings yield two different trees. A language like this is called **inherently ambiguous**.",
      { def: 'Inherently ambiguous language', text: 'a context-free language for which every context-free grammar is ambiguous.' },
      { topic: 'amb-inherent', input: { j: 2 }, caption: 'Words with j = 2 b\'s. Only aabbcc is in both halves, and only it has two trees. Watch how its two trees pair the b\'s with different neighbours.' },
      { predict: { q: 'With the grammar above, how many parse trees does abbc have?', options: ['None: it is not in the language', 'One', 'Two'], answer: 0, explain: 'abbc has i = 1, j = 2, k = 1: neither i = j nor j = k holds, so it is not in the language at all.' } },
      { sandbox: { kind: 'grammar', text: 'S → X C | A Y\nX → a X b | ε\nC → c C | ε\nA → a A | ε\nY → b Y c | ε', input: 'aabbcc' }, caption: 'Try aabbc (one half), abbcc (the other) and aabbcc (both).' },
      { list: ['Ambiguity of a grammar can often be fixed; inherent ambiguity of a language cannot.', 'Typical cause: a union of two languages whose overlap must be counted in two incompatible ways.', 'Deciding whether a grammar is ambiguous is undecidable in general.'] },
      { exercise: 'cf-x-inherent' },
    ],
  });

  // ---- chapter 2 exercises -------------------------------------------------------------------------------------
  ex({ id: 'cf-x-amb-sas', chapter: 'cf-ambiguity', title: 'A witness for S → S a S | b', kind: 'string',
    text: 'The grammar S → S a S | b is ambiguous. Give a word with two different parse trees.',
    accept: twoTrees('S -> S a S | b'), answer: 'babab', solution: 'babab', wrong: ['bab', 'ba', 'b'],
    hints: H('With one a there is only one way to build the word.', 'With two a\'s, which S a S is at the root: the one around the first a or the second?', 'babab: (bab)ab or ba(bab).') });
  ex({ id: 'cf-x-amb-if', chapter: 'cf-ambiguity', title: 'Which p gets the q?', kind: 'string', level: 2,
    text: 'In S → p S | p S q S | r, read p as "if", q as "else" and r as a plain statement. Give a word with two parse trees.',
    accept: twoTrees('S -> p S | p S q S | r'), answer: 'pprqr', solution: 'pprqr', wrong: ['prqr', 'ppr', 'pr'],
    hints: H('You need a q that could belong to either of two p\'s.', 'Two p\'s, then a statement, then the q and another statement.', 'pprqr: the q pairs with the first p or with the second.') });
  ex({ id: 'cf-x-amb-split', chapter: 'cf-ambiguity', title: 'Where does A end?', kind: 'string',
    text: 'Grammar: S → A B, A → a | a a, B → a b | b. Give a word with two parse trees.',
    accept: twoTrees('S -> A B\nA -> a | a a\nB -> a b | b'), answer: 'aab', solution: 'aab', wrong: ['ab', 'aaab', 'aabb'],
    hints: H('The trees differ in where the A part stops and the B part starts.', 'An a in the middle could belong to A or to B.', 'aab = a·ab = aa·b.') });
  ex({ id: 'cf-x-amb-which', chapter: 'cf-ambiguity', title: 'Which are ambiguous?', kind: 'choice', level: 2,
    text: 'Which of these grammars are ambiguous? Choose all that are.',
    options: ['S → S S | a', 'S → a S | a', 'S → a S b | S S | ε', 'S → ( S ) S | ε'], answer: [0, 2],
    solution: [0, 2], wrong: [[0], [0, 2, 3], [1, 3]], why: 'aaa has two trees in the first; in the third even ε does (S ⇒ ε, or S ⇒ S S ⇒ S ⇒ ε).',
    hints: H('Look for a word you can build in two ways.', 'S S next to S S: with three pieces, which pair is grouped first? And ε with S → S S...', 'The first and the third.') });
  ex({ id: 'cf-x-amb-count', chapter: 'cf-ambiguity', title: 'How many trees?', kind: 'number', level: 2,
    text: 'In E → E + E | x, how many different parse trees does x+x+x+x have?',
    answer: 5, solution: '5', wrong: ['3', '4', '6'], why: 'Three operators can be bracketed in 5 ways: the Catalan number C₃.',
    hints: H('Each tree is a way to put brackets around the sum.', 'Pick the + at the root (3 choices), then count the ways to bracket each side.', 'Root at the first +: 2 ways on the right; at the second: 1 × 1; at the third: 2 on the left. 2 + 1 + 2 = 5.') });
  ex({ id: 'cf-x-unamb-plus', chapter: 'cf-ambiguity', title: 'One tree for a⁺', kind: 'grammar', form: 'unambiguous', ref: 'S -> S S | a', alphabet: 'a',
    text: 'S → S S | a generates a⁺ ambiguously. Write an unambiguous grammar for the same language.',
    solution: 'S -> a S | a', wrong: ['S -> S S | a', 'S -> a S | S a | a', 'S -> a S | ε'],
    hints: H('Build the word in one direction only.', 'Each rule use adds one a at the front.', 'S → a S | a') });
  ex({ id: 'cf-x-unamb-expr', chapter: 'cf-ambiguity', title: 'Precedence by layers', kind: 'grammar', form: 'unambiguous', ref: 'E -> E + E | E * E | x', alphabet: 'x+*', level: 3,
    text: 'E → E + E | E * E | x is ambiguous. Write an unambiguous grammar for the same words in which * binds tighter than +, and both group to the left.',
    solution: 'E -> E + T | T\nT -> T * x | x', wrong: ['E -> E + E | E * E | x', 'E -> E + E | T\nT -> T * T | x', 'E -> E + T | T\nT -> T * x | x | E'],
    hints: H('Give sums and products separate nonterminals.', 'A sum is a list of products; a product is a list of x\'s. Recurse on the left for left grouping.', 'E → E + T | T, T → T * x | x') });
  ex({ id: 'cf-x-unamb-brackets', chapter: 'cf-ambiguity', title: 'Brackets without ambiguity', kind: 'grammar', form: 'unambiguous', ref: 'S -> S S | ( S ) | ε', alphabet: '()', level: 2,
    text: 'S → S S | ( S ) | ε generates the balanced bracket strings, ambiguously. Write an unambiguous grammar for them.',
    solution: 'S -> ( S ) S | ε', wrong: ['S -> S S | ( S ) | ε', 'S -> ( S ) | S S | ε', 'S -> ( S ) S | S ( S ) | ε'],
    hints: H('Decompose a nonempty word in exactly one way.', 'Its first bracket has exactly one partner; what comes before and after that partner is fixed.', 'S → ( S ) S | ε') });
  ex({ id: 'cf-x-fix-root', chapter: 'cf-ambiguity', title: 'What is at the root?', kind: 'choice',
    text: 'With E → E - T | T, T → T * F | F, F → ( E ) | n, which operator is at the root of the tree for n-n*n-n?',
    options: ['The first -', 'The *', 'The second -', 'Any of them, the grammar is ambiguous'], answer: 2,
    whyNot: { 0: 'E → E - T recurses on the left, so the leftmost - ends up deepest, not at the root.', 1: 'A * can only appear inside a T, below every -.', 3: 'This layered grammar is unambiguous.' },
    solution: 2, wrong: [0, 1, 3], why: 'Left recursion groups to the left: (n-(n*n))-n, so the last - is applied last, at the root.',
    hints: H('The operator at the root is the one evaluated last.', '- groups to the left here, and * binds tighter than -.', 'The second -: the tree is (n - (n*n)) - n.') });
  ex({ id: 'cf-x-inherent', chapter: 'cf-ambiguity', title: 'What inherent means', kind: 'choice',
    text: 'A context-free language L is inherently ambiguous. What follows?',
    options: ['Every grammar for L is ambiguous', 'Some grammar for L is ambiguous', 'L is not context-free', 'No PDA accepts L'], answer: 0,
    whyNot: { 1: 'That is true of every context-free language: you can always add a useless duplicate rule.', 2: 'It is context-free by assumption; it just has no unambiguous grammar.', 3: 'Every context-free language has a PDA.' },
    solution: 0, wrong: [1, 2, 3], why: 'Inherent ambiguity is a property of the language: no grammar for it, however clever, is unambiguous.',
    hints: H('Compare it with "this grammar is ambiguous".', 'Is it about one grammar, or about all grammars for L?', 'Every grammar for L is ambiguous.') });

  // =============================================================================================================
  // Chapter 3: cleanup and normal forms
  // =============================================================================================================
  C.lesson({
    id: 'cf-l-useless', chapter: 'cf-normal', title: 'Useless symbols, in the right order', minutes: 9,
    summary: 'A symbol is useful only if it can both produce a terminal string and be reached from the start; remove the non-generating ones first.',
    blocks: [
      "Grammars written by people (and produced by constructions) collect dead wood: nonterminals that never finish, and nonterminals no derivation ever reaches. They change nothing about the language, but every later algorithm must work around them.",
      { def: 'Generating', text: 'X generates if X ⇒* w for some terminal string w. Every terminal generates; A generates if some rule A → α has only generating symbols in α.' },
      { def: 'Reachable', text: 'X is reachable if S ⇒* α X β for some α, β. S is reachable; every symbol in a right side of a reachable nonterminal is reachable.' },
      "A symbol is **useful** when it is both. Both sets are computed by the same kind of loop: start small, add a symbol whenever a rule justifies it, stop when nothing changes.",
      { topic: 'clean-useless', input: { g: 'S → a | A B\nA → a\nB → b B' }, caption: 'B never finishes (B → b B forever), so S → A B goes; then A is no longer reachable. Watch A survive the first pass and fall in the second.' },
      { predict: { q: 'What if you remove unreachable symbols first, then non-generating ones, on that grammar?', options: ['The same result', 'A is left behind as a useless symbol', 'S is removed too'], answer: 1, explain: 'At first A is reachable (through S → A B), so it stays. Then B and the rule S → A B go, which leaves A unreachable, but the reachability pass is already over.' } },
      { warn: 'The order matters: non-generating first, then unreachable. Removing rules can make a symbol unreachable, but never makes one stop generating.' },
      { topic: 'clean-useless', input: { g: 'S → a S | A S\nA → a' }, caption: 'Here S itself does not generate: every rule for S keeps an S. The language is ∅, and nothing at all is left.' },
      { list: ['Generating: can finish. Reachable: can be used.', 'Remove non-generating symbols first, then unreachable ones.', 'If S does not generate, the language is empty.'] },
      { exercise: 'cf-x-genreach' },
      { exercise: 'cf-x-useful' },
      { exercise: 'cf-x-order' },
    ],
  });

  C.lesson({
    id: 'cf-l-eps-unit', chapter: 'cf-normal', title: 'ε-rules and unit rules', minutes: 11,
    summary: 'Replace each rule by every way of leaving out nullable symbols, then short-circuit chains of A → B.',
    blocks: [
      "Two more kinds of rule get in the way of tidy algorithms. An **ε-rule** A → ε makes a symbol vanish, so a rule's right side can shrink. A **unit rule** A → B just renames, and chains of them can even loop.",
      { def: 'Nullable', text: 'A is nullable if A ⇒* ε: either A → ε, or A → B₁…Bₖ with every Bᵢ nullable.' },
      "To remove ε-rules: find the nullable nonterminals; for every rule, add every version that leaves out some of its nullable symbols (but not the version that leaves out everything); then delete all ε-rules. If ε was in the language, it is lost; a new start symbol S₀ → S | ε puts it back.",
      { topic: 'clean-eps', input: { g: 'S → A b A\nA → a A | ε' }, caption: 'S → A b A has two nullable A\'s, so it splits into four rules: keep both, drop the first, drop the second, drop both. Count them as they appear.' },
      { predict: { q: 'A rule has three nullable symbols and one terminal on its right side. How many rules replace it?', options: ['3', '4', '8'], answer: 2, explain: 'Each of the three nullable symbols is kept or dropped independently: 2³ = 8 rules. None of them is empty, because the terminal always stays.' } },
      { h: 'Unit rules' },
      "A unit pair (A, B) means A ⇒* B using unit rules only (every A pairs with itself). For each unit pair (A, B) and each non-unit rule B → α, add A → α. Then drop the unit rules. Cycles like A → B → A are harmless: the pairs are a closure, computed once.",
      { topic: 'clean-unit', input: { g: 'E → E + T | T\nT → T * F | F\nF → ( E ) | x' }, caption: 'E reaches T and F by unit rules, so E inherits T\'s and F\'s real rules. Watch the unit pairs fill in first.' },
      { editor: { kind: 'grammar', text: 'S → A B | A | B\nA → a A | a\nB → b B | b', tests: 'a\nb\nab\naabbb\n-ε\n-ba' }, caption: 'The ε-free version of S → A B, A → a A | ε, B → b B | ε (minus ε itself). It still has two unit rules; can you remove them too?' },
      { list: ['Nullable: can vanish. Remove ε-rules by adding every way of leaving nullables out.', 'Keep ε in the language with a fresh start symbol, if it was there.', 'Unit pairs are a closure; copy the real rules along them, then drop A → B.'] },
      { exercise: 'cf-x-nullable' },
      { exercise: 'cf-x-eps-count' },
      { exercise: 'cf-x-noeps' },
      { exercise: 'cf-x-unitpairs' },
    ],
  });

  C.lesson({
    id: 'cf-l-cnf', chapter: 'cf-normal', title: 'Chomsky normal form', minutes: 12,
    summary: 'Every rule A → B C or A → a: parse trees become binary, and many algorithms become simple.',
    blocks: [
      "A normal form fixes the shape of every rule, so an algorithm needs to handle only a couple of cases. The best known one makes every parse tree binary.",
      { def: 'Chomsky normal form (CNF)', text: 'every rule is A → B C (two nonterminals) or A → a (one terminal); in addition S → ε is allowed for the start symbol S, and then S appears on no right side.' },
      { tip: 'Why keep S off the right sides when S → ε is a rule? Otherwise a rule like A → B S could use S → ε to make B S shrink to B, and a right side of two symbols would quietly stand for one: trees would no longer be binary and the 2n − 1 count would fail. When ε is not in the language there is no S → ε, and S may appear on right sides freely. The construction adds a fresh start symbol S0 anyway, which is always safe.' },
      { steps: ['Add a new start symbol S₀ → S, so the start never appears on a right side.', 'Remove ε-rules.', 'Remove unit rules.', 'Remove useless symbols.', 'Give each terminal inside a longer right side its own nonterminal: Tₐ → a.', 'Cut every right side longer than two into a chain: A → B C D becomes A → B X, X → C D.'] },
      { topic: 'cnf', input: { g: 'S → a S b | A\nA → c A | ε' }, caption: 'Follow the stages one by one. Watch the counter of rules not yet in CNF go down to zero, and the number of rules go up.' },
      { predict: { q: 'In CNF without ε, how many steps does a derivation of a word of length 5 take?', options: ['5', '9', '10'], answer: 1, explain: 'A → B C adds one symbol to the form, A → a turns a nonterminal into a letter. From S to 5 nonterminals takes 4 binary steps, and 5 terminal steps: 2·5 − 1 = 9.' } },
      "Why bother? In CNF every tree is binary, so the length of a word bounds the size of its trees. The CYK parser fills a triangle using only A → B C, and the pumping lemma of the last chapter counts nonterminals along a path of a binary tree.",
      { editor: { kind: 'grammar', text: 'S → A X | c\nX → S B\nA → a\nB → b', tests: 'c\nacb\naacbb\n-ab\n-ε' }, caption: 'S → a S b | c in Chomsky normal form. Each rule has two nonterminals or one terminal; ε is not in the language, so S may appear on a right side.' },
      { warn: 'The order of the stages matters: removing ε-rules can create unit rules, and removing unit rules can leave useless symbols. Shortening long rules last keeps the work small.' },
      { list: ['A → B C or A → a; S → ε only for the start symbol, and then the start is on no right side.', 'Start symbol, ε, units, useless, terminals, long rules: in that order.', 'A word of length n has a derivation of exactly 2n − 1 steps.'] },
      { exercise: 'cf-x-cnf-acb' },
      { exercise: 'cf-x-cnf-enda' },
      { exercise: 'cf-x-cnf-brackets' },
      { exercise: 'cf-x-cnf-steps' },
    ],
  });

  C.lesson({
    id: 'cf-l-leftrec', chapter: 'cf-normal', title: 'Left recursion and Greibach normal form', minutes: 12,
    summary: 'A → A α loops a top-down parser; turn it into right recursion, and go on until every rule starts with a terminal.',
    blocks: [
      "A rule like E → E + n is fine for describing sums, but a parser that expands the leftmost nonterminal first would expand E into E + n into E + n + n forever, without reading a symbol. That is **left recursion**: A ⇒⁺ A α.",
      "The immediate case has a standard cure. The rules A → A α | β say: one β, then any number of α's. Generate them in the other order:",
      { math: 'A → A α₁ | … | A αₘ | β₁ | … | βₙ\n      becomes\nA  → β₁ A\' | … | βₙ A\'\nA\' → α₁ A\' | … | αₘ A\' | ε' },
      { topic: 'left-rec', input: { g: 'E → E + n | n', w: 'n+n+n' }, caption: 'The tree for n+n+n before and after. The long left spine turns into a right spine: the same word, built from the other end.' },
      { predict: { q: 'Remove left recursion from S → S x | S y | z. Which rules for S\' do you get?', options: ['S\' → x S\' | y S\' | ε', 'S\' → S x | S y', 'S\' → z S\' | ε'], answer: 0, explain: 'The α\'s are x and y, the only β is z: S → z S\', S\' → x S\' | y S\' | ε. The language is z(x|y)*, as before.' } },
      "Indirect left recursion (S → A a, A → S c) hides the loop across two nonterminals. The general method orders the nonterminals, substitutes earlier ones into the left corners of later ones, and then removes the immediate recursion that appears.",
      { topic: 'left-rec', input: { g: 'S → A a | b\nA → S c | d', w: 'bcaca' }, caption: 'S ⇒ A a ⇒ S c a: a loop through A. Watch the substitution bring it into the open first.' },
      { h: 'Greibach normal form' },
      { def: 'Greibach normal form (GNF)', text: 'every rule is A → a B₁ … Bₖ (k ≥ 0): one terminal, then only nonterminals; S → ε allowed for a start that is on no right side.' },
      "In GNF each derivation step reads exactly one input symbol, so a word of length n has a derivation of exactly n steps, and a top-down PDA built from it never expands without reading. Getting there means removing all left recursion and then substituting until every rule starts with a terminal.",
      { topic: 'gnf', input: { g: 'S → S a | b' }, caption: 'S → S a | b: the left recursion goes first, then every right side starts with b or a.' },
      { list: ['Left recursion loops a top-down parser; right recursion does not.', 'A → A α | β becomes A → β A\', A\' → α A\' | ε.', 'GNF: one terminal first, then nonterminals; one input symbol per step.'] },
      { exercise: 'cf-x-lr-minus' },
      { exercise: 'cf-x-lr-indirect' },
      { exercise: 'cf-x-gnf-ba' },
      { exercise: 'cf-x-gnf-two' },
    ],
  });

  // ---- chapter 3 exercises -------------------------------------------------------------------------------------
  const yn = (o) => Object.fromEntries(Object.entries(o).map(([k, v]) => [k, v ? 'yes' : 'no']));
  ex({ id: 'cf-x-nullable', chapter: 'cf-normal', title: 'Which nonterminals vanish?', kind: 'table', table: 'custom',
    grammar: 'S -> A B | c S\nA -> a | ε\nB -> A A | b\nD -> d | A d',
    text: 'For the grammar S → A B | c S, A → a | ε, B → A A | b, D → d | A d, write yes or no: is each nonterminal nullable (can it derive ε)?',
    rows: ['S', 'A', 'B', 'D'], cols: ['nullable'], cells: yn({ 'S|nullable': true, 'A|nullable': true, 'B|nullable': true, 'D|nullable': false }),
    solution: yn({ 'S|nullable': true, 'A|nullable': true, 'B|nullable': true, 'D|nullable': false }),
    wrong: [yn({ 'S|nullable': false, 'A|nullable': true, 'B|nullable': true, 'D|nullable': false }), yn({ 'S|nullable': true, 'A|nullable': true, 'B|nullable': false, 'D|nullable': false }), yn({ 'S|nullable': true, 'A|nullable': true, 'B|nullable': true, 'D|nullable': true })],
    hints: H('Start with the nonterminals that have an ε-rule.', 'Then add any nonterminal with a rule whose right side is made only of nullable symbols. Repeat.', 'A (A → ε), then B (B → A A), then S (S → A B). D always needs a d: S, A, B yes; D no.') });
  ex({ id: 'cf-x-genreach', chapter: 'cf-normal', title: 'Generating and reachable', kind: 'table', table: 'custom', level: 2,
    grammar: 'S -> A B | a\nA -> a A\nB -> b\nC -> c S',
    text: 'For the grammar S → A B | a, A → a A, B → b, C → c S (as given, before removing anything), write yes or no in each cell.',
    rows: ['S', 'A', 'B', 'C'], cols: ['generating', 'reachable'],
    cells: yn({ 'S|generating': true, 'A|generating': false, 'B|generating': true, 'C|generating': true, 'S|reachable': true, 'A|reachable': true, 'B|reachable': true, 'C|reachable': false }),
    solution: yn({ 'S|generating': true, 'A|generating': false, 'B|generating': true, 'C|generating': true, 'S|reachable': true, 'A|reachable': true, 'B|reachable': true, 'C|reachable': false }),
    wrong: [yn({ 'S|generating': false, 'A|generating': false, 'B|generating': true, 'C|generating': false, 'S|reachable': true, 'A|reachable': true, 'B|reachable': true, 'C|reachable': false }), yn({ 'S|generating': true, 'A|generating': false, 'B|generating': true, 'C|generating': true, 'S|reachable': true, 'A|reachable': false, 'B|reachable': false, 'C|reachable': false })],
    hints: H('Generating: does some rule finish? A → a A never does.', 'Reachable: follow the right sides from S. Nothing mentions C.', 'Generating: S, B, C yes, A no. Reachable: S, A, B yes, C no.') });
  ex({ id: 'cf-x-useful', chapter: 'cf-normal', title: 'What survives the cleanup', kind: 'string', set: true, level: 2,
    text: 'Remove the useless symbols from S → A B | a, A → a A, B → b, C → c S, in the right order. Which nonterminals are left? Write them as a set.',
    answer: '{S}', solution: '{S}', wrong: ['{S, B}', '{S, B, C}', '{S, A, B}'],
    hints: H('First remove the non-generating symbols, with every rule that uses them.', 'A goes, and with it S → A B. Now recompute what is reachable from S.', 'Only S → a is left, so the set is {S}.') });
  ex({ id: 'cf-x-order', chapter: 'cf-normal', title: 'Why that order?', kind: 'choice',
    text: 'Why are non-generating symbols removed before unreachable ones?',
    options: ['Removing rules with non-generating symbols can make other symbols unreachable', 'Removing unreachable symbols can make other symbols non-generating', 'It is faster, but either order gives the same grammar', 'Unreachable symbols cannot be found until ε-rules are gone'], answer: 0,
    whyNot: { 1: 'Removing unreachable symbols only removes rules that no derivation from S uses, so no remaining symbol loses a way to finish.', 2: 'The other order can leave useless symbols behind.' },
    solution: 0, wrong: [1, 2, 3], why: 'Deleting S → A B (because B never finishes) can strand A, which is only discovered by a reachability pass done afterwards.',
    hints: H('Think of what each removal deletes: rules.', 'Which pass can be spoiled by deleting rules later?', 'The first option: removing non-generating symbols can strand others.') });
  ex({ id: 'cf-x-eps-count', chapter: 'cf-normal', title: 'Every way of leaving out', kind: 'number',
    text: 'Remove the ε-rules from S → X y X, X → x | ε. How many rules for S are there afterwards?',
    answer: 4, solution: '4', wrong: ['3', '2', '8'], why: 'X y X, y X, X y and y.',
    hints: H('X is nullable; S → X y X has two of them.', 'Keep or drop each X independently.', '2 × 2 = 4: X y X, y X, X y, y.') });
  ex({ id: 'cf-x-noeps', chapter: 'cf-normal', title: 'A grammar without ε-rules', kind: 'grammar', form: 'noeps', alphabet: 'ab', level: 2,
    text: 'S → A B, A → a A | ε, B → b B | ε generates a*b*. Write a grammar with no ε-rules at all for a*b* without ε (every nonempty word of a*b*).',
    member: (w) => w.length > 0 && /^a*b*$/.test(w),
    solution: 'S -> A B | A | B\nA -> a A | a\nB -> b B | b', wrong: ['S -> A B\nA -> a A | ε\nB -> b B | ε', 'S -> A B\nA -> a A | a\nB -> b B | b', 'S -> A B | A | B\nA -> a A | a\nB -> b B | b | a'],
    hints: H('A and B are nullable. Which versions of S → A B leave them out?', 'Keep A B, drop A, drop B (never both: that would be ε). A → a A | ε becomes A → a A | a.', 'S → A B | A | B, A → a A | a, B → b B | b') });
  ex({ id: 'cf-x-unitpairs', chapter: 'cf-normal', title: 'Unit pairs', kind: 'table', table: 'custom', cellKind: 'set', level: 2,
    grammar: 'S -> A | x S\nA -> B | y\nB -> z | A x',
    text: 'In S → A | x S, A → B | y, B → z | A x, list for each nonterminal X the nonterminals Y with X ⇒* Y by unit rules alone (X itself included).',
    rows: ['S', 'A', 'B'], cols: ['unit pairs'], cells: { 'S|unit pairs': 'S, A, B', 'A|unit pairs': 'A, B', 'B|unit pairs': 'B' },
    solution: { 'S|unit pairs': 'S, A, B', 'A|unit pairs': 'A, B', 'B|unit pairs': 'B' },
    wrong: [{ 'S|unit pairs': 'S, A', 'A|unit pairs': 'A, B', 'B|unit pairs': 'B' }, { 'S|unit pairs': 'S, A, B', 'A|unit pairs': 'A, B', 'B|unit pairs': 'B, A' }, { 'S|unit pairs': 'A, B', 'A|unit pairs': 'B', 'B|unit pairs': '' }],
    hints: H('A unit rule has a single nonterminal on its right side. Which rules here are unit rules?', 'S → A and A → B. B → A x is not a unit rule.', 'S: S, A, B; A: A, B; B: B.') });
  ex({ id: 'cf-x-cnf-acb', chapter: 'cf-normal', title: 'CNF for aⁿcbⁿ', kind: 'grammar', form: 'cnf', ref: 'S -> a S b | c', alphabet: 'abc', level: 2,
    text: 'Write a grammar in Chomsky normal form for the language of S → a S b | c.',
    solution: 'S -> A X | c\nX -> S B\nA -> a\nB -> b', wrong: ['S -> a S b | c', 'S -> A X | c\nX -> S A\nA -> a\nB -> b', 'S -> A X | c\nX -> S b\nA -> a'],
    hints: H('Give a and b their own nonterminals: A → a, B → b. ε is not in the language, so S may stay on a right side.', 'S → A S B has three symbols; cut it into two rules of two.', 'S → A X | c, X → S B, A → a, B → b') });
  ex({ id: 'cf-x-cnf-enda', chapter: 'cf-normal', title: 'CNF for words ending in a', kind: 'grammar', form: 'cnf', ref: 'S -> a S | b S | a', alphabet: 'ab',
    text: 'Write a grammar in Chomsky normal form for the language of S → a S | b S | a (the words over {a, b} that end in a).',
    solution: 'S -> A S | B S | a\nA -> a\nB -> b', wrong: ['S -> a S | b S | a', 'S -> A S | B S | a | b\nA -> a\nB -> b', 'S -> A S | B S | a\nA -> a\nB -> b | ε'],
    hints: H('S → a S mixes a terminal with a nonterminal; that is not allowed in a rule of length 2.', 'Replace the terminals by new nonterminals that produce them. Only the start symbol may ever have an ε-rule.', 'S → A S | B S | a, A → a, B → b') });
  ex({ id: 'cf-x-cnf-brackets', chapter: 'cf-normal', title: 'CNF with ε in the language', kind: 'grammar', form: 'cnf', ref: 'S -> ( S ) S | ε', alphabet: '()', level: 3,
    text: 'Write a grammar in Chomsky normal form for the balanced brackets S → ( S ) S | ε. ε is in the language, so you need a start symbol with an ε-rule that appears on no right side.',
    solution: 'S0 -> L A | L D | L C | L R | ε\nS -> L A | L D | L C | L R\nA -> S D\nD -> R S\nC -> S R\nL -> (\nR -> )',
    wrong: ['S -> ( S ) S | ε', 'S -> L A | L D | L C | L R | ε\nA -> S D\nD -> R S\nC -> S R\nL -> (\nR -> )', 'S0 -> L A | L R | ε\nS -> L A | L R\nA -> S D\nD -> R S\nL -> (\nR -> )'],
    hints: H('Remove ε first: S is nullable, so ( S ) S has four versions: ( S ) S, ( ) S, ( S ), ( ).', 'Add S0 → S | ε, remove the unit rule S0 → S by copying S\'s rules, then name the brackets L → (, R → ) and cut long rules.', 'S0 → L A | L D | L C | L R | ε; S → L A | L D | L C | L R; A → S D; D → R S; C → S R; L → (; R → )') });
  ex({ id: 'cf-x-cnf-steps', chapter: 'cf-normal', title: 'Steps in CNF', kind: 'number', level: 2,
    text: 'A grammar is in Chomsky normal form with no ε-rule. How many steps does any derivation of a word of length 6 take?',
    answer: 11, solution: '11', wrong: ['6', '12', '10'], why: '5 steps A → B C to get six nonterminals, then 6 steps A → a.',
    hints: H('Count the two kinds of steps separately.', 'Each A → B C adds one symbol to the form; each A → a turns a nonterminal into a letter.', '(6 − 1) + 6 = 11.') });
  ex({ id: 'cf-x-lr-minus', chapter: 'cf-normal', title: 'Turn the recursion around', kind: 'grammar', form: 'noleftrec', ref: 'E -> E - n | n', alphabet: 'n-',
    text: 'Remove the left recursion from E → E - n | n. Your grammar must generate the same words and have no left recursion.',
    solution: "E -> n E'\nE' -> - n E' | ε", wrong: ['E -> E - n | n', "E -> n E'\nE' -> - n | ε", "E -> n E'\nE' -> E' - n | ε"],
    hints: H('Every word is one n followed by any number of -n.', 'Generate the n first, then the repetitions with a new nonterminal that recurses on the right.', "E → n E', E' → - n E' | ε") });
  ex({ id: 'cf-x-lr-indirect', chapter: 'cf-normal', title: 'Hidden left recursion', kind: 'grammar', form: 'noleftrec', ref: 'A -> B a | c\nB -> A b | B d | e', alphabet: 'abcde', level: 3,
    text: 'A → B a | c, B → A b | B d | e is left-recursive through A ⇒ B a ⇒ A b a, and B → B d directly. Write an equivalent grammar with no left recursion (start symbol A).',
    solution: 'A -> B a | c\nB -> c b R | e R\nR -> a b R | d R | ε', wrong: ['A -> B a | c\nB -> A b | B d | e', 'A -> B a | c\nB -> e R\nR -> a b R | d R | ε', 'A -> B a | c\nB -> c b R | e R\nR -> a b R | ε'],
    hints: H('Substitute A\'s rules into B → A b: B → B a b | c b.', 'Now B → B a b | B d | c b | e has only immediate left recursion.', 'A → B a | c, B → c b R | e R, R → a b R | d R | ε') });
  ex({ id: 'cf-x-gnf-ba', chapter: 'cf-normal', title: 'GNF for b a*', kind: 'grammar', form: 'gnf', ref: 'S -> S a | b', alphabet: 'ab', level: 2,
    text: 'Write a grammar in Greibach normal form for the language of S → S a | b.',
    solution: 'S -> b | b Z\nZ -> a | a Z', wrong: ['S -> S a | b', 'S -> b Z\nZ -> a Z | ε', 'S -> b | b Z\nZ -> a | b Z'],
    hints: H('The language is one b followed by any number of a\'s.', 'S must start with b; a new nonterminal produces a nonempty run of a\'s, each rule starting with a.', 'S → b | b Z, Z → a | a Z') });
  ex({ id: 'cf-x-gnf-two', chapter: 'cf-normal', title: 'GNF by substitution', kind: 'grammar', form: 'gnf', ref: 'S -> A b | a\nA -> a A | b', alphabet: 'ab', level: 3,
    text: 'Write a grammar in Greibach normal form for the language of S → A b | a, A → a A | b.',
    solution: 'S -> a | a A B | b B\nA -> a A | b\nB -> b', wrong: ['S -> A b | a\nA -> a A | b', 'S -> a | a A b | b b\nA -> a A | b', 'S -> a | a A B\nA -> a A | b\nB -> b'],
    hints: H('A\'s rules already start with a terminal. S → A b does not: substitute A into it.', 'S → a A b | b b | a; then the trailing b\'s need a nonterminal B → b.', 'S → a | a A B | b B, A → a A | b, B → b') });

  // =============================================================================================================
  // Chapter 4: pushdown automata
  // =============================================================================================================
  const PDA_AB = 'start p\nstack-start Z\naccept f\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> f, Z\np, ε, Z -> f, Z';
  C.lesson({
    id: 'cf-l-pda', chapter: 'cf-pda', title: 'A machine with a stack', minutes: 12,
    summary: 'A pushdown automaton is a finite automaton that may push and pop symbols on an unbounded stack, and may guess.',
    blocks: [
      "A finite automaton cannot check aⁿbⁿ because it would have to remember n. Give it one unbounded memory, but a very disciplined one: a **stack**, where only the top is visible. Push an A for every a, pop one for every b, and accept when the bottom shows again.",
      { def: 'Pushdown automaton (PDA)', text: 'a 7-tuple (Q, Σ, Γ, δ, q₀, Z₀, F): states Q, input alphabet Σ, stack alphabet Γ, start state q₀, start stack symbol Z₀, accepting states F, and δ mapping (state, input symbol or ε, top of stack) to a finite set of (state, string to push).' },
      "A move (p, a, X) → (q, γ) means: in state p, reading a with X on top, pop X, push γ (written top first) and go to q. With ε for the input, the move reads nothing; with ε for the pop, it ignores the stack. A **configuration** is (state, input left, stack).",
      { topic: 'pda-run', input: { m: PDA_AB, w: 'aabb' }, caption: 'The stack grows with the a\'s and shrinks with the b\'s. Watch the moment Z is on top again: only then can the machine move to f.' },
      { predict: { q: 'On this machine, what happens with aab?', options: ['It accepts', 'It reads all the input but stays in q with A on top, so it rejects', 'It gets stuck on the first b'], answer: 1, explain: 'Two A\'s go on the stack, one b pops one of them. The input is used up with A still on top; the move to f needs Z on top. No accepting configuration, so aab is rejected.' } },
      { h: 'Nondeterminism' },
      "A PDA may have several moves from one configuration, and accepts if **some** run accepts. That lets it guess: for even palindromes it guesses where the middle is, pushing before and popping after.",
      { topic: 'pda-tree', input: { m: 'start q0\nstack-start Z\naccept q2\nq0, a, ε -> q0, A\nq0, b, ε -> q0, B\nq0, ε, ε -> q1, ε\nq1, a, A -> q1, ε\nq1, b, B -> q1, ε\nq1, ε, Z -> q2, Z', w: 'abba' }, caption: 'Every configuration is a node; every guess of the middle is a branch. Most branches die; one reaches q2 with all input read.' },
      { sandbox: { kind: 'pda', text: PDA_AB, input: 'aaabbb' }, caption: 'Run this PDA for aⁿbⁿ on your own inputs: ε, abab, aabbb.' },
      { list: ['A stack: push, pop, look only at the top.', 'A move reads one symbol or ε, pops one symbol or nothing, pushes a string.', 'Nondeterministic: accept if some run accepts.'] },
      { exercise: 'cf-x-stack' },
      { exercise: 'cf-x-pda-ab2' },
      { exercise: 'cf-x-pda-brackets' },
      { exercise: 'cf-x-pda-eqab' },
      { exercise: 'cf-x-pda-ratio' },
      { exercise: 'cf-x-pda-pal' },
      { exercise: 'cf-x-pda-or' },
    ],
  });

  C.lesson({
    id: 'cf-l-accept', chapter: 'cf-pda', title: 'Final state or empty stack', minutes: 8,
    summary: 'A PDA can accept by reaching an accepting state or by emptying its stack; the two give the same class of languages.',
    blocks: [
      "There are two natural ways for a PDA to say yes. **By final state**: all input read, in a state of F (whatever is on the stack). **By empty stack**: all input read, and the stack completely empty (whatever the state).",
      { def: 'Acceptance', text: 'L(P) = { w : (q₀, w, Z₀) ⊢* (f, ε, γ) for some f in F }; N(P) = { w : (q₀, w, Z₀) ⊢* (q, ε, ε) for some q }.' },
      "For a given machine the two languages usually differ. But any language accepted one way by some PDA is accepted the other way by another PDA. To go from final state to empty stack: when in an accepting state, jump to a new state that pops everything. To go back: put a new bottom marker under Z₀, and when it shows, the old stack is empty: move to a new accepting state.",
      { topic: 'pda-accept', input: { m: 'start q0\nstack-start Z\naccept q2\nq0, a, Z -> q0, A Z\nq0, a, A -> q0, A A\nq0, b, A -> q1, ε\nq1, b, A -> q1, ε\nq1, ε, Z -> q2, Z', w: 'ab' }, caption: 'A new bottom marker and a draining state turn final-state acceptance into empty-stack acceptance. Watch why the new marker is needed: without it, the old machine could empty its stack by accident.' },
      { predict: { q: 'Why add a new bottom marker when converting final state → empty stack?', options: ['To make the machine deterministic', 'So the old machine cannot empty its stack and be accepted without passing through an accepting state', 'Because empty-stack machines need two start symbols'], answer: 1, explain: 'If the old machine popped Z₀ on its own in a non-accepting run, the new machine would accept wrongly. The new marker sits underneath and is only removed by the draining state.' } },
      { sandbox: { kind: 'pda', text: 'start p\nstack-start Z\naccept-by empty\np, a, Z -> p, A\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε', input: 'aabb' }, caption: 'aⁿbⁿ with n ≥ 1, by empty stack: the first a replaces Z, so the stack is empty exactly when the b\'s have matched all the a\'s.' },
      { list: ['Final state: in F after the input. Empty stack: nothing left on the stack after the input.', 'Both define exactly the context-free languages.', 'A new bottom marker protects each conversion from accidents.'] },
      { exercise: 'cf-x-pda-empty' },
      { exercise: 'cf-x-modes' },
    ],
  });

  C.lesson({
    id: 'cf-l-cfg-pda', chapter: 'cf-pda', title: 'From a grammar to a PDA', minutes: 11,
    summary: 'A one-state PDA can guess a leftmost derivation on its stack (top-down), or build a rightmost derivation backwards (bottom-up).',
    blocks: [
      "Every grammar has a PDA, and the construction is short. Keep the part of the sentential form that is not yet matched on the stack. If a nonterminal is on top, **expand** it by guessing a rule; if a terminal is on top, **match** it against the next input symbol.",
      { math: 'for each rule A → α:   (q, ε, A) → (q, α)\nfor each terminal a:  (q, a, a) → (q, ε)\nstart with S on the stack, accept by empty stack' },
      { topic: 'pda-topdown', input: { g: 'S → a S b | c', w: 'aacbb' }, caption: 'Expand, match, match... The stack always holds the rest of the leftmost sentential form. Watch the derivation on the side advance with every expand.' },
      { predict: { q: 'Grammar S → a S b | c. The stack is S b (S on top) and the next input symbol is c. Which move leads to acceptance?', options: ['Expand S → a S b', 'Expand S → c, then match c', 'Match c against S'], answer: 1, explain: 'Only S → c puts a c on top, which then matches the input. Expanding S → a S b would need an a next.' } },
      "The other direction works bottom-up: **shift** input symbols onto the stack, and when the top of the stack is the right side of a rule, **reduce** it to the left side. Accept when only S is left. This is the heart of every shift-reduce parser.",
      { topic: 'pda-bottomup', input: { g: 'S → a S b | c', w: 'aacbb' }, caption: 'Shift, shift, shift c, reduce c to S, shift b, reduce a S b... Read the rightmost derivation upwards on the side.' },
      { list: ['Top-down: expand nonterminals, match terminals; one state, empty stack.', 'Bottom-up: shift symbols, reduce right sides.', 'Both are nondeterministic in general; parsing theory is about removing the guesses.'] },
      { exercise: 'cf-x-expand' },
    ],
  });

  C.lesson({
    id: 'cf-l-pda-cfg', chapter: 'cf-pda', title: 'From a PDA to a grammar', minutes: 10,
    summary: 'A nonterminal [p X q] stands for every input that takes the PDA from p to q while popping X for good.',
    blocks: [
      "The way back is the surprising half of the theorem: every PDA has a grammar. The idea is to name what a piece of a run does to the stack. Take a PDA accepting by empty stack. The nonterminal [p X q] generates exactly the inputs that take the machine from state p with X on top to state q, with X (and everything pushed above it) popped, and the stack below untouched.",
      { math: 'S → [q₀ Z₀ q]                              for every state q\n(p, a, X) → (r, ε):        [p X r] → a\n(p, a, X) → (r, Y₁…Yₖ):    [p X qₖ] → a [r Y₁ q₁] [q₁ Y₂ q₂] … [qₖ₋₁ Yₖ qₖ]\n                            for every choice of states q₁ … qₖ' },
      "The middle states are guessed: the grammar tries them all, and most of the resulting rules are useless and can be cleaned away.",
      { topic: 'pda-to-cfg', input: { m: 'start p\nstack-start Z\naccept-by empty\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> q, ε\np, ε, Z -> p, ε', w: 'aabb' }, caption: 'Watch the count of rules made against the count of useful ones. The tree for aabb shows each triple as a piece of the run.' },
      { predict: { q: 'A PDA has 3 states and 2 stack symbols. How many triple nonterminals [p X q] are there?', options: ['6', '12', '18'], answer: 2, explain: '3 choices for p, 2 for X, 3 for q: 3 · 2 · 3 = 18 (plus the start symbol S).' } },
      { list: ['[p X q]: the inputs that pop X while going from p to q.', 'One rule per move and per choice of intermediate states.', 'Grammars and PDAs describe exactly the same languages.'] },
      { exercise: 'cf-x-triples' },
      { exercise: 'cf-x-pda-to-gr' },
    ],
  });

  C.lesson({
    id: 'cf-l-dpda', chapter: 'cf-pda', title: 'Deterministic PDAs', minutes: 9,
    summary: 'Without guessing, a PDA recognises fewer languages: wcwᴿ is fine, wwᴿ is not.',
    blocks: [
      "For finite automata, guessing adds nothing. For PDAs it does. A PDA is **deterministic** when it never has a choice: for every state, input symbol and stack top there is at most one move, and an ε-move on a stack top excludes any reading move on the same top.",
      { def: 'Deterministic PDA (DPDA)', text: 'a PDA where for every state q, input a and stack symbol X, |δ(q, a, X)| + |δ(q, ε, X)| ≤ 1 (counting moves that ignore the stack as applying to every top).' },
      { topic: 'dpda', input: { m: 'start q0\nstack-start Z\naccept q2\nq0, a, ε -> q0, A\nq0, b, ε -> q0, B\nq0, c, ε -> q1, ε\nq1, a, A -> q1, ε\nq1, b, B -> q1, ε\nq1, ε, Z -> q2, Z', w: 'abcba' }, caption: 'With a middle marker c, the machine knows exactly when to stop pushing and start popping. No two moves compete.' },
      { topic: 'dpda', input: { m: 'start q0\nstack-start Z\naccept q2\nq0, a, ε -> q0, A\nq0, b, ε -> q0, B\nq0, ε, ε -> q1, ε\nq1, a, A -> q1, ε\nq1, b, B -> q1, ε\nq1, ε, Z -> q2, Z', w: 'abba' }, caption: 'Without the marker, the ε-move to q1 competes with every push. The highlighted pairs are the guesses the machine cannot avoid.' },
      { predict: { q: 'Is the language of even palindromes wwᴿ accepted by some deterministic PDA?', options: ['Yes, with more states', 'No: without a marker, no DPDA can tell where the middle is', 'Yes, by empty stack'], answer: 1, explain: 'It is context-free but not deterministic context-free. Intuitively, after reading aabbaa... a deterministic machine must commit to popping or pushing before it knows whether the middle has passed.' } },
      "Deterministic context-free languages are the ones practical parsers (LL, LR) handle. They are closed under complement, which the context-free languages are not, and every one has an unambiguous grammar.",
      { list: ['DPDA: never two applicable moves.', 'wcwᴿ and aⁿbⁿ are deterministic; wwᴿ is not.', 'Deterministic CFLs ⊊ CFLs; they are what LR parsers recognise.'] },
      { exercise: 'cf-x-dpda' },
    ],
  });

  // ---- chapter 4 exercises -------------------------------------------------------------------------------------
  ex({ id: 'cf-x-stack', chapter: 'cf-pda', title: 'What is on the stack?', kind: 'string',
    text: 'Run the PDA with moves p, a, Z → p, A Z; p, a, A → p, A A; p, b, A → q, ε; q, b, A → q, ε (start p, stack Z) on aab. What is on the stack afterwards, top first?',
    answer: ['AZ'], solution: 'A Z', wrong: ['Z', 'AAZ', 'ZA'],
    hints: H('Each a pushes one A.', 'After aa the stack is A A Z.', 'The b pops one A: A Z.') });
  ex({ id: 'cf-x-pda-ab2', chapter: 'cf-pda', title: 'Two b for every a', kind: 'machine', machine: 'pda', alphabet: 'ab',
    text: 'Build a PDA (accepting by final state) for aⁿb²ⁿ with n ≥ 0.',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && b[1] === 2 * b[0]; },
    solution: 'start p\nstack-start Z\naccept f\np, a, Z -> p, B B Z\np, a, B -> p, B B B\np, b, B -> q, ε\nq, b, B -> q, ε\nq, ε, Z -> f, Z\np, ε, Z -> f, Z',
    wrong: [PDA_AB, 'start p\nstack-start Z\naccept f\np, a, Z -> p, B B Z\np, a, B -> p, B B B\np, b, B -> q, ε\nq, b, B -> q, ε\nq, ε, Z -> f, Z', 'start p\nstack-start Z\naccept f\np, a, Z -> p, B B Z\np, a, B -> p, B B B\np, b, B -> p, ε\np, ε, Z -> f, Z'],
    hints: H('Push two symbols for every a, pop one for every b.', 'After the first b, do not allow any more a\'s: switch to a popping state.', 'Do not forget n = 0: from the start, Z on top may go straight to the accepting state.') });
  ex({ id: 'cf-x-pda-brackets', chapter: 'cf-pda', title: 'Round and square', kind: 'machine', machine: 'pda', alphabet: '()[]', level: 2,
    text: 'Build a PDA for the balanced strings over ( ) [ ], where each bracket is closed by its own kind.',
    member: (w) => { const st = []; for (const c of w) { if (c === '(' || c === '[') st.push(c); else { const o = st.pop(); if ((c === ')' && o !== '(') || (c === ']' && o !== '[')) return false; } } return !st.length; },
    solution: 'start q\nstack-start Z\naccept f\nq, (, ε -> q, P\nq, [, ε -> q, K\nq, ), P -> q, ε\nq, ], K -> q, ε\nq, ε, Z -> f, Z',
    wrong: ['start q\nstack-start Z\naccept f\nq, (, ε -> q, P\nq, [, ε -> q, P\nq, ), P -> q, ε\nq, ], P -> q, ε\nq, ε, Z -> f, Z', 'start q\nstack-start Z\naccept q\nq, (, ε -> q, P\nq, [, ε -> q, K\nq, ), P -> q, ε\nq, ], K -> q, ε'],
    hints: H('Push a symbol for each opening bracket, a different one for each kind.', 'A closing bracket may only pop its own kind.', 'Accept only when the bottom Z is on top again: q, ε, Z → f, Z.') });
  ex({ id: 'cf-x-pda-eqab', chapter: 'cf-pda', title: 'Equal counts in any order', kind: 'machine', machine: 'pda', alphabet: 'ab', level: 2,
    text: 'Build a PDA for the strings over {a, b} with as many a\'s as b\'s, in any order.',
    member: (w) => count(w, 'a') === count(w, 'b'),
    solution: 'start q\nstack-start Z\naccept f\nq, a, Z -> q, A Z\nq, a, A -> q, A A\nq, a, B -> q, ε\nq, b, Z -> q, B Z\nq, b, B -> q, B B\nq, b, A -> q, ε\nq, ε, Z -> f, Z',
    wrong: [PDA_AB, 'start q\nstack-start Z\naccept f\nq, a, Z -> q, A Z\nq, a, A -> q, A A\nq, b, Z -> q, B Z\nq, b, B -> q, B B\nq, b, A -> q, ε\nq, ε, Z -> f, Z'],
    hints: H('The stack holds the surplus: some A\'s or some B\'s, never both.', 'A symbol of the other kind cancels one from the stack; a symbol of the same kind (or on Z) is pushed.', 'q: a on Z or A pushes A, a on B pops; b symmetric; q, ε, Z → f, Z.') });
  ex({ id: 'cf-x-pda-ratio', chapter: 'cf-pda', title: 'One or two b per a', kind: 'machine', machine: 'pda', alphabet: 'ab', level: 3,
    text: 'Build a PDA for aⁱbʲ with i ≤ j ≤ 2i. Guessing is allowed.',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] <= b[1] && b[1] <= 2 * b[0]; },
    solution: 'start p\nstack-start Z\naccept f\np, a, ε -> p, A\np, a, ε -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> f, Z\np, ε, Z -> f, Z',
    wrong: ['start p\nstack-start Z\naccept f\np, a, ε -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> f, Z\np, ε, Z -> f, Z', 'start p\nstack-start Z\naccept f\np, a, ε -> p, A\np, a, ε -> p, A A\np, a, ε -> p, ε\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> f, Z\np, ε, Z -> f, Z'],
    hints: H('Decide, for each a, how many b\'s it will match.', 'On each a, guess: push one A, or push two.', 'p, a, ε → p, A and p, a, ε → p, A A; each b pops one A; accept on Z.') });
  ex({ id: 'cf-x-pda-pal', chapter: 'cf-pda', title: 'All palindromes', kind: 'machine', machine: 'pda', alphabet: 'ab', level: 3,
    text: 'Build a PDA for all palindromes over {a, b}, of even and of odd length.',
    member: (w) => w === rev(w),
    solution: 'start s\nstack-start Z\naccept t\ns, a, ε -> s, A\ns, b, ε -> s, B\ns, ε, ε -> m, ε\ns, a, ε -> m, ε\ns, b, ε -> m, ε\nm, a, A -> m, ε\nm, b, B -> m, ε\nm, ε, Z -> t, Z',
    wrong: ['start s\nstack-start Z\naccept t\ns, a, ε -> s, A\ns, b, ε -> s, B\ns, ε, ε -> m, ε\nm, a, A -> m, ε\nm, b, B -> m, ε\nm, ε, Z -> t, Z', 'start s\nstack-start Z\naccept t\ns, a, ε -> s, A\ns, b, ε -> s, B\ns, a, ε -> m, ε\ns, b, ε -> m, ε\nm, a, A -> m, ε\nm, b, B -> m, ε\nm, ε, Z -> t, Z'],
    hints: H('Push the first half, pop while matching the second half.', 'Guess the middle. For odd length, the middle symbol is read without being pushed.', 'Three ways to switch from s to m: ε, or read a, or read b, each without pushing.') });
  ex({ id: 'cf-x-pda-or', chapter: 'cf-pda', title: 'Two of three agree', kind: 'machine', machine: 'pda', alphabet: 'abc', level: 3,
    text: 'Build a PDA for aⁱbʲcᵏ with i = j or j = k.',
    member: (w) => { const b = blocks(w, 'abc'); return !!b && (b[0] === b[1] || b[1] === b[2]); },
    solution: 'start s\nstack-start Z\naccept r f\ns, ε, ε -> p, ε\ns, ε, ε -> u, ε\np, a, ε -> p, A\np, ε, Z -> r, Z\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> r, Z\nr, c, ε -> r, ε\nu, a, ε -> u, ε\nu, ε, ε -> v, ε\nv, b, ε -> v, B\nv, ε, Z -> f, Z\nv, c, B -> w, ε\nw, c, B -> w, ε\nw, ε, Z -> f, Z',
    wrong: ['start s\nstack-start Z\naccept r\ns, ε, ε -> p, ε\np, a, ε -> p, A\np, ε, Z -> r, Z\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> r, Z\nr, c, ε -> r, ε', 'start s\nstack-start Z\naccept r f\ns, ε, ε -> p, ε\ns, ε, ε -> u, ε\np, a, ε -> p, A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> r, Z\nr, c, ε -> r, ε\nu, a, ε -> u, ε\nu, ε, ε -> v, ε\nv, b, ε -> v, B\nv, c, B -> w, ε\nw, c, B -> w, ε\nw, ε, Z -> f, Z'],
    hints: H('A union: guess at the start which half to check.', 'Branch one counts a\'s against b\'s and skips c\'s; branch two skips a\'s and counts b\'s against c\'s.', 'Do not forget the cases with no b at all (i = j = 0, or j = k = 0): allow Z on top to lead straight to acceptance.') });
  ex({ id: 'cf-x-pda-empty', chapter: 'cf-pda', title: 'Accept by empty stack', kind: 'machine', machine: 'pda', alphabet: 'ab', acceptBy: 'empty', level: 2,
    text: 'Build a PDA that accepts aⁿbⁿ with n ≥ 1 by empty stack (write accept-by empty).',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] === b[1] && b[0] >= 1; },
    solution: 'start p\nstack-start Z\naccept-by empty\np, a, Z -> p, A\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε',
    wrong: ['start p\nstack-start Z\naccept f\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> f, Z', 'start p\nstack-start Z\naccept-by empty\np, a, Z -> p, A\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\np, ε, Z -> p, ε', 'start p\nstack-start Z\naccept-by empty\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε'],
    hints: H('The stack must become empty exactly when the b\'s have matched the a\'s.', 'If Z stays at the bottom, something must remove it; simpler: let the first a replace Z.', 'p, a, Z → p, A; p, a, A → p, A A; p, b, A → q, ε; q, b, A → q, ε.') });
  ex({ id: 'cf-x-modes', chapter: 'cf-pda', title: 'Two ways to accept', kind: 'choice',
    text: 'Which statement about acceptance by final state and by empty stack is true?',
    options: ['They define the same class of languages, though one machine may accept different languages in the two ways', 'Every PDA accepts the same language in both ways', 'Empty stack is strictly stronger', 'Final state is strictly stronger'], answer: 0,
    whyNot: { 1: 'A machine that empties its stack in a non-accepting state accepts different words in the two ways.' },
    solution: 0, wrong: [1, 2, 3], why: 'Each kind of machine can be converted into the other kind for the same language.',
    hints: H('Think of one machine first, then of all machines.', 'There are conversions in both directions.', 'Same class of languages, possibly different language for one given machine.') });
  ex({ id: 'cf-x-expand', chapter: 'cf-pda', title: 'One expand step', kind: 'string',
    text: 'The top-down PDA for S → a S b | c has S on top of its stack and the next input symbol is a. What does the expand move that leads to acceptance put on the stack in place of S? Write it top first.',
    answer: ['aSb'], solution: 'a S b', wrong: ['c', 'bSa', 'S'],
    hints: H('An expand move replaces a nonterminal by the right side of one of its rules.', 'The next input is a; only one rule for S starts with a.', 'a S b, with a on top, ready to be matched.') });
  ex({ id: 'cf-x-triples', chapter: 'cf-pda', title: 'Counting triples', kind: 'number',
    text: 'The PDA-to-grammar construction is applied to a PDA with 2 states and 3 stack symbols. How many nonterminals of the form [p X q] are there?',
    answer: 12, solution: '12', wrong: ['6', '9', '18'],
    hints: H('A triple picks a state, a stack symbol and a state.', '2 choices, 3 choices, 2 choices.', '2 · 3 · 2 = 12.') });
  ex({ id: 'cf-x-pda-to-gr', chapter: 'cf-pda', title: 'A grammar for this PDA', kind: 'grammar', alphabet: 'ab', level: 2,
    ref: { machine: 'start p\nstack-start Z\naccept f\np, a, ε -> p, X\np, ε, ε -> q, ε\nq, b, X -> q, ε\nq, b, Z -> q, Z\nq, ε, Z -> f, Z' },
    text: 'The PDA with moves p, a, ε → p, X; p, ε, ε → q, ε; q, b, X → q, ε; q, b, Z → q, Z; q, ε, Z → f, Z (start p, stack Z, accept f) accepts some language over {a, b}. Work out which, and write a grammar for it.',
    solution: 'S -> a S b | B\nB -> b B | ε', wrong: ['S -> a S b | ε', 'S -> a S | S b | ε', 'S -> a S b | B\nB -> a B | ε'],
    hints: H('Each a pushes an X; each b first pops X\'s.', 'Once the X\'s are gone, more b\'s are allowed (q, b, Z → q, Z), but no more a\'s.', 'aⁿbᵐ with m ≥ n: S → a S b | B, B → b B | ε.') });
  ex({ id: 'cf-x-dpda', chapter: 'cf-pda', title: 'Which need a guess?', kind: 'choice', level: 2,
    text: 'Which of these languages are accepted by some deterministic PDA? Choose all that are.',
    options: ['w c wᴿ over {a, b}, with c only in the middle', 'aⁿbⁿ', 'w wᴿ over {a, b}', 'aⁿbⁿ ∪ aⁿb²ⁿ'], answer: [0, 1],
    solution: [0, 1], wrong: [[0, 1, 2], [0], [0, 1, 3]], why: 'The marker and the switch from a to b tell the machine when to start popping; wwᴿ and aⁿbⁿ ∪ aⁿb²ⁿ need a guess (how many b per a must be decided before any b is read).',
    hints: H('A DPDA must decide what to push before it knows what comes later.', 'In wcwᴿ the c says when to switch; in wwᴿ nothing does.', 'aⁿb²ⁿ ∪ aⁿbⁿ: after the a\'s, push one or two per a? The machine cannot know yet. Answer: the first two.') });

  // =============================================================================================================
  // Chapter 5: limits and closure
  // =============================================================================================================
  C.lesson({
    id: 'cf-l-pump', chapter: 'cf-limits', title: 'The pumping lemma on a tree', minutes: 11,
    summary: 'A long enough word has a tall parse tree, a tall tree repeats a nonterminal on one path, and the repeat can be pumped.',
    blocks: [
      "To prove a language is not context-free, we need a property every context-free language has. It comes from parse trees. Put the grammar in Chomsky normal form with N nonterminals. A binary tree whose longest path has at most N nonterminals has at most 2^(N−1) leaves. So a word longer than that has a path with more than N nonterminals, and by pigeonhole some nonterminal A appears twice on it.",
      "Cut the tree at the two A's. The upper A yields v x y, the lower one yields x, and the rest of the word is u … z. Replacing the lower A's subtree by the upper one repeats v and y; replacing the upper by the lower removes them. Every such word is still generated.",
      { def: 'Pumping lemma for context-free languages', text: 'if L is context-free, there is p ≥ 1 such that every s in L with |s| ≥ p can be written s = u v x y z with |vxy| ≤ p and |vy| ≥ 1, and u vⁱ x yⁱ z is in L for every i ≥ 0.' },
      { topic: 'cfpump-tree', input: { g: 'S → A T | A B\nT → S B\nA → a\nB → b', w: 'aaabbb' }, caption: 'Follow the longest path from the root. The repeated nonterminal is marked; then watch v and y grow together as i goes up.' },
      { predict: { q: 'Why is |vxy| ≤ p, and not just the whole word?', options: ['Because x is always short', 'Choose the repeat among the lowest N + 1 nonterminals of the path; the subtree there is short', 'It is not needed in proofs'], answer: 1, explain: 'Looking only at the bottom part of the longest path, a repeat already happens within N + 1 nonterminals, so the upper A\'s subtree has height at most N + 1 and yields at most p symbols.' } },
      { warn: 'Two pumped pieces, v and y, move together, and they may sit far from each other in the word only up to the window |vxy| ≤ p. Most mistakes in proofs come from forgetting that v and y can be anywhere within that window, including empty (but not both).' },
      { list: ['Long word → tall tree → repeated nonterminal on a path.', 'Two pieces v and y pumped together, within a window of length p.', 'The lemma is a necessary condition: it can show a language is not context-free, never that it is.'] },
      { exercise: 'cf-x-lemma' },
      { exercise: 'cf-x-lemma-only' },
    ],
  });

  C.lesson({
    id: 'cf-l-pumpgame', chapter: 'cf-limits', title: 'Winning the pumping game', minutes: 12,
    summary: 'A proof by the pumping lemma is a game you must win against every split: choose the word well and the rest is bookkeeping.',
    blocks: [
      "The lemma has a ∃ p ∀ s ∃ split ∀ i shape, which is easiest to think of as a game against an adversary who claims L is context-free.",
      { steps: ['The adversary picks p.', 'You pick a word s in L with |s| ≥ p.', 'The adversary splits s = u v x y z with |vxy| ≤ p and |vy| ≥ 1.', 'You pick i ≥ 0. You win if u vⁱ x yⁱ z is not in L.'] },
      "If you can win against **every** split, L is not context-free. The skill is all in the choice of s: pick a word so tight that every window of length p breaks something when pumped.",
      { topic: 'cfpump-game', input: { lang: 'anbncn', p: 3, s: '' }, caption: 'With s = aᵖbᵖcᵖ, the window vxy cannot touch all three blocks. Watch the adversary try every split and fail.' },
      { predict: { q: 'For aⁿbⁿcⁿ, the adversary takes v and y inside the a block and the b block. Which i wins?', options: ['i = 1', 'i = 0 or i = 2: the c block stays the same while the others change', 'No i wins against that split'], answer: 1, explain: 'Pumping changes the numbers of a\'s and b\'s but not of c\'s, so for any i ≠ 1 the three counts are no longer equal.' } },
      { topic: 'cfpump-game', input: { lang: 'ww', p: 3, s: 'abab' }, caption: 'A weak word for w w: abab is in the language and long enough, but the adversary pumps the a in both halves at once and survives. Long blocks, as in aᵖbᵖaᵖbᵖ, leave it no such split.' },
      { topic: 'cfpump-game', input: { lang: 'anbn', p: 3, s: '' }, caption: 'Against aⁿbⁿ, which is context-free, the adversary always survives: v and y are one a and one b around the middle.' },
      { tip: 'Good words pin the window down: make each block at least p long, so v x y fits inside at most two neighbouring blocks.' },
      { list: ['You choose s and i; the adversary chooses p and the split.', 'Your word must defeat every split, not just one.', 'Typical case analysis: where can a window of length p sit?'] },
      { exercise: 'cf-x-pump-abc' },
      { exercise: 'cf-x-pump-sandwich' },
      { exercise: 'cf-x-pump-ww' },
      { exercise: 'cf-x-pump-cross' },
      { exercise: 'cf-x-pump-growing' },
      { exercise: 'cf-x-pump-squares' },
    ],
  });

  C.lesson({
    id: 'cf-l-closure', chapter: 'cf-limits', title: 'Closure and non-closure', minutes: 12,
    summary: 'Union, concatenation and star glue grammars; intersection with a regular language runs a PDA and a DFA together; intersection and complement fail.',
    blocks: [
      "Closure properties build new context-free languages from old ones, and prove that some languages are not context-free without pumping anything.",
      { math: 'union:          S → S₁ | S₂\nconcatenation:  S → S₁ S₂\nstar:           S → S₁ S | ε\n(rename the nonterminals of the two grammars apart first)' },
      { topic: 'cf-closure', input: { op: 'union', g1: 'S → a S b | ε', g2: 'S → c S | c' }, caption: 'The two grammars are renamed apart (S1, S2), then joined under a new start symbol. Watch the words of both appear.' },
      { predict: { q: 'Why rename the nonterminals before gluing?', options: ['For readability only', 'So the rules of one grammar cannot be used inside the other, which would add words', 'Because the start symbols must differ'], answer: 1, explain: 'If both grammars used A for different things, a derivation could mix their rules and produce words in neither language.' } },
      { h: 'Intersection with a regular language' },
      "Two PDAs cannot be run together, because they would need two stacks. A PDA and a DFA can: the product machine tracks (PDA state, DFA state) and uses the one stack. So a context-free language intersected with a regular one is context-free.",
      { topic: 'cf-intersect', input: { m: 'start q0\nstack-start Z\naccept q2\nq0, a, Z -> q0, A Z\nq0, a, A -> q0, A A\nq0, b, A -> q1, ε\nq1, b, A -> q1, ε\nq1, ε, Z -> q2, Z', d: 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o', w: 'aabb' }, caption: 'Each product state is a pair. The PDA moves as before; the DFA moves alongside on every symbol read, and stays put on ε-moves.' },
      { h: 'What fails' },
      { topic: 'cf-nonclosure', input: { n: 9 }, caption: 'L₁ = aⁿbⁿcᵐ and L₂ = aᵐbⁿcⁿ are both context-free. Their intersection is aⁿbⁿcⁿ, which is not. Watch the words in both sets.' },
      "Complement fails too: if context-free languages were closed under complement, then, since L₁ ∩ L₂ is the complement of (complement L₁) ∪ (complement L₂), they would be closed under intersection.",
      { list: ['Closed: union, concatenation, star, reversal, intersection with a regular language.', 'Not closed: intersection, complement.', 'To show L is not context-free, intersect it with a well-chosen regular language and pump the result.'] },
      { exercise: 'cf-x-closure-which' },
      { exercise: 'cf-x-complement' },
      { exercise: 'cf-x-gr-union' },
      { exercise: 'cf-x-gr-concat' },
      { exercise: 'cf-x-gr-star' },
      { exercise: 'cf-x-gr-intersect' },
      { exercise: 'cf-x-both' },
    ],
  });

  // ---- chapter 5 exercises -------------------------------------------------------------------------------------
  ex({ id: 'cf-x-lemma', chapter: 'cf-limits', title: 'The conditions of the lemma', kind: 'choice',
    text: 'In the context-free pumping lemma, which conditions does the split s = u v x y z satisfy?',
    options: ['|vxy| ≤ p and |vy| ≥ 1', '|uv| ≤ p and |v| ≥ 1', '|vy| ≤ p and |x| ≥ 1', '|vxy| ≥ p and |vy| ≥ 1'], answer: 0,
    whyNot: { 1: 'That is the regular pumping lemma, with one pumped piece near the start.', 3: 'The window is short, not long: at most p.' },
    solution: 0, wrong: [1, 2, 3], why: 'The window v x y is short, and at least one of v and y is nonempty.',
    hints: H('Two pieces are pumped, v and y.', 'They sit in a short window, and they cannot both be empty.', '|vxy| ≤ p and |vy| ≥ 1.') });
  ex({ id: 'cf-x-lemma-only', chapter: 'cf-limits', title: 'What surviving proves', kind: 'choice', level: 2,
    text: 'For some language L you cannot find a word that beats every split; the adversary always survives. What does that prove?',
    options: ['L is context-free', 'L is not context-free', 'Nothing about whether L is context-free', 'L is regular'], answer: 2,
    whyNot: { 0: 'Some languages that are not context-free still satisfy the pumping property.' },
    solution: 2, wrong: [0, 1, 3], why: 'The lemma is a necessary condition only. Passing it proves nothing.',
    hints: H('Is the lemma an "if" or an "if and only if"?', 'Context-free ⇒ pumpable. Does pumpable ⇒ context-free?', 'Nothing: the lemma can only refute.') });
  const pumpX = (id, lang, title, text, sol, wrong, hints, level) => ex({ id, chapter: 'cf-limits', title, kind: 'pumping', lang, cf: true, level: level || 2, text, solution: sol, wrong, hints });
  pumpX('cf-x-pump-abc', 'anbncn', 'Three equal blocks', 'Show that aⁿbⁿcⁿ is not context-free: choose a word, let the adversary split it, then pump it out of the language.',
    { s: 'aaabbbccc', i: 0 }, [{ s: 'aaabbbccc', i: 1 }, { s: 'aabbc', i: 0 }, { s: 'ab', i: 0 }],
    H('Make each block at least p long.', 'A window of length p touches at most two of the three blocks.', 's = aᵖbᵖcᵖ (aaabbbccc for p = 3) and i = 0.'));
  pumpX('cf-x-pump-sandwich', 'aba-n', 'A sandwich', 'Show that aⁿbⁿaⁿ is not context-free with the pumping game.',
    { s: 'aaabbbaaa', i: 0 }, [{ s: 'aaabbbaaa', i: 1 }, { s: 'abba', i: 0 }, { s: 'aaabbaaa', i: 0 }],
    H('The same trick as for three equal blocks.', 'The window cannot reach both outer blocks of a\'s.', 's = aᵖbᵖaᵖ and i = 0.'));
  pumpX('cf-x-pump-ww', 'ww', 'A word twice', 'Show that { w w : w in {a, b}* } is not context-free with the pumping game.',
    { s: 'aaabbbaaabbb', i: 0 }, [{ s: 'abab', i: 0 }, { s: 'aaaaaa', i: 0 }, { s: 'aaabbbaaabbb', i: 1 }],
    H('Words like aaaaaa or abab are too easy for the adversary: a short repeated piece can be pumped in both halves alike.', 'Use long blocks: aᵖbᵖaᵖbᵖ.', 's = aᵖbᵖaᵖbᵖ and i = 0.'), 3);
  pumpX('cf-x-pump-cross', 'abcd-cross', 'Crossed counts', 'Show that aⁿbᵐcⁿdᵐ is not context-free with the pumping game.',
    { s: 'aaabbbcccddd', i: 0 }, [{ s: 'aaabbbcccddd', i: 1 }, { s: 'abcd', i: 0 }, { s: 'aaabcccd', i: 2 }],
    H('The a\'s must match the c\'s, the b\'s the d\'s: the pairs cross.', 'With every block p long, a window can never reach both a and c, nor both b and d.', 's = aᵖbᵖcᵖdᵖ and i = 0.'), 3);
  pumpX('cf-x-pump-growing', 'ijk-lt', 'Strictly growing', 'Show that aⁱbʲcᵏ with i < j < k is not context-free with the pumping game.',
    { s: 'aaabbbbccccc', i: 0 }, [{ s: 'aaabbbbccccc', i: 1 }, { s: 'abc', i: 2 }, { s: 'aaabbbccccc', i: 2 }],
    H('Take blocks that are as close as allowed: aᵖbᵖ⁺¹cᵖ⁺².', 'Pumping up a window with a or b catches the next block; pumping down a window with c falls behind.', 's = aᵖbᵖ⁺¹cᵖ⁺² (aaabbbbccccc for p = 3). The computer pumps one b with two c\'s; i = 0 then leaves as many b\'s as a\'s, so it wins.'), 3);
  pumpX('cf-x-pump-squares', 'squares', 'Square lengths', 'Show that { a^(n²) : n ≥ 0 } is not context-free with the pumping game.',
    { s: 'aaaaaaaaa', i: 2 }, [{ s: 'a', i: 2 }, { s: 'aaaaaaaaa', i: 1 }, { s: 'aaaaaaaa', i: 2 }],
    H('Over one letter, only the length matters.', 'Take s = a^(p²). Pumping once more adds between 1 and p symbols.', 'p² < p² + |vy| ≤ p² + p < (p + 1)²: s = a⁹ for p = 3, i = 2.'));
  ex({ id: 'cf-x-closure-which', chapter: 'cf-limits', title: 'Closed or not?', kind: 'choice', level: 2,
    text: 'Under which operations are the context-free languages closed? Choose all.',
    options: ['union', 'concatenation', 'star', 'intersection with a regular language', 'intersection', 'complement'], answer: [0, 1, 2, 3],
    solution: [0, 1, 2, 3], wrong: [[0, 1, 2, 3, 4, 5], [0, 1, 2], [0, 1, 2, 3, 4]], why: 'Grammars glue for the first three, the product with a DFA gives the fourth; aⁿbⁿcᵐ ∩ aᵐbⁿcⁿ breaks intersection, and then complement.',
    hints: H('Which constructions can be done with grammars alone?', 'Can a PDA run two stacks? Can it run a DFA alongside?', 'Union, concatenation, star and intersection with a regular language.') });
  ex({ id: 'cf-x-complement', chapter: 'cf-limits', title: 'Why not complement', kind: 'choice', level: 2,
    text: 'Which argument shows that the context-free languages are not closed under complement?',
    options: ['Closure under complement and union would give closure under intersection, which fails', 'A PDA cannot swap its accepting and rejecting states', 'Every complement of a context-free language is regular', 'The pumping lemma fails for complements'], answer: 0,
    whyNot: { 1: 'Swapping states fails for nondeterministic machines, but that alone proves nothing: some other PDA might accept the complement.', 2: 'The complement of a regular language is regular, and many context-free complements are not regular.' },
    solution: 0, wrong: [1, 2, 3], why: 'L₁ ∩ L₂ = complement(complement(L₁) ∪ complement(L₂)).',
    hints: H('Use a law from set theory.', 'De Morgan: intersection from union and complement.', 'If complement were closed, intersection would be too; it is not.') });
  ex({ id: 'cf-x-gr-union', chapter: 'cf-limits', title: 'A union of two', kind: 'grammar', alphabet: 'ab',
    text: 'Write a grammar for { aⁿbⁿ } ∪ { bⁿaⁿ } (n ≥ 0).',
    member: (w) => { const x = blocks(w, 'ab'), y = blocks(w, 'ba'); return (!!x && x[0] === x[1]) || (!!y && y[0] === y[1]); },
    solution: 'S -> X | Y\nX -> a X b | ε\nY -> b Y a | ε', wrong: ['S -> a S b | b S a | ε', 'S -> X Y\nX -> a X b | ε\nY -> b Y a | ε', 'S -> X | Y\nX -> a X b | ε\nY -> b Y a | a b'],
    hints: H('Write a grammar for each part, with different nonterminals.', 'Then let the start symbol choose one of them.', 'S → X | Y, X → a X b | ε, Y → b Y a | ε') });
  ex({ id: 'cf-x-gr-concat', chapter: 'cf-limits', title: 'One after the other', kind: 'grammar', alphabet: 'abcd',
    text: 'Write a grammar for aⁿbⁿcᵐdᵐ (n, m ≥ 0).',
    member: (w) => { const b = blocks(w, 'abcd'); return !!b && b[0] === b[1] && b[2] === b[3]; },
    solution: 'S -> X Y\nX -> a X b | ε\nY -> c Y d | ε', wrong: ['S -> a S b | c S d | ε', 'S -> a S d | B\nB -> b B c | ε', 'S -> X | Y\nX -> a X b | ε\nY -> c Y d | ε'],
    hints: H('The word is a word of aⁿbⁿ followed by a word of cᵐdᵐ.', 'Concatenation: S → S₁ S₂.', 'S → X Y, X → a X b | ε, Y → c Y d | ε') });
  ex({ id: 'cf-x-gr-star', chapter: 'cf-limits', title: 'Any number of blocks', kind: 'grammar', alphabet: 'ab', level: 2,
    text: 'Write a grammar for the star of { aⁿbⁿ : n ≥ 1 }: any number of blocks like ab, aabb, aaabbb, one after another (ε included).',
    member: (w) => { if (!/^(a+b+)*$/.test(w)) return false; return (w.match(/a+b+/g) || []).every((p) => { const k = p.indexOf('b'); return k * 2 === p.length; }); },
    solution: 'S -> X S | ε\nX -> a X b | a b', wrong: ['S -> a S b | S S | ε', 'S -> a S b | ε', 'S -> X S | ε\nX -> a X b | ε\nX -> b a'],
    hints: H('First a grammar X for one block aⁿbⁿ with n ≥ 1.', 'Then repeat X any number of times.', 'S → X S | ε, X → a X b | a b') });
  ex({ id: 'cf-x-gr-intersect', chapter: 'cf-limits', title: 'Intersect with a regular language', kind: 'grammar', alphabet: 'ab', level: 2,
    text: 'Write a grammar for aⁿbⁿ ∩ { words whose length is a multiple of 4 }.',
    member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] === b[1] && w.length % 4 === 0; },
    solution: 'S -> a a S b b | ε', wrong: ['S -> a S b | ε', 'S -> a a S b | ε', 'S -> a a S b b | a b'],
    hints: H('aⁿbⁿ has length 2n. When is 2n a multiple of 4?', 'n must be even: wrap two a\'s and two b\'s at a time.', 'S → a a S b b | ε') });
  ex({ id: 'cf-x-both', chapter: 'cf-limits', title: 'In both languages', kind: 'string',
    text: 'L₁ = { aⁿbⁿcᵐ } and L₂ = { aᵐbⁿcⁿ } (all exponents ≥ 0). Give the word of length 6 that is in both.',
    answer: ['aabbcc'], solution: 'aabbcc', wrong: ['aabbc', 'abcabc', 'aaabbb'],
    hints: H('A word in both has as many a\'s as b\'s, and as many b\'s as c\'s.', 'So all three blocks have the same length.', 'aabbcc.') });

  // =============================================================================================================
  // Tour and course
  // =============================================================================================================
  C.tour({
    id: 'cf-tour', title: 'Tour: grammars, machines and the pumping game', blurb: 'Where to type a grammar, how to watch it derive a word, run a PDA, and play against the adversary.',
    steps: [
      { route: 'topic=cfg-derive', target: '#inputs', text: 'Every topic starts with its inputs. Here you type a grammar, one rule per line, and a word to derive. The chips below are ready-made examples.' },
      { target: '#stageWrap', text: 'The stage draws the derivation: each row is one sentential form, and the nonterminal about to be rewritten is lit.' },
      { target: '#btnPlay', text: 'Play steps through the derivation; the timeline under the stage lets you jump back and forth.' },
      { target: '#say', text: 'Each step is told in words, with the rule that was used.' },
      { route: 'topic=amb-find', target: '#stageWrap', text: 'The ambiguity finder searches words in order of length until one has two parse trees, and draws both.' },
      { route: 'topic=pda-run', target: '#inputs', text: 'A PDA is written as moves "state, read, pop -> state, push". Edit machine opens a drawing editor; Text shows the moves as text.' },
      { target: '#stageWrap', text: 'The stack is drawn beside the machine: watch it grow and shrink as the input is read.' },
      { route: 'topic=cfpump-game', target: '#inputs', text: 'In the pumping game you choose the language and your word; the adversary chooses p and the split.' },
      { route: 'learn', target: '#learnView', text: 'The lessons and exercises of part 3 are under Learn: grammars, ambiguity, normal forms, PDAs and the limits of the class.' },
    ],
  });

  C.course({
    id: 'cf-course', title: 'Context-free languages, start to finish', blurb: 'From the first derivation to proving languages are not context-free: every topic of part 3 in teaching order, with lessons and exercises on the way.',
    steps: [
      { topic: 'cfg-derive', note: 'Watch which nonterminal is rewritten at each step: leftmost on one side, rightmost on the other.' },
      { topic: 'cfg-tree', note: 'The yield along the bottom becomes the word only when every leaf is a terminal.' },
      { topic: 'cfg-orders', note: 'One tree, two walks: the tree never changes, only the order the nodes light up.' },
      { lesson: 'cf-l-design', note: 'Four moves for designing grammars.' },
      { topic: 'cfg-design', note: 'Green words are right, red ones missing or extra: fix the grammar until no red is left.' },
      { exercise: 'cf-x-gr-split', note: 'Find the hidden split of the b block.' },
      { topic: 'cfg-hierarchy', note: 'Where the nonterminal sits in each rule decides the type.' },
      { topic: 'amb-find', note: 'The first word with two trees is the witness; compare the two trees it draws.' },
      { topic: 'amb-fix', note: 'Two trees, two values; the layered grammar keeps only one.' },
      { topic: 'amb-inherent', note: 'Only the words in both halves have two trees, and no grammar can avoid them.' },
      { exercise: 'cf-x-amb-sas', note: 'Find a witness yourself.' },
      { topic: 'clean-useless', note: 'A symbol that survives the first pass can fall in the second.' },
      { topic: 'clean-eps', note: 'Each nullable symbol doubles the versions of a rule.' },
      { topic: 'clean-unit', note: 'Unit pairs fill in first; then the real rules are copied along them.' },
      { topic: 'cnf', note: 'The count of rules not in CNF falls to zero, stage by stage.' },
      { exercise: 'cf-x-cnf-acb', note: 'Your first grammar in CNF.' },
      { topic: 'left-rec', note: 'The left spine of the tree becomes a right spine.' },
      { topic: 'gnf', note: 'At the end every right side starts with a terminal.' },
      { topic: 'pda-run', note: 'Watch the stack: Z on top again is the signal to accept.' },
      { topic: 'pda-tree', note: 'Every guess of the middle is a branch; most die.' },
      { topic: 'pda-accept', note: 'The new bottom marker prevents accidental acceptance.' },
      { exercise: 'cf-x-pda-eqab', note: 'Build a PDA whose stack holds the surplus.' },
      { topic: 'pda-topdown', note: 'The stack always holds the rest of the leftmost sentential form.' },
      { topic: 'pda-bottomup', note: 'Read the rightmost derivation upwards as the reductions happen.' },
      { topic: 'pda-to-cfg', note: 'Many triples are made; few are useful.' },
      { topic: 'dpda', note: 'Competing moves are the guesses a deterministic machine is not allowed.' },
      { topic: 'cfpump-tree', note: 'The repeated nonterminal on the longest path; then v and y grow together.' },
      { topic: 'cfpump-game', note: 'A good word leaves the adversary no split that survives.' },
      { exercise: 'cf-x-pump-abc', note: 'Win the game yourself.' },
      { topic: 'cf-closure', note: 'Rename apart, then glue under a new start symbol.' },
      { topic: 'cf-intersect', note: 'The DFA moves alongside the PDA, sharing its one stack.' },
      { topic: 'cf-nonclosure', note: 'Two context-free languages whose common words are aⁿbⁿcⁿ.' },
      { exercise: 'cf-x-closure-which', note: 'Sort the operations into closed and not closed.' },
    ],
  });
})();
