// Part 2, finite automata and regular languages: the chapters, the lessons, a guided tour and a course.
// The exercises are in 21-regular-ex.js. Each lesson teaches one idea: it motivates it, embeds the topic
// that animates it with an input chosen for the point being made, asks for a prediction, gives a machine
// or an expression to try, sums up, and leads to its exercises. Every machine and language here is our own.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const X = (id) => ({ exercise: id });

  // Expressions in running text are set as code, so that their stars are not read as *italic* marks.
  const EXPR = /^[abcrsh012ε∅|*+?()]+$/;
  const prose = (s) => (typeof s !== 'string' ? s : s.split(/(`[^`]*`)/).map((part, i) => (i % 2 ? part : part.replace(/[^\s`]+/g, (tok) => {
    if (!tok.includes('*') || tok[0] === '*') return tok;
    const m = /^(["“]?)(.*?)([.,:;"”]*)$/.exec(tok);
    let core = m[2], tail = m[3];
    if (core.endsWith('?') && /[*)]\?$/.test(core)) { core = core.slice(0, -1); tail = '?' + tail; }
    return EXPR.test(core) ? m[1] + '`' + core + '`' + tail : tok;
  }))).join(''));
  const TEXT_KEYS = ['p', 'tip', 'warn', 'caption', 'q', 'explain', 'note', 'why'];
  const proseBlock = (b) => {
    if (typeof b === 'string') return prose(b);
    if (!b || typeof b !== 'object') return b;
    const o = Object.assign({}, b);
    for (const k of TEXT_KEYS) if (typeof o[k] === 'string') o[k] = prose(o[k]);
    if (b.def) o.text = prose(b.text);
    for (const k of ['list', 'steps']) if (Array.isArray(b[k])) o[k] = b[k].map(prose);
    if (Array.isArray(b.table)) o.table = b.table.map((r) => r.map(prose));
    if (b.predict) o.predict = Object.assign({}, b.predict, { q: prose(b.predict.q), explain: prose(b.predict.explain), options: b.predict.options.map(prose) });
    return o;
  };
  const lesson = (l) => C.lesson(Object.assign({}, l, { summary: prose(l.summary), blocks: l.blocks.map(proseBlock) }));

  // ---- chapters -------------------------------------------------------------------------------------------
  C.chapter({ id: 'reg-automata', part: 'regular', n: 1, title: 'Finite automata', blurb: 'DFAs, NFAs and ε-moves: machines with a fixed, finite memory, and the subset construction that shows nondeterminism adds no power.' });
  C.chapter({ id: 'reg-closure', part: 'regular', n: 2, title: 'Closure properties', blurb: 'Complement, product, union, concatenation, star, reversal, homomorphisms and quotients: new regular languages from old ones, by building machines.' });
  C.chapter({ id: 'reg-regex', part: 'regular', n: 3, title: 'Regular expressions', blurb: 'A notation for regular languages, and Kleene\'s theorem both ways: expressions become automata and automata become expressions.' });
  C.chapter({ id: 'reg-limits', part: 'regular', n: 4, title: 'Beyond regular', blurb: 'Why a finite memory cannot count: the pumping lemma as a game you can win, and Myhill–Nerode, which says exactly what a machine must remember.' });
  C.chapter({ id: 'reg-minimise', part: 'regular', n: 5, title: 'Minimisation and decisions', blurb: 'The smallest DFA, found by table filling or by refining blocks, and questions about regular languages that always have an answer.' });
  C.chapter({ id: 'reg-beyond', part: 'regular', n: 6, title: 'Machines that do more', blurb: 'Machines that print, machines that walk back, and two everyday uses: searching text and cutting code into tokens.' });

  // ---- machines used in the lessons ---------------------------------------------------------------------------
  const B3 = 'start b0\naccept b0\nb0 -a-> b0\nb0 -b-> b1\nb1 -a-> b1\nb1 -b-> b2\nb2 -a-> b2\nb2 -b-> b0';
  const BA_STAR = 'start s\naccept t\ns -b-> t\nt -a-> t';
  const ABA = 'start p\naccept s\np -a,b-> p\np -a-> q\nq -b-> r\nr -a-> s\ns -a,b-> s';
  const SECOND_LAST_B = 'start p\naccept r\np -a,b-> p\np -b-> q\nq -a,b-> r';
  const ECYCLE = 'start s\naccept f\ns -ε-> x\nx -ε-> y\ny -ε-> s\nx -a-> f\ny -b-> y\nf -ε-> y';
  const ENDS_BA = 'start p\naccept r\np -a,b-> p\np -b-> q\nq -a-> r';
  const ABSTAR = 'start s\naccept f\ns -a-> s\ns -ε-> m\nm -b-> m\nm -ε-> f\nf -a-> f';
  const EVEN_B = 'start e\naccept e\ne -a-> e\ne -b-> o\no -a-> o\no -b-> e';
  const STARTS_A = 'start s\naccept y\ns -a-> y\ns -b-> n\ny -a,b-> y\nn -a,b-> n';
  const A_BA = 'start s\naccept t\ns -a-> t\nt -b-> s';
  const AA = 'start n\naccept y\nn -a-> h\nn -b-> n\nh -a-> y\nh -b-> n\ny -a,b-> y';
  const ENDS_AB5 = 'start A\naccept D\nA -a-> B\nA -b-> C\nB -a-> E\nB -b-> D\nC -a-> B\nC -b-> C\nD -a-> E\nD -b-> C\nE -a-> E\nE -b-> D';

  // =========================================================================================================
  // Chapter 1: finite automata
  // =========================================================================================================
  lesson({
    id: 'reg-dfa-read', chapter: 'reg-automata', title: 'A machine with a finite memory', minutes: 10,
    summary: 'A deterministic finite automaton reads its input once, left to right, and all it remembers is the state it is in.',
    blocks: [
      'Think of a turnstile, a traffic light or a vending machine. Each is always in one of a few situations, and each event moves it to the next one. It never keeps a full history: it keeps just enough to react correctly to what comes next. A **finite automaton** is exactly that idea, made precise and used to sort strings into "yes" and "no".',
      'Here is a small question to sort by: does a string over {a, b} contain a multiple of three b\'s? A machine does not need to count all the b\'s. It only needs the count *mod 3*: three situations, called b0, b1 and b2. An a changes nothing; a b moves one step round the cycle.',
      { topic: 'dfa-run', input: { m: B3, w: 'abbab' }, caption: 'Step through the run on abbab. Watch the single lit state: after each symbol it is everything the machine knows. The run underneath records the states one by one.' },
      { predict: { q: 'The machine has read abb. Which state is it in?', options: ['b0', 'b1', 'b2'], answer: 2, explain: 'Two b\'s so far, and the a changed nothing: b0, then b0, b1, b2.' } },
      { h: 'The definition' },
      { def: 'DFA', text: 'a deterministic finite automaton is a tuple (Q, Σ, δ, q₀, F): a finite set of states Q, an alphabet Σ, a transition function δ : Q × Σ → Q, a start state q₀ ∈ Q and a set of accepting states F ⊆ Q.' },
      'The machine starts in q₀ and, for each symbol, follows δ. It **accepts** the string if the state it is in *after the last symbol* is in F. The language of the machine, L(M), is the set of strings it accepts.',
      { math: 'δ(b0, a) = b0    δ(b0, b) = b1\nδ(b1, a) = b1    δ(b1, b) = b2\nδ(b2, a) = b2    δ(b2, b) = b0\nq₀ = b0, F = {b0}' },
      { warn: 'Passing through an accepting state on the way counts for nothing. Only the state at the very end decides.' },
      { predict: { q: 'Does this machine accept the empty string ε?', options: ['Yes', 'No', 'A DFA cannot read ε'], answer: 0, explain: 'On ε the machine makes no moves at all, so it ends where it started, in b0, which is accepting. Zero b\'s is a multiple of three.' } },
      { h: 'Run it yourself' },
      { sandbox: { kind: 'fa', text: B3, input: 'bbabba' }, caption: 'Type other strings and run them. Try ε (leave the field empty), bbb, and a long string of a\'s.' },
      { tip: 'When you design a DFA, first decide what each state *means*. Here b1 means "the number of b\'s so far leaves remainder 1". Every move then follows from the meanings.' },
      { h: 'Recap' },
      { list: ['A DFA has finitely many states and exactly one move per state and symbol.', 'It reads each symbol once, left to right, and never goes back.', 'It accepts when the state after the last symbol is accepting; ε is accepted exactly when the start state is accepting.', 'Its whole memory is the current state.'] },
      X('reg-ex-dfa-ends-a'), X('reg-ex-dfa-run-state'), X('reg-ex-dfa-count-moves'), X('reg-ex-dfa-facts'),
    ],
  });

  lesson({
    id: 'reg-dfa-design', chapter: 'reg-automata', title: 'Designing a DFA: decide what to remember', minutes: 12,
    summary: 'A DFA is designed by asking what the future needs to know about the past. Each answer becomes a state.',
    blocks: [
      'Building a DFA is not about guessing arrows. Ask one question: *after reading some of the input, what do I need to know to decide about any continuation?* List the possible answers. Each one is a state, and the moves almost write themselves.',
      'Take the strings that end in bab. What matters about the input so far is how much of bab it currently ends with: nothing, b, ba, or all of bab. Four states.',
      { topic: 'dfa-design', input: { task: 'ends', p: 'bab' }, caption: 'The machine is built state by state, each move with its reason. Watch the moves that fall back: after ba, another a leaves the input ending in ...baa, which starts nothing.' },
      { predict: { q: 'The machine is in the state "ends in bab" and reads a. Where does it go?', options: ['Back to the start (no progress)', 'To "ends in ba"', 'It stays: bab has been seen'], answer: 1, explain: 'The input now ends in ...baba, and its longest end that begins bab is ba. Matches can overlap, so progress is kept, not thrown away.' } },
      'The falling-back moves are where most mistakes happen. When the next symbol breaks the pattern, do not reset to the start by reflex. Look at what the input now ends with and keep the longest part that is still useful.',
      { h: 'Other things worth remembering' },
      { list: ['A remainder: for binary numbers divisible by 3, remember the value mod 3, since reading bit b turns value v into 2v + b.', 'A count that saturates: for "at least two b\'s", remember 0, 1 or "two or more".', 'Two facts at once: remember a pair, one part for each fact (this is the product construction of the next chapter).'] },
      { topic: 'dfa-design', input: { task: 'mod', n: 3 }, caption: 'Remainders as states: each move is a little sum, 2r + b mod 3.' },
      { h: 'Your turn' },
      'This machine is meant to accept the strings whose length is a multiple of 3, but one move is wrong. Test it, find the failing string, and fix the text.',
      { editor: { kind: 'dfa', text: 'start l0\naccept l0\nl0 -a,b-> l1\nl1 -a,b-> l2\nl2 -a-> l0\nl2 -b-> l1', tests: 'ε\naab\nbbb\n-ab\n-abbb\nababab' }, caption: 'Press Test. A red row is a string where the machine and the expected answer disagree.' },
      { h: 'Recap' },
      { list: ['Decide what the future needs to know; that is the set of states.', 'Write down the meaning of each state, then derive each move from the meanings.', 'On a broken pattern, fall back to the longest useful ending, not to the start.', 'Check the empty string and the shortest strings by hand.'] },
      X('reg-ex-dfa-no-aaa'), X('reg-ex-dfa-contains-bba'), X('reg-ex-dfa-table'), X('reg-ex-dfa-mod3-two'), X('reg-ex-dfa-runs-even'), X('reg-ex-dfa-bin5'),
    ],
  });

  lesson({
    id: 'reg-dfa-dead', chapter: 'reg-automata', title: 'Missing moves and the dead state', minutes: 7,
    summary: 'A missing move is a shorthand for a dead state: a trap that never accepts and never lets go.',
    blocks: [
      'Drawing every move of a DFA is tedious when most of them lead nowhere useful. So we allow ourselves to leave moves out, with one agreed meaning: **a missing move rejects**. The run falls into an invisible **dead state** that loops on every symbol and is not accepting.',
      'This machine accepts b followed by any number of a\'s. From s there is no a-move, and from t there is no b-move.',
      { topic: 'dfa-dead', input: { m: BA_STAR, w: 'baab' }, caption: 'The run on baab reads b, a, a happily, then meets a b with nowhere to go. Watch the dead state appear and swallow the rest.' },
      { predict: { q: 'The input is baaba instead. At which symbol is its fate sealed?', options: ['At the first a', 'At the second b', 'Only at the end'], answer: 1, explain: 'From t there is no b-move, so the second b sends the run into the dead state, and nothing after it can bring it back.' } },
      { def: 'Complete DFA', text: 'a DFA with a move from every state on every symbol. Any DFA becomes complete by adding one dead state d, sending every missing move to d, and letting d loop on every symbol.' },
      'Adding the dead state never changes the language. It matters when you build something *from* the machine: the next chapter flips accepting states to get the complement, and that only works on a complete machine.',
      { sandbox: { kind: 'fa', text: BA_STAR + '\ns -a-> d\nt -b-> d\nd -a,b-> d', input: 'baab' }, caption: 'The same machine, completed by hand. It accepts the same strings; now the dead state is drawn.' },
      { h: 'Recap' },
      { list: ['A missing move means "reject".', 'The dead state is the trap behind every missing move; it is not accepting and loops on everything.', 'Complete a DFA before complementing it or taking products.'] },
      X('reg-ex-dfa-two-b'), X('reg-ex-dfa-starts-ba'),
    ],
  });

  lesson({
    id: 'reg-nfa-intro', chapter: 'reg-automata', title: 'Nondeterminism: many fingers at once', minutes: 12,
    summary: 'An NFA may have several moves, or none, on a symbol. It accepts if some way of choosing leads to acceptance.',
    blocks: [
      'Building a DFA for "contains aba" means thinking about fall-backs. There is a lazier way to describe the same language: *wait, then at some a guess that aba starts here, and check it.* A machine that is allowed to guess is a **nondeterministic finite automaton**.',
      { def: 'NFA', text: 'a tuple (Q, Σ, δ, q₀, F) like a DFA, except that δ : Q × Σ → 𝒫(Q) gives a *set* of next states, possibly empty. It accepts w if at least one run on w ends in an accepting state.' },
      'You can picture all the guesses at once: put a finger on every state the machine could be in. Each symbol moves every finger along every matching arrow; fingers with no arrow drop off.',
      { topic: 'nfa-run', input: { m: ABA, w: 'babab' }, caption: 'The lit set grows and shrinks. p stays lit for ever (it waits), q lights up after each a (a guess), and s, once reached, stays.' },
      { predict: { q: 'After reading baba, which states are lit?', options: ['{p, q}', '{p, q, s}', '{s}', '{p, r, s}'], answer: 1, explain: 'After bab the lit set is {p, r}. The a then takes p to p and q, and r to s: {p, q, s}.' } },
      'Another way to see the same thing is the **computation tree**: one branch for every choice. The string is accepted if any leaf at the bottom is accepting.',
      { topic: 'nfa-tree', input: { m: SECOND_LAST_B, w: 'abba' }, caption: 'The machine guesses which b is second from the end. Dead branches stop; one branch survives to an accepting leaf.' },
      { warn: 'An NFA does not "accept when every run accepts". One accepting run is enough, and runs that die or end elsewhere do no harm.' },
      { h: 'Try it' },
      { editor: { kind: 'nfa', text: 'start p\naccept r\np -a,b-> p\np -b-> q\nq -a,b-> r', tests: 'ba\nbb\nabba\n-ab\n-b\n-ε' }, caption: 'Second from the end is b. Change it to "third from the end is b" (one more state) and adjust the tests.' },
      { h: 'Recap' },
      { list: ['An NFA may have zero, one or several moves on a symbol.', 'Track it with the set of lit states, or with the tree of all choices.', 'It accepts if some run ends in an accepting state.', 'NFAs are often far easier to design: wait, guess, check.'] },
      X('reg-ex-nfa-ends-bab'), X('reg-ex-nfa-aa-or-bb'), X('reg-ex-nfa-lit'), X('reg-ex-nfa-accepts'),
    ],
  });

  lesson({
    id: 'reg-nfa-eps', chapter: 'reg-automata', title: 'ε-moves and the ε-closure', minutes: 9,
    summary: 'An ε-move changes state without reading anything. The ε-closure of a state is everywhere such moves can reach.',
    blocks: [
      'Sometimes it is handy to let a machine change state *for free*, without reading a symbol: to glue two machines together, or to make a part optional. Such a move is labelled ε.',
      { def: 'ε-closure', text: 'the ε-closure of a state q, written E(q), is the set of states reachable from q by following ε-moves only, q itself included. The closure of a set is the union of the closures of its members.' },
      'With ε-moves, the lit set is always closed: after every symbol, and at the very start, light up the whole ε-closure. Cycles of ε-moves are harmless; you just stop when nothing new is added.',
      { topic: 'nfa-eclosure', input: { m: ECYCLE, q: 's' }, caption: 'The closure of s spreads along ε-arrows like water: to x, to y, and back to s, where it stops because s is already wet.' },
      { predict: { q: 'What is the ε-closure of f in the same machine?', options: ['{f}', '{f, y}', '{f, y, s, x}', '{f, x}'], answer: 2, explain: 'f has an ε-move to y; y to s; s to x; x to y, already in. So E(f) = {f, y, s, x}.' } },
      { warn: 'ε-arrows only go one way. If u -ε-> t, then t is in the closure of u, but u is not in the closure of t unless there is an ε-path back.' },
      { h: 'A union, glued with ε' },
      { sandbox: { kind: 'fa', text: 'start s\naccept a2 b2\ns -ε-> a1\ns -ε-> b1\na1 -a-> a2\na2 -a-> a2\nb1 -b-> b2\nb2 -b-> b2', input: 'bbb' }, caption: 'Some a\'s or some b\'s (at least one). The start state splits into two machines without reading anything.' },
      { h: 'Recap' },
      { list: ['An ε-move changes state without reading.', 'E(q): everything reachable by ε-moves, q included; ε-cycles are fine.', 'Take the closure at the start and after every symbol.', 'ε-moves make gluing machines easy: union, concatenation and star all use them.'] },
      X('reg-ex-nfa-eclosure'), X('reg-ex-enfa-build'), X('reg-ex-nfa-len-2-or-3'),
    ],
  });

  lesson({
    id: 'reg-subset', chapter: 'reg-automata', title: 'The subset construction', minutes: 12,
    summary: 'A set of lit states is itself a state of a DFA. Following the sets turns any NFA into an equivalent DFA.',
    blocks: [
      'Here is the key observation. When we simulated an NFA, we only ever kept one thing: *the set of lit states*. That set is determined by the input so far, and there are finitely many possible sets. So a DFA whose states are those sets can do the same job.',
      { def: 'Subset construction', text: 'from an NFA N with states Q, build a DFA whose states are subsets of Q. Its start state is E({q₀}); from a subset S on symbol c it moves to E(the union of δ(q, c) over q ∈ S); a subset is accepting when it contains an accepting state of N.' },
      'Only the subsets you can actually reach matter, so build them on demand, starting from the start subset, like a breadth-first search.',
      { topic: 'subset-build', input: { m: ENDS_BA }, caption: 'Strings that end in ba. Watch new subsets appear only when a move produces one never seen before.' },
      { predict: { q: 'This NFA has 3 states, so up to 8 subsets. How many are reachable?', options: ['2', '3', '5', '8'], answer: 1, explain: 'Only {p}, {p, q} and {p, r} ever appear, because p is always lit.' } },
      { h: 'With ε-moves' },
      'With ε-moves the recipe is the same, with a closure after every step. The start subset is the closure of the start state.',
      { topic: 'subset-enfa', input: { m: ABSTAR }, caption: 'a*b*a*: each box swells to its ε-closure before it becomes a DFA state.' },
      { tip: 'The empty set ∅ can appear: it is the subset reached when every finger has dropped off. It is the dead state of the DFA.' },
      { h: 'Recap' },
      { list: ['The lit set of an NFA is a state of a DFA.', 'Start from E({q₀}); build only reachable subsets.', 'A subset accepts when it holds an accepting state.', 'So NFAs, with or without ε, accept exactly the same languages as DFAs.'] },
      X('reg-ex-subset-table'), X('reg-ex-subset-count'), X('reg-ex-subset-dfa'), X('reg-ex-enfa-step'),
    ],
  });

  lesson({
    id: 'reg-blowup', chapter: 'reg-automata', title: 'When the DFA must be huge', minutes: 8,
    summary: 'Nondeterminism adds no power, but it can save an exponential number of states.',
    blocks: [
      'The subset construction can produce 2ⁿ states from n. Is that just a weakness of the method, or are some languages really that expensive for a DFA? Take "the k-th symbol from the end is a". An NFA guesses the position with k + 1 states.',
      { topic: 'nfa-guess', input: { k: 2, w: 'abba' }, caption: 'The NFA guesses at every a that it is the second from the end. Many guesses are alive at once; one is right.' },
      'A DFA cannot guess. It reads left to right and does not know where the end is, so it must remember the last k symbols, all of them. Two different endings of length k differ at some position, and appending the right number of symbols puts that position k-th from the end: one string is accepted, the other not. So the DFA needs a separate state for each of the 2ᵏ endings.',
      { topic: 'subset-blowup', input: { k: 3 }, caption: 'For k = 3, all 8 subsets appear. Each one is a different memory of the last three symbols.' },
      { predict: { q: 'How many states does the smallest DFA need for k = 4?', options: ['5', '8', '16', '32'], answer: 2, explain: 'One state for each of the 2⁴ = 16 possible endings of length 4.' } },
      { h: 'Recap' },
      { list: ['NFAs and DFAs accept the same languages, but not at the same size.', 'k-th from the end: k + 1 NFA states, 2ᵏ DFA states.', 'The argument, "these strings need different states", returns as Myhill–Nerode in chapter 4.'] },
      X('reg-ex-blowup-number'), X('reg-ex-nfa-fourth-last'), X('reg-ex-nfa-facts'),
    ],
  });

  // =========================================================================================================
  // Chapter 2: closure properties
  // =========================================================================================================
  lesson({
    id: 'reg-complement-product', chapter: 'reg-closure', title: 'Complement and the product construction', minutes: 12,
    summary: 'Flip the accepting states of a complete DFA for the complement; run two DFAs side by side for intersection, union and difference.',
    blocks: [
      'If L is regular, is "everything except L" regular too? With a DFA the answer is a one-liner: keep the machine, swap accepting and non-accepting states. Every string still has exactly one run, and its verdict is reversed.',
      'But there is a catch. With missing moves, some strings have no run that reaches the end: they die. Flipping does not bring them back to life.',
      { topic: 'dfa-complement', input: { m: A_BA }, caption: 'A machine for a(ba)* with missing moves. Watch what flipping alone does, and how completing it with a dead state first repairs it.' },
      { predict: { q: 'Flip this machine without completing it. Is b accepted?', options: ['Yes, b is not in a(ba)*, so the complement accepts it', 'No: b still dies at the missing move from s'], answer: 1, explain: 'Flipping changes verdicts at the end of a run, but b never reaches the end. Add the dead state first; it becomes accepting after the flip.' } },
      { h: 'Two machines at once' },
      'For intersection, run two DFAs in parallel on the same input. A state of the combined machine is a **pair** (p, q): where the first machine is, and where the second is. Each symbol moves both parts.',
      { def: 'Product construction', text: 'from complete DFAs A and B, build a DFA with states Q_A × Q_B, start (a₀, b₀), and δ((p, q), c) = (δ_A(p, c), δ_B(q, c)). Accept (p, q) when both accept (intersection), either accepts (union), or A accepts and B does not (difference).' },
      { topic: 'closure-product', input: { a: EVEN_B, b: STARTS_A, op: 'union' }, caption: 'An even number of b\'s, or starts with a. The pairs are built on demand; the operation only decides which pairs accept.' },
      { predict: { q: 'The two machines have 2 and 3 states. At most how many states can the product have?', options: ['5', '6', '8', '9'], answer: 1, explain: 'One state per pair: 2 × 3 = 6, although not every pair need be reachable.' } },
      { h: 'Recap' },
      { list: ['Complement: complete the DFA, then flip accepting states. It does not work on an NFA.', 'Product: pairs of states, both parts moving together.', 'Intersection, union and difference differ only in which pairs accept.', 'So regular languages are closed under all of these.'] },
      X('reg-ex-complement-dfa'), X('reg-ex-complement-trap'), X('reg-ex-product-dfa'), X('reg-ex-product-states'), X('reg-ex-difference-dfa'),
    ],
  });

  lesson({
    id: 'reg-glue', chapter: 'reg-closure', title: 'Union, concatenation and star by gluing', minutes: 10,
    summary: 'With ε-moves, NFAs snap together like building blocks: side by side for union, end to end for concatenation, in a loop for star.',
    blocks: [
      'The product handles union, but there is a cheaper way with NFAs. Add a new start state with ε-moves into both machines: the NFA guesses which one the string belongs to. For **concatenation**, add ε-moves from the accepting states of the first machine to the start of the second, and only the second machine\'s accepting states stay accepting.',
      { topic: 'closure-glue', input: { op: 'concat', a: 'start p\naccept q\np -b-> q\nq -a-> q', b: 'start u\naccept w\nu -a-> v\nv -b-> w' }, caption: 'ba* followed by ab. The ε-arrow is the moment the NFA guesses that the first part is over.' },
      'For the **star** of a language, any number of pieces one after another, loop back from the accepting states to the start with ε, and make sure ε itself is accepted.',
      { predict: { q: 'To accept ε, can we simply make the old start state accepting?', options: ['Yes, that is enough', 'No: if the start state has arrows coming back into it, extra strings slip in'], answer: 1, explain: 'A run can come back to the old start in the middle of a piece and stop there. The safe recipe adds a fresh start state that is accepting and has an ε-move to the old start.' } },
      { topic: 'closure-glue', input: { op: 'wrong', a: 'start s\naccept f\ns -b-> s\ns -a-> f' }, caption: 'The tempting shortcut on (b*a)*: the old start becomes accepting, and the string b, which is no piece at all, gets accepted.' },
      { sandbox: { kind: 'fa', text: 'start n\naccept n f\nn -ε-> s\ns -b-> s\ns -a-> f\nf -ε-> s', input: 'bab' }, caption: 'The safe star of b*a: a new start n that accepts ε. Run b: it is rightly rejected, since every piece ends in a.' },
      { h: 'Recap' },
      { list: ['Union: a new start with ε-moves into both machines.', 'Concatenation: ε from the first machine\'s accepting states to the second\'s start.', 'Star: ε back to the start, plus a new accepting start state for ε.', 'These three are the heart of turning expressions into automata.'] },
      X('reg-ex-union-nfa'), X('reg-ex-star-nfa'),
    ],
  });

  lesson({
    id: 'reg-more-closure', chapter: 'reg-closure', title: 'Reversal, homomorphisms and quotients', minutes: 12,
    summary: 'Three more operations that keep languages regular, each with a construction you can watch.',
    blocks: [
      '**Reversal.** To accept every string of L written backwards, run the machine backwards: turn every arrow around, make the old start accepting, and start from the old accepting states (with a new start and ε-moves if there are several).',
      { topic: 'closure-reverse', input: { m: 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x', w: 'baa' }, caption: 'A DFA for "ends with ab" reversed is an NFA for "starts with ba". The reversed machine is usually not deterministic.' },
      { predict: { q: 'Is the reversal of a DFA always a DFA?', options: ['Yes', 'No'], answer: 1, explain: 'Two arrows labelled a into the same state become two arrows labelled a out of it. Reversed machines are NFAs in general.' } },
      '**Homomorphisms.** A homomorphism h replaces each symbol by a fixed string, say h(a) = 10 and h(b) = 0. Applying h to every string of L gives h(L). On a machine: replace each arrow labelled a by a little path spelling h(a).',
      '**Inverse homomorphisms.** h⁻¹(L) is the set of strings w with h(w) in L. To accept it, read a symbol a of w by running the machine for L on the whole of h(a) in one step.',
      { topic: 'closure-hom', input: { mode: 'inv', m: 'start e\naccept e\ne -0,1-> o\no -0,1-> e', h: 'a = 001, b = 1' }, caption: 'h⁻¹ of "even length", with h(a) = 001 and h(b) = 1. One move of the new machine stands for a whole walk in the old one.' },
      '**Quotients.** The right quotient L / M is the set of strings x for which some y in M makes xy a string of L. Keep the machine for L, and make a state accepting if *some* string of M leads from it to acceptance.',
      { topic: 'closure-quotient', input: { a: 'start p\naccept p\np -a-> q\nq -b-> r\nr -b-> p', b: 'start s\naccept s\ns -b-> s' }, caption: '(abb)* divided by b*: a state becomes accepting if some run of b\'s leads from it to acceptance. The answer is (abb)*(ε|a|ab).' },
      { h: 'Recap' },
      { list: ['Reversal: turn the arrows around (the result is an NFA).', 'h(L): replace each arrow by a path for h of its symbol.', 'h⁻¹(L): one move reads a whole h(a) in the old machine.', 'L / M: the same machine with more accepting states.'] },
      X('reg-ex-reverse'), X('reg-ex-hom-regex'), X('reg-ex-invhom'), X('reg-ex-quotient'), X('reg-ex-closure-choice'),
    ],
  });

  // =========================================================================================================
  // Chapter 3: regular expressions
  // =========================================================================================================
  lesson({
    id: 'reg-regex-read', chapter: 'reg-regex', title: 'Regular expressions', minutes: 10,
    summary: 'A regular expression describes a language with three operations: union, concatenation and star.',
    blocks: [
      'Machines are good for running, but awkward for writing down in a sentence. Regular expressions are the short, typed form of the same languages, used in every text editor and programming language.',
      { def: 'Regular expression', text: 'over Σ: ∅, ε and each symbol a ∈ Σ are expressions; if r and s are expressions, so are r|s (union), rs (concatenation) and r* (star: zero or more copies). Parentheses group. We also write r+ for rr* and r? for r|ε.' },
      { math: 'L(∅) = {}    L(ε) = {ε}    L(a) = {a}\nL(r|s) = L(r) ∪ L(s)\nL(rs) = { xy : x ∈ L(r), y ∈ L(s) }\nL(r*) = {ε} ∪ L(r) ∪ L(rr) ∪ …' },
      'Precedence works like arithmetic: star binds tightest (like a power), then concatenation (like times), then union (like plus).',
      { topic: 'regex-tree', input: { r: 'a(b|ab)*|b*' }, caption: 'The expression is read as a tree. Check where the union splits and what each star applies to.' },
      { predict: { q: 'Does a(b|ab)*|b* match abab?', options: ['Yes', 'No'], answer: 0, explain: 'Take the left side: a, then the blocks b and ab. a · b · ab = abab.' } },
      { warn: '∅ and ε are different. ε matches the empty string; ∅ matches nothing at all. So aε = a, but a∅ = ∅, and ∅* = ε.' },
      { h: 'Try some expressions' },
      { editor: { kind: 'regex', text: '(a|b)*bb', tests: 'bb\nabb\nbabb\n-b\n-bba\n-ε' }, caption: 'Strings that end in bb. Change it to "contains bb" and fix the tests to match.' },
      { h: 'Recap' },
      { list: ['Three operations: |, concatenation, *; plus ∅ and ε.', 'Star first, then concatenation, then union.', 'ε is the empty string; ∅ is the empty language.', 'r+ and r? are shorthands, not new power.'] },
      X('reg-ex-rx-precedence'), X('reg-ex-rx-match'), X('reg-ex-rx-even-len'), X('reg-ex-rx-same-ends'), X('reg-ex-rx-at-most-two-b'), X('reg-ex-rx-no-ab'), X('reg-ex-rx-third-last-b'),
    ],
  });

  lesson({
    id: 'reg-regex-write', chapter: 'reg-regex', title: 'Writing expressions that are right', minutes: 10,
    summary: 'Think in blocks: cut every string of the language into pieces of a few kinds, then write one expression per piece.',
    blocks: [
      'Writing an expression from an English description is a skill of its own. The trick that works most often is to **cut the strings into blocks**. If you can say "every string is a sequence of blocks of these kinds", the expression is a star of a union.',
      'Example: the strings in which every a is immediately followed by b. Cut before each a: the blocks are ab and lone b\'s. So the language is (ab|b)*.',
      { predict: { q: 'Which expression describes the strings with no two a\'s in a row?', options: ['(ab|b)*', '(b|ab)*(a|ε)', 'b*(ab)*', '(a|b)*b'], answer: 1, explain: 'Every a except possibly the last one is followed by b. So blocks b and ab, and maybe one final a.' } },
      { h: 'Check with the machine' },
      'An expression is easy to get almost right. Test it on the shortest strings and on the edges: ε, one symbol, and strings that just fail.',
      { editor: { kind: 'regex', text: '(b|ab)*', tests: 'ε\nb\nab\nbab\na\naba\n-aa\n-baab' }, caption: 'This is meant to be "no two a\'s in a row". Two tests fail. Fix it.' },
      { topic: 'regex-glushkov', input: { r: '(b|ab)*(a|ε)' }, caption: 'A preview of the next lesson: the corrected expression becomes an automaton you can run. Each state is one occurrence of a symbol.' },
      { h: 'Recap' },
      { list: ['Cut strings into blocks; a star of a union of blocks follows.', 'Handle the edges separately: the beginning, the end, ε.', 'Test the shortest strings and the near misses.'] },
      X('reg-ex-rx-a-then-bb'), X('reg-ex-rx-odd-a'), X('reg-ex-rx-a-mod3'), X('reg-ex-rx-bin-mult4'), X('reg-ex-rx-short-both'), X('reg-ex-rx-even-even'),
    ],
  });

  lesson({
    id: 'reg-thompson', chapter: 'reg-regex', title: 'From expression to automaton', minutes: 11,
    summary: 'Every regular expression becomes an NFA, piece by piece: Thompson\'s construction glues small machines; the position automaton needs no ε at all.',
    blocks: [
      'Kleene\'s theorem says that regular expressions and finite automata describe exactly the same languages. This lesson is the first direction: **expression to automaton**.',
      'Thompson\'s construction follows the tree of the expression from the leaves up. A symbol becomes a two-state machine; union, concatenation and star are the ε-gluing of the last chapter. Each step adds at most two states, so the machine stays small.',
      { topic: 'regex-thompson', input: { r: 'b(ab)*|a' }, caption: 'Watch each node of the tree become a small machine, and the machines join with ε-moves.' },
      { predict: { q: 'Thompson\'s machine for an expression with n symbols and operators has about how many states?', options: ['about n', 'about 2n', 'about n²', 'about 2ⁿ'], answer: 1, explain: 'Each symbol or operator adds at most two states, so the size grows linearly.' } },
      { h: 'Without ε: the position automaton' },
      'Another construction numbers the symbol occurrences of the expression, its **positions**, and makes one state per position, plus a start state. There is a move from position i to position j on j\'s symbol when j can come right after i in some match.',
      { topic: 'regex-glushkov', input: { r: 'a(ba)*b' }, caption: 'Positions become states. Notice there are no ε-moves, and every arrow into a state carries that state\'s own symbol.' },
      { sandbox: { kind: 'regex', text: 'a(ba)*b', input: 'abab' }, caption: 'Run the expression directly on strings; behind the scenes it is turned into an automaton.' },
      { h: 'Recap' },
      { list: ['Expression → NFA, leaf by leaf (Thompson): linear size, with ε-moves.', 'The position automaton: one state per symbol occurrence plus a start, no ε-moves.', 'So every regular expression describes a language a finite automaton accepts.'] },
      X('reg-ex-nfa-from-regex'), X('reg-ex-glushkov-count'),
    ],
  });

  lesson({
    id: 'reg-derivatives', chapter: 'reg-regex', title: 'Derivatives: what is left to match', minutes: 9,
    summary: 'The derivative of an expression by a symbol describes what may follow that symbol. Taking derivatives again and again builds a DFA whose states are expressions.',
    blocks: [
      'Read one symbol of the input. What must the *rest* of the input look like for the whole string to match? That is again a language, and it can again be written as an expression: the **derivative**.',
      { def: 'Derivative', text: 'the derivative of a language L by a symbol c is { w : cw ∈ L }. For expressions it is computed by rules: the derivative of c by c is ε, of another symbol is ∅, of r|s is the union of the derivatives, of r* is (derivative of r) r*, and of rs it is (derivative of r) s, plus the derivative of s when r matches ε.' },
      { topic: 'regex-derivatives', input: { r: '(a|ba)*b' }, caption: 'Each new expression is a new DFA state. A state accepts when its expression matches ε. Watch the same expressions come back, which is why the process stops.' },
      { predict: { q: 'What is the derivative of (a|ba)*b by a?', options: ['(a|ba)*b itself', 'ba*b', '∅', 'ε'], answer: 0, explain: 'A leading a can only be the block a. After it, the rest must again be blocks followed by b: the same expression.' } },
      { tip: 'Derivatives are a matching algorithm too: to test w, take derivatives by its symbols one after another and check whether the final expression matches ε.' },
      { h: 'Recap' },
      { list: ['Derivative by c: what may follow c.', 'Expressions become states; matching ε means accepting.', 'Simplifying along the way keeps the number of different expressions finite.'] },
      X('reg-ex-derivative'), X('reg-ex-derivative-2'),
    ],
  });

  lesson({
    id: 'reg-eliminate', chapter: 'reg-regex', title: 'From automaton to expression', minutes: 12,
    summary: 'The other half of Kleene\'s theorem: remove states one by one, writing expressions on the arrows, until one arrow is left.',
    blocks: [
      'Now the second direction of Kleene\'s theorem: every finite automaton has an equivalent expression. The idea of **state elimination** is to allow expressions as arrow labels, and then remove the states in the middle one at a time without changing the language.',
      'When a state m is removed, every path p → m → r must be kept. If p reaches m on X, m loops on Y, and m reaches r on Z, then the new arrow from p to r gets X Y* Z, joined by | with whatever arrow p → r already had.',
      { math: 'p --X--> m --Z--> r,  loop Y on m\nbecomes\np --(old | X Y* Z)--> r' },
      { topic: 'regex-eliminate', input: { m: 'start x\naccept z\nx -a-> y\nx -b-> x\ny -b-> z\ny -a-> y\nz -a-> y\nz -b-> x', order: [] }, caption: 'A new start and a new accepting state are added first, so they are never removed. Watch every pass through the removed state turn into a starred label.' },
      { predict: { q: 'Does the order in which states are removed change the language of the final expression?', options: ['Yes', 'No, only the way it is written'], answer: 1, explain: 'Every order gives an equivalent expression, though some orders give much shorter ones.' } },
      { h: 'The same result as a table' },
      'An older method computes, for every pair of states, an expression for the paths between them that only pass through the first k states, for k = 0, 1, 2, ... It is state elimination done for all pairs at once.',
      { topic: 'regex-kleene', input: { m: 'start x\naccept x\nx -a-> y\ny -b-> x\ny -a-> y' }, caption: 'Each new column allows one more state in the middle of a path. The answer is the entry from start to the accepting state in the last column.' },
      { h: 'Recap' },
      { list: ['Removing m: for every p → m → r add X Y* Z to the arrow p → r.', 'Add a fresh start and a fresh accepting state first.', 'Different orders, equivalent answers.', 'With the previous lesson: expressions and finite automata describe the same languages, the regular languages.'] },
      X('reg-ex-elim-label'), X('reg-ex-rx-from-dfa'), X('reg-ex-rx-from-nfa'),
    ],
  });

  lesson({
    id: 'reg-regex-algebra', chapter: 'reg-regex', title: 'Simplifying and comparing expressions', minutes: 10,
    summary: 'Expressions obey algebraic laws that shorten them, and two expressions can always be checked for equality, with a counterexample when they differ.',
    blocks: [
      'Machines produce long expressions. A handful of laws shrink them without changing the language.',
      { table: [['law', 'why'], ['`r|r = r`', 'a union with itself adds nothing'], ['`εr = rε = r`', 'ε is the unit of concatenation'], ['`∅r = r∅ = ∅`', 'nothing to concatenate with'], ['`r|∅ = r`', '∅ is the unit of union'], ['`(r*)* = r*`', 'starring twice adds nothing'], ['`∅* = ε`', 'zero copies of nothing'], ['`(ε|r)r* = r*`', 'one optional copy is already in `r*`']], caption: 'Some laws used by the simplifier.' },
      { topic: 'regex-simplify', input: { r: '(ε|a)(a*)*(ε|b)b*' }, caption: 'Each step names the law it uses. Watch the expression shrink to something you can read at a glance.' },
      { predict: { q: 'Is (a|b)* equal to (a*b*)*?', options: ['Yes', 'No: (a*b*)* cannot match ba'], answer: 0, explain: 'ba is b (from one a*b* with no a\'s) followed by a (from another with no b\'s). Any string can be cut into such pieces.' } },
      { h: 'Equal or not?' },
      'Two expressions are equal exactly when their minimal DFAs are the same, so equality can always be decided. When they differ, a shortest string that tells them apart can be found by searching the product of the two machines.',
      { topic: 'regex-equiv', input: { r: 'a(ba)*b', s: '(ab)*ab' }, caption: 'Both describe (ab)+, written differently. The check builds both machines and finds no difference.' },
      { h: 'Recap' },
      { list: ['Simplify with laws: units, zeros, idempotence, (r*)* = r*.', 'Equality of expressions is decidable, through automata.', 'A shortest counterexample is the best way to see why two expressions differ.'] },
      X('reg-ex-simplify'), X('reg-ex-simplify-2'), X('reg-ex-equiv-choice'), X('reg-ex-counterexample'),
    ],
  });

  // =========================================================================================================
  // Chapter 4: beyond regular
  // =========================================================================================================
  lesson({
    id: 'reg-pump-dfa', chapter: 'reg-limits', title: 'Long strings must loop', minutes: 9,
    summary: 'A DFA with p states that reads p symbols visits some state twice. The piece between the visits can be repeated or cut out.',
    blocks: [
      'A finite automaton has a fixed number of states, say p. Feed it a string of length p or more: its run lists at least p + 1 states, so some state must appear twice (the pigeonhole principle). The symbols read between the two visits take the machine round a loop.',
      { topic: 'pump-dfa', input: { m: AA, s: 'abaab' }, caption: 'The DFA for "contains aa". Watch the first repeated state, and the three pieces it cuts: x before the loop, y around it, z after.' },
      { predict: { q: 'In this run on abaab, what is y?', options: ['a', 'ab', 'aba', 'b'], answer: 1, explain: 'The run is n, h, n, ...: the state n repeats after reading ab. So x = ε, y = ab, z = aab.' } },
      'Going round the loop twice, or not at all, ends in the same state as going round once. So xz, xyyz, xyyyz, ... are all accepted exactly when xyz is.',
      { def: 'Pumping lemma', text: 'if L is regular, there is a number p such that every string s ∈ L with |s| ≥ p can be split as s = xyz with |xy| ≤ p and |y| ≥ 1, so that xyⁱz ∈ L for every i ≥ 0.' },
      { tip: '|xy| ≤ p holds because the first repeat happens within the first p symbols. That is what lets you pin y down when you use the lemma.' },
      { h: 'Recap' },
      { list: ['p states, p symbols: some state repeats.', 'The loop y can be pumped up or down.', 'The repeat comes early: |xy| ≤ p, and y is not empty.'] },
      X('reg-ex-pump-dfa-y'),
    ],
  });

  lesson({
    id: 'reg-pump-game', chapter: 'reg-limits', title: 'The pumping game', minutes: 12,
    summary: 'To prove a language is not regular, play the pumping lemma as a game against an opponent who claims it is, and win against every move.',
    blocks: [
      'The pumping lemma is best used backwards: if a language has long strings that *cannot* be pumped, it is not regular. The quantifiers in the lemma (there is a p, for every s, there is a split, for every i) become a game with two players.',
      { steps: ['The computer, claiming the language is regular, picks p.', 'You pick a string s in the language with |s| ≥ p.', 'The computer splits s = xyz with |xy| ≤ p and |y| ≥ 1, as cleverly as it can.', 'You pick i ≥ 0. You win if xyⁱz is not in the language.'] },
      'If you have a strategy that wins against *every* p and *every* split, the language is not regular. Choosing s well is the whole art: pick it so that the first p symbols are all the same, and y has nowhere to hide.',
      { topic: 'pump-game', input: { lang: 'a-le-b', p: 3, s: 'aaabbb', i: 2 }, caption: 'aⁿbᵐ with n ≤ m. With s = aaabbb, y can only hold a\'s; pumping up gives more a\'s than b\'s.' },
      { predict: { q: 'Same language, same string, but you choose i = 0. Do you win?', options: ['Yes', 'No: removing a\'s keeps n ≤ m'], answer: 1, explain: 'Fewer a\'s than b\'s is still in the language. Here you must pump up.' } },
      { warn: 'A badly chosen string loses even for a non-regular language. With ababab for "#a = #b", the computer pumps ab and the balance never breaks. Losing one game proves nothing; you need a string that beats every split.' },
      { topic: 'pump-game', input: { lang: 'equal-ab', p: 3, s: 'ababab', i: 2 }, caption: 'A poor choice: the computer splits off ab, which keeps the balance for every i.' },
      { h: 'Recap' },
      { list: ['The game: they pick p, you pick s, they split, you pick i.', 'Pick s so that the first p symbols are all alike.', 'Decide whether to pump up (i = 2) or down (i = 0).', 'Losing a game does not show a language is regular; a machine does.'] },
      X('reg-ex-pump-a-lt-b'), X('reg-ex-pump-pal'), X('reg-ex-pump-equal'), X('reg-ex-pump-anb2n'), X('reg-ex-pump-parens'), X('reg-ex-pump-a-gt-b'), X('reg-ex-pump-ww'), X('reg-ex-pump-square'), X('reg-ex-pump-prime'), X('reg-ex-pump-meaning'),
    ],
  });

  lesson({
    id: 'reg-nerode', chapter: 'reg-limits', title: 'Myhill–Nerode: what a machine must remember', minutes: 12,
    summary: 'Two strings must lead to different states if some continuation accepts one and rejects the other. Count the classes, and you have the size of the smallest DFA.',
    blocks: [
      'The pumping lemma only says "no". A sharper tool says exactly how much memory a language needs. Take two strings x and y. If some continuation z puts xz in the language but not yz, a DFA must end in different states after x and after y: from one state, z could not lead to two verdicts.',
      { def: 'Distinguishable', text: 'x and y are distinguishable by L if some z has exactly one of xz, yz in L. Otherwise they are equivalent, x ≡ y. This is an equivalence relation; its classes are the Myhill–Nerode classes of L.' },
      { def: 'Myhill–Nerode theorem', text: 'L is regular if and only if it has finitely many classes. Then the number of classes is the number of states of its smallest complete DFA.' },
      { topic: 'nerode-game', input: { lang: 'diff3' }, caption: '#a − #b divisible by 3. Strings fall into exactly three classes, by the difference mod 3. Watch each new string join a class or be told apart by a suffix.' },
      { predict: { q: 'For "#a − #b divisible by 3", are ab and ba in the same class?', options: ['Yes', 'No'], answer: 0, explain: 'Both have difference 0, and every continuation adds the same amount to both, so no z can separate them.' } },
      'For a non-regular language the classes never stop coming. For aⁿbⁿ, the strings a, aa, aaa, ... are pairwise distinguishable: aⁱ followed by bⁱ is in, aʲ followed by bⁱ is not.',
      { topic: 'nerode-game', input: { lang: 'anbn', n: 5 }, caption: 'aⁿbⁿ: every new power of a opens a new class. No finite machine can keep up.' },
      { h: 'Recap' },
      { list: ['x and y are distinguishable when some z separates them.', 'Finitely many classes ⇔ regular; the number of classes is the size of the minimal DFA.', 'To prove non-regularity, give infinitely many pairwise distinguishable strings.'] },
      X('reg-ex-nerode-classes'), X('reg-ex-nerode-distinguish'), X('reg-ex-nerode-infinite'), X('reg-ex-which-regular'),
    ],
  });

  // =========================================================================================================
  // Chapter 5: minimisation and decisions
  // =========================================================================================================
  lesson({
    id: 'reg-min-table', chapter: 'reg-minimise', title: 'Minimising by table filling', minutes: 12,
    summary: 'Mark every pair of states some string tells apart; the pairs left unmarked can be merged.',
    blocks: [
      'Many DFAs for one language exist, and some carry redundant states that remember a difference that never matters. Myhill–Nerode says the smallest DFA has one state per class. To find the classes inside a given DFA, find which of its states are **distinguishable**.',
      { steps: ['Remove the states that cannot be reached from the start.', 'Mark every pair of one accepting and one non-accepting state: ε tells them apart.', 'Repeat: mark a pair {p, q} if some symbol c takes it to a pair that is already marked.', 'Stop when a round marks nothing. Unmarked pairs are equivalent: merge them.'] },
      { topic: 'min-table', input: { m: ENDS_AB5 }, caption: 'A 5-state DFA for "ends in ab". Watch which pairs get an x in round 0, which in round 1, and which are never marked.' },
      { predict: { q: 'A and C are both non-accepting. On a both go to B, on b both go to C. Will they ever be marked?', options: ['Yes', 'No, they merge'], answer: 1, explain: 'Every symbol takes them to the same state, so no string can tell them apart.' } },
      { tip: 'The marking runs backwards from the end: a pair marked in round k is told apart by a string of length k.' },
      { h: 'Recap' },
      { list: ['Drop unreachable states first.', 'Round 0: accepting versus non-accepting.', 'Then mark pairs that move to marked pairs, until nothing changes.', 'Merge the unmarked pairs; the result is the minimal DFA.'] },
      X('reg-ex-min-table'), X('reg-ex-min-number'), X('reg-ex-min-dfa'),
    ],
  });

  lesson({
    id: 'reg-min-refine', chapter: 'reg-minimise', title: 'Refining blocks, reversing twice, and uniqueness', minutes: 12,
    summary: 'Two more ways to minimise: split blocks of states until they are stable, or reverse and determinise twice. All of them find the same machine.',
    blocks: [
      'Table filling looks at pairs. **Partition refinement** looks at blocks: start with two blocks, accepting and non-accepting, and split a block whenever its states disagree about which block a symbol sends them to. When no block splits, each block is one state of the minimal DFA.',
      { topic: 'min-partition', input: { m: ENDS_AB5, how: 'moore' }, caption: 'Round by round, blocks split. When a round splits nothing, the blocks are the classes.' },
      { predict: { q: 'How many blocks will be left at the end for this machine?', options: ['2', '3', '4', '5'], answer: 1, explain: 'One for "no progress" (A, C), one for "ends in a" (B, E), one for "ends in ab" (D).' } },
      'A cleverer bookkeeping, splitting by one block at a time and always choosing the smaller half, gives a fast algorithm used in practice.',
      { topic: 'min-partition', input: { m: ENDS_AB5, how: 'hopcroft' }, caption: 'The same machine, with splitters chosen one by one.' },
      { h: 'A surprising trick' },
      'Reverse the machine, determinise it with the subset construction, then do both again. The result is always the minimal DFA. It can be slow, but it works even when you start from an NFA.',
      { topic: 'min-brzozowski', input: { m: ENDS_AB5 }, caption: 'Reverse, determinise, reverse, determinise. Four steps, and the redundant states are gone.' },
      { h: 'Only one answer' },
      'Every method lands on the same machine, and so would any student\'s: the minimal complete DFA of a language is **unique up to renaming its states**, because its states are the Myhill–Nerode classes.',
      { topic: 'min-unique', input: { a: 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x', b: ENDS_AB5 }, caption: 'Two machines for "ends in ab". After minimising, one is the other with new names.' },
      { h: 'Recap' },
      { list: ['Partition refinement: split blocks until stable.', 'Double reversal: reverse and determinise, twice.', 'The minimal DFA is unique up to the names of the states.'] },
      X('reg-ex-min-unique'),
    ],
  });

  lesson({
    id: 'reg-decide', chapter: 'reg-minimise', title: 'Questions with guaranteed answers', minutes: 12,
    summary: 'Is the language empty? Finite? Are two machines equivalent? For finite automata, every one of these questions has an algorithm.',
    blocks: [
      'Later parts of this course meet questions about machines that no algorithm can answer. For finite automata, the important questions are all **decidable**, and the algorithms are simple searches on the diagram.',
      { h: 'Emptiness' },
      'L(M) is non-empty exactly when some accepting state is reachable from the start. A breadth-first search answers it, and the path it finds spells a shortest accepted string.',
      { topic: 'decide-empty', input: { m: 'start s\naccept f\ns -a-> t\nt -a-> s\nt -b-> t\nu -b-> f\nf -a-> u' }, caption: 'The search spreads from s. f exists, but no path leads to it: the language is empty.' },
      { h: 'Finiteness' },
      'L(M) is infinite exactly when there is a loop on some path from the start to an accepting state. Loops in dead or unreachable parts do not count.',
      { topic: 'decide-finite', input: { m: 'start s\naccept f\ns -a-> f\ns -b-> d\nd -a,b-> d' }, caption: 'The only loop is on the dead state, so it cannot help any accepted string grow: finite.' },
      { predict: { q: 'A DFA has a loop that is reachable from the start, but no accepting state is reachable from the loop. Is its language infinite?', options: ['Yes, because of the loop', 'No: the loop never helps reach acceptance'], answer: 1, explain: 'Only loops that are both reachable and co-reachable (can still reach an accepting state) make the language infinite.' } },
      { h: 'Equivalence and inclusion' },
      'Two DFAs accept the same language exactly when the product machine for their symmetric difference (accept pairs where exactly one accepts) has an empty language. If it is not empty, the search returns a shortest string on which they disagree.',
      { topic: 'decide-equiv', input: { a: 'start x\naccept y\nx -a-> x\nx -b-> y\ny -a-> x\ny -b-> y', b: 'start u\naccept v\nu -a-> u\nu -b-> v\nv -a,b-> v' }, caption: '"Ends in b" against "contains b": pairs of states are explored until one pair disagrees, and the path to it, ba, is the counterexample.' },
      { h: 'Counting' },
      { topic: 'decide-count', input: { m: 'start z\naccept z one two\nz -a-> one\nz -b-> z\none -a-> two\none -b-> z\ntwo -b-> z', n: 6 }, caption: 'How many strings of each length avoid aaa? Each column adds up the ways to arrive in each state.' },
      { h: 'Recap' },
      { list: ['Empty: is an accepting state reachable?', 'Infinite: is there a loop on a path from the start to acceptance?', 'Equivalent: is the symmetric difference empty? If not, you get a counterexample.', 'Included: is L(A) minus L(B) empty?'] },
      X('reg-ex-decide-empty'), X('reg-ex-decide-finite'), X('reg-ex-decide-count'), X('reg-ex-decide-counterex'), X('reg-ex-decide-inclusion'),
    ],
  });

  // =========================================================================================================
  // Chapter 6: machines that do more
  // =========================================================================================================
  lesson({
    id: 'reg-transducers', chapter: 'reg-beyond', title: 'Machines that print: Moore and Mealy', minutes: 10,
    summary: 'Give a finite automaton an output and it becomes a transducer. A Moore machine prints in its states; a Mealy machine prints on its moves.',
    blocks: [
      'So far our machines only answer yes or no. Many real devices respond as they go: a vending machine drops a sweet, a controller switches a light. Attach an output to the automaton and it **translates** an input string into an output string.',
      { def: 'Moore machine', text: 'a DFA without accepting states, plus an output alphabet Δ and a function λ : Q → Δ. It prints λ of every state it is in, the start state included, so the output is one symbol longer than the input.' },
      { def: 'Mealy machine', text: 'the same, but λ : Q × Σ → Δ prints on every move, so the output is exactly as long as the input.' },
      { topic: 'moore-mealy', input: { how: 'moore', w: '2112' }, caption: 'A sweet costs 3; coins are 1 and 2. The Moore machine prints with its states: watch it print even before the first coin.' },
      { predict: { q: 'The same coins go into the Mealy machine. How many symbols does it print?', options: ['3', '4', '5'], answer: 1, explain: 'One output per move, and four coins make four moves.' } },
      { topic: 'moore-mealy', input: { how: 'mealy', w: '2112' }, caption: 'The Mealy machine prints on its arrows, and needs fewer states.' },
      'The two kinds can imitate each other. Moore to Mealy is easy: print, on each arrow, the output of the state it enters. Mealy to Moore splits each state by the output it has just printed.',
      { topic: 'moore-mealy', input: { how: 'toMoore', w: '21' }, caption: 'Splitting the Mealy machine\'s states by what they just printed.' },
      { h: 'Recap' },
      { list: ['Moore: output per state, |output| = |input| + 1.', 'Mealy: output per move, |output| = |input|.', 'Each kind can be converted to the other (ignoring the Moore machine\'s first output).'] },
      X('reg-ex-moore-output'), X('reg-ex-mealy-output'), X('reg-ex-mealy-build'), X('reg-ex-moore-length'),
    ],
  });

  lesson({
    id: 'reg-twoway', chapter: 'reg-beyond', title: 'Two-way automata', minutes: 8,
    summary: 'Letting the head move back over the input looks like more power. It is not: two-way DFAs still accept only regular languages.',
    blocks: [
      'What if a DFA could re-read its input, moving its head left as well as right between two end markers ⊢ and ⊣? It still cannot write anything down, so its only memory is its state and where its head is.',
      { topic: 'twoway', input: { ex: 'third', w: 'abbab' }, caption: 'To check the third symbol from the end, this machine runs to the right end, steps back three places and looks. Follow the head through time.' },
      { predict: { q: 'Can a two-way DFA accept aⁿbⁿ by walking back and forth to compare the blocks?', options: ['Yes', 'No'], answer: 1, explain: 'To compare the blocks it would have to remember a count, and its state is its only memory. Two-way DFAs accept exactly the regular languages.' } },
      'A two-way machine can also loop: walking back and forth for ever without deciding. A run is caught looping when a configuration (state and head position) comes back, since from then on it repeats exactly.',
      { topic: 'twoway', input: { ex: 'bounce', w: 'aa' }, caption: 'A configuration repeats, so the machine will never halt on this input.' },
      { h: 'Recap' },
      { list: ['Two-way DFAs read their input as often as they like but never write.', 'They accept exactly the regular languages, though they can be much smaller.', 'They can loop; a repeated configuration proves it.'] },
      X('reg-ex-twoway-power'),
    ],
  });

  lesson({
    id: 'reg-kmp', chapter: 'reg-beyond', title: 'Searching text with a DFA', minutes: 10,
    summary: 'A DFA for "ends with the pattern" finds every occurrence of the pattern in a text, reading each character once and never looking back.',
    blocks: [
      'Finding a word in a long text is one of the oldest uses of automata. The naive search starts over at every position and re-reads characters. A DFA does better: its state is the longest beginning of the pattern that the text read so far ends with, and every time it reaches the last state, a match ends there.',
      'The only work is in the fall-back moves, and they come from the **border** of each prefix of the pattern: its longest proper beginning that is also an ending.',
      { topic: 'kmp', input: { p: 'abcab', t: 'abcabcabca' }, caption: 'The pattern abcab in the text abcabcabca. After the first match the DFA does not start again from nothing: the ending ab is already the start of the next match.' },
      { predict: { q: 'How many times does abcab occur in abcabcabca, overlaps counted?', options: ['1', '2', '3'], answer: 1, explain: 'At positions 1 and 4. The second occurrence begins with the ab that ends the first.' } },
      { editor: { kind: 'dfa', text: 'start s0\naccept s3\ns0 -a-> s1\ns0 -b-> s0\ns1 -a-> s1\ns1 -b-> s2\ns2 -a-> s3\ns2 -b-> s0\ns3 -a-> s1\ns3 -b-> s2', tests: 'aba\nababa\nbbaba\n-ab\n-abab\n-abba' }, caption: 'A search DFA for aba: it accepts exactly when the text read so far ends with aba. Find the move from s3 that uses the border a.' },
      { h: 'Recap' },
      { list: ['States: how much of the pattern the text currently ends with (m + 1 of them).', 'Fall-back moves follow the borders of the prefixes.', 'The search reads each character of the text once.'] },
      X('reg-ex-kmp-failure'), X('reg-ex-kmp-dfa'), X('reg-ex-kmp-count'),
    ],
  });

  lesson({
    id: 'reg-lexer', chapter: 'reg-beyond', title: 'Lexers: many expressions at once', minutes: 10,
    summary: 'A compiler\'s first stage cuts source code into tokens. Each kind of token is a regular expression; together they become one DFA.',
    blocks: [
      'Before a compiler can understand if a<=12, it must see the pieces: the keyword if, the name a, the operator <=, the number 12. That is the job of the **lexer**, and it is pure regular-language machinery.',
      { steps: ['Write one regular expression per kind of token: keywords, names, numbers, operators, spaces.', 'Turn them all into one NFA (a union) that remembers which rule each accepting state belongs to, then into a DFA.', 'From the current position, run the DFA as far as it can go, remembering the last accepting position.', 'Cut the token there (the longest match). If two rules match the same longest piece, the rule listed first wins.'] },
      { topic: 'lexer', input: { line: 'if iffy<=7', order: 'if' }, caption: 'Watch the scanner run past if into iffy: the longest match makes iffy a name, not the keyword if followed by fy.' },
      { predict: { q: 'With the rule ID listed before IF, what does the lexer make of the word if?', options: ['IF', 'ID', 'An error'], answer: 1, explain: 'Both rules match if with the same length, so the tie goes to the rule listed first. Keywords must come before identifiers.' } },
      { topic: 'lexer', input: { line: 'if b', order: 'id' }, caption: 'Rules in the wrong order: the keyword is swallowed by the identifier rule.' },
      { h: 'Recap' },
      { list: ['One regular expression per kind of token.', 'One DFA for all of them, with each accepting state tagged by its rule.', 'Longest match first; ties go to the earlier rule.', 'Backing up to the last accepting position handles prefixes like < before <=.'] },
      X('reg-ex-lexer-longest'), X('reg-ex-lexer-tie'), X('reg-ex-lexer-id'), X('reg-ex-lexer-num'),
    ],
  });

  // ---- a guided tour -----------------------------------------------------------------------------------------
  const proseSteps = (o) => Object.assign(o, { steps: o.steps.map((st) => Object.assign({}, st, st.text ? { text: prose(st.text) } : {}, st.note ? { note: prose(st.note) } : {})) });
  C.tour(proseSteps({
    id: 'reg-tour', title: 'Tour: finite automata', blurb: 'From a first DFA run to a pumping game, in eight steps.',
    steps: [
      { route: 'part=regular', target: '#main', text: 'Part 2 of the catalogue: finite automata and regular languages. Every card is a topic that animates one idea.' },
      { route: 'topic=dfa-run', target: '#stageWrap', text: 'A DFA reads a string. The lit state is the machine\'s whole memory; the run grows under the input.' },
      { target: '#btnPlay', text: 'Play steps through the run; the arrow keys go one step at a time, forwards or back.' },
      { target: '#inputs', text: 'Change the machine or the string here, or pick a preset. Try the empty string.' },
      { route: 'topic=subset-build', target: '#stageWrap', text: 'The subset construction: each set of NFA states becomes one DFA state, built only when it is reached.' },
      { route: 'topic=pump-game', target: '#inputs', text: 'The pumping game. Choose a language, a string and an i, and try to beat the computer\'s split.' },
      { route: 'sandbox', target: '#sbEditor', text: 'The sandbox: draw or type your own automaton, run it, test it on a list of strings, and convert it.' },
      { route: 'learn', target: '[data-chapter="reg-automata"]', text: 'Lessons and exercises for this part start here. Exercises are checked at once, with a counterexample when an answer is wrong.' },
    ],
  }));

  // ---- a course ---------------------------------------------------------------------------------------------
  C.course(proseSteps({
    id: 'reg-course', title: 'Regular languages, start to finish', blurb: 'An ordered path through every topic of part 2, from a first DFA run to lexers, with a word on what to watch at each step.',
    steps: [
      { topic: 'dfa-run', note: 'One lit state at a time: it is all the machine knows.' },
      { topic: 'dfa-design', note: 'Each state is an answer to "what must I remember?".' },
      { topic: 'dfa-dead', note: 'A missing move falls into a trap that never lets go.' },
      { exercise: 'reg-ex-dfa-contains-bba', note: 'Build one yourself; mind the fall-back on a third b.' },
      { topic: 'nfa-run', note: 'Many fingers at once: the lit set grows and shrinks.' },
      { topic: 'nfa-tree', note: 'The same run as a tree of choices; one accepting leaf is enough.' },
      { topic: 'nfa-eclosure', note: 'ε-moves spread for free, and cycles stop on their own.' },
      { topic: 'nfa-guess', note: 'Guessing where the end is: k + 1 states.' },
      { topic: 'subset-build', note: 'A set of lit states is one DFA state.' },
      { topic: 'subset-enfa', note: 'Take the ε-closure after every step.' },
      { topic: 'subset-blowup', note: 'Every subset appears: the DFA really needs 2ᵏ states.' },
      { topic: 'dfa-complement', note: 'Flip the accepting states, but only after completing the machine.' },
      { topic: 'closure-product', note: 'Pairs of states; the operation picks which pairs accept.' },
      { topic: 'closure-glue', note: 'ε-moves snap machines together; see why star needs a new start.' },
      { topic: 'closure-reverse', note: 'Arrows turned around: a DFA becomes an NFA.' },
      { topic: 'closure-hom', note: 'One move of the new machine is a whole walk in the old one.' },
      { topic: 'closure-quotient', note: 'Same machine, more accepting states.' },
      { topic: 'regex-tree', note: 'Star first, then concatenation, then union.' },
      { topic: 'regex-thompson', note: 'Tree nodes become little machines, glued with ε.' },
      { topic: 'regex-glushkov', note: 'One state per symbol occurrence, no ε at all.' },
      { topic: 'regex-derivatives', note: 'Expressions as states; matching ε means accepting.' },
      { topic: 'regex-eliminate', note: 'Each removed state leaves X Y* Z on the arrows around it.' },
      { topic: 'regex-kleene', note: 'The same idea for all pairs at once, one more middle state per column.' },
      { topic: 'regex-simplify', note: 'Each step names the law it uses.' },
      { topic: 'regex-equiv', note: 'Equality is decided by machines, with a shortest counterexample.' },
      { topic: 'pump-dfa', note: 'p states and p symbols: the first repeat cuts x, y, z.' },
      { topic: 'pump-game', note: 'Choose s so that y has nowhere to hide.' },
      { exercise: 'reg-ex-pump-pal', note: 'Win a game on your own.' },
      { topic: 'nerode-game', note: 'Strings that some suffix tells apart need different states.' },
      { topic: 'min-table', note: 'Marks spread backwards from accepting versus non-accepting.' },
      { topic: 'min-partition', note: 'Blocks split until they are stable.' },
      { topic: 'min-brzozowski', note: 'Reverse and determinise, twice.' },
      { topic: 'min-unique', note: 'Two minimal machines, one up to renaming.' },
      { topic: 'decide-empty', note: 'Emptiness is reachability.' },
      { topic: 'decide-finite', note: 'Only loops between the start and acceptance count.' },
      { topic: 'decide-equiv', note: 'Pairs that disagree are the counterexamples.' },
      { topic: 'decide-count', note: 'Counting strings by length, column by column.' },
      { topic: 'moore-mealy', note: 'Output per state against output per move.' },
      { topic: 'twoway', note: 'Walking back adds no power; a repeated configuration means a loop.' },
      { topic: 'kmp', note: 'After a match, the border keeps the head start.' },
      { topic: 'lexer', note: 'Longest match first, ties to the earlier rule.' },
    ],
  }));
})();
