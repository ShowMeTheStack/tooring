// Part 6, decidability and computability: chapters, lessons, exercises, a tour and a course. The lessons
// tell the story from problems a machine can settle (questions about DFAs and grammars), through the
// halting problem acted out, recognisers and their complements, reductions and Rice's theorem, to the
// puzzles that hide a machine (dominoes, grammars, tiles) and the far edge (busy beavers, description
// length, unprovable truths). Exercises classify problems, point reductions the right way, apply Rice's
// recipe, solve domino puzzles and tilings (checked by the engines), and find the flaw in a fake proof.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const H = (a, b, c) => [a, b, c];
  const ex = (x) => C.exercise(Object.assign({ level: 1 }, x));

  // ---- chapters --------------------------------------------------------------------------------------------
  const P = 'computability';
  C.chapter({ id: 'comp-decidable', part: P, n: 1, title: 'Questions a machine can settle', blurb: 'Questions about machines turned into languages, and deciders that always answer: membership, emptiness and equivalence for DFAs, membership and emptiness for grammars.' });
  C.chapter({ id: 'comp-halting', part: P, n: 2, title: 'The halting problem', blurb: 'A table of programs run on programs, a machine built to contradict every row, and why every clever halting checker gets caught.' });
  C.chapter({ id: 'comp-recognisable', part: P, n: 3, title: 'Recognisable and co-recognisable', blurb: 'Machines that say yes when the answer is yes and may wait for ever otherwise; dovetailing; why yes-and-no recognisers together make a decider.' });
  C.chapter({ id: 'comp-reductions', part: P, n: 4, title: 'Reductions and Rice’s theorem', blurb: 'Programs that write programs: mapping reductions and which way they point, oracles, and a two-question recipe for a whole family of undecidable problems.' });
  C.chapter({ id: 'comp-puzzles', part: P, n: 5, title: 'Dominoes, grammars and tiles', blurb: 'Innocent puzzles with a machine hidden inside: the domino matching puzzle, questions about grammars, and tilings that compute.' });
  C.chapter({ id: 'comp-beyond', part: P, n: 6, title: 'Beyond the edge', blurb: 'Functions that outgrow every program, strings with no short description, and true statements with no proof.' });

  // ---- shared pieces ---------------------------------------------------------------------------------------
  // the four classes a problem can fall into
  const CLASSES = ['Decidable', 'Recognisable, but not co-recognisable', 'Co-recognisable, but not recognisable', 'Neither recognisable nor co-recognisable'];
  const CLASS_WHY = [
    'Decidable means one machine halts on every input with the right answer. Is there really a bound on how long the search can take?',
    'Recognisable means a machine says yes on every yes-instance (it may wait for ever on the others). Can the yes-instances be confirmed by a finite piece of evidence?',
    'Co-recognisable means the no-instances can be confirmed by finite evidence. Can they here?',
    'Neither means no finite evidence confirms a yes, and none confirms a no. Is that so here?',
  ];
  const classify = (x) => ex(Object.assign({ kind: 'choice', options: CLASSES, whyNot: CLASS_WHY, solution: x.answer, wrong: [0, 1, 2, 3].filter((i) => i !== x.answer).slice(0, 2) }, x));

  // the three verdicts of Rice's recipe
  const RICE = ['Yes: it is about the language alone and non-trivial, so Rice’s theorem makes it undecidable', 'No: it is not a property of the language alone (two machines with the same language can disagree)', 'No: the property is trivial (every recogniser’s language has it, or none does)'];
  const RICE_WHY = ['Check the first question: would two machines with exactly the same language always get the same answer?', 'Is there a pair of machines with the same language that the property tells apart? If not, it is about the language alone.', 'Can you name one recognisable language that has the property and one that does not? Then it is not trivial.'];
  const rice = (x) => ex(Object.assign({ kind: 'choice', options: RICE, whyNot: RICE_WHY, solution: x.answer, wrong: [0, 1, 2].filter((i) => i !== x.answer) }, x));

  // A string exercise whose checker says why an answer fails: accept returns true or {ok: false, why}.
  const withReason = (x, test) => ex(Object.assign({ kind: 'string' }, x, { accept: (a) => { const r = test(a); return r === true ? true : { ok: false, why: r }; } }));

  // ---- the domino puzzle, checked by T.pcp ----
  const dominoes = (list) => list.map((d) => { const [top, bottom] = d.split('/'); return { top, bottom }; });
  const domTable = (list) => ({ table: [['domino'].concat(list.map((_, i) => String(i + 1))), ['top'].concat(list.map((d) => '`' + d.split('/')[0] + '`')), ['bottom'].concat(list.map((d) => '`' + d.split('/')[1] + '`'))], caption: 'Use any domino as often as you like, in any order.' });
  /** Read "1 3 2", "1,3,2" or "132" (fewer than ten dominoes) into 0-based indexes, or a reason */
  const readSeq = (a, n) => {
    const s = String(a).trim();
    const parts = /[\s,]/.test(s) ? s.split(/[\s,]+/).filter(Boolean) : [...s];
    if (!parts.length) return 'Write the domino numbers in order, like 1 3 2.';
    const bad = parts.find((p) => !/^\d+$/.test(p) || +p < 1 || +p > n);
    if (bad !== undefined) return '"' + bad + '" is not a domino number from 1 to ' + n + '.';
    return parts.map((p) => +p - 1);
  };
  const pcpEx = (x) => {
    const D = dominoes(x.dominoes);
    return withReason(Object.assign({ placeholder: 'domino numbers, like 1 3 2', text: [x.intro, domTable(x.dominoes), 'Type your match as the domino numbers in order, separated by spaces, like `1 3 2`.'] }, x), (a) => {
      const seq = readSeq(a, D.length);
      if (typeof seq === 'string') return seq;
      const v = T.pcp.verify(D, seq);
      if (v.ok) return true;
      return 'The top row reads ' + v.top + ' and the bottom row reads ' + v.bottom + '. ' + (v.top.startsWith(v.bottom) ? 'The top is ahead: keep going.' : v.bottom.startsWith(v.top) ? 'The bottom is ahead: keep going.' : 'They clash at symbol ' + (1 + [...v.top].findIndex((c, i) => c !== v.bottom[i])) + ', so no continuation can repair this start.');
    });
  };

  // ---- tilings, checked by T.wang ----
  const COL = ['amber', 'blue', 'green'];
  const FILL = ['#e2a227', '#3d7fd6', '#3aa66b'];
  const tilesOf = (list) => list.map((s) => ({ n: +s[0], e: +s[1], s: +s[2], w: +s[3] }));
  /** Wang tiles drawn as squares cut into four triangles, numbered */
  const tileSvg = (list) => {
    const S = 64, G = 22, W = list.length * (S + G) - G + 8;
    // each triangle shrunk a little towards its own centre, so the four never touch and the edges read apart
    const tri = (x, c, pts) => { const cx = pts.reduce((a, p) => a + p[0], 0) / 3, cy = pts.reduce((a, p) => a + p[1], 0) / 3; return '<polygon points="' + pts.map(([px, py]) => (x + cx + (px - cx) * 0.86).toFixed(1) + ',' + (cy + (py - cy) * 0.86).toFixed(1)).join(' ') + '" fill="' + FILL[c] + '" stroke="currentColor" stroke-width="1"/>'; };
    let out = '<svg viewBox="0 0 ' + W + ' ' + (S + 30) + '" width="' + W + '" style="max-width:100%;color:var(--fg,#444)" role="img" aria-label="the tiles">';
    list.forEach((t, i) => {
      const x = 4 + i * (S + G), c = [...t].map(Number);
      out += tri(x, c[0], [[0, 4], [S, 4], [S / 2, 4 + S / 2]]) + tri(x, c[1], [[S, 4], [S, 4 + S], [S / 2, 4 + S / 2]]) + tri(x, c[2], [[0, 4 + S], [S, 4 + S], [S / 2, 4 + S / 2]]) + tri(x, c[3], [[0, 4], [0, 4 + S], [S / 2, 4 + S / 2]]);
      out += '<text x="' + (x + S / 2) + '" y="' + (S + 24) + '" text-anchor="middle" font-size="14" fill="currentColor">' + (i + 1) + '</text>';
    });
    return out + '</svg>';
  };
  const tileTable = (list) => ({ table: [['tile', 'north', 'east', 'south', 'west']].concat(list.map((t, i) => [String(i + 1)].concat([...t].map((c) => COL[+c])))), caption: 'The same tiles in words. Tiles may not be turned.' });
  /** Read "1 2 / 3 4" or "12/34" (rows from the top, cells from the left) into a board, or a reason */
  const readBoard = (a, n, W, Hh) => {
    const rows = String(a).trim().split(/\s*[/;|]\s*/).filter(Boolean);
    if (rows.length !== Hh) return 'The board has ' + Hh + ' rows; separate them with /, like 1 2 / 3 4.';
    const board = [];
    for (const r of rows) {
      const cells = /[\s,]/.test(r) ? r.split(/[\s,]+/).filter(Boolean) : [...r];
      if (cells.length !== W) return 'Every row needs ' + W + ' tiles; "' + r + '" has ' + cells.length + '.';
      const bad = cells.find((c) => !/^\d+$/.test(c) || +c < 1 || +c > n);
      if (bad !== undefined) return '"' + bad + '" is not a tile number from 1 to ' + n + '.';
      board.push(cells.map((c) => +c - 1));
    }
    return board;
  };
  const tileEx = (x) => {
    const tiles = tilesOf(x.tiles);
    return withReason(Object.assign({ placeholder: 'rows from the top, like 1 2 / 3 4', text: [x.intro, { svg: tileSvg(x.tiles), caption: 'Each tile has a colour on each edge.' }, tileTable(x.tiles), 'Type the board row by row from the top, rows separated by /, each row from left to right: for example `1 2 / 3 4`.'] }, x), (a) => {
      const b = readBoard(a, tiles.length, x.w, x.h);
      if (typeof b === 'string') return b;
      for (let y = 0; y < x.h; y++) for (let i = 0; i < x.w; i++) {
        const c = tiles[b[y][i]];
        if (i > 0 && tiles[b[y][i - 1]].e !== c.w) return 'In row ' + (y + 1) + ', tiles ' + (b[y][i - 1] + 1) + ' and ' + (b[y][i] + 1) + ' meet with ' + COL[tiles[b[y][i - 1]].e] + ' against ' + COL[c.w] + '.';
        if (y > 0 && tiles[b[y - 1][i]].s !== c.n) return 'In column ' + (i + 1) + ', tile ' + (b[y - 1][i] + 1) + ' has ' + COL[tiles[b[y - 1][i]].s] + ' at the bottom but tile ' + (b[y][i] + 1) + ' below it has ' + COL[c.n] + ' on top.';
      }
      return T.wang.check(tiles, b) ? true : 'Some edges do not agree.';
    });
  };

  // a few machines shared by lessons and exercises
  const EVEN_A = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const ISLAND = 'start p\naccept t\np -a-> q\np -b-> p\nq -a-> p\nq -b-> r\nr -a,b-> r\ns -a-> t\nt -b-> s';
  const SEEK_A = 'start: s\naccept: yes\ns, b -> s, b, R\ns, a -> yes, a, S\ns, _ -> s, _, R';
  const RUNAWAY = 'start: r\nr, _ -> r, 1, R';
  const SYMDIFF = 'start EN\naccept EN OB\nEN -a-> ON\nEN -b-> EB\nEB -a-> ON\nEB -b-> EB\nON -a-> EN\nON -b-> OB\nOB -a-> EN\nOB -b-> OB';
  const BB2 = 'start: A\naccept: H\nA, _ -> B, 1, R\nA, 1 -> B, 1, L\nB, _ -> A, 1, L\nB, 1 -> H, 1, R';
  const BB3 = 'start: A\naccept: H\nA, _ -> B, 1, R\nA, 1 -> H, 1, R\nB, _ -> C, _, R\nB, 1 -> B, 1, R\nC, _ -> C, 1, L\nC, 1 -> A, 1, L';

  // =========================================================================================================
  // Chapter 1: questions a machine can settle
  // =========================================================================================================
  C.lesson({
    id: 'comp-l-questions', chapter: 'comp-decidable', title: 'A question becomes a language', minutes: 10,
    summary: 'Any yes-or-no question about machines can be written as a set of strings, and a decider is a machine that always answers. The first one: does this DFA accept this string?',
    blocks: [
      'Up to now our machines answered questions about strings: does *abba* have an even number of a’s? From here on we ask questions about **machines**: does this automaton accept anything at all? Do these two grammars say the same thing? Does this program ever stop?',
      'The trick that lets a machine answer a question about a machine is plain: write the machine down as a string. A DFA is a finite list of states and arrows, so it can be spelled out in bits, just like a file on a disk. We write ⟨D⟩ for that description, and ⟨D, w⟩ for a DFA and a string packed together.',
      { def: 'A problem as a language', text: 'a yes-or-no question becomes the set of descriptions whose answer is yes. For example A_DFA = { ⟨D, w⟩ : D is a DFA and D accepts w }.' },
      'Now "can a machine answer this question?" is a question we already know how to ask: is this language decidable?',
      { def: 'Decider', text: 'a Turing machine that halts on every input, accepting or rejecting. A language is **decidable** when some decider accepts exactly its strings.' },
      { def: 'Recogniser', text: 'a Turing machine that accepts exactly the strings of the language; on the others it may reject or run for ever. A language with a recogniser is **recognisable**.' },
      'Why insist on halting? Because a machine that has not answered *yet* is useless to whoever is waiting for it: you cannot tell "still thinking" from "never going to answer".',
      { h: 'The decider for A_DFA' },
      'The decider for A_DFA does the obvious thing: unpack the DFA, put a finger on its start state, and move the finger once per symbol of w. When the symbols run out it looks at the state.',
      { topic: 'dec-adfa', input: { m: EVEN_A, w: 'abba' }, caption: 'The decider unpacks ⟨D, w⟩ and runs D. Watch the step counter: it stops after exactly |w| moves, never more.' },
      { predict: { q: 'Could the decider for A_DFA ever run for ever on some ⟨D, w⟩?', options: ['Yes, if D has a loop in it', 'No: D moves once per symbol, so the run ends after |w| moves', 'Only if w is very long'], answer: 1, explain: 'A loop in the diagram is not a loop in time. Each symbol is read once and moves the finger once, so the run takes exactly |w| moves, however the arrows are drawn.' } },
      { h: 'Try it' },
      { sandbox: { kind: 'fa', text: EVEN_A, input: 'abba' }, caption: 'This DFA accepts the strings with an even number of a’s. Run it on a few strings and count the moves: always one per symbol.' },
      'One more idea runs through the whole part. Any reasonable way of computing (a register machine, a program in your favourite language, a Turing machine with many tapes) decides exactly the same problems. That belief, that the Turing machine captures what "computable by an algorithm" means, is the **Church–Turing thesis**. It is not a theorem: "algorithm" was an informal word before it, and the thesis is the claim that the formal definition caught it. Every result below about Turing machines is therefore a result about every programming language.',
      { tip: 'When you write a decider, the first thing to check is not "is it right?" but "does it always stop?". Most wrong deciders in this part are machines that sometimes wait for ever.' },
      { list: ['A question about machines becomes a language of descriptions.', 'A decider must halt on every input; a recogniser only on the yes-instances.', 'A_DFA is decidable: simulate D for |w| moves.', 'Church–Turing: Turing machines decide exactly what algorithms decide.'] },
      { exercise: 'comp-x-adfa-moves' }, { exercise: 'comp-x-decider-def' }, { exercise: 'comp-x-church-turing' },
    ],
  });

  C.lesson({
    id: 'comp-l-dfa-questions', chapter: 'comp-decidable', title: 'Is it empty? Are they equal?', minutes: 12,
    summary: 'Emptiness of a DFA is a question of reachability, and equality of two DFAs turns into emptiness of a third DFA built from both.',
    blocks: [
      'Here is a harder-looking question: does a DFA accept **any** string at all? There are infinitely many strings, so trying them one by one never finishes when the answer is no. We need a smarter idea.',
      'The smarter idea: a DFA accepts something exactly when some accepting state can be **reached** from the start state by following arrows. The labels do not matter, only the arrows. And reachability in a finite graph is a finite search.',
      { def: 'E_DFA', text: '{ ⟨D⟩ : D is a DFA and L(D) = ∅ }.' },
      { steps: ['Mark the start state.', 'Mark every state an arrow leads to from a marked state.', 'Repeat until a round marks nothing new (at most one round per state).', 'Accept (L(D) is empty) if no accepting state is marked; reject otherwise.'] },
      { topic: 'dec-edfa', input: { m: 'start a\naccept d\na -0-> b\na -1-> a\nb -0-> a\nb -1-> b\nc -0-> d\nc -1-> c\nd -0,1-> d' }, caption: 'The marks spread from a along the arrows and stop. The accepting state d sits on an island no mark reaches: the language is empty.' },
      { predict: { q: 'A DFA has an accepting state with arrows coming into it. Must its language be non-empty?', options: ['Yes, any arrow in will do', 'No: the arrows might come only from states that cannot themselves be reached'], answer: 1, explain: 'Arrows into an accepting state help only if their source can be reached from the start. The island in the figure above has plenty of arrows into d, all from c, which nothing reaches.' } },
      { sandbox: { kind: 'fa', text: ISLAND, input: 'abab' }, caption: 'Accepting state t is on an island with s. Try strings: nothing reaches t. Which states can you reach at all?' },
      { h: 'Equality, by building a third machine' },
      'Do two DFAs D₁ and D₂ accept the same language? Their languages differ exactly when some string is in one but not the other: the **symmetric difference**. And a DFA for the symmetric difference can be built by running D₁ and D₂ side by side (the product construction), accepting when exactly one of them accepts.',
      { math: 'L(C) = (L(D₁) ∖ L(D₂)) ∪ (L(D₂) ∖ L(D₁))\nL(D₁) = L(D₂)  ⇔  L(C) = ∅' },
      'So the equality question becomes the emptiness question, which we can already answer. This move, answering a new question by turning it into one we can already answer, is the seed of everything in chapter 4.',
      { topic: 'dec-eqdfa', input: { a: 'start p\naccept p\np -a-> q\nq -b-> p', b: 'start p\naccept r\np -a-> q\nq -b-> r\nr -a-> q' }, caption: '(ab)* and (ab)⁺ differ on one string only. Watch the product machine: its start pair is accepting in one machine and not the other, so the empty string is the witness.' },
      { predict: { q: 'The product machine for the symmetric difference has an accepting pair reachable from the start. What does that give you, besides the answer "not equal"?', options: ['Nothing more', 'A string on which the two DFAs disagree: the labels along the path to that pair'], answer: 1, explain: 'The path of marks is a real string. Reading its labels gives a counterexample, which is what the checker in this app shows you when a DFA you build is wrong.' } },
      { list: ['E_DFA: mark what the start can reach; empty when no accepting state is marked.', 'EQ_DFA: build the symmetric-difference DFA, then ask E_DFA.', 'Only arrows matter for emptiness, not their labels.', 'A reachable accepting pair spells out a counterexample.'] },
      { exercise: 'comp-x-edfa-reach' }, { exercise: 'comp-x-edfa-which' }, { exercise: 'comp-x-eq-witness' }, { exercise: 'comp-x-symdiff' }, { exercise: 'comp-x-all-dfa' },
    ],
  });

  C.lesson({
    id: 'comp-l-cfg-questions', chapter: 'comp-decidable', title: 'Questions about grammars', minutes: 12,
    summary: 'Does a grammar generate a string? Does it generate anything? Both are decidable, but only after we make sure the search is finite.',
    blocks: [
      'Does the grammar S → a S b | S S | ε generate *abab*? The naive decider tries derivations one after another. But with a rule like S → S S, derivations can grow and shrink and grow again: the search has no end in sight, and if the answer is no, it never stops.',
      'The fix is to rewrite the grammar first so that the search becomes finite. In **Chomsky normal form** every rule is A → B C or A → a (plus S → ε when the empty string belongs). Then each step either adds one symbol or turns a variable into a terminal, and a derivation of a string of length n ≥ 1 takes exactly **2n − 1** steps. A finite number of derivations of that length exist, so trying them all is a decider. The CYK table does the same job far faster.',
      { topic: 'dec-acfg', input: { g: 'S → a S b | S S | ε', w: 'abab' }, caption: 'First the grammar is put in Chomsky normal form, then the CYK table is filled bottom up. Watch the top cell: S there means yes.' },
      { predict: { q: 'In Chomsky normal form, how many steps does a derivation of a 5-symbol string take?', options: ['5', '9', '10', 'It depends on the grammar'], answer: 1, explain: '2n − 1 = 9: four steps of the form A → B C split one variable into two (from 1 variable to 5), and five steps A → a turn each variable into a terminal.' } },
      { h: 'Does the grammar generate anything?' },
      'For emptiness the marks flow backwards. A variable is **generating** when it can turn into a string of terminals. Terminals are trivially fine; a variable becomes generating as soon as one of its rules has a right side made only of terminals and generating variables. Repeat until nothing changes, then look at the start variable.',
      { topic: 'dec-ecfg', input: { g: 'S → a S b | B\nB → C c | b\nC → C C' }, caption: 'B gets its mark from B → b in the first round, then S from S → B. C never gets one: every rule for C needs a C first.' },
      { predict: { q: 'A grammar has the single rule S → a S. Is its language empty?', options: ['No, it contains a, aa, aaa, …', 'Yes: no derivation ever finishes'], answer: 1, explain: 'Every sentential form still contains S, so no derivation ever reaches a string of terminals. "Can be rewritten for ever" is not the same as "generates something".' } },
      { editor: { kind: 'grammar', text: 'S → a S b | S S | ε', tests: 'ε\nab\nabab\naabb\n-abba\n-ba' }, caption: 'Test the grammar from the figure on strings. Then delete the ε rule: what happens to every test?' },
      { h: 'Every context-free language is decidable' },
      'Fix one grammar G. A machine that holds G inside and runs the A_CFG decider on ⟨G, w⟩ halts on every w. So every context-free language is decidable. Note what we did not do: simulate a pushdown automaton directly. A nondeterministic PDA can follow a branch of ε-moves that never ends, so a straight simulation is not a decider.',
      { topic: 'dec-cfl', caption: 'One grammar, built into a machine, tested on several strings. Each run halts, whether the answer is yes or no.' },
      { warn: 'Not every question about grammars is this friendly. Whether two grammars are equal, or whether a grammar is ambiguous, is undecidable (chapter 5).' },
      { list: ['A_CFG: convert to Chomsky normal form, then the search is finite (2n − 1 steps; CYK).', 'E_CFG: mark generating variables until nothing changes; empty if S is unmarked.', 'Every context-free language is decidable.', 'Simulating a PDA naively is not a decider: ε-branches can run for ever.'] },
      { exercise: 'comp-x-cnf-steps' }, { exercise: 'comp-x-ecfg-rounds' }, { exercise: 'comp-x-ecfg-which' }, { exercise: 'comp-x-pda-sim' }, { exercise: 'comp-x-decidable-list' },
    ],
  });

  // ---- exercises, chapter 1 ----
  ex({ id: 'comp-x-adfa-moves', chapter: 'comp-decidable', title: 'How long does A_DFA take?', kind: 'number',
    text: 'The decider for A_DFA is given ⟨D, w⟩ where D has 12 states and w = *babbab*. How many moves of D does it simulate before it answers?',
    answer: 6, solution: '6', wrong: ['12', '7', '72'],
    hints: H('Does the number of states matter for the length of the run?', 'A DFA moves exactly once for each symbol it reads.', '6: one move per symbol of babbab, whatever the size of D.') });
  ex({ id: 'comp-x-decider-def', chapter: 'comp-decidable', title: 'Decider or recogniser?', kind: 'choice',
    text: 'A machine M accepts every string that contains *aa*. On strings without *aa* it sometimes rejects and sometimes runs for ever. Which is true?',
    options: ['M is a decider for the language of strings containing aa', 'M is a recogniser for that language, but not a decider', 'M is neither, since it does not halt on everything', 'M shows that the language is undecidable'], answer: 1,
    why: 'It accepts exactly the right strings, so it recognises the language; it does not always halt, so it is not a decider. The language itself is decidable, by a different machine.',
    whyNot: ['A decider must halt on every input, including the ones it rejects.', null, 'A recogniser may run for ever on strings outside the language: that is allowed.', 'One bad machine says nothing about the language: a better machine (scan for aa, then stop at the end) decides it.'],
    solution: 1, wrong: [0, 3],
    hints: H('What does a recogniser have to do on strings in the language? And outside it?', 'A decider must also halt on the strings outside the language.', 'A recogniser, not a decider. The language is still decidable: another machine scans once and halts.') });
  ex({ id: 'comp-x-church-turing', chapter: 'comp-decidable', title: 'What kind of claim is the thesis?', kind: 'choice',
    text: 'Which describes the Church–Turing thesis best?',
    options: ['A theorem proved from the definition of a Turing machine', 'The claim that the informal idea of an algorithm is captured exactly by Turing machines', 'The fact that Turing machines are faster than other models', 'The statement that the halting problem is undecidable'], answer: 1,
    why: 'It links an informal notion to a formal one, so it cannot be proved; every model proposed since has turned out to be equivalent, which is the evidence for it.',
    whyNot: ['To prove it you would need a formal definition of "algorithm", and then it would be that definition you were comparing with.', null, 'It says nothing about speed; equivalent models can differ greatly in time.', 'That is a theorem about Turing machines; the thesis is what makes it a statement about all algorithms.'],
    solution: 1, wrong: [0, 3],
    hints: H('Can you prove something about "algorithm" if algorithm has no formal definition?', 'The thesis connects an informal word to a formal model.', 'The second option: it is a claim, supported by every model being equivalent, not a theorem.') });

  ex({ id: 'comp-x-edfa-reach', chapter: 'comp-decidable', title: 'Spread the marks', kind: 'string', set: true,
    text: ['Run the E_DFA decider on this DFA by hand. Which states end up marked (reachable from the start)? Write them as a set, like {p, q}.', { code: ISLAND, lang: 'machine' }],
    answer: '{p, q, r}', solution: 'r, q, p', wrong: ['{p, q, r, s, t}', '{p, q}', '{p, q, r, t}'],
    why: 'And since t is not marked, L(D) = ∅: the decider accepts ⟨D⟩.',
    hints: H('Start with p. Which states do arrows from p lead to?', 'p reaches q; q reaches p and r; r only loops. Nothing leads into s or t from these.', '{p, q, r}. The accepting state t is unmarked, so the language is empty.') });
  ex({ id: 'comp-x-edfa-which', chapter: 'comp-decidable', title: 'Which languages are empty?', kind: 'choice', level: 2,
    text: ['Which of these DFAs (over {a, b}) accept no string at all? Choose all that apply.'],
    options: ['`start p` · `accept q` · `p -a-> p` · `q -b-> p`', '`start p` · `accept p` · `p -a-> q`', '`start p` · `accept r` · `p -a-> q` · `q -b-> q` · `r -a-> p`', '`start p` · `accept q` · `p -b-> r` · `r -a-> q`'], answer: [0, 2],
    solution: [0, 2], wrong: [[0], [0, 1, 2], [2, 3]],
    hints: H('For each one, mark what p reaches, and look at the accepting states.', 'In the second, the start state itself accepts: ε is in the language.', 'The first and the third: q (resp. r) has arrows out, but none in from anything p reaches. The second accepts ε and the fourth accepts ba.') });
  ex({ id: 'comp-x-eq-witness', chapter: 'comp-decidable', title: 'Catch two DFAs disagreeing', kind: 'string',
    text: ['The first DFA accepts the strings that contain *ab*; the second accepts the strings that end in *b*. They are not equal. Give a string on which they disagree.', { sandbox: { kind: 'fa', text: 'start n\naccept y\nn -a-> s\nn -b-> n\ns -a-> s\ns -b-> y\ny -a,b-> y', input: 'abba' }, caption: 'Contains ab.' }, { sandbox: { kind: 'fa', text: 'start n\naccept y\nn -a-> n\nn -b-> y\ny -b-> y\ny -a-> n', input: 'abba' }, caption: 'Ends in b.' }],
    accept: (w) => /ab/.test(w) !== /b$/.test(w), solution: 'b', wrong: ['ab', 'a', 'ε'],
    why: 'The product DFA reaches a pair where exactly one machine accepts: that path is your string.',
    whyNot: 'On that string both machines give the same answer. Look for a string that ends in b with no ab, or one with ab that ends in a.',
    hints: H('A string in one language but not the other.', 'Try strings with no a at all, or strings that end in a.', 'b (ends in b, no ab) or aba (contains ab, ends in a). The shortest is b.') });
  ex({ id: 'comp-x-symdiff', chapter: 'comp-decidable', title: 'Build the symmetric difference', kind: 'machine', machine: 'dfa', alphabet: 'ab', level: 2,
    text: 'D₁ accepts the strings over {a, b} with an even number of a’s; D₂ accepts the strings that end in b. Build a DFA for the symmetric difference: the strings accepted by exactly one of them. (This is the machine the EQ_DFA decider tests for emptiness.)',
    member: (w) => ([...w].filter((c) => c === 'a').length % 2 === 0) !== w.endsWith('b'), ref: { machine: SYMDIFF },
    solution: SYMDIFF,
    wrong: ['start EN\naccept EB\nEN -a-> ON\nEN -b-> EB\nEB -a-> ON\nEB -b-> EB\nON -a-> EN\nON -b-> OB\nOB -a-> EN\nOB -b-> OB', 'start EN\naccept EN EB OB\nEN -a-> ON\nEN -b-> EB\nEB -a-> ON\nEB -b-> EB\nON -a-> EN\nON -b-> OB\nOB -a-> EN\nOB -b-> OB', 'start EN\naccept EN OB\nEN -a-> ON\nEN -b-> EB\nEB -a-> EN\nEB -b-> EB\nON -a-> EN\nON -b-> OB\nOB -a-> ON\nOB -b-> OB'],
    hints: H('Run both machines side by side: a state is a pair (parity of a’s, whether the last symbol was b).', 'Four pairs: E or O for the parity, N or B for "ended in b". Accept the pairs where exactly one machine accepts.', 'States EN (start), EB, ON, OB; a flips E/O and goes to N; b keeps the parity and goes to B. Accept EN (D₁ yes, D₂ no) and OB (D₁ no, D₂ yes).') });
  ex({ id: 'comp-x-all-dfa', chapter: 'comp-decidable', title: 'Does it accept everything?', kind: 'choice', level: 2,
    text: 'ALL_DFA asks whether a DFA accepts every string over its alphabet. Which decider is correct?',
    options: ['Try every string up to length 100; accept if all are accepted', 'Swap accepting and non-accepting states of the (complete) DFA, then run the E_DFA decider on the result', 'Accept if every state is accepting', 'Run the E_DFA decider on D itself and answer the opposite'], answer: 1,
    why: 'L(D) is everything exactly when its complement is empty, and complementing a complete DFA is just swapping the accepting states.',
    whyNot: ['A DFA with 200 states might first reject a string of length 150.', null, 'Unreachable states could be non-accepting without harming anything: the test is too strict.', 'Not empty is not the same as everything.'],
    solution: 1, wrong: [0, 3],
    hints: H('Which question we can already answer is closest to "accepts everything"?', 'L(D) = Σ* exactly when the complement of L(D) is empty.', 'Complement the DFA (swap accepting states; make it complete first), then ask E_DFA.') });

  ex({ id: 'comp-x-cnf-steps', chapter: 'comp-decidable', title: 'Steps in a Chomsky derivation', kind: 'number',
    text: 'A grammar is in Chomsky normal form. Exactly how many steps does any derivation of a string of length 8 take?',
    answer: 15, solution: '15', wrong: ['8', '16', '7'],
    hints: H('Count the two kinds of steps separately: A → B C and A → a.', 'To end with 8 terminals you need 8 variables (7 splitting steps), then 8 steps to turn them into terminals.', '2·8 − 1 = 15.') });
  ex({ id: 'comp-x-ecfg-rounds', chapter: 'comp-decidable', title: 'Rounds of marking', kind: 'table', table: 'custom', level: 2,
    text: ['Run the emptiness decider on this grammar. In round 1 a variable gets its mark if one of its rules has only terminals on the right; in each later round, if one of its rules has only terminals and variables marked in earlier rounds. For each variable write the round in which it is marked, or *never*.', { code: 'S → A B | C S\nA → a A | b\nB → A A | B c\nC → C a', lang: 'grammar' }],
    rows: ['S', 'A', 'B', 'C'], cols: ['marked in round'], cells: { 'S|marked in round': '3', 'A|marked in round': '1', 'B|marked in round': '2', 'C|marked in round': 'never' },
    solution: { 'S|marked in round': '3', 'A|marked in round': '1', 'B|marked in round': '2', 'C|marked in round': 'never' },
    wrong: [{ 'S|marked in round': '2', 'A|marked in round': '1', 'B|marked in round': '2', 'C|marked in round': 'never' }, { 'S|marked in round': '3', 'A|marked in round': '1', 'B|marked in round': '2', 'C|marked in round': '4' }],
    hints: H('Only A has a rule with nothing but terminals on the right (A → b).', 'Round 2: B → A A uses only marked A. Round 3: S → A B. C → C a always needs C itself.', 'S: 3, A: 1, B: 2, C: never. S is marked, so the language is not empty.') });
  ex({ id: 'comp-x-ecfg-which', chapter: 'comp-decidable', title: 'Which grammars generate nothing?', kind: 'choice', level: 2,
    text: 'Which of these grammars (start variable S) have an empty language? Choose all that apply.',
    options: ['S → a S b | S S', 'S → A a | b B ; A → S ; B → b', 'S → A B ; A → a A ; B → b', 'S → a S | ε'], answer: [0, 2],
    solution: [0, 2], wrong: [[0], [0, 1, 2], [2, 3]],
    hints: H('Look for a rule whose right side is all terminals: without one, nothing gets marked.', 'In the second grammar B → b, so S → b B finishes. In the third, A → a A never finishes, and S needs A.', 'The first and third are empty. The second generates bb; the fourth generates a*, including ε.') });
  ex({ id: 'comp-x-pda-sim', chapter: 'comp-decidable', title: 'Why not just run the PDA?', kind: 'choice', level: 2,
    text: 'A student proposes a decider for a context-free language L: take a PDA for L and simulate every branch of it on w, accepting if some branch accepts. Why is this not (yet) a decider?',
    options: ['A PDA cannot be simulated by a Turing machine', 'Some branch might keep making ε-moves for ever, so the simulation might never finish when w is not in L', 'Context-free languages are not decidable', 'The stack can hold only finitely many symbols'], answer: 1,
    why: 'Exactly: the fix is to go through a grammar in Chomsky normal form, where every derivation of w has a known length.',
    whyNot: ['A Turing machine can simulate a PDA easily, using its tape as the stack.', null, 'They are: through Chomsky normal form and CYK.', 'The stack is unbounded; that is part of the problem, since ε-moves can keep pushing.'],
    solution: 1, wrong: [0, 2],
    hints: H('Does every branch of a PDA end?', 'ε-moves read nothing, so a branch can push and push without using up its input.', 'An endless ε-branch: the simulation might never finish on a string not in L.') });
  ex({ id: 'comp-x-decidable-list', chapter: 'comp-decidable', title: 'Which are decidable?', kind: 'choice', level: 2,
    text: 'Which of these problems are decidable? Choose all that apply.',
    options: ['Does DFA D accept some string of odd length?', 'Does grammar G generate the string *abba*?', 'Do DFAs D₁ and D₂ accept the same language?', 'Is the language of grammar G empty?', 'Does DFA D accept infinitely many strings?'], answer: [0, 1, 2, 3, 4],
    solution: [0, 1, 2, 3, 4], wrong: [[1, 2, 3], [0, 1, 2, 3]],
    hints: H('Each can be turned into a question about a finite graph or a finite table.', 'Odd length: intersect D with a two-state DFA for odd length and ask E_DFA. Infinitely many: is there a cycle on a path from the start to an accepting state?', 'All five are decidable.') });

  // =========================================================================================================
  // Chapter 2: the halting problem
  // =========================================================================================================
  C.lesson({
    id: 'comp-l-diagonal', chapter: 'comp-halting', title: 'A table of programs run on programs', minutes: 10,
    summary: 'List programs down the side and their descriptions across the top, and write what each does on each. A program that flips the diagonal cannot be any row.',
    blocks: [
      'Imagine a huge spreadsheet. Down the side, every program there is: P₁, P₂, P₃, … Across the top, the same programs, but as **descriptions**: ⟨P₁⟩, ⟨P₂⟩, ⟨P₃⟩, … Programs read strings, and a description is a string, so every program can be run on every description. In each cell we write what happens: **halts** or **loops**.',
      'A program running on its own description sounds odd, but it is ordinary: a compiler can compile its own source, a word counter can count the words of its own code.',
      { topic: 'halt-diagonal', caption: 'The table fills cell by cell. Then watch the diagonal: the new program does the opposite of what each program does on its own description.' },
      'Now define a new program, call it D, by reading the diagonal and flipping it: on input ⟨Pᵢ⟩, D halts if Pᵢ loops on ⟨Pᵢ⟩, and loops if Pᵢ halts on ⟨Pᵢ⟩.',
      { predict: { q: 'Could D be program P₃ in the list?', options: ['Yes, if P₃ happens to behave like that', 'No: D and P₃ do different things on ⟨P₃⟩'], answer: 1, explain: 'By construction D does the opposite of P₃ on input ⟨P₃⟩. Two programs that disagree on some input are different programs. The same argument works for every row.' } },
      'So D is not in the list. But the list was supposed to hold **every** program. Something must give: D is perfectly well defined as a description of behaviour, yet if D were a real program it would be in the list. The only way out is that **no program can compute D**. And the one step of D that might be impossible is reading the diagonal: deciding whether Pᵢ halts on ⟨Pᵢ⟩.',
      { tip: 'This is the same diagonal argument that shows there are more sets of natural numbers than natural numbers. Here it shows there are more behaviours than programs.' },
      { h: 'The counting view' },
      'There is a second, blunter reason some problems have no program. Programs are finite strings, so they can be listed: there are countably many. Languages are arbitrary sets of strings, and there are uncountably many. Almost every language has no machine at all. The halting problem is special only because it is a language we care about.',
      { list: ['Every program can be run on every description, giving a table.', 'Flipping the diagonal gives behaviour that differs from every row.', 'So that behaviour has no program, and the culprit is "does Pᵢ halt on ⟨Pᵢ⟩?".', 'Counting: countably many machines, uncountably many languages.'] },
      { exercise: 'comp-x-diag-fill' }, { exercise: 'comp-x-diag-where' }, { exercise: 'comp-x-count' },
    ],
  });

  C.lesson({
    id: 'comp-l-build-d', chapter: 'comp-halting', title: 'Build D and feed it itself', minutes: 12,
    summary: 'Suppose a machine H decides halting. A few lines of wrapping turn it into a machine D that contradicts H on D’s own description.',
    blocks: [
      'Let us act the proof out. Suppose someone hands us a machine H, and promises: on input ⟨M, w⟩, H always halts, and says **yes** if M halts on w and **no** if M runs for ever. That would decide HALT = { ⟨M, w⟩ : M halts on w }.',
      'We build a new machine D around H. It takes one input, a description ⟨M⟩:',
      { steps: ['Run H on ⟨M, ⟨M⟩⟩: will M halt when given its own description?', 'If H says **yes**, go into an endless loop.', 'If H says **no**, halt.'] },
      'D is contrary on purpose. Now the crucial move: run D on **its own** description ⟨D⟩.',
      { topic: 'halt-build-d', caption: 'Both branches are played out. Whatever H predicts about D on ⟨D⟩, D does the opposite. Watch where each branch ends.' },
      { predict: { q: 'H says that D halts on ⟨D⟩. What does D then actually do on ⟨D⟩?', options: ['It halts, as H said', 'It loops for ever, so H was wrong', 'It depends on what H does next'], answer: 1, explain: 'D asked H exactly this question, heard "yes", and by its second line went into the endless loop. If instead H says "no", D halts. Either way H is wrong about one input, so H does not decide HALT.' } },
      'Every step of D is easy if H exists: copying a description, calling H, looping or halting. So the only thing that can be wrong is the assumption. **No machine decides HALT.** It is undecidable.',
      { warn: 'A common slip: "D is contradictory, so D does not exist". D is built from H by honest steps; what does not exist is H. The contradiction is aimed at the assumption, not at the construction.' },
      { h: 'What a real attempt looks like' },
      'Replace H by something real, say "simulate M for 40 steps; if it has halted say yes, else say no". This H always answers. Feed the D built from it to itself and see which way it fails.',
      { topic: 'halt-build-d', input: { branch: 'both', real: 40 }, caption: 'With a real H the contradiction becomes a concrete wrong answer. Watch for the line where H’s verdict and D’s behaviour part ways.' },
      { predict: { q: 'Is HALT recognisable (a machine that says yes on every halting pair, possibly waiting for ever on the others)?', options: ['Yes: simulate M on w and accept when it halts', 'No, for the same reason it is undecidable'], answer: 0, explain: 'Simulating is a fine recogniser: if M halts, the simulation sees it. What we cannot do is say **no** in finite time. That asymmetry is the subject of chapter 3.' } },
      { list: ['Assume H decides halting; wrap it into D, which does the opposite of H’s prediction.', 'Run D on ⟨D⟩: H is wrong either way, so H cannot exist.', 'The assumption fails, not the construction.', 'HALT is recognisable (simulate) but not decidable.'] },
      { exercise: 'comp-x-d-on-d' }, { exercise: 'comp-x-flaw-simulate' }, { exercise: 'comp-x-flaw-dfa-diag' },
    ],
  });

  C.lesson({
    id: 'comp-l-fool', chapter: 'comp-halting', title: 'Fool the decider', minutes: 9,
    summary: 'Every candidate halting checker you could write is caught by the D built from it. Try a few strategies and watch each one fail.',
    blocks: [
      'It is tempting to think the halting problem is only a trick about self-reference, and that a careful checker would work on "real" programs. Let us take real strategies seriously and see where each breaks.',
      { topic: 'halt-fool', input: { kind: 'sim', N: 50, guess: 'loops' }, caption: 'Strategy: simulate 50 steps, and if the program has not stopped, guess "loops". It is right on many programs. Watch how D, built from this very strategy, runs just long enough to make it wrong.' },
      { predict: { q: 'The checker is changed to simulate 200 steps instead of 50. What happens?', options: ['It is now correct', 'A new D, built from the new checker, still catches it'], answer: 1, explain: 'Any fixed budget can be outrun: the D built from the 200-step checker simply runs a little longer than 200 steps before stopping. Choose a budget and the D for that budget beats it.' } },
      { h: 'Watching for repeats' },
      'A better idea: watch the whole configuration (state, tape, head). If it ever repeats exactly, the machine is in a loop for sure. That is correct whenever it says "loops". But a machine can run for ever without repeating, by using fresh tape.',
      { sandbox: { kind: 'tm', text: RUNAWAY, input: '' }, caption: 'This machine writes 1 and moves right, for ever. No configuration repeats, because the tape keeps growing. A repeat-watcher waits in vain.' },
      { topic: 'halt-fool', input: { kind: 'watch', N: 150, guess: 'halts' }, caption: 'The repeat-watcher, forced to give an answer after 150 steps, guesses "halts" if it saw no repeat. Watch D exploit exactly that guess.' },
      { tip: 'Real tools that prove termination do exist and are useful. They succeed on many programs and say "I don’t know" on the rest. What cannot exist is one that always answers correctly.' },
      { list: ['A step budget is outrun by a machine that runs one step longer.', 'Watching for repeats is sound, but misses runs that use fresh tape.', 'Every strategy that always answers is caught by its own D.', 'Useful checkers exist; complete and correct ones do not.'] },
      { exercise: 'comp-x-flaw-repeats' }, { exercise: 'comp-x-halt-class' },
    ],
  });

  // ---- exercises, chapter 2 ----
  ex({ id: 'comp-x-diag-fill', chapter: 'comp-halting', title: 'Flip the diagonal', kind: 'table', table: 'custom',
    text: ['Here is a corner of the table: what four programs do when run on each other’s descriptions. D does the opposite of each program on that program’s own description. Fill in D’s row: *halts* or *loops*.', { table: [['', '⟨P₁⟩', '⟨P₂⟩', '⟨P₃⟩', '⟨P₄⟩'], ['P₁', 'halts', 'loops', 'halts', 'halts'], ['P₂', 'halts', 'loops', 'loops', 'halts'], ['P₃', 'loops', 'halts', 'loops', 'halts'], ['P₄', 'loops', 'loops', 'halts', 'halts']] }],
    rows: ['D'], cols: ['⟨P₁⟩', '⟨P₂⟩', '⟨P₃⟩', '⟨P₄⟩'], cells: { 'D|⟨P₁⟩': 'loops', 'D|⟨P₂⟩': 'halts', 'D|⟨P₃⟩': 'halts', 'D|⟨P₄⟩': 'loops' },
    solution: { 'D|⟨P₁⟩': 'loops', 'D|⟨P₂⟩': 'halts', 'D|⟨P₃⟩': 'halts', 'D|⟨P₄⟩': 'loops' },
    wrong: [{ 'D|⟨P₁⟩': 'halts', 'D|⟨P₂⟩': 'loops', 'D|⟨P₃⟩': 'loops', 'D|⟨P₄⟩': 'halts' }, { 'D|⟨P₁⟩': 'loops', 'D|⟨P₂⟩': 'halts', 'D|⟨P₃⟩': 'loops', 'D|⟨P₄⟩': 'loops' }],
    hints: H('Read only the diagonal: P₁ on ⟨P₁⟩, P₂ on ⟨P₂⟩, and so on.', 'The diagonal reads halts, loops, loops, halts.', 'Flip it: loops, halts, halts, loops.') });
  ex({ id: 'comp-x-diag-where', chapter: 'comp-halting', title: 'Where does D differ from P₇?', kind: 'number',
    text: 'In the diagonal construction, D is guaranteed to behave differently from program P₇ on one particular input. Give the number k such that this input is ⟨Pₖ⟩.',
    answer: 7, solution: '7', wrong: ['1', '8'],
    hints: H('D was defined from the diagonal cells.', 'The diagonal cell in row P₇ is in column ⟨P₇⟩.', '7: on ⟨P₇⟩, D does the opposite of P₇.') });
  ex({ id: 'comp-x-count', chapter: 'comp-halting', title: 'Why most languages have no machine', kind: 'choice', level: 2,
    text: 'Which argument shows that some languages over {0, 1} are not recognised by any Turing machine?',
    options: ['Turing machines are finite, so they recognise only finite languages', 'Machines have finite descriptions, so there are countably many; languages are all subsets of {0,1}*, of which there are uncountably many', 'Every language is recognisable, but some are not decidable', 'There are more Turing machines than languages'], answer: 1,
    whyNot: ['Plenty of infinite languages are recognised, for example all strings of even length.', null, 'The counting argument shows the opposite: most languages are not even recognisable.', 'It is the other way round.'],
    solution: 1, wrong: [0, 3],
    hints: H('Can the machines be listed one by one?', 'Each machine is a finite string, so yes. Can all subsets of {0,1}* be listed? Diagonalise.', 'Countably many machines, uncountably many languages, so almost all languages have no recogniser.') });
  ex({ id: 'comp-x-d-on-d', chapter: 'comp-halting', title: 'What does D do on ⟨D⟩?', kind: 'choice',
    text: 'D runs the supposed halting decider H on ⟨M, ⟨M⟩⟩, loops if H says "halts" and halts if H says "loops". Suppose H says "loops" about D on ⟨D⟩. What follows?',
    options: ['D loops on ⟨D⟩, so H was right', 'D halts on ⟨D⟩, so H was wrong', 'D crashes', 'Nothing: H might say something else next time'], answer: 1,
    why: 'Deciders are deterministic: H’s answer on ⟨D, ⟨D⟩⟩ is fixed, and D does the opposite of it.',
    whyNot: ['Read D’s third line again: on "loops" it halts.', null, 'D is an ordinary machine; it halts or loops like any other.', 'H is a deterministic machine: on the same input it always gives the same answer.'],
    solution: 1, wrong: [0, 3],
    hints: H('Follow D’s instructions with H’s answer.', 'If H says "loops", D’s rule is to halt.', 'D halts on ⟨D⟩, so H’s prediction was wrong.') });
  ex({ id: 'comp-x-flaw-simulate', chapter: 'comp-halting', title: 'Spot the flaw: a halting decider', kind: 'choice',
    text: ['A fake proof that HALT is decidable:', { steps: ['On input ⟨M, w⟩, simulate M on w step by step.', 'If the simulation halts, accept.', 'If the simulation never halts, reject.', 'Every case is covered, so this decides HALT.'] }, 'Which step is wrong?'],
    options: ['Step 1: a machine cannot simulate another machine', 'Step 2: halting does not mean accepting', 'Step 3: the machine can never observe "never halts" in finite time, so it never reaches the reject', 'Step 4: there is a third case, crashing'], answer: 2,
    why: 'This machine is a recogniser for HALT, not a decider: on a looping M it simply loops too.',
    whyNot: ['The universal machine does exactly this.', 'Step 2 is about HALT, which asks only whether M halts; accepting there is right.', null, 'A machine that "crashes" (no rule applies) halts.'],
    solution: 2, wrong: [0, 1],
    hints: H('Which step needs the machine to know something about the infinite future?', 'To reject, it would have to wait until "never" is over.', 'Step 3: "never halts" is not something a simulation ever sees. The machine recognises HALT but does not decide it.') });
  ex({ id: 'comp-x-flaw-dfa-diag', chapter: 'comp-halting', title: 'Spot the flaw: diagonalising DFAs', kind: 'choice', level: 3,
    text: ['A fake proof that A_DFA is undecidable:', { steps: ['Suppose a DFA H decides A_DFA.', 'Build a DFA D that, on input ⟨M⟩, runs H on ⟨M, ⟨M⟩⟩ and accepts exactly when H rejects.', 'Run D on ⟨D⟩: D accepts ⟨D⟩ exactly when D does not accept ⟨D⟩.', 'Contradiction, so A_DFA is undecidable.'] }, 'What is wrong?'],
    options: ['Step 1: A_DFA is decided by a Turing machine, and need not be decided by a DFA; a decider of any kind is what matters', 'Step 3: D cannot be run on its own description', 'Step 4: a contradiction proves nothing', 'Nothing: A_DFA really is undecidable'], answer: 0,
    why: 'The argument at best shows that no DFA decides A_DFA (which is true, since it is not even regular). A Turing machine decides it easily.',
    whyNot: [null, 'Any machine can be run on any string, including its own description.', 'A contradiction refutes the assumption, which here is too strong.', 'We decided A_DFA in chapter 1 by simulation.'],
    solution: 0, wrong: [1, 3],
    hints: H('A_DFA is decidable: we built the decider. So something must be off.', 'What kind of machine is the "decider" assumed to be?', 'Step 1 assumes the decider is a DFA. The argument only shows that no DFA decides A_DFA; a Turing machine does.') });
  ex({ id: 'comp-x-flaw-repeats', chapter: 'comp-halting', title: 'Spot the flaw: watching for repeats', kind: 'choice', level: 2,
    text: ['A fake proof that HALT is decidable:', { steps: ['A machine has finitely many states.', 'So if M runs long enough, some state must repeat.', 'A repeated state means M is in a loop.', 'So: simulate M on w; if it halts accept, if a state repeats reject.'] }, 'Which step is wrong?'],
    options: ['Step 1', 'Step 2', 'Step 3: the same state with a different tape or head position is not a loop', 'Step 4: halting machines never repeat a state'], answer: 2,
    why: 'Only a repeated whole configuration (state, tape and head) proves a loop, and a machine can avoid ever repeating one by using new tape.',
    whyNot: ['That is part of the definition of a Turing machine.', 'Pigeonhole: after more steps than states, some state has repeated.', null, 'They can: a machine that counts down a number on its tape revisits states many times and still halts.'],
    solution: 2, wrong: [0, 1],
    hints: H('Is a state the whole story of where a Turing machine is?', 'The tape and head position matter too.', 'Step 3: the same state with different tape contents can lead somewhere new. Only a whole repeated configuration proves a loop.') });
  classify({ id: 'comp-x-halt-class', chapter: 'comp-halting', title: 'Classify: HALT',
    text: 'Classify HALT = { ⟨M, w⟩ : M halts on w }.', answer: 1,
    why: 'Simulate M on w and accept if it halts: a recogniser. If its complement were also recognisable, HALT would be decidable.',
    hints: H('Can you confirm "M halts on w" with finite evidence?', 'The run itself, if it halts, is finite evidence. Can you confirm "M does not halt"?', 'Recognisable but not co-recognisable: otherwise both sides would be recognisable and HALT decidable.') });

  // =========================================================================================================
  // Chapter 3: recognisable and co-recognisable
  // =========================================================================================================
  C.lesson({
    id: 'comp-l-recognisers', chapter: 'comp-recognisable', title: 'Saying yes, eventually', minutes: 11,
    summary: 'A recogniser only promises an answer when the answer is yes. Running many searches fairly side by side, dovetailing, is the main trick for building one.',
    blocks: [
      'Think of a detective who will tell you the moment the suspect is found, but who, if the suspect does not exist, keeps searching for ever. That is a **recogniser**: yes-instances are confirmed in finite time; no-instances may get no answer at all.',
      { sandbox: { kind: 'tm', text: SEEK_A, input: 'bbab' }, caption: 'This machine walks right looking for an a. If there is one it accepts; if not, it walks into the blanks for ever. Try bbab, then bbb.' },
      'Many problems about programs have this shape. "Does program P accept **at least one** input?" If yes, there is a witness: an input and a finite run that accepts it. If no, there is nothing to show.',
      { h: 'Dovetailing' },
      'How do we find the witness? Trying the inputs one at a time, each to completion, can get stuck: if P runs for ever on the first input we try, we never reach the second. The cure is to share time fairly: in round 1 give input 1 one step; in round 2 give inputs 1 and 2 one step each; in round 3 inputs 1, 2 and 3; and so on. Every input eventually gets as many steps as it needs.',
      { topic: 'rec-dovetail', input: { p: 'ba' }, caption: 'Inputs across, steps down. P loops early on some inputs, yet the diagonal sweep still reaches the input it accepts. Watch the sweep never get stuck.' },
      { predict: { q: 'P accepts no input at all. What does the dovetailing recogniser do?', options: ['It rejects after trying all inputs', 'It runs for ever', 'It rejects after the first round in which every input has looped'], answer: 1, explain: 'There are infinitely many inputs, and it can never be sure that a running one will not accept later. With no witness, it searches for ever: allowed for a recogniser.' } },
      { def: 'Recognisable by witnesses', text: 'a language L is recognisable exactly when there is a decidable "checking" relation R such that x ∈ L ⇔ there is some finite witness c with R(x, c). The recogniser tries all witnesses, dovetailing if needed.' },
      { tip: 'To show a problem is recognisable, ask: "if the answer is yes, what finite thing proves it?" A run that halts, an accepting computation, a string the machine accepts, a matching row of dominoes.' },
      { list: ['A recogniser confirms yes-instances; on no-instances it may run for ever.', 'Look for a finite witness for yes.', 'Dovetailing shares steps fairly so one endless run cannot block the others.', 'Recognisable languages are closed under union and intersection.'] },
      { exercise: 'comp-x-dovetail-round' }, { exercise: 'comp-x-class-some' }, { exercise: 'comp-x-closure' },
    ],
  });

  C.lesson({
    id: 'comp-l-both-sides', chapter: 'comp-recognisable', title: 'Both sides at once', minutes: 12,
    summary: 'If the yes-instances and the no-instances can both be confirmed, run both searches side by side and you have a decider. That is why the complement of A_TM is not recognisable.',
    blocks: [
      'Flip the detective around. A language is **co-recognisable** when its complement is recognisable: the no-instances can be confirmed by finite evidence.',
      { def: 'Co-recognisable', text: 'L is co-recognisable when its complement L̄ is recognisable.' },
      'Now suppose a language is both. We have a machine R₁ that eventually says yes on members, and a machine R₂ that eventually says yes on non-members. Run them in turns, one step each. Every string is either in L or not, so one of them will eventually accept, and we know which.',
      { topic: 'rec-both', input: { w: 'bbbb' }, caption: 'Left: a recogniser for L. Right: a recogniser for the complement. They take turns. Exactly one of them ever accepts, so together they always answer.' },
      { predict: { q: 'Why must the two machines run in turns rather than one after the other?', options: ['To save time', 'Because the first one might run for ever on this input, and we would never start the second'], answer: 1, explain: 'If w is not in L, R₁ may run for ever; waiting for it to finish before starting R₂ would wait for ever. Alternating steps guarantees R₂ gets its chance.' } },
      { math: 'L decidable  ⇔  L recognisable and L co-recognisable' },
      { h: 'The first language with no recogniser' },
      'A_TM = { ⟨M, w⟩ : M accepts w } is recognisable (simulate M, accept if it accepts) and undecidable (the D argument works just as well for accepting as for halting). So by the box above, it cannot also be co-recognisable. Its complement, the pairs where M does **not** accept w, has **no recogniser at all**.',
      'This gives us a map with four regions, and every problem lives in one of them:',
      { table: [['', 'complement recognisable', 'complement not recognisable'], ['recognisable', '**decidable**: A_DFA, E_CFG', 'A_TM, HALT, "P accepts something"'], ['not recognisable', 'complement of A_TM, E_TM', 'EQ_TM, "M halts on every input"']], caption: 'Recognisable along the top row, co-recognisable down the first column.' },
      { warn: 'Being undecidable does not make a problem unrecognisable. A_TM is undecidable and recognisable. Always ask the two questions separately: finite evidence for yes? finite evidence for no?' },
      { list: ['Co-recognisable: the complement is recognisable.', 'Both recognisable and co-recognisable ⇔ decidable (run both in turns).', 'A_TM is recognisable but undecidable, so its complement is not recognisable.', 'Classify by asking separately for finite evidence of yes and of no.'] },
      { exercise: 'comp-x-both-why' }, { exercise: 'comp-x-class-atm' }, { exercise: 'comp-x-class-etm' }, { exercise: 'comp-x-class-coatm' }, { exercise: 'comp-x-class-eqtm' }, { exercise: 'comp-x-class-bounded' }, { exercise: 'comp-x-class-total' }, { exercise: 'comp-x-class-finite' },
    ],
  });

  // ---- exercises, chapter 3 ----
  ex({ id: 'comp-x-dovetail-round', chapter: 'comp-recognisable', title: 'When is the witness found?', kind: 'number', level: 2,
    text: 'A dovetailing recogniser works in rounds: in round r it gives inputs 1, 2, …, r one more step each. So input i runs its first step in round i. The program accepts input 4 on its 3rd step and nothing earlier. In which round is the acceptance seen?',
    answer: 6, solution: '6', wrong: ['7', '4', '12'],
    hints: H('Input 4 starts in round 4.', 'Its first step is in round 4, its second in round 5, …', 'Round 4 + 3 − 1 = 6.') });
  classify({ id: 'comp-x-class-some', chapter: 'comp-recognisable', title: 'Classify: accepts something', level: 2,
    text: 'Classify NE_TM = { ⟨M⟩ : M accepts at least one string }.', answer: 1,
    why: 'A witness for yes is one string and an accepting run, found by dovetailing. Its complement is E_TM, which is not recognisable.',
    hints: H('If M accepts something, what finite thing proves it?', 'One string and the finite accepting run. Dovetail over all strings and step counts.', 'Recognisable but not co-recognisable (its complement E_TM has no recogniser).') });
  ex({ id: 'comp-x-closure', chapter: 'comp-recognisable', title: 'What recognisers can combine', kind: 'choice', level: 2,
    text: 'L₁ and L₂ are recognisable. Which of these must also be recognisable? Choose all that apply.',
    options: ['L₁ ∪ L₂', 'L₁ ∩ L₂', 'The complement of L₁', 'L₁ L₂ (concatenation)'], answer: [0, 1, 3],
    solution: [0, 1, 3], wrong: [[0, 1, 2, 3], [0, 1]],
    hints: H('Union: run both recognisers in turns. Intersection: run both, accept when both have accepted.', 'Concatenation: dovetail over the ways to split w and the steps of both machines.', 'Union, intersection and concatenation, but not complement: A_TM is recognisable and its complement is not.') });
  ex({ id: 'comp-x-both-why', chapter: 'comp-recognisable', title: 'Why the combined machine halts', kind: 'choice',
    text: 'R₁ recognises L and R₂ recognises its complement. The combined machine runs them in turns on w. Why does it always halt?',
    options: ['Both R₁ and R₂ are deciders', 'w is in L or not in L, so exactly one of R₁, R₂ accepts after finitely many steps', 'It stops after a fixed number of steps', 'Recognisers always halt'], answer: 1,
    whyNot: ['They need not be: each may run for ever on strings outside its language.', null, 'No fixed bound is known in advance.', 'A recogniser may run for ever on strings outside its language.'],
    solution: 1, wrong: [0, 3],
    hints: H('Where is w: in L, or in the complement?', 'Whichever it is, the matching recogniser accepts after finitely many of its own steps.', 'Exactly one accepts in finite time, and taking turns means it gets those steps.') });
  classify({ id: 'comp-x-class-atm', chapter: 'comp-recognisable', title: 'Classify: A_TM',
    text: 'Classify A_TM = { ⟨M, w⟩ : M accepts w }.', answer: 1,
    why: 'Simulating M is a recogniser; it is undecidable, so it cannot also be co-recognisable.',
    hints: H('Finite evidence for "M accepts w"?', 'The accepting run. Finite evidence for "M does not accept w"?', 'Recognisable, not co-recognisable.') });
  classify({ id: 'comp-x-class-etm', chapter: 'comp-recognisable', title: 'Classify: E_TM', level: 2,
    text: 'Classify E_TM = { ⟨M⟩ : L(M) = ∅ }.', answer: 2,
    why: 'Its complement (M accepts something) is recognisable by dovetailing; E_TM itself is undecidable, so it is not recognisable.',
    hints: H('What would prove that M accepts nothing? Is that finite?', 'What would prove that M accepts something?', 'Co-recognisable but not recognisable: a no-instance has a witness (a string M accepts).') });
  classify({ id: 'comp-x-class-coatm', chapter: 'comp-recognisable', title: 'Classify: M does not accept w', level: 2,
    text: 'Classify the complement of A_TM: { ⟨M, w⟩ : M does not accept w } (it rejects or runs for ever).', answer: 2,
    why: 'Its complement is A_TM, which is recognisable; it is not recognisable itself, or A_TM would be decidable.',
    hints: H('What is the complement of this language?', 'A_TM is recognisable, so this one is co-recognisable.', 'Co-recognisable, not recognisable.') });
  classify({ id: 'comp-x-class-eqtm', chapter: 'comp-recognisable', title: 'Classify: two machines, one language', level: 3,
    text: 'Classify EQ_TM = { ⟨M₁, M₂⟩ : L(M₁) = L(M₂) }.', answer: 3,
    why: 'Equal languages have no finite witness (they agree on infinitely many strings), and neither do unequal ones (the difference may be a string one machine never finishes on). Both A_TM and its complement reduce to it.',
    hints: H('A difference would be a string w in one language and not the other. Can you confirm "M₂ does not accept w" in finite time?', 'Neither side has finite evidence in general: reductions from A_TM and from its complement both land here.', 'Neither recognisable nor co-recognisable.') });
  classify({ id: 'comp-x-class-bounded', chapter: 'comp-recognisable', title: 'Classify: halts within 100 steps',
    text: 'Classify { ⟨M⟩ : M halts on the empty input within 100 steps }.', answer: 0,
    why: 'Simulate 100 steps and look: the bound makes it a decider.',
    whyNot: [null, 'Look at the number 100: how long can the check take?', 'Look at the number 100: how long can the check take?', 'Look at the number 100: how long can the check take?'],
    hints: H('How long does it take to check?', 'Simulate at most 100 steps.', 'Decidable: the bound turns an open-ended search into a finite one.') });
  classify({ id: 'comp-x-class-total', chapter: 'comp-recognisable', title: 'Classify: halts on everything', level: 3,
    text: 'Classify TOTAL = { ⟨M⟩ : M halts on every input }.', answer: 3,
    why: 'Yes-instances would need infinitely many halting runs; a no-instance needs an endless run, which is not finite either.',
    hints: H('What would prove that M halts on every input? Finitely many runs?', 'What would prove M fails to halt on some input? Can you see "never" in finite time?', 'Neither: no finite evidence on either side.') });
  classify({ id: 'comp-x-class-finite', chapter: 'comp-recognisable', title: 'Classify: a finite language', level: 3,
    text: 'Classify FIN_TM = { ⟨M⟩ : L(M) is finite }.', answer: 3,
    why: 'No finite run shows the language stops growing, and no finite run shows it never stops. It is neither.',
    hints: H('Could a finite amount of evidence show that M accepts only finitely many strings?', 'And could finite evidence show it accepts infinitely many?', 'Neither recognisable nor co-recognisable.') });

  // =========================================================================================================
  // Chapter 4: reductions and Rice's theorem
  // =========================================================================================================
  C.lesson({
    id: 'comp-l-mapping', chapter: 'comp-reductions', title: 'A program that writes programs', minutes: 13,
    summary: 'A mapping reduction from A to B is a computable translation of A’s questions into B’s questions with the same answers. Its output is usually a new machine with the old one built in.',
    blocks: [
      'Once we know one problem is undecidable, we can spread the news. Suppose a decider for B existed. If we could translate every question about A into a question about B with the same answer, the B-decider would also decide A. If A is known to be undecidable, that is impossible, so B is undecidable too.',
      { def: 'Mapping reduction', text: 'A ≤ₘ B when there is a computable function f with x ∈ A ⇔ f(x) ∈ B for every string x.' },
      'The translation f must be computable: it must **always halt** with its output. That rules out running M on w inside f, because that might never finish. Instead f **writes down** a new machine that will run M on w later, when somebody runs the new machine.',
      { topic: 'red-transformer', input: { r: 'ATM-HALT', m: 'contains-11', w: '011' }, caption: 'A_TM ≤ HALT: from ⟨M, w⟩ the reduction writes M′, which runs M on its input and loops wherever M would reject. Watch the reduction finish before M′ ever runs.' },
      { predict: { q: 'M rejects w. What does the new machine M′ do on w?', options: ['It rejects too', 'It loops for ever', 'It accepts'], answer: 1, explain: 'M′ copies M but turns every rejection into an endless loop. So M′ halts on w exactly when M accepts w: ⟨M, w⟩ ∈ A_TM ⇔ ⟨M′, w⟩ ∈ HALT.' } },
      { h: 'Machines whose language is a switch' },
      'A favourite pattern: the new machine ignores its own input, or uses it only after a check. Then its whole language is one of two things, depending on whether M accepts w.',
      { topic: 'red-transformer', input: { r: 'ATM-REGULAR', m: 'anbn', w: 'ab' }, caption: 'A_TM ≤ REGULAR: M′ accepts strings of the form aⁿbⁿ straight away, and accepts everything else only if M accepts w. So L(M′) is all strings (regular) or just aⁿbⁿ (not regular).' },
      { predict: { q: 'In this reduction, what is L(M′) when M does **not** accept w?', options: ['All strings', 'The aⁿbⁿ strings only', 'The empty language'], answer: 1, explain: 'The second branch never accepts, so only the strings let in by the first check remain: aⁿbⁿ, which is not regular.' } },
      { tip: 'The test bench at the end of each reduction tries the new machine on sample inputs. It is a sanity check, not part of the reduction: the reduction itself never runs anything.' },
      { list: ['A ≤ₘ B: a computable f with x ∈ A ⇔ f(x) ∈ B.', 'f must always halt, so it writes a machine instead of running one.', 'The new machine’s language is a switch flipped by whether M accepts w.', 'If A is undecidable and A ≤ₘ B, then B is undecidable.'] },
      { exercise: 'comp-x-pick-f' }, { exercise: 'comp-x-switch-lang' }, { exercise: 'comp-x-flaw-run-inside' },
    ],
  });

  C.lesson({
    id: 'comp-l-direction', chapter: 'comp-reductions', title: 'Which way does the arrow point?', minutes: 10,
    summary: 'A ≤ B means A is no harder than B. Easiness flows backwards along the arrow; hardness flows forwards. Pointing it the wrong way proves nothing.',
    blocks: [
      'The most common mistake in this whole subject is a reduction pointed the wrong way. Let us make the direction impossible to forget.',
      'Read A ≤ B as "A is **no harder than** B": a solver for B can be used to solve A. Then the two rules are common sense:',
      { list: ['If B is easy (decidable), A is easy too: easiness flows **backwards**, from B to A.', 'If A is hard (undecidable), B is hard too: hardness flows **forwards**, from A to B.'] },
      { topic: 'red-direction', input: { c: 'atm-halt' }, caption: 'Right way: A_TM ≤ HALT. The known-hard problem is on the left, the problem we want to prove hard on the right. Watch hardness travel along the arrow.' },
      { predict: { q: 'You want to prove that a new problem NEW is undecidable. Which do you show?', options: ['NEW ≤ A_TM', 'A_TM ≤ NEW'], answer: 1, explain: 'The known-hard problem goes on the left. Showing NEW ≤ A_TM would only say that NEW is no harder than A_TM, which even an easy problem satisfies.' } },
      { topic: 'red-direction', input: { c: 'adfa-atm' }, caption: 'Wrong way: A_DFA ≤ A_TM is true, but A_DFA is decidable. Reducing an easy problem to a hard one proves nothing about either.' },
      { h: 'Complements travel too' },
      'If f reduces A to B, the same f reduces the complement of A to the complement of B, since x ∈ A ⇔ f(x) ∈ B is the same as x ∉ A ⇔ f(x) ∉ B. So recognisability also flows backwards: if A ≤ₘ B and B is recognisable, so is A.',
      { topic: 'red-direction', input: { c: 'atm-etm' }, caption: 'A_TM reduces to the complement of E_TM, not to E_TM itself. Watch why the complement is needed.' },
      { warn: 'A_TM ≤ₘ E_TM is impossible: the complement of A_TM would then reduce to the complement of E_TM, which is recognisable, making the complement of A_TM recognisable. Mapping reductions cannot always swap yes and no.' },
      { list: ['A ≤ B: A is no harder than B.', 'Decidable and recognisable flow backwards (from B to A).', 'Undecidable flows forwards: to prove NEW undecidable, show KNOWN ≤ NEW.', 'f reduces A to B ⇔ f reduces Ā to B̄.'] },
      { exercise: 'comp-x-dir-prove' }, { exercise: 'comp-x-dir-conclude' }, { exercise: 'comp-x-dir-backwards' }, { exercise: 'comp-x-flaw-direction' }, { exercise: 'comp-x-dir-etm' },
    ],
  });

  C.lesson({
    id: 'comp-l-oracle', chapter: 'comp-reductions', title: 'Ask the oracle', minutes: 9,
    summary: 'A Turing reduction may ask a magic box many questions and use the answers freely. It is more generous than a mapping reduction, and measures what is decidable "given" another problem.',
    blocks: [
      'Imagine a sealed box that answers one question instantly: "does M accept w?". Nobody can build it, but we can ask what we could do **if** we had it. A machine allowed to consult such a box is an **oracle machine**.',
      { def: 'Turing reduction', text: 'A ≤_T B when some oracle machine with an oracle for B decides A. It may ask any number of questions and do anything with the answers, including negating them.' },
      { topic: 'red-turing', input: { c: 'co-atm', m: 'aa-recogniser', w: 'ab' }, caption: 'The complement of A_TM with an A_TM oracle: ask once, then say the opposite. One question and a negation, which a mapping reduction cannot do.' },
      { predict: { q: 'With an oracle for A_TM, can you decide HALT?', options: ['No, HALT is undecidable', 'Yes: build M′ that accepts whenever M halts, and ask the oracle about ⟨M′, w⟩'], answer: 1, explain: 'Undecidable means no ordinary machine decides it. With the A_TM box, M′ = "run M; accept whether it accepts or rejects" turns halting into accepting.' } },
      { topic: 'red-turing', input: { c: 'etm', m: 'anbn', w: '' }, caption: 'E_TM with an A_TM oracle: build a machine that dovetails over all strings and accepts as soon as M accepts any, then ask about it once.' },
      'Every mapping reduction is a Turing reduction that asks exactly one question and passes the answer on unchanged. Turing reductions are coarser: they treat a problem and its complement as equally hard. So when you need to separate recognisable from co-recognisable, use mapping reductions.',
      { tip: 'Oracles do not end undecidability: the halting problem for machines **with** an A_TM oracle is undecidable again, by the same D argument. There is a whole ladder of ever harder problems.' },
      { list: ['An oracle answers a fixed problem in one step.', 'A ≤_T B: an oracle for B lets a machine decide A.', 'Turing reductions may ask many questions and negate answers.', 'A and its complement are Turing-equivalent, though not mapping-equivalent in general.'] },
      { exercise: 'comp-x-turing-vs-map' }, { exercise: 'comp-x-oracle-which' },
    ],
  });

  C.lesson({
    id: 'comp-l-rice', chapter: 'comp-reductions', title: 'Rice’s theorem: a two-question recipe', minutes: 12,
    summary: 'Any non-trivial question about the language a machine recognises is undecidable. Two questions tell you whether the theorem applies.',
    blocks: [
      'After a few reductions a pattern appears: does L(M) contain 1? Is L(M) empty? Is L(M) regular? Every one of them falls to the same construction. Rice’s theorem says it once for all of them.',
      { def: 'Rice’s theorem', text: 'let 𝒫 be a property of recognisable languages that some recognisable language has and some does not. Then { ⟨M⟩ : L(M) has 𝒫 } is undecidable.' },
      'Using it is a recipe with two questions:',
      { steps: ['**Semantic?** Does the answer depend only on L(M), the language? Test it: could two machines with the same language get different answers? If yes, Rice does not apply.', '**Non-trivial?** Is there one machine whose language has the property and one whose language does not? If every language has it, or none does, it is trivially decidable.', 'Both yes: undecidable, by Rice’s theorem.'] },
      { topic: 'rice-classify', input: { p: 'has-1' }, caption: '"L(M) contains the string 1". Watch both questions being answered with real machines as witnesses.' },
      { predict: { q: 'Property: "M has at most 3 states". Does Rice’s theorem apply?', options: ['Yes, it is non-trivial', 'No: two machines with the same language can have 3 and 30 states'], answer: 1, explain: 'It is about the machine, not its language: add useless states and the language stays the same while the answer changes. (It is also plainly decidable: count the states.)' } },
      { topic: 'rice-classify', input: { p: 'states' }, caption: 'The state-count property fails the first question. Watch the two machines with the same language and different answers.' },
      { warn: 'Rice not applying does not mean decidable. "M halts on input 01" is about behaviour, not the language (a machine can loop instead of rejecting without changing L(M)), so Rice is silent, yet it is undecidable by a direct reduction from HALT.' },
      { list: ['Semantic: depends only on L(M).', 'Non-trivial: some language has it, some does not.', 'Both: undecidable.', 'Not semantic or trivial: Rice says nothing, so decide it by other means.'] },
      { exercise: 'comp-x-rice-contains' }, { exercise: 'comp-x-rice-states' }, { exercise: 'comp-x-rice-trivial' }, { exercise: 'comp-x-rice-regular' }, { exercise: 'comp-x-rice-steps' }, { exercise: 'comp-x-rice-reverse' }, { exercise: 'comp-x-rice-halts' }, { exercise: 'comp-x-flaw-rice' },
    ],
  });

  C.lesson({
    id: 'comp-l-rice-proof', chapter: 'comp-reductions', title: 'Rice’s theorem, built', minutes: 10,
    summary: 'The proof is one reduction from A_TM with a gate: the new machine first runs M on w, and only if that accepts does it behave like a machine with the property.',
    blocks: [
      'Here is the whole proof, as a machine you could write. Suppose the empty language does **not** have the property 𝒫, and pick any machine T whose language does (non-triviality gives one). From ⟨M, w⟩ build:',
      { code: 'M_w, on input x:\n  1. run M on w   (if it rejects or loops, so does M_w)\n  2. if it accepted, run T on x and answer as T does', lang: 'machine' },
      'If M accepts w, the gate opens and L(M_w) = L(T), which has 𝒫. If not, M_w accepts nothing: L(M_w) = ∅, which lacks 𝒫. So ⟨M, w⟩ ∈ A_TM ⇔ ⟨M_w⟩ has 𝒫, and a decider for 𝒫 would decide A_TM.',
      { topic: 'rice-proof', input: { p: 'has-1', m: 'contains-11', w: '11' }, caption: 'M accepts w, so the gate opens and M_w copies T. Watch the test bench: M_w’s language has the property.' },
      { predict: { q: 'What if the empty language **does** have 𝒫?', options: ['The proof breaks and the property might be decidable', 'Run the same proof for the opposite property, which ∅ lacks; a property is decidable exactly when its opposite is'], answer: 1, explain: 'Deciding 𝒫 and deciding "not 𝒫" are the same task with answers swapped. So we may always assume ∅ lacks the property.' } },
      { topic: 'rice-proof', input: { p: 'empty', m: 'contains-11', w: '011' }, caption: 'The property "L = ∅" holds for ∅ itself, so the proof switches to its opposite. Watch the step where it says so.' },
      { list: ['Gate: M_w runs M on w first.', 'Then it behaves like T, whose language has the property.', 'L(M_w) is L(T) or ∅, flipped by whether M accepts w.', 'If ∅ has the property, prove it for the opposite property.'] },
      { exercise: 'comp-x-rice-gate' }, { exercise: 'comp-x-rice-empty-case' },
    ],
  });

  // ---- exercises, chapter 4 ----
  ex({ id: 'comp-x-pick-f', chapter: 'comp-reductions', title: 'Which translation reduces A_TM to HALT?', kind: 'choice', level: 2,
    text: 'Which function f is a mapping reduction from A_TM to HALT? (It must be computable, and ⟨M, w⟩ ∈ A_TM ⇔ f(⟨M, w⟩) ∈ HALT.)',
    options: ['f(⟨M, w⟩) = ⟨M, w⟩', 'f(⟨M, w⟩) = ⟨M′, w⟩, where M′ runs M and loops for ever wherever M would reject', 'f runs M on w and outputs a halting machine if M accepts, and a looping one otherwise', 'f(⟨M, w⟩) = ⟨M′, w⟩, where M′ runs M and accepts wherever M would reject'], answer: 1,
    whyNot: ['If M rejects w, then M halts on w: the pair is in HALT but not in A_TM.', null, 'f must always halt, and running M on w might not.', 'Then M′ halts whenever M halts, which again includes rejections.'],
    solution: 1, wrong: [0, 2],
    hints: H('The trouble with the identity: a machine that rejects has halted.', 'We need M′ to halt only when M accepts. What should M′ do instead of rejecting?', 'The second: M′ loops instead of rejecting, so it halts exactly when M accepts.') });
  ex({ id: 'comp-x-switch-lang', chapter: 'comp-reductions', title: 'What is the new machine’s language?', kind: 'choice', level: 2,
    text: 'From ⟨M, w⟩ a reduction writes M′: "On input x: if x = 0110, accept. Otherwise run M on w, and accept if it accepts." What is L(M′)?',
    options: ['{0110} if M accepts w, and all strings otherwise', 'All strings if M accepts w, and {0110} otherwise', 'Always {0110}', 'Empty if M does not accept w'], answer: 1,
    whyNot: ['It is the other way round: when M accepts w, every x gets through the second branch.', null, 'When M accepts w, the second branch accepts every other x as well.', '0110 is always accepted by the first line.'],
    solution: 1, wrong: [0, 3],
    hints: H('0110 is always accepted. What about other strings?', 'Other strings are accepted exactly when M accepts w.', 'All strings when M accepts w; just {0110} otherwise. A switch between a language that is everything and one that is not.') });
  ex({ id: 'comp-x-flaw-run-inside', chapter: 'comp-reductions', title: 'Spot the flaw: a reduction that runs M', kind: 'choice', level: 2,
    text: ['A fake proof that A_TM ≤ₘ E_DFA (which would make E_DFA undecidable, yet it is decidable):', { steps: ['Given ⟨M, w⟩, run M on w.', 'If M accepts, output a DFA with an empty language; otherwise output a DFA accepting everything.', 'Then ⟨M, w⟩ ∈ A_TM ⇔ the output is in E_DFA.'] }, 'What is wrong?'],
    options: ['Step 1: f must be computable, so it must always halt, and running M on w may not', 'Step 2: a DFA cannot have an empty language', 'Step 3: the equivalence is backwards', 'Nothing: E_DFA really is undecidable'], answer: 0,
    why: 'A reduction may not run the machine it is given; it writes a new machine that will do the running.',
    whyNot: [null, 'A DFA with no accepting states has an empty language.', 'The equivalence would be right, if f were computable.', 'E_DFA is decided by reachability.'],
    solution: 0, wrong: [1, 3],
    hints: H('What is required of the function f in a mapping reduction?', 'It must be computable: halt on every input with its output.', 'Step 1: running M on w might never finish, so this f is not computable.') });

  ex({ id: 'comp-x-dir-prove', chapter: 'comp-reductions', title: 'Which reduction do you need?', kind: 'choice',
    text: 'You want to prove that a problem NEWPROB is undecidable, using the fact that HALT is undecidable. What must you show?',
    options: ['NEWPROB ≤ₘ HALT', 'HALT ≤ₘ NEWPROB', 'Either one works', 'NEWPROB ≤ₘ A_DFA'], answer: 1,
    whyNot: ['That says NEWPROB is no harder than HALT; even easy problems are.', null, 'Only one direction carries hardness to NEWPROB.', 'That would show NEWPROB decidable.'],
    solution: 1, wrong: [0, 2],
    hints: H('A ≤ B reads "A is no harder than B".', 'Hardness flows forwards along the arrow, from the left to the right.', 'HALT ≤ₘ NEWPROB: the known-hard problem on the left.') });
  ex({ id: 'comp-x-dir-conclude', chapter: 'comp-reductions', title: 'What follows from EQ_DFA ≤ E_DFA?', kind: 'choice',
    text: 'We showed EQ_DFA ≤ₘ E_DFA (build the symmetric-difference DFA). E_DFA is decidable. What follows?',
    options: ['EQ_DFA is decidable', 'E_DFA is harder than EQ_DFA', 'Nothing', 'EQ_DFA is undecidable'], answer: 0,
    whyNot: [null, 'A ≤ B says the left side is no harder; it says nothing about B being harder.', 'Decidability flows backwards along the arrow.', 'Undecidability flows forwards, from left to right, and nothing on the left was known to be undecidable.'],
    solution: 0, wrong: [2, 3],
    hints: H('Which way does decidability flow?', 'Backwards: if the right side is decidable, so is the left.', 'EQ_DFA is decidable.') });
  ex({ id: 'comp-x-dir-backwards', chapter: 'comp-reductions', title: 'A student reduces to A_TM', kind: 'choice', level: 2,
    text: 'A student wants to show that PROB is undecidable, and proves PROB ≤ₘ A_TM. What has actually been shown?',
    options: ['PROB is undecidable', 'PROB is recognisable, and nothing about undecidability', 'PROB is decidable', 'PROB is not recognisable'], answer: 1,
    why: 'A_TM is recognisable, and recognisability flows backwards along the arrow. Hardness of A_TM tells nothing about PROB.',
    whyNot: ['The hard problem is on the right, so its hardness does not reach PROB.', null, 'A_TM is not decidable, so nothing decidable flows back.', 'Recognisability flows backwards from A_TM, so PROB is recognisable.'],
    solution: 1, wrong: [0, 2],
    hints: H('What does A_TM have that can flow backwards to PROB?', 'A_TM is recognisable.', 'Only that PROB is recognisable. To prove it undecidable, reduce A_TM to PROB.') });
  ex({ id: 'comp-x-flaw-direction', chapter: 'comp-reductions', title: 'Spot the flaw: the wrong direction', kind: 'choice', level: 2,
    text: ['A fake proof that E_DFA is undecidable:', { steps: ['Given a DFA D, build a Turing machine M_D that simulates D.', 'Then L(D) = ∅ exactly when L(M_D) = ∅, so E_DFA ≤ₘ E_TM.', 'E_TM is undecidable.', 'So E_DFA is undecidable.'] }, 'Which step fails?'],
    options: ['Step 1', 'Step 2', 'Step 3', 'Step 4: the reduction points the wrong way for this conclusion'], answer: 3,
    why: 'E_DFA ≤ E_TM only says E_DFA is no harder than E_TM. Hardness of the right side does not flow back.',
    whyNot: ['A Turing machine can simulate a DFA.', 'The equivalence holds, and the translation is computable.', 'E_TM is undecidable (by Rice).', null],
    solution: 3, wrong: [0, 2],
    hints: H('Each of steps 1 to 3 is true.', 'Look at the direction of the arrow and what flows along it.', 'Step 4: from E_DFA ≤ E_TM and E_TM undecidable, nothing follows about E_DFA.') });
  ex({ id: 'comp-x-dir-etm', chapter: 'comp-reductions', title: 'Why not A_TM ≤ₘ E_TM?', kind: 'choice', level: 3,
    text: 'The easy reduction from A_TM lands in the complement of E_TM. Why can there be no mapping reduction from A_TM to E_TM itself?',
    options: ['Because E_TM is decidable', 'It would give a mapping reduction from the complement of A_TM to the complement of E_TM, which is recognisable, so the complement of A_TM would be recognisable', 'Because E_TM is recognisable and A_TM is not', 'There can be; nobody has found it yet'], answer: 1,
    whyNot: ['E_TM is undecidable.', null, 'It is the other way round: A_TM is recognisable, E_TM is not.', 'It is provably impossible, not merely unknown.'],
    solution: 1, wrong: [0, 3],
    hints: H('A reduction from A to B is also one from the complement of A to the complement of B.', 'The complement of E_TM (accepts something) is recognisable. What would flow backwards?', 'Recognisability would flow back to the complement of A_TM, which is not recognisable. Contradiction.') });

  ex({ id: 'comp-x-turing-vs-map', chapter: 'comp-reductions', title: 'Turing, but not mapping', kind: 'choice', level: 2,
    text: 'Let Ā be the complement of A_TM. Which is true?',
    options: ['Ā ≤ₘ A_TM and Ā ≤_T A_TM', 'Ā ≤_T A_TM but not Ā ≤ₘ A_TM', 'Neither', 'Ā ≤ₘ A_TM but not Ā ≤_T A_TM'], answer: 1,
    why: 'With an A_TM oracle, ask and negate. A mapping reduction would make Ā recognisable, since A_TM is.',
    whyNot: ['A mapping reduction to A_TM would make Ā recognisable.', null, 'The oracle machine "ask once, answer the opposite" is a Turing reduction.', 'Every mapping reduction is a Turing reduction, so this is impossible.'],
    solution: 1, wrong: [0, 3],
    hints: H('What can an oracle machine do with the answer that a mapping reduction cannot?', 'Negate it. And recognisability flows backwards along mapping reductions.', 'Turing-reducible (ask and negate), but not mapping-reducible (Ā is not recognisable).') });
  ex({ id: 'comp-x-oracle-which', chapter: 'comp-reductions', title: 'What an A_TM oracle buys', kind: 'choice', level: 3,
    text: 'A machine may ask an oracle for A_TM. Which of these can it decide? Choose all that apply.',
    options: ['HALT', 'E_TM', 'The complement of A_TM', 'The halting problem for machines that themselves have an A_TM oracle'], answer: [0, 1, 2],
    solution: [0, 1, 2], wrong: [[0, 1, 2, 3], [0, 2]],
    hints: H('HALT: turn rejection into acceptance and ask. Complement: ask and negate.', 'E_TM: build a machine that dovetails and accepts if M accepts anything; ask whether it accepts ε.', 'The first three. The last is undecidable again, by the same diagonal argument one level up.') });

  rice({ id: 'comp-x-rice-contains', chapter: 'comp-reductions', title: 'Rice: contains 0110?',
    text: 'Property: "L(M) contains the string 0110". Does Rice’s theorem show { ⟨M⟩ : the property holds } undecidable?', answer: 0,
    hints: H('Do two machines with the same language agree on whether 0110 is in it?', 'Some machines accept 0110, some do not.', 'Yes: semantic and non-trivial.') });
  rice({ id: 'comp-x-rice-states', chapter: 'comp-reductions', title: 'Rice: an even number of states',
    text: 'Property: "M has an even number of states". Does Rice’s theorem show it undecidable?', answer: 1,
    hints: H('Add one unreachable state to a machine. What happens to its language? To the property?', 'The language is unchanged, the answer flips.', 'No: it is about the machine, not the language. (And it is decidable: count.)') });
  rice({ id: 'comp-x-rice-trivial', chapter: 'comp-reductions', title: 'Rice: recognisable language',
    text: 'Property: "L(M) is a recognisable language". Does Rice’s theorem show it undecidable?', answer: 2,
    hints: H('Which machines have this property?', 'L(M) is recognisable by M itself, for every M.', 'No: every machine has it, so it is trivial (always yes).') });
  rice({ id: 'comp-x-rice-regular', chapter: 'comp-reductions', title: 'Rice: a regular language', level: 2,
    text: 'Property: "L(M) is regular". Does Rice’s theorem show it undecidable?', answer: 0,
    hints: H('Two machines with the same language: same answer?', 'Some machines recognise regular languages (∅), some do not (aⁿbⁿ).', 'Yes: semantic and non-trivial.') });
  rice({ id: 'comp-x-rice-steps', chapter: 'comp-reductions', title: 'Rice: halts on ε within 50 steps', level: 2,
    text: 'Property: "M halts on the empty input within 50 steps". Does Rice’s theorem show it undecidable?', answer: 1,
    hints: H('Could two machines with the same language differ on this?', 'Pad a machine with 60 idle steps before it starts: same language, different answer.', 'No: not about the language. (It is decidable: simulate 50 steps.)') });
  rice({ id: 'comp-x-rice-reverse', chapter: 'comp-reductions', title: 'Rice: closed under reversal', level: 2,
    text: 'Property: "whenever L(M) contains w, it also contains w reversed". Does Rice’s theorem show it undecidable?', answer: 0,
    hints: H('Does the property mention anything but the language?', 'Palindromes have it; {ab} does not.', 'Yes: semantic and non-trivial.') });
  rice({ id: 'comp-x-rice-halts', chapter: 'comp-reductions', title: 'Rice: halts on 01', level: 3,
    text: 'Property: "M halts on input 01". Does Rice’s theorem show it undecidable?', answer: 1,
    why: 'Rice is silent, yet the problem is still undecidable, by a direct reduction from HALT.',
    hints: H('Does halting depend only on what is accepted?', 'A machine that loops on 01 and one that rejects 01 can have the same language.', 'No: it is about behaviour, not the language. It is still undecidable, but by reduction from HALT, not by Rice.') });
  ex({ id: 'comp-x-flaw-rice', chapter: 'comp-reductions', title: 'Spot the flaw: Rice on the machine', kind: 'choice', level: 2,
    text: ['A fake proof:', { steps: ['Let 𝒫 be the property "M has exactly five states".', 'Some machines have five states and some do not, so 𝒫 is non-trivial.', 'By Rice’s theorem, deciding 𝒫 is undecidable.'] }, 'What is wrong?'],
    options: ['Step 2: the property is trivial', 'Step 3: Rice’s theorem needs a property of the language L(M), and this is a property of the machine', 'Nothing: it is undecidable', 'Rice’s theorem only applies to DFAs'], answer: 1,
    why: 'The property is decidable: read the description and count the states.',
    whyNot: ['It is non-trivial, true; the trouble is elsewhere.', null, 'Count the states in ⟨M⟩: that is a decider.', 'It is a theorem about Turing machines.'],
    solution: 1, wrong: [0, 2],
    hints: H('Rice asks two questions. Was the first one checked?', 'Do two machines with the same language always have the same number of states?', 'Step 3: the property is not semantic, so Rice does not apply; and counting states decides it.') });
  ex({ id: 'comp-x-rice-gate', chapter: 'comp-reductions', title: 'Behind the gate', kind: 'choice', level: 2,
    text: 'In the proof of Rice’s theorem, M_w on input x first runs M on w, then runs T on x. Suppose M runs for ever on w. What is L(M_w)?',
    options: ['L(T)', '∅', 'All strings', 'L(M)'], answer: 1,
    whyNot: ['The second line is never reached.', null, 'Nothing is ever accepted.', 'M_w never answers based on M’s language.'],
    solution: 1, wrong: [0, 3],
    hints: H('Does M_w ever reach its second line?', 'It waits for M on w, for ever, on every input x.', '∅: M_w accepts nothing.') });
  ex({ id: 'comp-x-rice-empty-case', chapter: 'comp-reductions', title: 'When the empty language has the property', kind: 'choice', level: 3,
    text: 'The property 𝒫 is "L(M) has at most two strings". The empty language has it. How does the proof of Rice’s theorem go?',
    options: ['It cannot be applied, so 𝒫 might be decidable', 'Use the opposite property "more than two strings", which ∅ lacks; a decider for 𝒫 would give one for the opposite', 'Pick T with L(T) = ∅', 'Reduce from E_DFA instead'], answer: 1,
    whyNot: ['The proof adapts easily.', null, 'Then L(M_w) would be ∅ in both cases: the switch does nothing.', 'E_DFA is decidable, so reducing from it proves nothing.'],
    solution: 1, wrong: [0, 2],
    hints: H('Deciding 𝒫 and deciding its opposite are the same job.', 'The opposite property is not held by ∅.', 'Run the proof for "more than two strings", with T accepting all strings, say.') });

  // =========================================================================================================
  // Chapter 5: dominoes, grammars and tiles
  // =========================================================================================================
  C.lesson({
    id: 'comp-l-pcp', chapter: 'comp-puzzles', title: 'The domino puzzle', minutes: 12,
    summary: 'A puzzle a child could play: lay dominoes in a row so the top string equals the bottom string. No algorithm decides whether a set of dominoes has a solution.',
    blocks: [
      'Here is a puzzle with no machines in sight. You have a few kinds of dominoes, each with a string on top and a string on the bottom, and as many copies of each as you like. Lay some in a row. You win when the string along the top equals the string along the bottom.',
      { def: 'Post correspondence problem (PCP)', text: 'given dominoes (t₁/b₁), …, (tₖ/bₖ), is there a sequence i₁, …, iₙ with n ≥ 1 such that top(i₁) top(i₂) … top(iₙ) = bottom(i₁) bottom(i₂) … bottom(iₙ)? Such a sequence is a **match**.' },
      { topic: 'pcp-play', caption: 'Eight dominoes long. Watch the rows: one runs ahead, the other catches up, and they never disagree, until at the end they line up exactly.' },
      { predict: { q: 'A domino set where every top is longer than its bottom. Can it have a match?', options: ['Yes, if the symbols fit', 'No: the top row always ends up longer'], answer: 1, explain: 'The top row grows faster with every domino, so the two rows can never have the same length. Quick checks like this solve some instances, but not all.' } },
      { h: 'Searching, and why it may never end' },
      'A solver need not remember whole rows. After a partial match one row is a prefix of the other, and only the **overhang** (the extra part, and which row it is on) matters for what can come next. A breadth-first search over overhangs finds a shortest match if one exists.',
      { topic: 'pcp-search', caption: 'The search explores overhangs level by level, cutting dead ends where the rows clash and repeats it has seen before. Watch the overhangs it keeps.' },
      { topic: 'pcp-search', input: { d: ['a/aa', 'b/ab'], bound: 5 }, caption: 'Here the overhang keeps growing and never repeats, so the search has nothing to cut. With no bound it would run for ever.' },
      { predict: { q: 'So is PCP recognisable?', options: ['Yes: try all sequences, shortest first, and accept on a match', 'No'], answer: 0, explain: 'A match is a finite witness, and checking it is easy. PCP is recognisable and undecidable, so its complement ("no match exists") is not recognisable.' } },
      { list: ['Dominoes, unlimited copies, top row must equal bottom row.', 'Only the overhang matters; search over overhangs.', 'Some instances can be settled (lengths, first symbols); not all.', 'PCP is recognisable (a match is a witness) but undecidable.'] },
      { exercise: 'comp-x-pcp-three' }, { exercise: 'comp-x-pcp-four' }, { exercise: 'comp-x-pcp-five' }, { exercise: 'comp-x-pcp-seven' }, { exercise: 'comp-x-pcp-start' }, { exercise: 'comp-x-pcp-none' }, { exercise: 'comp-x-pcp-unary' },
    ],
  });

  C.lesson({
    id: 'comp-l-pcp-machine', chapter: 'comp-puzzles', title: 'A machine made of dominoes', minutes: 12,
    summary: 'Any machine and input can be turned into dominoes whose matches spell out an accepting computation. So a PCP solver would decide A_TM.',
    blocks: [
      'Why should a domino puzzle be as hard as the halting problem? Because the dominoes can be made to **write out a computation**. A match will spell #C₀#C₁#C₂#…, the configurations of a run, one after another.',
      'The trick is a lag. The bottom row is always one configuration ahead of the top. To catch up, the top must copy the configuration the bottom just wrote, and each domino that copies a cell near the head writes the **next** configuration’s version of it on the bottom. So the bottom is forced to compute.',
      { topic: 'pcp-tm', input: { m: 'flip', w: '01' }, caption: 'The machine flips 0s to 1s until it meets a 1. The first domino starts the bottom one configuration ahead; watch each round copy one configuration and produce the next.' },
      { predict: { q: 'The machine rejects its input. Can the dominoes still have a match?', options: ['Yes, the copy dominoes can always close it', 'No: only the accepting state has dominoes that let the top catch up'], answer: 1, explain: 'The top can catch up only through the "eat" and "finish" dominoes, and they exist only for the accepting state. No accepting configuration, no way to end level.' } },
      { h: 'Forcing the first domino' },
      'The construction needs the match to **start** with the special first domino. The modified puzzle (MPCP) demands exactly that. To turn it into the ordinary puzzle, hide stars between the symbols: on top a star before each symbol, on the bottom a star after each. Now no domino can begin a match, except a copy of domino 1 given one extra star in front on the bottom. A closing domino swallows the final star.',
      { topic: 'pcp-mpcp', caption: 'Stars are slipped between the symbols. Watch which domino is the only one whose top and bottom start with the same symbol.' },
      { math: 'A_TM  ≤ₘ  MPCP  ≤ₘ  PCP' },
      { tip: 'Both steps are computable rewritings that never run the machine: they just write dominoes. That is what makes them mapping reductions.' },
      { list: ['Matches spell the accepting computation #C₀#C₁#…', 'The bottom row runs one configuration ahead; copying forces computing.', 'Only accepting configurations let the top catch up.', 'Stars force the first domino: MPCP reduces to PCP.'] },
      { exercise: 'comp-x-mpcp-star' }, { exercise: 'comp-x-pcp-reject' },
    ],
  });

  C.lesson({
    id: 'comp-l-grammar-questions', chapter: 'comp-puzzles', title: 'Undecidable questions about grammars', minutes: 12,
    summary: 'Is a grammar ambiguous? Do two grammars generate the same strings? Dominoes hide inside both questions, so neither has an algorithm.',
    blocks: [
      'In chapter 1 grammars were friendly: membership and emptiness were decidable. Two natural questions are not. The domino puzzle is the bridge.',
      'Number the dominoes 1 to k, and treat the numbers as extra terminal symbols. Build two grammars: one spells the tops, followed by the domino numbers **in reverse**; the other spells the bottoms, likewise.',
      { code: 'dominoes 1 = ab/a, 2 = b/bb\nT → a b T 1 | b T 2 | a b 1 | b 2\nB → a B 1 | b b B 2 | a 1 | b b 2\nS → T | B', lang: 'grammar' },
      'Each grammar on its own is unambiguous: the numbers at the end record exactly which rules were used. A string has two parse trees in S → T | B only if both T and B generate it, which means the same sequence of dominoes gives the same top and bottom string: a match.',
      { topic: 'ugram-ambiguity', caption: 'A domino set turned into a grammar. When a match exists, one string gets two trees: watch the two derivations meet on the same string.' },
      { predict: { q: 'Dominoes 1 = ab/a and 2 = b/bb. The sequence 1, 2 is a match (abb on both rows). Which string has two parse trees in S → T | B?', options: ['abb12', 'abb21', 'abb'], answer: 1, explain: 'Both rows read abb, and the numbers come at the end in reverse order: 2 then 1. So abb21 is generated by T and by B.' } },
      { math: 'PCP ≤ₘ AMBIGUOUS_CFG' },
      { h: 'Are two grammars equal?' },
      'Listing the strings of two grammars, shortest first, finds a difference if there is one: inequality is recognisable. But if they are equal the search never ends. Equality of grammars is undecidable (the domino puzzle again, through the complement of a grammar language), and so is "does G generate every string?".',
      { topic: 'ugram-equivalence', input: { g1: 'S -> a S | a | ε', g2: 'S -> a S | a', n: 5 }, caption: 'The two grammars agree on every non-empty string and differ only on ε. Watch the listing find the difference at length 0.' },
      { editor: { kind: 'grammar', text: 'S -> a S b | S S | ε', tests: 'ε\nab\naabb\nabab\n-ba\n-aab' }, caption: 'Compare grammars by testing strings: change this grammar to S → a S b S | ε and run the tests. They agree here; can testing ever prove two grammars equal?' },
      { list: ['Decidable: membership, emptiness, finiteness.', 'Undecidable: ambiguity, equality of two grammars, generating every string.', 'Domino numbers written in reverse let two parse trees mean a match.', 'Inequality is recognisable (find a difference); equality is not.'] },
      { exercise: 'comp-x-bottom-grammar' }, { exercise: 'comp-x-two-trees' }, { exercise: 'comp-x-cfg-decide' }, { exercise: 'comp-x-cfg-equal-class' },
    ],
  });

  C.lesson({
    id: 'comp-l-tiling', chapter: 'comp-puzzles', title: 'Tiles that compute', minutes: 11,
    summary: 'Square tiles with coloured edges, never turned, touching edges matching. Rows of tiles can be forced to carry out a computation, so whether tiles cover the whole plane is undecidable.',
    blocks: [
      'Another puzzle: square tiles with a colour on each edge. Copy them as often as you like but never turn them, and place them so every pair of touching edges has the same colour. Can you fill the board?',
      { topic: 'tile-puzzle', caption: 'The solver fills cells left to right, top to bottom, and backs up when nothing fits. Watch the backtracks.' },
      { predict: { q: 'A set of tiles fills a 3 × 3 board. Must it also fill the same board wrapped round, where the right edge touches the left and the bottom touches the top?', options: ['Yes', 'No: the wrap adds new edges that must agree'], answer: 1, explain: 'Wrapping adds matching conditions between the first and last columns and rows. The next figure shows the same tiles failing on the wrapped board.' } },
      { topic: 'tile-puzzle', input: { wrap: 'torus' }, caption: 'The same four tiles on a wrapped board: the search runs out of choices.' },
      { h: 'Rows that count' },
      'Now design the colours so that each row **forces** the next. In the figure, the north edges of a row spell a binary number, a carry enters on the right, and the south edges spell the number plus one. Laying tiles row after row is running a counter.',
      { topic: 'tile-compute', caption: 'Each row is the previous number plus one. Watch the carry travel left through the 1s.' },
      { predict: { q: 'The board forbids a carry out of the left edge. A 2-bit counter starts at 01. How many rows can be laid?', options: ['As many as you like', 'Rows for 01, 10 and 11, then it is stuck', 'Only one'], answer: 1, explain: 'After 11, adding one would carry out of the left edge, which is forbidden: no tile fits and the tiling stops, exactly when the computation overflows.' } },
      { topic: 'tile-compute', input: { bits: 2, start: 1, rows: 5, over: 'none' }, caption: 'Overflow forbidden: watch the tiling get stuck on the row after 11.' },
      'The same idea, with tiles for a Turing machine’s configurations instead of a counter, makes tiling the **whole infinite plane** possible exactly when the machine runs for ever. So the tiling problem is undecidable. A finite board, on the other hand, can always be settled by search.',
      { list: ['Tiles: never turned, touching edges match.', 'A finite board is decidable by search (with backtracking).', 'Rows can be forced to compute the next configuration.', 'Tiling the whole plane ⇔ the machine never halts: undecidable.'] },
      { exercise: 'comp-x-tile-small' }, { exercise: 'comp-x-tile-wide' }, { exercise: 'comp-x-tile-big' }, { exercise: 'comp-x-tile-next-row' }, { exercise: 'comp-x-tile-class' },
    ],
  });

  // ---- exercises, chapter 5 ----
  pcpEx({ id: 'comp-x-pcp-three', chapter: 'comp-puzzles', title: 'Dominoes: a match of three', level: 1,
    intro: 'Find a match for these dominoes.', dominoes: ['a/bab', 'bb/b', 'b/ba'],
    solution: '2 1 2', wrong: ['2 1', '1 2', '2 1 3', '9'],
    why: 'Both rows read bbabb.',
    hints: H('Which dominoes can start a match? Their top and bottom must begin with the same symbol.', 'Domino 2 starts: bb over b, the top is ahead by b. Domino 1 puts bab under that b.', '2 1 2: the top reads bb·a·bb and the bottom b·bab·b, both bbabb.') });
  pcpEx({ id: 'comp-x-pcp-four', chapter: 'comp-puzzles', title: 'Dominoes: a match of four', level: 2,
    intro: 'Find a match for these dominoes.', dominoes: ['b/bab', 'b/a', 'ab/b'],
    solution: '1 3 2 3', wrong: ['1 3', '1 3 2', '3 1'],
    why: 'Both rows read babbab.',
    hints: H('Only domino 1 can start: its top and bottom both begin with b.', 'After domino 1 the bottom is ahead by ab. Domino 3 has ab on top.', '1 3 2 3: top b·ab·b·ab, bottom bab·b·a·b, both babbab.') });
  pcpEx({ id: 'comp-x-pcp-five', chapter: 'comp-puzzles', title: 'Dominoes: a match of five', level: 2,
    intro: 'Find a match for these dominoes. Keep track of the overhang: which row is ahead, and by what.', dominoes: ['a/ba', 'b/aba', 'aab/a'],
    solution: '3 3 1 2 1', wrong: ['3 1', '3 3 1', '1 3'],
    why: 'Both rows read aabaababa.',
    hints: H('Only domino 3 can start (a over a). The top is then ahead by ab.', 'Each next domino’s bottom must begin with the overhang. After 3 the overhang ab, top side; try 3 again.', '3 3 1 2 1: top aab·aab·a·b·a, bottom a·a·ba·aba·ba, both aabaababa.') });
  pcpEx({ id: 'comp-x-pcp-seven', chapter: 'comp-puzzles', title: 'Dominoes: a long match', level: 3,
    intro: 'These dominoes have a match of seven. The search topic can help you keep the overhangs straight.', dominoes: ['bbb/b', 'b/abb', 'a/bb'],
    solution: '1 3 2 2 3 1 1', wrong: ['1 3 2', '1 1 1', '1 3 2 2 3'],
    why: 'Both rows read bbbabbabbbbbb.',
    hints: H('Only domino 1 can start. Then the top is ahead by bb.', 'Write the overhang after each domino: after 1 the top is ahead by bb; after 3 it is ahead by a; keep going and watch for the moment it shrinks to nothing.', '1 3 2 2 3 1 1: top bbb·a·b·b·a·bbb·bbb, bottom b·bb·abb·abb·bb·b·b; both rows read bbbabbabbbbbb.') });
  ex({ id: 'comp-x-pcp-start', chapter: 'comp-puzzles', title: 'Which domino can start?', kind: 'string', set: true,
    text: ['A match must begin with a domino whose top and bottom agree as far as the shorter one goes. Which of these dominoes could be first in a match? Write their numbers as a set, like {1, 2}.', domTable(['ab/b', 'a/ab', 'ba/b', 'b/bab'])],
    answer: '{2, 4}', solution: '4, 2', wrong: ['{1, 2, 3, 4}', '{2}', '{1, 3}'],
    hints: H('Compare the first symbols of top and bottom.', 'For domino 2, a is a prefix of ab. For domino 4, b is a prefix of bab.', '{2, 4}. Dominoes 1 and 3 clash on their first symbol.') });
  ex({ id: 'comp-x-pcp-none', chapter: 'comp-puzzles', title: 'Which puzzles have no match?', kind: 'choice', level: 2,
    text: 'Which of these domino sets have no match at all? Choose all that apply.',
    options: ['aa/a, ab/b, b/ab', 'a/ba, b/ab', 'ab/a, ba/b', 'a/aa, ba/a'], answer: [1, 2, 3],
    solution: [1, 2, 3], wrong: [[1, 2], [0, 1, 2, 3], [2, 3]],
    hints: H('For each set, ask which domino could start, and whether the rows can ever have equal length.', 'In the second set no domino can start: the first symbols always clash. In the third every top is longer than its bottom. In the fourth only a/aa can start, and after it the bottom is ahead by a’s that only a/aa can follow, making it worse.', 'The second, third and fourth have no match. The first has the match 1 3: aa·b over a·ab, both aab.') });
  ex({ id: 'comp-x-pcp-unary', chapter: 'comp-puzzles', title: 'Dominoes over one letter', kind: 'choice', level: 3,
    text: 'If every domino uses only the letter a, the puzzle is decidable. Why?',
    options: ['Only lengths matter: a match exists iff some domino is balanced, or one has a longer top and another a longer bottom', 'Because a one-letter alphabet gives finitely many dominoes', 'It is not decidable: the reduction from A_TM works over any alphabet', 'Because the search always repeats an overhang within five steps'], answer: 0,
    why: 'With differences d > 0 and −e < 0, use the first e times and the second d times: the lengths balance.',
    whyNot: [null, 'Even with one letter there are infinitely many possible dominoes; the point is what a match needs.', 'The reduction needs at least two symbols to write configurations.', 'No such fixed bound holds; the real reason is about lengths.'],
    solution: 0, wrong: [2, 3],
    hints: H('With one letter, two strings are equal exactly when they have the same length.', 'Give each domino the number (top length − bottom length). A match is a choice of counts making the total zero.', 'The first option: either some domino has difference 0, or there are positive and negative differences, which can be balanced.') });
  ex({ id: 'comp-x-mpcp-star', chapter: 'comp-puzzles', title: 'Hide the stars', kind: 'string', level: 2,
    text: 'In the conversion from the modified puzzle to the ordinary one, every domino other than the special first one gets a star * before each symbol on top and after each symbol on the bottom. What does the domino ab/ba become? Answer as top/bottom.',
    answer: ['*a*b/b*a*'], solution: '*a*b / b*a*', wrong: ['a*b*/*b*a', '*a*b/*b*a', '*a*b/b*a'],
    hints: H('Top: put * in front of each symbol.', 'Bottom: put * after each symbol.', '*a*b/b*a*.') });
  ex({ id: 'comp-x-pcp-reject', chapter: 'comp-puzzles', title: 'Dominoes for a machine that rejects', kind: 'choice', level: 2,
    text: 'The dominoes built from a machine M and input w have a match exactly when…',
    options: ['M halts on w', 'M accepts w', 'M rejects w', 'M runs for ever on w'], answer: 1,
    whyNot: ['Halting by rejecting gives no match: there are no dominoes to finish from a rejecting state.', null, 'Rejecting configurations give the top no way to catch up.', 'An endless run never lets the rows end level.'],
    solution: 1, wrong: [0, 2],
    hints: H('Which dominoes let the top row catch up with the bottom?', 'The "eat" and "finish" dominoes, which exist only for the accepting state.', 'Exactly when M accepts w.') });

  ex({ id: 'comp-x-bottom-grammar', chapter: 'comp-puzzles', title: 'The grammar of the bottoms', kind: 'grammar', alphabet: ['a', 'b', '1', '2'], level: 2,
    text: ['Dominoes: 1 = *ab/a*, 2 = *b/bb*. The grammar of the tops is shown. Write the grammar of the **bottoms**: every non-empty sequence of dominoes, with the bottom strings in order followed by the domino numbers in reverse order.', { code: 'T → a b T 1 | b T 2 | a b 1 | b 2', lang: 'grammar' }],
    ref: 'B -> a B 1 | b b B 2 | a 1 | b b 2',
    solution: 'B -> X 1 | Y 2\nX -> a B | a\nY -> b b B | b b',
    wrong: ['B -> a B 1 | b b B 2 | ε', 'B -> a b B 1 | b B 2 | a b 1 | b 2', 'B -> 1 a B | 2 b b B | 1 a | 2 b b'],
    hints: H('Copy the shape of T, but use the bottom strings.', 'Domino 1’s bottom is a, domino 2’s is bb. A sequence of one domino is a base case.', 'B → a B 1 | b b B 2 | a 1 | b b 2.') });
  ex({ id: 'comp-x-two-trees', chapter: 'comp-puzzles', title: 'The string with two trees', kind: 'string', level: 2,
    text: ['With the dominoes 1 = *aa/a*, 2 = *b/ab*, the match 1, 2 gives *aab* on both rows. In the grammar S → T | B built from them (numbers in reverse at the end), which string has two parse trees?'],
    answer: ['aab21'], solution: 'aab21', wrong: ['aab12', 'aab', '21aab'],
    hints: H('Write the rows first, then the numbers.', 'The numbers come at the end, in reverse order of the sequence.', 'aab21.') });
  ex({ id: 'comp-x-cfg-decide', chapter: 'comp-puzzles', title: 'Grammar questions: which have algorithms?', kind: 'choice', level: 2,
    text: 'Which of these questions about context-free grammars are decidable? Choose all that apply.',
    options: ['Does G generate the string abba?', 'Is L(G) empty?', 'Is G ambiguous?', 'Do G₁ and G₂ generate the same language?', 'Is L(G) infinite?', 'Does G generate every string over its alphabet?'], answer: [0, 1, 4],
    solution: [0, 1, 4], wrong: [[0, 1], [0, 1, 2, 4], [0, 1, 3, 4]],
    hints: H('Membership and emptiness were in chapter 1.', 'Infinite: in Chomsky normal form (after cleaning up), is there a cycle among the useful variables?', 'Membership, emptiness and infiniteness are decidable; ambiguity, equality and "everything" are not.') });
  classify({ id: 'comp-x-cfg-equal-class', chapter: 'comp-puzzles', title: 'Classify: equal grammars', level: 3,
    text: 'Classify EQ_CFG = { ⟨G₁, G₂⟩ : L(G₁) = L(G₂) }.', answer: 2,
    why: 'Inequality has a finite witness (a string in one and not the other, checked by CYK), so EQ_CFG is co-recognisable; it is undecidable, so it is not recognisable.',
    hints: H('What finite evidence shows two grammars differ?', 'One string, and membership in a grammar is decidable.', 'Co-recognisable, not recognisable.') });

  tileEx({ id: 'comp-x-tile-small', chapter: 'comp-puzzles', title: 'Tile a 2 × 2 board', level: 1,
    intro: 'Fill a 2 × 2 board with these tiles (repeats allowed, no turning) so that every pair of touching edges has the same colour. The outer edges may be any colour.', tiles: ['0110', '2212', '2022', '1012'], w: 2, h: 2,
    solution: '3 1 / 2 4', wrong: ['1 3 / 2 4', '3 1 / 4 2', '1 2 3'],
    hints: H('Start with the top-left cell, then find a tile whose west edge matches its east edge.', 'Tile 3 has east green; only tile 1 has west green… check tile 1’s west edge.', '3 1 / 2 4: row 1 is tile 3 then tile 1, row 2 is tile 2 then tile 4.') });
  tileEx({ id: 'comp-x-tile-wide', chapter: 'comp-puzzles', title: 'Tile a 3 × 2 board', level: 2,
    intro: 'Fill a board 3 tiles wide and 2 tiles high with these tiles so that every pair of touching edges agrees. There is exactly one way.', tiles: ['0122', '0201', '0022', '2110'], w: 3, h: 2,
    solution: '2 1 2 / 3 4 2', wrong: ['2 1 2 / 2 1 2', '1 2 1 / 3 4 2', '2 1 / 3 4'],
    hints: H('In a row, each tile’s west edge must equal the east edge of the tile before it.', 'Row 1 alternates tiles 2 and 1. The south edges of row 1 decide the north edges of row 2.', '2 1 2 / 3 4 2.') });
  tileEx({ id: 'comp-x-tile-big', chapter: 'comp-puzzles', title: 'Tile a 3 × 3 board', level: 3,
    intro: 'Fill a 3 × 3 board with these five tiles so that every pair of touching edges agrees. There is exactly one way. Work row by row, and back up when you get stuck.', tiles: ['0122', '2221', '0001', '1210', '2112'], w: 3, h: 3,
    solution: '2 1 3 / 5 2 1 / 4 5 2', wrong: ['2 1 3 / 5 2 1 / 4 5 1', '1 3 1 / 5 2 1 / 4 5 2', '2 1 3 / 5 2 1'],
    hints: H('Write each tile as (north, east, south, west). Which tiles can follow which in a row?', 'The middle row must have north edges equal to the south edges of the top row. Try 2 1 3 on top.', '2 1 3 / 5 2 1 / 4 5 2.') });
  ex({ id: 'comp-x-tile-next-row', chapter: 'comp-puzzles', title: 'The next row of the counter', kind: 'string',
    text: 'In the counting tiles, the north edges of a row spell a binary number and the south edges spell that number plus one. A 5-bit row has north edges 01011. What do its south edges spell?',
    answer: ['01100'], solution: '01100', wrong: ['01010', '11011', '1100'],
    hints: H('Add one in binary.', 'The carry turns the trailing 1s into 0s and the first 0 into 1.', '01011 + 1 = 01100.') });
  ex({ id: 'comp-x-tile-class', chapter: 'comp-puzzles', title: 'Finite boards and the plane', kind: 'choice', level: 2,
    text: 'Which statements are true? Choose all that apply.',
    options: ['Whether a tile set fills a given 5 × 5 board is decidable', 'Whether a tile set fills the whole infinite plane is undecidable', 'Whether a tile set fills the plane is decidable, by trying ever larger boards', 'If a tile set fills every n × n board, it fills the plane'], answer: [0, 1, 3],
    solution: [0, 1, 3], wrong: [[0, 1], [0, 2, 3]],
    hints: H('A finite board has finitely many fillings.', 'Trying larger boards detects failure (some board cannot be filled), but never confirms success.', 'The first, second and fourth. The fourth holds by a compactness argument: the third fails because success is never confirmed.') });

  // =========================================================================================================
  // Chapter 6: beyond the edge
  // =========================================================================================================
  C.lesson({
    id: 'comp-l-busy-beaver', chapter: 'comp-beyond', title: 'Busy beavers', minutes: 11,
    summary: 'Among machines with n states that halt on a blank tape, which runs longest? The answer grows faster than any computable function.',
    blocks: [
      'A contest: build a Turing machine with n states (plus a halting state), start it on a completely blank tape, and it must eventually halt. Whoever’s machine runs for the most steps wins. The winning number of steps is BB(n).',
      { sandbox: { kind: 'tm', text: BB2, input: '' }, caption: 'A 2-state contender. Run it from the blank tape and count the steps and the 1s it leaves behind.' },
      { topic: 'bb-hunt', input: { m: 'start A\nA, 0 -> B, 1, R\nA, 1 -> H, 1, L\nB, 0 -> B, 1, L\nB, 1 -> C, 0, R\nC, 0 -> C, 1, L\nC, 1 -> A, 1, L' }, caption: 'A 3-state champion, 21 steps. Watch the head sweep back and forth over its own growing trail.' },
      { predict: { q: 'Every n has finitely many n-state machines. So why can no program compute BB(n)?', options: ['There are too many machines to try', 'To take the maximum you must know which machines never halt, and that is the halting problem'], answer: 1, explain: 'Run them all: the halting ones finish, but at any moment some are still running, and you cannot tell the slow ones from the endless ones. Knowing BB(n) would settle exactly that.' } },
      'In fact if BB were computable, the halting problem on blank tape would be decidable: run M for BB(n) + 1 steps; if it has not halted by then, it never will. Turning this around, BB grows faster than **every** computable function, eventually.',
      { topic: 'bb-hunt', input: { m: 'start A\nA, 0 -> B, 1, R\nA, 1 -> B, 1, R\nB, 0 -> A, 0, L\nB, 1 -> H, 1, R' }, caption: 'A machine that bounces for ever. Small machines can be proved to loop by hand, one by one; the work explodes with n.' },
      { tip: 'BB(1) to BB(4) are small and known, and BB(5) has been settled by a long collective proof checked by computer. Each value is a finite fact, yet no single program produces them all.' },
      { list: ['BB(n): the most steps an n-state machine takes before halting, from a blank tape.', 'Each value is a definite number.', 'Computing BB would decide halting on blank tape.', 'BB eventually outgrows every computable function.'] },
      { exercise: 'comp-x-bb-build' }, { exercise: 'comp-x-bb-steps' }, { exercise: 'comp-x-bb-ones' }, { exercise: 'comp-x-flaw-bb' }, { exercise: 'comp-x-bb-decide' },
    ],
  });

  C.lesson({
    id: 'comp-l-kolmogorov', chapter: 'comp-beyond', title: 'How short can a description be?', minutes: 10,
    summary: 'A string is simple when a short program prints it. Most strings have no short program, and no program can find the shortest one.',
    blocks: [
      'Which is simpler: 011011011011011011 or 110100011011100101? Both have 18 symbols. The first is "011, six times", a description far shorter than the string. The second seems to have no pattern at all. That intuition has a precise form.',
      { def: 'Kolmogorov complexity', text: 'K(s) is the length of the shortest program (in a fixed programming language) that prints s and halts. Changing the language changes K by at most a constant.' },
      { topic: 'kolmo', caption: 'A periodic string. Watch each method of describing it, and how the repeat beats writing it out.' },
      { topic: 'kolmo', input: { s: '1101000110111001011010' }, caption: 'Coin flips. Every method costs about as much as the string itself.' },
      { predict: { q: 'How many binary strings of length 20 have a description shorter than 10 bits?', options: ['About half', 'At most 1023, out of over a million', 'All of them, with a clever enough language'], answer: 1, explain: 'There are only 2⁰ + 2¹ + … + 2⁹ = 1023 descriptions shorter than 10 bits, and each describes at most one string. So almost all strings are incompressible.' } },
      { h: 'Why K cannot be computed' },
      'Suppose a program could compute K. Then this short program would exist: "find the first string s with K(s) > 1 000 000, and print it". That program is a few hundred bits long plus the number, far shorter than a million bits, yet it prints a string whose shortest description is supposed to be longer than a million bits. Contradiction, so K is not computable.',
      { warn: 'Compressors give **upper bounds** on K. A program can never certify that a string has no shorter description.' },
      { list: ['K(s): the shortest program printing s.', 'Counting: most strings of length n need about n bits.', 'Compression gives upper bounds only.', '"The first string needing a long description" is itself a short description: K is not computable.'] },
      { exercise: 'comp-x-kolmo-count' }, { exercise: 'comp-x-kolmo-which' }, { exercise: 'comp-x-flaw-kolmo' },
    ],
  });

  C.lesson({
    id: 'comp-l-incompleteness', chapter: 'comp-beyond', title: 'True, but not provable', minutes: 9,
    summary: 'Proofs can be checked by a machine. If proofs could settle every true statement about machines halting, the halting problem would be decidable. So some truths have no proof.',
    blocks: [
      'A proof in a formal system is a finite string, and checking that a proof is correct is a mechanical task. So a machine can **list every theorem**: generate all strings, keep the valid proofs, print what they prove.',
      { topic: 'godel', input: { target: 'sum' }, caption: 'An everyday theorem appears in the list after enough proofs are checked. Watch the list grow.' },
      'Now take the statements "M does not halt on the blank tape". Suppose the system is sound (proves only true things) and complete for these statements (proves every true one). Then here is a decider for halting on blank tape:',
      { steps: ['Run M on the blank tape, and in turns, list the theorems.', 'If M halts, answer "halts".', 'If the list prints "M does not halt", answer "does not halt".'] },
      { predict: { q: 'Why does this decider always stop?', options: ['Because every machine halts eventually', 'Because either M halts (and the run sees it) or "M does not halt" is true, and then by completeness it is eventually listed'], answer: 1, explain: 'One of the two searches always succeeds, just like running a recogniser and a co-recogniser in turns. But halting is undecidable, so the assumption fails: some true statement "M does not halt" has no proof.' } },
      { topic: 'godel', input: { target: 'loops' }, caption: 'A machine that never halts. Its run never ends; the theorem list may never mention it either. Watch both searches carry on.' },
      { tip: 'This is an intuition for incompleteness, not the full theorem: the real result applies to arithmetic itself and builds a sentence that talks about its own provability.' },
      { list: ['Theorems of a formal system can be listed by a machine.', 'Sound and complete for non-halting would decide halting.', 'So some true "M never halts" statements are unprovable.', 'The self-referential sentence is the diagonal argument again.'] },
      { exercise: 'comp-x-godel-why' }, { exercise: 'comp-x-godel-sound' },
    ],
  });

  // ---- exercises, chapter 6 ----
  ex({ id: 'comp-x-bb-build', chapter: 'comp-beyond', title: 'A busy little beaver', kind: 'machine', machine: 'tm', alphabet: '1', tape: ['1'], level: 3,
    text: 'Build a Turing machine with two working states A and B, plus an accepting halt state H (at most 3 states in all). Started on the blank tape, it must halt in H leaving exactly four 1s in a row (and nothing else). Write the blank as _.',
    output: () => '1111', maxLen: -1, maxStates: 3, steps: 200,
    start: 'start: A\naccept: H\n',
    solution: BB2,
    wrong: ['start: A\naccept: H\nA, _ -> B, 1, R\nB, _ -> A, 1, R\nA, 1 -> H, 1, R', 'start: A\naccept: H\nA, _ -> A, 1, R', 'start: A\naccept: H\nA, _ -> B, 1, R\nB, _ -> C, 1, R\nC, _ -> D, 1, R\nD, _ -> H, 1, R'],
    hints: H('With two states you cannot simply write four 1s moving right: you would need four states. The head must turn back.', 'Let A write 1 and move right into B; let B write 1 and move left back into A. What happens when A then reads a 1?', 'A,_ → B,1,R; A,1 → B,1,L; B,_ → A,1,L; B,1 → H,1,R. It halts after 6 steps with 1111.') });
  ex({ id: 'comp-x-bb-steps', chapter: 'comp-beyond', title: 'Count the steps', kind: 'number', level: 2,
    text: ['Run this 3-state machine from a blank tape. How many steps does it take before it halts (count the step into H)?', { code: BB3, lang: 'machine' }, { sandbox: { kind: 'tm', text: BB3, input: '' }, caption: 'Step through it, or count by hand first.' }],
    answer: 14, solution: '14', wrong: ['13', '21', '6'],
    hints: H('Keep a list of (state, head position, symbol read).', 'The first five steps: A writes 1, B writes a blank and moves right, C writes 1 twice going left, then C on 1 goes back to A.', '14 steps: A B C C C A B B B B C C C A, the last one into H.') });
  ex({ id: 'comp-x-bb-ones', chapter: 'comp-beyond', title: 'Count the 1s', kind: 'number', level: 2,
    text: ['The same 3-state machine: how many 1s are on the tape when it halts?', { code: BB3, lang: 'machine' }],
    answer: 6, solution: '6', wrong: ['5', '4', '14'],
    hints: H('Run it to the end (14 steps).', 'Note that B writes a blank once at the start, which C later fills in.', '6: the cells from one left of the start to four right of it are all 1.') });
  ex({ id: 'comp-x-flaw-bb', chapter: 'comp-beyond', title: 'Spot the flaw: computing BB', kind: 'choice', level: 2,
    text: ['A fake program for BB(n):', { steps: ['List all machines with n states: there are finitely many.', 'Run them all on the blank tape, side by side.', 'When every machine that will halt has halted, take the largest step count.', 'Print it.'] }, 'Which step cannot be carried out?'],
    options: ['Step 1', 'Step 2', 'Step 3: the program cannot tell when the last halting machine has halted, since the others might be slow or endless', 'Step 4'], answer: 2,
    why: 'Knowing that moment is the same as knowing which machines never halt.',
    whyNot: ['Listing finitely many descriptions is easy.', 'Dovetailing finitely many runs is easy.', null, 'Printing is easy, once you have the number.'],
    solution: 2, wrong: [0, 1],
    hints: H('Which step needs to know the future?', 'At any moment some machines are still running. Will they halt?', 'Step 3: deciding that all halting machines are done is the halting problem.') });
  ex({ id: 'comp-x-bb-decide', chapter: 'comp-beyond', title: 'If BB were known', kind: 'choice', level: 2,
    text: 'Suppose someone tells you BB(4) = 107. How can you decide whether a given 4-state machine halts on the blank tape?',
    options: ['You cannot; halting is undecidable', 'Run it for 107 steps: if it has not halted by then, it never will', 'Run it for 4 steps', 'Check whether it has a halting state'], answer: 1,
    why: 'For a fixed n this is fine: a single number settles every n-state machine. What cannot exist is a program producing BB(n) for every n.',
    whyNot: ['Undecidability is about all machines at once; for one fixed n, knowing BB(n) settles it.', null, 'Machines may halt much later than step 4.', 'Having a halting state does not mean reaching it.'],
    solution: 1, wrong: [0, 3],
    hints: H('What does BB(4) bound?', 'Every 4-state machine that halts does so within BB(4) steps.', 'Run 107 steps; still running means running for ever.') });
  ex({ id: 'comp-x-kolmo-count', chapter: 'comp-beyond', title: 'How many short descriptions?', kind: 'number', level: 2,
    text: 'Descriptions are binary strings. How many binary strings have length less than 8 (including the empty string)? This bounds how many strings can have a description shorter than 8 bits.',
    answer: 255, solution: '255', wrong: ['256', '128', '8'],
    hints: H('Count the strings of each length 0, 1, …, 7.', '1 + 2 + 4 + … + 128.', '2⁸ − 1 = 255.') });
  ex({ id: 'comp-x-kolmo-which', chapter: 'comp-beyond', title: 'Which has the shortest description?', kind: 'choice',
    text: 'Each string below has 32 symbols. Which surely has a much shorter description than its length?',
    options: ['01101110010111011110001001101010', '00010001000100010001000100010001', '11010010011101000110101101100100', '10111000110100101100111010000111'], answer: 1,
    why: 'It is "0001, eight times".',
    solution: 1, wrong: [0, 2],
    hints: H('Look for a repeat.', 'One of them is a short block repeated.', 'The second: 0001 eight times.') });
  ex({ id: 'comp-x-flaw-kolmo', chapter: 'comp-beyond', title: 'Spot the flaw: an optimal compressor', kind: 'choice', level: 3,
    text: ['A fake claim: "Our compressor finds the shortest program for every string."', { steps: ['Given s, try all programs in order of length.', 'Run each one; the first that prints s is the shortest.', 'Output it.'] }, 'What is wrong?'],
    options: ['Step 1: there are infinitely many programs', 'Step 2: some shorter programs never halt, and you cannot tell which; waiting on them may never end, skipping them may skip the answer', 'Step 3: the output might be longer than s', 'Nothing: K is computable this way'], answer: 1,
    why: 'Run them in turns and you get upper bounds that improve over time, but never the knowledge that no shorter one will still finish.',
    whyNot: ['Programs shorter than |s| + c are finitely many: the search space is finite.', null, 'Printing s literally is always a candidate, so the shortest is at most about |s|.', 'K is not computable.'],
    solution: 1, wrong: [0, 3],
    hints: H('What happens when you run a program that never halts?', 'Can you tell a slow program from an endless one?', 'Step 2: it hides the halting problem.') });
  ex({ id: 'comp-x-godel-why', chapter: 'comp-beyond', title: 'Why some truths have no proof', kind: 'choice', level: 2,
    text: 'A formal system is sound and its proofs can be checked by machine. Which assumption, added to these, would make the halting problem on blank tape decidable?',
    options: ['The system proves every true statement of the form "M does not halt on the blank tape"', 'The system proves "M halts" for every halting M', 'The system has finitely many axioms', 'The system is consistent'], answer: 0,
    why: 'Halting runs show themselves; completeness for non-halting would give the other side. Both sides recognisable means decidable.',
    whyNot: [null, 'That side is already easy: run M and you see it halt.', 'This changes nothing about what can be listed.', 'Soundness already gives consistency.'],
    solution: 0, wrong: [1, 3],
    hints: H('Which side of the halting question is hard to confirm?', '"Halts" shows itself when the run stops. "Never halts" needs a proof.', 'The first: then search proofs and run M in turns; one of them finishes.') });
  ex({ id: 'comp-x-godel-sound', chapter: 'comp-beyond', title: 'Listing the theorems', kind: 'choice',
    text: 'Why can a machine list all theorems of a formal system whose proofs can be checked mechanically?',
    options: ['Because there are finitely many theorems', 'Generate every finite string in turn, check whether it is a valid proof, and print its conclusion if so', 'Because every true statement is a theorem', 'It cannot'], answer: 1,
    whyNot: ['There are infinitely many.', null, 'That is exactly what fails.', 'It can, by enumerating proofs.'],
    solution: 1, wrong: [0, 2],
    hints: H('A proof is a finite string.', 'Checking a proof is mechanical.', 'Enumerate strings, keep valid proofs, print their conclusions.') });

  // ---- a guided tour -------------------------------------------------------------------------------------------
  C.tour({
    id: 'comp-tour', title: 'Tour: the edge of computation', blurb: 'Where the undecidability material is, and how to use it.',
    steps: [
      { route: 'learn', target: '.part .chap-card[data-chapter="comp-decidable"]', text: 'Part 6 starts with questions a machine **can** settle, then crosses the line. Each chapter has lessons first, then exercises.' },
      { route: 'topic=halt-build-d', target: '#stageWrap', text: 'The halting proof, acted out: H is wrapped into D, and D is run on its own description.' },
      { target: '#btnPlay', text: 'Play the steps, or step one at a time. Every branch of the argument gets its own frames.' },
      { target: '#inputs', text: 'Change the inputs: pick one branch, or give H a real strategy and watch exactly where it goes wrong.' },
      { route: 'topic=red-direction', target: '#stageWrap', text: 'Reductions point one way. This topic shows which way hardness and decidability travel along the arrow.' },
      { route: 'topic=pcp-play', target: '#inputs', text: 'The domino puzzle. Type your own dominoes and your own sequence, and watch the rows agree or clash.' },
      { route: 'lesson=comp-l-rice', target: '.ls-predict', text: 'In lessons, answer the prediction before reading on. Guessing first makes the explanation stick.' },
      { route: 'exercise=comp-x-pcp-three', target: '#answer', text: 'Exercises are checked at once. For dominoes, type the sequence; the checker lays the rows and tells you where they clash.' },
      { target: '#btnHint', text: 'Stuck? Hints come one at a time; the last one is a worked answer.' },
    ],
  });

  // ---- a course ------------------------------------------------------------------------------------------------
  C.course({
    id: 'comp-course', title: 'Course: what machines cannot do', blurb: 'From deciders that always answer, through the halting problem and reductions, to dominoes, tiles and busy beavers.',
    steps: [
      { topic: 'dec-adfa', note: 'A decider that cannot get stuck: one move per symbol.' },
      { topic: 'dec-edfa', note: 'Emptiness is reachability: watch the marks stop spreading.' },
      { topic: 'dec-eqdfa', note: 'Equality becomes emptiness of a product machine.' },
      { topic: 'dec-acfg', note: 'Chomsky normal form makes the search finite; watch the top cell of CYK.' },
      { topic: 'dec-ecfg', note: 'Marks flow backwards from terminals to the start variable.' },
      { lesson: 'comp-l-questions', note: 'Deciders, recognisers and the Church–Turing thesis.' },
      { topic: 'halt-diagonal', note: 'The flipped diagonal differs from every row.' },
      { topic: 'halt-build-d', note: 'Whatever H predicts about D on ⟨D⟩, D does the opposite.' },
      { topic: 'halt-fool', note: 'Every real strategy is caught by its own D.' },
      { exercise: 'comp-x-flaw-simulate', note: 'Find the step a simulation can never take.' },
      { topic: 'rec-dovetail', note: 'Fair sharing of steps: no endless run blocks the rest.' },
      { topic: 'rec-both', note: 'Two recognisers in turns always answer.' },
      { exercise: 'comp-x-class-etm', note: 'Finite evidence for yes, for no, or neither?' },
      { topic: 'red-transformer', note: 'The reduction writes a machine and never runs it.' },
      { topic: 'red-direction', note: 'Hardness flows forwards, decidability backwards.' },
      { exercise: 'comp-x-dir-prove', note: 'Point the arrow the right way.' },
      { topic: 'red-turing', note: 'An oracle may be asked many times, and its answer negated.' },
      { topic: 'rice-classify', note: 'Two questions: about the language? non-trivial?' },
      { topic: 'rice-proof', note: 'The gate: run M on w first, then behave like T.' },
      { exercise: 'comp-x-rice-states', note: 'A property of the machine, not its language.' },
      { topic: 'pcp-play', note: 'Rows that run ahead, catch up, and finally agree.' },
      { topic: 'pcp-search', note: 'Only the overhang matters.' },
      { exercise: 'comp-x-pcp-four', note: 'Solve one yourself.' },
      { topic: 'pcp-tm', note: 'The bottom row computes one configuration ahead.' },
      { topic: 'ugram-ambiguity', note: 'Two parse trees are a match in disguise.' },
      { topic: 'tile-compute', note: 'Each row of tiles is the next step of a counter.' },
      { exercise: 'comp-x-tile-small', note: 'Fill a board by hand.' },
      { topic: 'bb-hunt', note: 'Small machines, enormous running times.' },
      { topic: 'kolmo', note: 'A short description, or none at all.' },
      { topic: 'godel', note: 'A sound, complete proof system would decide halting.' },
    ],
  });
})();
