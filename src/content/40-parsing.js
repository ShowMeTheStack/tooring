// Part 4, Parsing: chapters, lessons, exercises, a tour and a course. The order follows a natural path:
// parsing by trial and error first (backtracking, packrat), then removing the guesswork top down (FIRST,
// FOLLOW, LL(1)), then bottom up (shift-reduce and the LR family), then the general algorithms that take any
// grammar (CYK, Earley), and last operator precedence and a tiny front end that ties lexer and parser
// together. Every grammar, word and machine here is our own.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content, K = T.Check;
  const H = (a, b, c) => [a, b, c];
  const ex = (x) => C.exercise(Object.assign({ level: 1 }, x));
  const gram = (text) => ({ code: text, lang: 'grammar' });

  // ---- checks this part needs beyond the language of a grammar ------------------------------------------
  // Grammar exercises here may add a requirement beyond the language: x.also(G) returns a sentence when
  // the student's grammar falls short (it must be LL(1), or mean the same when read as a PEG).
  const mustBeLL1 = (G) => {
    const t = T.ll.ll1Table(G);
    if (!t.conflicts.length) return null;
    return 'Your grammar generates the right strings, but it is not LL(1) yet. ' + t.conflicts[0].say;
  };
  const pegAgrees = (G) => {
    const d = T.parse.contrastPEG(G, 6);
    return d.length ? 'Your grammar generates the right strings, but read as a PEG it does not: ' + d[0].say : null;
  };

  // Item sets typed on one line, separated by semicolons: E → E - • P; P → • q. Arrows -> or →, dots • · or .
  const normItem = (s) => String(s).replace(/^\s*\[|\]\s*$/g, '').replace(/->/g, '→').replace(/[.·∙]/g, '•').replace(/\s+/g, '');
  const itemSet = (list) => [...new Set(list.map(normItem).filter(Boolean))].sort().join('\n');
  const itemsAccept = (want) => (text) => itemSet(String(text).split(';')) === itemSet(want);
  const cellAccept = (A, a) => (text) => {
    const t = String(text).replace(/\s+/g, ' ').trim().replace(/^M\s*\[\s*(.*?)\s*\]$/, '$1').replace(/^\(\s*(.*?)\s*\)$/, '$1');
    const m = /^(\S+?)\s*[,\s]\s*(\S+)$/.exec(t);
    return !!m && m[1] === A && m[2] === a;
  };

  // An LR table to fill in, built from the engine so the state numbers match what the student is shown.
  function lrExercise(g, kind) {
    const G = T.grammar.parse(g), t = T.lr.buildTable(G, kind, { precedence: false });
    const rows = t.states.map((s) => String(s.id)), cols = t.terminals.concat(t.nonterminals);
    const cells = {};
    for (const s of t.states) {
      for (const a of t.terminals) cells[s.id + '|' + a] = t.action[s.id] && t.action[s.id][a] ? T.lr.actionText(t.action[s.id][a]) : '';
      for (const A of t.nonterminals) cells[s.id + '|' + A] = t.goto[s.id] && t.goto[s.id][A] !== undefined ? String(t.goto[s.id][A]) : '';
    }
    const states = [['state', 'items']].concat(t.states.map((s) => [String(s.id), s.items.map((i) => T.lr.itemText(t.aug, i)).join(',   ')]));
    const rules = G.productions.map((p, i) => (i + 1) + '. ' + p.A + ' → ' + (p.rhs.length ? p.rhs.join(' ') : 'ε')).join('\n');
    return { G, t, rows, cols, cells, states, rules };
  }

  // ---- chapters -------------------------------------------------------------------------------------------
  C.chapter({ id: 'parse-ch-search', part: 'parsing', n: 1, title: 'Parsing by trial and error', blurb: 'Recursive descent that guesses and backs up, and packrat parsing, which commits to the first choice that works and remembers everything.' });
  C.chapter({ id: 'parse-ch-ll', part: 'parsing', n: 2, title: 'Top down without guessing: FIRST, FOLLOW and LL(1)', blurb: 'One symbol of lookahead picks the rule: FIRST and FOLLOW sets, the LL(1) table and its conflicts, rewriting grammars, generated parsers and recovery from errors.' });
  C.chapter({ id: 'parse-ch-lr', part: 'parsing', n: 3, title: 'Bottom up: shift-reduce and the LR family', blurb: 'Handles, items and the goto automaton, the LR(0), SLR(1), LALR(1) and LR(1) tables, precedence declarations, and which grammar each method takes.' });
  C.chapter({ id: 'parse-ch-general', part: 'parsing', n: 4, title: 'Parsing any grammar: CYK and Earley', blurb: 'Two algorithms that take every context-free grammar, ambiguous or left-recursive, and find all the trees.' });
  C.chapter({ id: 'parse-ch-front', part: 'parsing', n: 5, title: 'Operators and a tiny front end', blurb: 'Operator-precedence parsing with three relations between terminals, and a lexer and an LR parser working together on real source text.' });

  // =========================================================================================================
  // Chapter 1: parsing by trial and error
  // =========================================================================================================
  C.lesson({
    id: 'parse-l-backtrack', chapter: 'parse-ch-search', title: 'Recursive descent that guesses and backs up', minutes: 10,
    summary: 'One procedure per nonterminal, alternatives tried in order, and a rewind when a guess goes wrong.',
    blocks: [
      'A grammar tells you which strings belong to a language. A **parser** does more: given one string, it finds *how* the grammar builds it, the parse tree. Every compiler, every config-file reader and every calculator app starts with one.',
      'The most direct way to write a parser is to turn each nonterminal into a procedure. The procedure for S tries the right sides of S one after the other: a terminal must match the next input symbol, a nonterminal is a call to its own procedure. When something fails, rewind the input to where this attempt began and try the next alternative.',
      { def: 'Backtracking recursive descent', text: 'a top-down parser with one procedure per nonterminal that tries the alternatives of a rule in order, and on failure restores the input position and tries the next one. It succeeds when the start symbol\'s procedure consumes the whole input.' },
      { h: 'Watch it guess' },
      { topic: 'rd-backtrack', input: { g: 'S → A c | A d\nA → a b | a', w: 'abd', mode: 'full' }, frame: 8, caption: 'The call stack grows as procedures call each other. Watch for the moment A → a b has already succeeded and the parser still has to come back into A.' },
      { predict: { q: 'Grammar S → A c | A d, A → a b | a, input abd. The parser tries S → A c, and A → a b matches ab. Then c does not match d. What does a full backtracking parser do next?', options: ['It rejects the input', 'It re-enters A and tries A → a, then gives up on S → A c, then tries S → A d from the start', 'It skips the d and carries on'], answer: 1, explain: 'Every way of continuing has to be tried before the parser may move on to the next alternative of S. A → a leaves b where c is expected, which also fails, so it rewinds to the start and tries S → A d, where A → a b and then d succeed.' } },
      { h: 'The trap: undoing a call that already returned' },
      'A cheap version of backtracking only retries alternatives *inside* the procedure that is running. Once A has returned, its choice is frozen. That is simpler, but it rejects strings it should accept. Take S → A b, A → a b | a, on the input ab: A grabs ab, nothing is left for the b of S, and the frozen A never gets to try the shorter a.',
      { topic: 'rd-backtrack', input: { g: 'S → A b\nA → a b | a', w: 'ab', mode: 'limited' }, frame: 11, caption: 'Limited backtracking: A keeps its first success, so ab is wrongly rejected. Open the topic and switch to full backtracking to see it accepted.' },
      { warn: 'Left recursion sinks this method completely. With E → E + n | n, the procedure for E calls E again before reading anything, and again, forever. The topic refuses such grammars; a later lesson shows how to rewrite them.' },
      { h: 'Try it yourself' },
      { sandbox: { kind: 'grammar', text: 'S → A b\nA → a b | a', input: 'ab' }, caption: 'This sandbox finds the tree whatever it takes. Both ab and abb are in the language; the limited parser misses one of them.' },
      'Backtracking always works on a grammar without left recursion, but it can take exponential time: each failure can force a different combination of earlier choices to be retried. The rest of this part is about doing better: remembering results (packrat), or looking ahead so that there is nothing to undo (LL), or delaying decisions until the evidence is in (LR).',
      { list: ['One procedure per nonterminal; alternatives are tried in order.', 'Failure rewinds the input and tries the next alternative.', 'Full backtracking may have to undo calls that already returned; limited backtracking does not, and loses strings.', 'Left recursion makes it loop; the worst case is exponential time.'] },
      { exercise: 'parse-ex-bt-limited' },
      { exercise: 'parse-ex-bt-leftrec' },
    ],
  });

  C.lesson({
    id: 'parse-l-peg', chapter: 'parse-ch-search', title: 'Packrat parsing: commit to the first choice that works', minutes: 9,
    summary: 'Ordered choice and a memo table give linear time, but the grammar now means something different.',
    blocks: [
      'Backtracking is slow because it parses the same piece of input with the same nonterminal over and over. A **packrat** parser keeps a table: for each nonterminal and each input position, the result of the first attempt (failed, or succeeded and ended here). Ask again and the answer comes from the table.',
      'That only works if a nonterminal has *one* answer at each position. So the alternatives become an **ordered choice**: try the first; if it succeeds, that is the result, and the others are never tried, even if something later fails. A grammar read this way is a **parsing expression grammar** (PEG).',
      { def: 'Ordered choice', text: 'e₁ / e₂ tries e₁ at the current position; if e₁ succeeds its result is final; only if e₁ fails is e₂ tried at the same position.' },
      { topic: 'peg-packrat', input: { g: 'S → A c | A d\nA → a b | a', w: 'abd' }, caption: 'Each memo cell is filled once. The second time A is asked about position 0, the answer is read from the table instead of being worked out again.' },
      { predict: { q: 'As a PEG: S ← A b, A ← a b / a. Does it accept ab?', options: ['Yes, like the grammar does', 'No: A succeeds with a b and is never asked to try a'], answer: 1, explain: 'A\'s first choice succeeds and consumes ab. Ordered choice never revisits it, so S finds no b and fails. The context-free grammar generates ab; the PEG does not.' } },
      { topic: 'peg-packrat', input: { g: 'S → A b\nA → a b | a', w: 'ab' }, frame: 9, caption: 'The same grammar read as a PEG commits too early and rejects ab.' },
      { table: [['', 'context-free grammar', 'PEG'], ['alternatives', 'all are possible', 'the first that succeeds wins'], ['ambiguity', 'possible', 'impossible: one parse at most'], ['parsing time', 'cubic in general (CYK, Earley)', 'linear with a memo table'], ['left recursion', 'fine for CYK and Earley', 'loops, like recursive descent']], caption: 'Same notation, two meanings.' },
      { tip: 'Put the longer alternative first. A ← a b / a tries the longer match before the shorter one, which is usually what you mean.' },
      { h: 'Try it yourself' },
      { editor: { kind: 'grammar', text: 'S → A z\nA → y | y y', tests: 'yz\nyyz\n-z\n-yyyz' }, caption: 'As a grammar this accepts yz and yyz. Read as a PEG it accepts only one of them. Which order of A\'s alternatives makes the PEG agree?' },
      { list: ['A packrat parser memoises each (nonterminal, position) pair, so it runs in linear time.', 'The price is ordered choice: the first success is final.', 'A PEG is never ambiguous, but it may accept less than the grammar you wrote.', 'Longer alternatives usually go first.'] },
      { exercise: 'parse-ex-peg-accepts' },
      { exercise: 'parse-ex-peg-reorder' },
      { exercise: 'parse-ex-peg-facts' },
    ],
  });

  ex({ id: 'parse-ex-bt-limited', chapter: 'parse-ch-search', title: 'Full or limited backtracking?', kind: 'choice', level: 2,
    text: ['Take the grammar below, alternatives tried left to right, and the input pp.', gram('S → A p\nA → p p | p'), 'Which parser accepts pp?'],
    options: ['Both full and limited backtracking', 'Only full backtracking, which can go back into A after it returned', 'Only limited backtracking', 'Neither: pp is not in the language'],
    answer: 1, why: 'A → p p takes both p\'s and returns; S then needs one more p. Only a parser that may re-enter the finished call to A can try A → p.',
    solution: 1, wrong: [0, 3],
    hints: H('First check that pp is in the language at all: which derivation gives it?', 'A\'s first alternative succeeds and eats the whole input. What is left for the p in S → A p?', 'S ⇒ A p ⇒ p p, using A → p. Full backtracking finds it by re-entering A; limited backtracking keeps A → p p and rejects. Answer: only full backtracking.') });
  ex({ id: 'parse-ex-bt-leftrec', chapter: 'parse-ch-search', title: 'Which grammar loops?', kind: 'choice',
    text: 'A backtracking recursive-descent parser is given each of these grammars. On which of them can it call the same procedure forever without reading a symbol? Choose all of them.',
    options: ['L → L & t | t', 'L → t & L | t', 'S → A x | y, A → S z | w', 'S → x S | ε'],
    answer: [0, 2], why: 'Both are left-recursive: L directly, S indirectly through A (S calls A, A calls S, nothing read in between).',
    solution: [0, 2], wrong: [[0], [0, 1, 2]],
    hints: H('A loop without reading needs a procedure that can reach itself as the first thing it does.', 'Look for left recursion, including the indirect kind that goes through another nonterminal.', 'L → L & t is directly left-recursive; S → A x with A → S z is indirectly left-recursive. The other two read a t or an x before recursing.') });
  ex({ id: 'parse-ex-peg-accepts', chapter: 'parse-ch-search', title: 'What does the PEG accept?', kind: 'choice', level: 2,
    text: ['Read this grammar as a PEG, with the alternatives as an ordered choice:', gram('S → A z\nA → y | y y'), 'Which of these strings does the PEG accept? Choose all.'],
    options: ['yz', 'yyz', 'z', 'yyyz'],
    answer: [0], why: 'A always commits to its first choice y. So the PEG accepts exactly yz, while the grammar also generates yyz.',
    solution: [0], wrong: [[0, 1], [1]],
    hints: H('At position 0, A tries y first. When does that fail?', 'It fails only if the input does not start with y. Otherwise A is y and never y y.', 'Only yz: after A takes one y, the next symbol must be z.') });
  ex({ id: 'parse-ex-peg-reorder', chapter: 'parse-ch-search', title: 'Make the PEG agree', kind: 'grammar', level: 2, alphabet: 'yz',
    text: ['The grammar below generates yz and yyz, but read as a PEG it accepts only yz.', gram('S → A z\nA → y | y y'), 'Write a grammar for the same language that means the same thing when read as a PEG (ordered choice, top alternative first).'],
    ref: 'S -> A z\nA -> y | y y', also: pegAgrees,
    solution: 'S -> A z\nA -> y y | y', wrong: ['S -> A z\nA -> y | y y', 'S -> A z\nA -> y y'],
    hints: H('The problem is that A commits to y before trying y y.', 'Ordered choice should try the longer alternative first.', 'S → A z, A → y y | y. On yz, A tries y y, fails at z, then tries y.') });
  ex({ id: 'parse-ex-peg-facts', chapter: 'parse-ch-search', title: 'What the memo table buys', kind: 'choice', level: 1,
    text: 'A packrat parser stores, for every nonterminal and every input position, the result of the first attempt. With a fixed grammar, how does its running time grow with the length n of the input?',
    options: ['Linearly, in n', 'Like n³, as for CYK', 'Exponentially, as for backtracking', 'It may not finish on some inputs'],
    answer: 0, why: 'There are (number of nonterminals) × (n + 1) memo cells, each filled once with a bounded amount of work.',
    solution: 0, wrong: [1, 2],
    hints: H('Count the memo cells.', 'Each cell is computed at most once; afterwards it is only looked up.', 'Linear: a fixed number of nonterminals times n + 1 positions.') });

  // =========================================================================================================
  // Chapter 2: FIRST, FOLLOW and LL(1)
  // =========================================================================================================
  C.lesson({
    id: 'parse-l-first', chapter: 'parse-ch-ll', title: 'FIRST: how a phrase can begin', minutes: 12,
    summary: 'The terminals that can start a string derived from a symbol, computed round by round until nothing changes.',
    blocks: [
      'Backtracking guesses and pays for it. Could the parser *know* which alternative to take, just by looking at the next input symbol? It could, if every alternative announced which symbols it can begin with. That announcement is the FIRST set.',
      { def: 'FIRST(α)', text: 'for a string α of grammar symbols, the set of terminals that begin some string derived from α, together with ε if α can derive the empty string.' },
      'Three facts give all of FIRST:',
      { list: ['A terminal begins with itself: FIRST(a) = {a}.', 'For a rule A → X₁ X₂ … Xₖ, everything in FIRST(X₁) except ε is in FIRST(A). If X₁ can vanish (ε ∈ FIRST(X₁)), look at X₂ as well, and so on.', 'If every Xᵢ can vanish (or the right side is ε), then ε ∈ FIRST(A).'] },
      'The sets depend on each other, so we start them all empty and go through every rule again and again. A round that adds nothing means we are done: the sets can only grow, and there are finitely many terminals.',
      { topic: 'first-sets', input: { g: 'S → A B c\nA → a A | ε\nB → b | ε' }, caption: 'Watch FIRST(S): it takes a from A, then, because A can vanish, b from B, and because B can vanish too, c.' },
      { predict: { q: 'Grammar S → A B c, A → a A | ε, B → b | ε. Is ε in FIRST(S)?', options: ['Yes, because A and B can both vanish', 'No, because c can never vanish'], answer: 1, explain: 'S always ends with the terminal c, so every string S derives has at least one symbol. FIRST(S) = {a, b, c}.' } },
      { warn: 'A common slip: putting ε into FIRST(A) because *some* symbol on the right can vanish. ε goes in only when the *whole* right side can vanish.' },
      { h: 'FIRST of a string' },
      'The table we build next needs FIRST of whole right sides, not just of nonterminals. The rule is the same as for one rule: walk along the string, collect FIRST of each symbol without ε, and stop at the first symbol that cannot vanish. If you fall off the end, add ε.',
      { math: 'FIRST(B c)    = {b, c}\nFIRST(A B)    = {a, b, ε}\nFIRST(ε)      = {ε}' },
      { tip: 'Open the topic and type a grammar of your own: every round is shown, with the rule that added each symbol.' },
      { list: ['FIRST(α) says which terminals can start α, plus ε if α can vanish.', 'Compute it as a fixpoint: repeat over all rules until a round adds nothing.', 'Look past a symbol only when it can vanish.', 'ε ∈ FIRST(A) only when a whole right side of A can vanish.'] },
      { exercise: 'parse-ex-first-1' },
      { exercise: 'parse-ex-first-2' },
      { exercise: 'parse-ex-first-3' },
      { exercise: 'parse-ex-first-string' },
    ],
  });

  C.lesson({
    id: 'parse-l-follow', chapter: 'parse-ch-ll', title: 'FOLLOW: what can come next', minutes: 11,
    summary: 'When a nonterminal may vanish, the parser must know which symbols may come after it.',
    blocks: [
      'FIRST tells the parser when to pick an alternative that *reads something*. But what about A → ε? Choosing it reads nothing, so the next input symbol is whatever comes *after* A. The parser should pick A → ε exactly when the next symbol can follow A.',
      { def: 'FOLLOW(A)', text: 'the set of terminals that can appear immediately to the right of A in some sentential form derived from the start symbol, together with $ (the end of input) if A can be the last symbol.' },
      { list: ['$ ∈ FOLLOW(S) for the start symbol S.', 'For a rule A → α B β: everything in FIRST(β) except ε goes into FOLLOW(B).', 'If β can vanish (or is empty), everything in FOLLOW(A) goes into FOLLOW(B): what follows A can follow B, since B ends A.'] },
      { topic: 'follow-sets', input: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε' }, caption: 'The bracket ] reaches FOLLOW(A) directly from L → [ A ], then flows into FOLLOW(R) because R sits at the end of A\'s rule.' },
      { predict: { q: 'Same grammar: L → [ A ], A → x R | ε, R → ; x R | ε. What is FOLLOW(R)?', options: ['{;}', '{]}', '{], $}', '{x}'], answer: 1, explain: 'R appears only at the end of right sides of A and of R itself, so FOLLOW(R) ⊇ FOLLOW(A) = {]}. Nothing else ever follows R.' } },
      { warn: 'FOLLOW never contains ε. The end of input is written $. And do not forget the third rule: it is the one that most often goes missing.' },
      { h: 'Try it yourself' },
      { editor: { kind: 'grammar', text: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', tests: '[]\n[x]\n[x;x;x]\n-[x;]\n-[;x]' }, caption: 'The list grammar of the topic. Add a rule that lets lists nest, then work out how FOLLOW(A) changes.' },
      { list: ['FOLLOW(A) is what may come right after A; it decides when A → ε is the right choice.', '$ follows the start symbol.', 'A → α B β puts FIRST(β) into FOLLOW(B), and FOLLOW(A) too when β can vanish.', 'Again a fixpoint: repeat until nothing changes.'] },
      { exercise: 'parse-ex-follow-1' },
      { exercise: 'parse-ex-follow-2' },
      { exercise: 'parse-ex-follow-3' },
    ],
  });

  C.lesson({
    id: 'parse-l-ll1-table', chapter: 'parse-ch-ll', title: 'The LL(1) table and its conflicts', minutes: 13,
    summary: 'FIRST and FOLLOW fill a table that names the rule for each nonterminal and next symbol; two rules in one cell is a conflict.',
    blocks: [
      'Now the two sets come together. The **LL(1) table** M has a row for each nonterminal and a column for each terminal and $. M[A, a] is the rule to use when A must be expanded and a is the next input symbol.',
      { steps: ['For each rule A → α and each terminal a in FIRST(α), put A → α in M[A, a].', 'If ε ∈ FIRST(α), also put A → α in M[A, b] for every b in FOLLOW(A) (including $).', 'Every cell left empty is an error: no rule can start that way.'] },
      { topic: 'll1-table', input: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε' }, caption: 'Rules that read something go under their FIRST; the ε-rules go under FOLLOW. Watch where A → ε lands.' },
      { def: 'LL(1) grammar', text: 'a grammar whose LL(1) table has at most one rule in every cell. The name says: Left-to-right scan, Leftmost derivation, 1 symbol of lookahead.' },
      { h: 'When a cell gets two rules' },
      'Two kinds of clash can put two rules in one cell:',
      { list: ['**FIRST/FIRST**: two alternatives of A can begin with the same terminal, as in S → x = E | x ( ).', '**FIRST/FOLLOW**: A can vanish, and a terminal that can follow A can also begin another alternative of A.'] },
      { topic: 'll1-conflict', input: { g: 'S → A a b\nA → a | ε' }, frame: 3, caption: 'A FIRST/FOLLOW conflict: after S → A a b, the next symbol a could be A\'s own a, or the a that follows A when A vanishes.' },
      { predict: { q: 'Grammar S → A a b, A → a | ε. On the input ab, which rule must the parser use for A?', options: ['A → a', 'A → ε', 'Either works'], answer: 1, explain: 'If A takes the a, the remaining b cannot match S\'s a. The right choice is A → ε, but on aab it would be A → a. With one symbol of lookahead (a in both cases) the parser cannot tell: that is the conflict.' } },
      { tip: 'A grammar with a conflict is not necessarily bad, and the language may still have an LL(1) grammar. The next lessons rewrite such grammars.' },
      { warn: 'Every ambiguous grammar and every left-recursive grammar has a conflict. But a conflict does not prove ambiguity: S → A a b, A → a | ε is unambiguous.' },
      { list: ['M[A, a] holds the rule to use for A when a is next.', 'Rules go under FIRST of their right side; rules that can vanish also go under FOLLOW of their left side.', 'At most one rule per cell means the grammar is LL(1).', 'Conflicts are FIRST/FIRST or FIRST/FOLLOW.'] },
      { exercise: 'parse-ex-ll1-1' },
      { exercise: 'parse-ex-ll1-2' },
      { exercise: 'parse-ex-ll1-3' },
      { exercise: 'parse-ex-ll1-cell' },
      { exercise: 'parse-ex-ll1-cell-2' },
      { exercise: 'parse-ex-ll1-kind' },
      { exercise: 'parse-ex-ll1-which' },
    ],
  });

  C.lesson({
    id: 'parse-l-predictive', chapter: 'parse-ch-ll', title: 'The predictive parse: a stack that predicts', minutes: 10,
    summary: 'A stack of symbols still to be matched, the table to expand nonterminals, and no backtracking at all.',
    blocks: [
      'With the table in hand, parsing needs no procedures and no guessing. A stack holds what the parser still *expects* to see, starting with S on top of $. At each step:',
      { steps: ['If the top is a terminal: it must equal the next input symbol. Pop it and advance; otherwise it is an error.', 'If the top is a nonterminal A and the next symbol is a: look up M[A, a]. Pop A and push the right side of that rule, rightmost symbol first, so the leftmost ends on top. An empty cell is an error.', 'When the top is $ and the input is at $: accept.'] },
      { topic: 'll1-parse', input: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;x]' }, caption: 'The stack on one side, the input on the other, the tree growing from the top. Each expansion adds the children of one node, leftmost first.' },
      { predict: { q: 'Same grammar, input [x;]. Which input symbol does the parser stop at with an error?', options: ['[', ';', ']', 'it accepts'], answer: 2, explain: 'After ; is matched, R → ; x R has left x on top of the stack. The next input is ], which is not x: error at ].' } },
      'The parser finds the error at the earliest possible moment: it never reads a symbol that could not continue some sentence. This is called the *valid prefix* property, and LR parsers share it.',
      { topic: 'll1-parse', input: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;]' }, frame: 8, caption: 'The same parse failing. Note that nothing is undone: an LL(1) parser never needs to go back.' },
      'The expansions, read in order, are exactly a **leftmost derivation** of the input. That is the second L in LL.',
      { tip: 'Count the steps: each terminal is matched once, and each expansion adds a node to the tree. The work is linear in the size of the tree.' },
      { list: ['The stack holds the symbols still expected; it starts as S $.', 'Terminals on top are matched; nonterminals are expanded by the table.', 'Right sides are pushed in reverse, so their first symbol is on top.', 'No backtracking; errors are found as early as possible.'] },
      { exercise: 'parse-ex-pred-count' },
      { exercise: 'parse-ex-pred-error' },
    ],
  });

  C.lesson({
    id: 'parse-l-rewrite', chapter: 'parse-ch-ll', title: 'Making a grammar LL(1): left recursion and left factoring', minutes: 14,
    summary: 'Two rewrites remove the most common conflicts without changing the language.',
    blocks: [
      'The grammars people write first are rarely LL(1). Lists come out left-recursive (L → L & t | t), and commands that share a beginning come out with common prefixes. Two mechanical rewrites fix both.',
      { h: 'Removing left recursion' },
      'A rule A → A α | β says: an A is a β followed by any number of α\'s. Say that directly, with a new nonterminal for the tail:',
      { math: 'A  → A α | β          becomes          A  → β A\'\n                                         A\' → α A\' | ε' },
      { topic: 'left-recursion', input: { g: 'L → L ; x | x' }, frame: 4, caption: 'The list grammar is rewritten so that the recursion comes at the end. The language stays the same; the trees now lean the other way.' },
      { predict: { q: 'After removing the left recursion from E → E - n | n you get E → n E\', E\' → - n E\' | ε. In the tree for n - n - n, which two n\'s does the deepest - sit between?', options: ['the first two, as before', 'the last two: the trees now lean to the right'], answer: 1, explain: 'The new tree hangs every - n off a chain of E\' nodes going right. The language is the same, but the shape is not; a compiler restores left-to-right grouping while it walks the tree.' } },
      { warn: 'Indirect left recursion (S → A x, A → S z | w) hides behind another nonterminal. Substitute A\'s rules into S first, then remove the direct left recursion. The topic shows the order in which this is done.' },
      { topic: 'left-recursion', input: { g: 'S → A a | b\nA → S c | d' }, frame: 5, caption: 'Indirect left recursion: A is replaced in S\'s rules until S calls itself directly, and then that is removed.' },
      { h: 'Left factoring' },
      'When two alternatives start with the same symbols, delay the choice until after the shared part:',
      { math: 'A → α β₁ | α β₂          becomes          A  → α A\'\n                                         A\' → β₁ | β₂' },
      { topic: 'left-factor', input: { g: 'C → d o x | d o y | d z' }, frame: 3, caption: 'The longest shared prefix comes out first; then factoring repeats inside the new nonterminal.' },
      { h: 'Try it yourself' },
      { editor: { kind: 'grammar', text: 'L → L & t | t', tests: 't\nt&t\nt&t&t\n-\n-&t\n-t&' }, caption: 'Rewrite this list grammar so it is no longer left-recursive. The tests check that the language has not changed.' },
      { tip: 'Neither rewrite promises an LL(1) grammar: they remove two causes of conflicts, not all of them. Always rebuild the table to check.' },
      { list: ['A → A α | β becomes A → β A\', A\' → α A\' | ε.', 'Indirect left recursion is first turned into direct left recursion by substitution.', 'A → α β₁ | α β₂ becomes A → α A\', A\' → β₁ | β₂.', 'The language is unchanged; the trees change shape.'] },
      { exercise: 'parse-ex-rw-list' },
      { exercise: 'parse-ex-rw-factor' },
      { exercise: 'parse-ex-rw-two-ops' },
      { exercise: 'parse-ex-rw-optional' },
      { exercise: 'parse-ex-rw-indirect' },
    ],
  });

  C.lesson({
    id: 'parse-l-codegen', chapter: 'parse-ch-ll', title: 'Recursive descent written from the table', minutes: 9,
    summary: 'The LL(1) table turned into code: one procedure per nonterminal, one branch per lookahead.',
    blocks: [
      'Hand-written parsers in real compilers are usually recursive descent, the same shape as the backtracking parser of the first lesson, but with every choice decided by one look at the next token. The LL(1) table says exactly what each procedure should do.',
      { code: 'procedure R():\n  if next = ";":   match(";"); match("x"); R()\n  else if next = "]":   return            -- R → ε, since ] ∈ FOLLOW(R)\n  else: error("expected ; or ]")', lang: 'grammar' },
      { topic: 'rd-codegen', input: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;x]' }, caption: 'The generated procedures on the left, the call stack running them. The procedure stack is the predictive parser\'s stack in disguise.' },
      { predict: { q: 'In the generated procedure for A (A → x R | ε), what happens when the next token is ] ?', options: ['It reports an error', 'It returns at once without reading anything', 'It calls R'], answer: 1, explain: '] is in FOLLOW(A), so M[A, ]] holds A → ε: the procedure has nothing to do.' } },
      'Each procedure body is one row of the table: a branch for every non-empty cell, and an error for the rest. The call stack replaces the explicit stack, and the tree can be built as procedures return.',
      { topic: 'rd-codegen', input: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[xx]' }, frame: 9, caption: 'An error: R sees x where only ; or ] may come.' },
      { tip: 'Hand-written parsers often check FOLLOW lazily: the ε branch becomes the default "else return", and the error shows up one call later. The table-driven version reports it earlier.' },
      { list: ['One procedure per nonterminal, one branch per non-empty table cell.', 'A terminal on a right side is a match, a nonterminal is a call.', 'The ε-rule is chosen on FOLLOW.', 'The call stack plays the part of the parser\'s stack.'] },
      { exercise: 'parse-ex-codegen' },
      { exercise: 'parse-ex-codegen-calls' },
    ],
  });

  C.lesson({
    id: 'parse-l-panic', chapter: 'parse-ch-ll', title: 'Panic mode: carrying on after an error', minutes: 9,
    summary: 'Skip input until something can follow, so one mistake does not hide all the others.',
    blocks: [
      'A compiler that stops at the first error is annoying: you fix one bracket and find the next problem only on the next run. **Panic mode** lets the parser recover and keep going, at the cost of a few messages that may be noise.',
      { def: 'Synchronising set', text: 'for a nonterminal A, the input symbols at which the parser gives up on A and carries on with what follows it. The usual choice is FOLLOW(A), sometimes plus a few strong tokens such as ; or a keyword.' },
      { steps: ['Top is a terminal that does not match: report it and pop the terminal, as if it had been there.', 'Top is a nonterminal A and M[A, a] is empty: if a is in A\'s synchronising set, pop A (as if A were finished).', 'Otherwise skip the input symbol a and look again.'] },
      { topic: 'll1-panic', input: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: 'n+)n' }, caption: 'After + the parser needs a T but sees ). Since ) is in FOLLOW(T), T is popped. Then the stray ) and n are skipped.' },
      { predict: { q: 'Same grammar and input n+)n. How many errors does the parser report before it reaches the end?', options: ['1', '2', '3'], answer: 2, explain: 'One for the missing T (pop T), one for the extra ), one for the extra n: three repairs, and the input is rejected.' } },
      { topic: 'll1-panic', input: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: '(n+n' }, frame: 14, caption: 'An unclosed bracket: the expected ) is missing, so it is popped as if it had been there.' },
      { warn: 'Recovery never turns a wrong program into a right one. The input is still rejected; the point is to report more of the real errors in one run.' },
      { list: ['Panic mode pops a missing terminal, pops a nonterminal at a synchronising symbol, and skips other input.', 'FOLLOW sets make natural synchronising sets.', 'It always terminates: every step pops the stack or consumes input.', 'The verdict is still "rejected".'] },
      { exercise: 'parse-ex-panic-sync' },
      { exercise: 'parse-ex-panic-what' },
      { exercise: 'parse-ex-panic-count' },
    ],
  });

  // ---- chapter 2 exercises ---------------------------------------------------------------------------------
  const GA = 'S -> K m\nK -> g K | ε';
  const GB = 'P -> C R\nR -> ! C R | ε\nC -> w A\nA -> a A | ε';
  const GC = 'S -> A B C\nA -> a | ε\nB -> b | ε\nC -> c | A';
  const GD = 'M -> { E }\nE -> k : v F | ε\nF -> & k : v F | ε';
  const GF = 'S -> T U\nT -> U t | ε\nU -> u U | ε';
  const show = (g) => gram(g.replace(/->/g, '→'));

  ex({ id: 'parse-ex-first-1', chapter: 'parse-ch-ll', title: 'FIRST sets: a run of g\'s', kind: 'table', table: 'first', grammar: GA,
    text: ['Fill in FIRST of each nonterminal.', show(GA)],
    solution: { S: 'g, m', K: 'g, ε' }, wrong: [{ S: 'g', K: 'g, ε' }, { S: 'g, m', K: 'g' }, { S: 'g, m, ε', K: 'g, ε' }],
    hints: H('FIRST(K): K → g K starts with g, and K → ε adds ε.', 'S → K m: K can vanish, so look past it to m. But m cannot vanish, so ε is not in FIRST(S).', 'S: g, m. K: g, ε.') });
  ex({ id: 'parse-ex-first-2', chapter: 'parse-ch-ll', title: 'FIRST sets: a map in braces', kind: 'table', table: 'first', grammar: GD,
    text: ['This grammar describes maps like {k:v&k:v}. Fill in FIRST of each nonterminal.', show(GD)],
    solution: { M: '{', E: 'k, ε', F: '&, ε' }, wrong: [{ M: '{, k', E: 'k, ε', F: '&, ε' }, { M: '{', E: 'k', F: '&' }],
    hints: H('M always starts with the brace.', 'E and F each have an ε alternative.', 'M: {. E: k, ε. F: &, ε.') });
  ex({ id: 'parse-ex-first-3', chapter: 'parse-ch-ll', title: 'FIRST sets: vanishing in a chain', kind: 'table', table: 'first', grammar: GC, level: 2,
    text: ['Fill in FIRST of each nonterminal. Several of them can vanish, so look carefully past each one.', show(GC)],
    solution: { S: 'a, b, c, ε', A: 'a, ε', B: 'b, ε', C: 'a, c, ε' }, wrong: [{ S: 'a, b, c', A: 'a, ε', B: 'b, ε', C: 'a, c, ε' }, { S: 'a, b, c, ε', A: 'a, ε', B: 'b, ε', C: 'c' }, { S: 'a', A: 'a, ε', B: 'b, ε', C: 'a, c, ε' }],
    hints: H('C → A means C inherits all of FIRST(A), ε included.', 'S → A B C: every one of A, B and C can vanish.', 'S: a, b, c, ε. A: a, ε. B: b, ε. C: a, c, ε.') });
  ex({ id: 'parse-ex-first-4', chapter: 'parse-ch-ll', title: 'FIRST sets: looking through U', kind: 'table', table: 'first', grammar: GF, level: 3,
    text: ['Fill in FIRST of each nonterminal.', show(GF)],
    solution: { S: 't, u, ε', T: 't, u, ε', U: 'u, ε' }, wrong: [{ S: 't, u, ε', T: 'u, ε', U: 'u, ε' }, { S: 'u, ε', T: 't, u, ε', U: 'u, ε' }, { S: 't, u', T: 't, u', U: 'u, ε' }],
    hints: H('Start with U: it is u U or nothing.', 'In T → U t, U can vanish, so t is in FIRST(T) as well as u. And T → ε gives ε.', 'S: t, u, ε. T: t, u, ε. U: u, ε.') });
  ex({ id: 'parse-ex-first-string', chapter: 'parse-ch-ll', title: 'FIRST of a right side', kind: 'string', set: true, level: 2,
    text: ['In this grammar, what is FIRST(B C)? Write it as a set, with ε if it belongs.', show(GC)],
    answer: '{a, b, c, ε}', solution: 'b, c, a, ε', wrong: ['{b, c}', '{b, c, ε}', '{a, b, c}'],
    hints: H('FIRST(B) without ε comes first. Can B vanish?', 'B can vanish, so add FIRST(C). C can vanish too.', 'Both can vanish: {b} ∪ {a, c} ∪ {ε} = {a, b, c, ε}.') });

  ex({ id: 'parse-ex-follow-1', chapter: 'parse-ch-ll', title: 'FOLLOW sets: a run of g\'s', kind: 'table', table: 'follow', grammar: GA,
    text: ['Fill in FOLLOW of each nonterminal. Use $ for the end of the input.', show(GA)],
    solution: { S: '$', K: 'm' }, wrong: [{ S: '$', K: 'm, $' }, { S: '$', K: 'g, m' }, { S: '', K: 'm' }],
    hints: H('$ follows the start symbol.', 'K appears in S → K m (followed by m) and at the end of K → g K, which adds FOLLOW(K) to itself, nothing new.', 'S: $. K: m.') });
  ex({ id: 'parse-ex-follow-2', chapter: 'parse-ch-ll', title: 'FOLLOW sets: pipelines', kind: 'table', table: 'follow', grammar: GB, level: 2,
    text: ['This grammar describes pipelines like wa!w!waa. Fill in FOLLOW of each nonterminal.', show(GB)],
    solution: { P: '$', C: '!, $', R: '$', A: '!, $' }, wrong: [{ P: '$', C: '!', R: '$', A: '!' }, { P: '$', C: '!, $', R: '$', A: 'a, !, $' }, { P: '$', C: '!, $', R: '!, $', A: '!, $' }],
    hints: H('C is followed by R, and R can vanish. So FOLLOW(C) has FIRST(R) without ε and also what follows the left side.', 'A is last in C → w A, so FOLLOW(A) ⊇ FOLLOW(C).', 'P: $. C: !, $. R: $. A: !, $.') });
  ex({ id: 'parse-ex-follow-3', chapter: 'parse-ch-ll', title: 'FOLLOW sets: looking through U', kind: 'table', table: 'follow', grammar: GF, level: 3,
    text: ['Fill in FOLLOW of each nonterminal.', show(GF)],
    solution: { S: '$', T: 'u, $', U: 't, $' }, wrong: [{ S: '$', T: 'u', U: 't, $' }, { S: '$', T: 'u, $', U: 't' }, { S: '$', T: 'u, t, $', U: 't, $' }],
    hints: H('In S → T U, T is followed by U, which can vanish.', 'U appears in S → T U (at the end), in T → U t (before t) and at the end of U → u U.', 'S: $. T: u, $. U: t, $.') });

  ex({ id: 'parse-ex-ll1-1', chapter: 'parse-ch-ll', title: 'An LL(1) table: a run of g\'s', kind: 'table', table: 'll1', grammar: GA,
    text: ['Fill in the LL(1) table: in each cell the right side of the rule to use, or nothing.', show(GA)],
    solution: { 'S|g': 'K m', 'S|m': 'K m', 'K|g': 'g K', 'K|m': 'ε' }, wrong: [{ 'S|g': 'K m', 'K|g': 'g K', 'K|m': 'ε' }, { 'S|g': 'K m', 'S|m': 'K m', 'K|g': 'g K', 'K|m': 'ε', 'K|$': 'ε' }],
    hints: H('FIRST(K m) = {g, m}: S → K m goes under both.', 'K → ε goes under FOLLOW(K), which is {m}. Not under $.', 'S: K m under g and m. K: g K under g, ε under m.') });
  ex({ id: 'parse-ex-ll1-2', chapter: 'parse-ch-ll', title: 'An LL(1) table: a map in braces', kind: 'table', table: 'll1', grammar: GD, level: 2,
    text: ['Fill in the LL(1) table.', show(GD)],
    solution: { 'M|{': '{ E }', 'E|k': 'k : v F', 'E|}': 'ε', 'F|&': '& k : v F', 'F|}': 'ε' },
    wrong: [{ 'M|{': '{ E }', 'E|k': 'k : v F', 'E|$': 'ε', 'F|&': '& k : v F', 'F|$': 'ε' }, { 'M|{': '{ E }', 'E|k': 'k : v F', 'E|}': 'ε', 'F|&': '& k : v F' }],
    hints: H('The rules that read something go under their first terminal.', 'E and F can vanish; what follows each of them? Both end just before }.', 'M: { E } under {. E: k : v F under k, ε under }. F: & k : v F under &, ε under }.') });
  ex({ id: 'parse-ex-ll1-3', chapter: 'parse-ch-ll', title: 'An LL(1) table: pipelines', kind: 'table', table: 'll1', grammar: GB, level: 2,
    text: ['Fill in the LL(1) table.', show(GB)],
    solution: { 'P|w': 'C R', 'R|!': '! C R', 'R|$': 'ε', 'C|w': 'w A', 'A|a': 'a A', 'A|!': 'ε', 'A|$': 'ε' },
    wrong: [{ 'P|w': 'C R', 'R|!': '! C R', 'R|$': 'ε', 'C|w': 'w A', 'A|a': 'a A', 'A|$': 'ε' }, { 'P|w': 'C R', 'R|!': '! C R', 'R|$': 'ε', 'R|w': 'ε', 'C|w': 'w A', 'A|a': 'a A', 'A|!': 'ε', 'A|$': 'ε' }],
    hints: H('FOLLOW(R) = {$} and FOLLOW(A) = {!, $}.', 'Each ε-rule goes under every symbol of its FOLLOW set.', 'P: C R under w. R: ! C R under !, ε under $. C: w A under w. A: a A under a, ε under ! and $.') });
  const GX = 'S -> X Y z\nX -> x X | ε\nY -> y | X w';
  ex({ id: 'parse-ex-ll1-cell', chapter: 'parse-ch-ll', title: 'Find the conflict', kind: 'string', level: 2,
    text: ['This grammar is not LL(1). Which cell of its table holds two rules? Answer with the row and the column, like K, m.', show(GX)],
    placeholder: 'row, column', accept: cellAccept('X', 'x'), answer: 'X, x', solution: 'X, x', wrong: ['Y, x', 'S, x', 'X, w'],
    hints: H('X can vanish. What can follow X?', 'In Y → X w, w follows X; in S → X Y z, FIRST(Y) follows X, and FIRST(Y) contains x through Y → X w.', 'x ∈ FOLLOW(X), so X → ε goes under x; X → x X is there too. The cell is M[X, x].') });
  ex({ id: 'parse-ex-ll1-cell-2', chapter: 'parse-ch-ll', title: 'Find the conflict again', kind: 'string', level: 3,
    text: ['And this one: which cell holds two rules?', show(GF)],
    placeholder: 'row, column', accept: cellAccept('T', 'u'), answer: 'T, u', solution: 'M[T, u]', wrong: ['U, u', 'T, t', 'S, u'],
    hints: H('T can vanish, and T can begin with u (through U t).', 'What can follow T? Look at S → T U.', 'u ∈ FOLLOW(T) and u ∈ FIRST(U t): both T → U t and T → ε land in M[T, u].') });
  ex({ id: 'parse-ex-ll1-kind', chapter: 'parse-ch-ll', title: 'Which kind of conflict?', kind: 'choice', level: 2,
    text: ['The grammar below is not LL(1). What kind of conflict does it have?', gram('D → i | i = n')],
    options: ['FIRST/FIRST: both alternatives can begin with i', 'FIRST/FOLLOW: D can vanish', 'It has no conflict', 'A conflict caused by left recursion'],
    answer: 0, solution: 0, wrong: [1, 2],
    hints: H('Can D derive the empty string?', 'No. So look at the first symbols of the two alternatives.', 'FIRST/FIRST: both start with i. Left factoring fixes it.') });
  ex({ id: 'parse-ex-ll1-which', chapter: 'parse-ch-ll', title: 'Which grammars are LL(1)?', kind: 'choice', level: 2,
    text: 'Which of these grammars are LL(1)? Choose all of them.',
    options: ['S → K m, K → g K | ε', 'R → R & t | t', 'M → { E }, E → k : v F | ε, F → & k : v F | ε', 'S → A a b, A → a | ε'],
    answer: [0, 2], why: 'The second is left-recursive; the fourth has a FIRST/FOLLOW conflict on a.',
    solution: [0, 2], wrong: [[0, 1, 2], [0, 2, 3]],
    hints: H('A left-recursive grammar is never LL(1).', 'For the grammars with ε-rules, compare FIRST of the other alternative with FOLLOW.', 'LL(1): the first and the third.') });

  ex({ id: 'parse-ex-pred-count', chapter: 'parse-ch-ll', title: 'Count the expansions', kind: 'number', level: 2,
    text: ['The predictive parser for this grammar reads {k:v&k:v}. How many times does it expand a nonterminal (use a table entry), counting ε-rules?', show(GD)],
    answer: 4, solution: '4', wrong: ['3', '5'],
    hints: H('One expansion per interior node of the parse tree.', 'M, then E, then F twice: once for & k : v F and once for ε.', '4: M → { E }, E → k : v F, F → & k : v F, F → ε.') });
  ex({ id: 'parse-ex-pred-error', chapter: 'parse-ch-ll', title: 'Where does it stop?', kind: 'string', level: 1,
    text: ['The predictive parser for this grammar reads {k:&} and stops at an error. Which input symbol is it looking at when it stops?', show(GD)],
    answer: '&', solution: '&', wrong: ['}', ':'],
    hints: H('Follow the stack: { E } is pushed, { matched, then E → k : v F.', 'After k and : are matched, the top of the stack is v.', 'v does not match &: it stops at &.') });

  ex({ id: 'parse-ex-rw-list', chapter: 'parse-ch-ll', title: 'Rewrite a list grammar', kind: 'grammar', level: 1, alphabet: '&t',
    text: ['This grammar describes lists like t&t&t but is left-recursive. Write an LL(1) grammar for the same language.', gram('L → L & t | t')],
    ref: 'L -> L & t | t', also: mustBeLL1,
    solution: 'L -> t R\nR -> & t R | ε', wrong: ['L -> L & t | t', 'L -> t & L | t', 'L -> t R\nR -> & t R | & t'],
    hints: H('A list is one t followed by any number of & t.', 'Make a new nonterminal for "any number of & t", recursing on the right.', 'L → t R, R → & t R | ε. (L → t & L | t is right-recursive but not LL(1): both start with t.)') });
  ex({ id: 'parse-ex-rw-factor', chapter: 'parse-ch-ll', title: 'Left-factor some commands', kind: 'grammar', level: 2, alphabet: 'gonset',
    text: ['Three commands share a beginning. Left-factor the grammar until it is LL(1), keeping the language.', gram('C → g o n | g o s | g e t')],
    ref: 'C -> g o n | g o s | g e t', also: mustBeLL1,
    solution: 'C -> g D\nD -> o E | e t\nE -> n | s', wrong: ['C -> g o D | g e t\nD -> n | s', 'C -> g D\nD -> o E | e t\nE -> n | s | t'],
    hints: H('All three alternatives start with g: factor that out first.', 'Inside the new nonterminal, two alternatives still share o.', 'C → g D, D → o E | e t, E → n | s.') });
  ex({ id: 'parse-ex-rw-two-ops', chapter: 'parse-ch-ll', title: 'Two operators, one rewrite', kind: 'grammar', level: 2, alphabet: 'n-^',
    text: ['Remove the left recursion so the grammar becomes LL(1).', gram('E → E - n | E ^ n | n')],
    ref: 'E -> E - n | E ^ n | n', also: mustBeLL1,
    solution: 'E -> n R\nR -> - n R | ^ n R | ε', wrong: ['E -> n R\nR -> - n R | ε', 'E -> n - E | n ^ E | n', 'E -> n R\nR -> - n R | ^ n R'],
    hints: H('Both left-recursive alternatives turn into alternatives of the tail.', 'E is an n followed by any number of "- n" or "^ n".', 'E → n R, R → - n R | ^ n R | ε.') });
  ex({ id: 'parse-ex-rw-optional', chapter: 'parse-ch-ll', title: 'An optional initialiser', kind: 'grammar', level: 2, alphabet: 'i=n',
    text: ['A declaration is a name i, optionally followed by = and a value (n or another name i). Make this grammar LL(1) without changing its language.', gram('D → i | i = n | i = i')],
    ref: 'D -> i | i = n | i = i', also: mustBeLL1,
    solution: 'D -> i Q\nQ -> = V | ε\nV -> n | i', wrong: ['D -> i | i Q\nQ -> = n | = i', 'D -> i Q\nQ -> = V\nV -> n | i', 'D -> i = V | i\nV -> n | i'],
    hints: H('All three alternatives start with i.', 'After i comes either nothing or = and a value.', 'D → i Q, Q → = V | ε, V → n | i.') });
  ex({ id: 'parse-ex-rw-indirect', chapter: 'parse-ch-ll', title: 'Indirect left recursion', kind: 'grammar', level: 3, alphabet: 'xyzw',
    text: ['S calls A and A calls S, both at the left edge. Write an LL(1) grammar for the same language.', gram('S → A x | y\nA → S z | w')],
    ref: 'S -> A x | y\nA -> S z | w', also: mustBeLL1,
    solution: 'S -> y R | w x R\nR -> z x R | ε', wrong: ['S -> A x | y\nA -> S z | w', 'S -> y R | w x R\nR -> z R | ε', 'S -> y R | w x R\nR -> z x R'],
    hints: H('Substitute A\'s rules into S → A x: S → S z x | w x | y.', 'Now remove the direct left recursion: S is a start (y or w x) followed by any number of z x.', 'S → y R | w x R, R → z x R | ε.') });

  ex({ id: 'parse-ex-codegen', chapter: 'parse-ch-ll', title: 'What the procedure for F does', kind: 'choice', level: 1,
    text: ['A recursive-descent parser is generated from the LL(1) table of this grammar. In the procedure for F, the next token is }. What does F do?', show(GD)],
    options: ['Returns at once, reading nothing', 'Reports an error', 'Matches } and returns', 'Calls E'],
    answer: 0, why: '} ∈ FOLLOW(F), so M[F, }] holds F → ε.',
    solution: 0, wrong: [1, 2],
    hints: H('Look at row F of the table.', 'Which rule sits in M[F, }]?', 'F → ε: the procedure returns without reading; the } is matched by M\'s procedure.') });
  ex({ id: 'parse-ex-codegen-calls', chapter: 'parse-ch-ll', title: 'How deep does it go?', kind: 'number', level: 2,
    text: ['The generated recursive-descent parser for this grammar reads wa!w. How many procedure calls are made in all, counting the first call to P?', show(GB)],
    answer: 8, solution: '8', wrong: ['7', '6'],
    hints: H('One call per nonterminal node in the parse tree, ε-nodes included.', 'Draw the tree: P → C R; C → w A with A → a A and then A → ε; R → ! C R with C → w A, A → ε; and the last R → ε.', 'P once, C twice, A three times, R twice: 8 calls.') });

  ex({ id: 'parse-ex-panic-sync', chapter: 'parse-ch-ll', title: 'A synchronising set', kind: 'string', set: true, level: 1,
    text: ['Panic mode uses FOLLOW sets as synchronising sets. For the pipeline grammar below, at which input symbols does the parser give up on C and pop it? Write a set; use $ for the end of input.', show(GB)],
    answer: '{!, $}', solution: '$, !', wrong: ['{!}', '{w}', '{a, !, $}'],
    hints: H('The synchronising set of C is FOLLOW(C).', 'C is followed by R, which starts with ! or vanishes.', '{!, $}.') });
  ex({ id: 'parse-ex-panic-what', chapter: 'parse-ch-ll', title: 'What panic mode does', kind: 'choice', level: 2,
    text: ['With the pipeline grammar and FOLLOW sets for synchronising, the parser reads wa!!w. After the first ! is matched, C is on top of the stack and the next input is the second !. What happens?', show(GB)],
    options: ['C is popped, since ! is in its synchronising set', 'The second ! is skipped', 'The parser stops', 'C is expanded by C → w A anyway'],
    answer: 0, why: 'M[C, !] is empty, but ! ∈ FOLLOW(C): pop C and carry on, so R → ! C R reads the second !.',
    solution: 0, wrong: [1, 2],
    hints: H('Is M[C, !] empty?', 'Yes. Then is ! in FOLLOW(C)?', 'It is, so C is popped; the second ! is then read by the next R → ! C R.') });
  ex({ id: 'parse-ex-panic-count', chapter: 'parse-ch-ll', title: 'Pretending symbols were there', kind: 'number', level: 3,
    text: ['The map grammar reads {k:v&&k:v} with panic mode. After the first & is matched, the stack expects k : v F. How many terminals does the parser pop, pretending they were there, before it can carry on?', show(GD)],
    answer: 3, solution: '3', wrong: ['1', '0'],
    hints: H('A terminal on top that does not match is popped, as if it had been there.', 'The next input is the second &, and the stack shows k, then :, then v.', 'k, : and v are each popped (3), then F → & k : v F reads the second & and the rest parses.') });

  // =========================================================================================================
  // Chapter 3: bottom up
  // =========================================================================================================
  C.lesson({
    id: 'parse-l-handles', chapter: 'parse-ch-lr', title: 'Shift, reduce, and the handle', minutes: 11,
    summary: 'Build the tree from the leaves up: shift symbols onto a stack, and reduce when a right side is on top.',
    blocks: [
      'Top-down parsers must choose a rule *before* they have seen what it covers. Bottom-up parsers wait. They read symbols onto a stack, and only when a whole right side is sitting there do they replace it by its left side. The decision is made with all the evidence in view.',
      { def: 'Shift-reduce parsing', text: 'a stack and the rest of the input. **Shift** moves the next input symbol onto the stack. **Reduce** by A → β replaces β on top of the stack by A. Accept when the stack holds only the start symbol and the input is used up.' },
      { topic: 'shift-reduce', input: { g: 'E → E + T | T\nT → x | ( E )', w: 'x+(x+x)' }, caption: 'Shifts push symbols, reductions fold them into a node. Read the reductions from the end backwards: they spell a rightmost derivation.' },
      'Not every right side on the stack should be reduced. With E → E + T | T, the stack E + T could reduce T to E, giving E + E, from which nothing can continue. The right reduction is the one that leads back to S.',
      { def: 'Handle', text: 'in a right sentential form, an occurrence of a right side β together with its rule A → β, such that replacing it by A gives the previous step of a rightmost derivation. In a shift-reduce parser the handle is always on top of the stack.' },
      { predict: { q: 'With E → E + T | T and T → x | ( E ), the stack holds E + T and the next input is +. What should the parser do?', options: ['Shift the +', 'Reduce T to E', 'Reduce E + T to E'], answer: 2, explain: 'E + T is the handle. Reducing only T would leave E + E, which no rule can reduce. After E + T becomes E, the + is shifted.' } },
      { warn: 'The hard part of bottom-up parsing is recognising the handle: when to reduce, and by which rule. The rest of this chapter builds a machine that knows.' },
      { topic: 'shift-reduce', input: { g: 'L → x L | ε', w: 'xx' }, caption: 'An ε-rule: the parser reduces nothing to L after the last x, then folds right to left.' },
      { list: ['Shift reads a symbol onto the stack; reduce replaces a right side on top by its left side.', 'The reductions, read backwards, form a rightmost derivation.', 'The handle is the right side to reduce, and it is always on top of the stack.', 'Deciding shift or reduce is the whole problem; LR tables solve it.'] },
      { exercise: 'parse-ex-handle-1' },
      { exercise: 'parse-ex-handle-2' },
      { exercise: 'parse-ex-sr-count' },
    ],
  });

  C.lesson({
    id: 'parse-l-lr0-items', chapter: 'parse-ch-lr', title: 'LR(0) items: where the parser might be', minutes: 13,
    summary: 'A dot in a rule marks how much of it has been seen; closure and goto build an automaton of item sets.',
    blocks: [
      'How can a parser know whether the top of its stack is a handle? It keeps track of every rule it might be in the middle of, and how far through each one it is.',
      { def: 'LR(0) item', text: 'a rule with a dot in its right side, like E → E - • P: the parser has seen E - and hopes to see a P next. An item with the dot at the end, E → E - P •, is complete: its right side is on top of the stack.' },
      { def: 'Closure', text: 'of a set of items: whenever the dot is just before a nonterminal B, add B → • γ for every rule of B, and repeat. If we hope to see a B next, we may be at the start of any of B\'s rules.' },
      { def: 'Goto(I, X)', text: 'take every item of I with the dot just before X, move the dot over X, and close the result.' },
      'Starting from the closure of S\' → • S (a new start rule, so that accepting is a single complete item), goto builds all the item sets reachable on every symbol. The sets are the states of a DFA, the **LR(0) automaton**. Its input is the stack: reading the stack from the bottom up lands in the state that knows what may be on top.',
      { topic: 'lr0-items', input: { g: 'E → E + T | T\nT → x | ( E )' }, caption: 'Each new state starts with its kernel (the items whose dot moved) and then closes. Watch the state for ( : it predicts E\'s rules again, and from there T\'s.' },
      { predict: { q: 'Grammar E → E - P | P, P → q | [ E ]. How many items are in the closure of P → [ • E ] ?', options: ['1', '3', '5'], answer: 2, explain: 'P → [ • E ], then E → • E - P and E → • P, then P → • q and P → • [ E ]: five items.' } },
      { tip: 'Two different paths to the same set of items reach the same state. That is why the automaton stays small: the state after [ on any depth of brackets is one and the same.' },
      { topic: 'lr0-items', input: { g: 'L → x L | ε' }, caption: 'An ε-rule gives a complete item L → • straight away, in the start state.' },
      { list: ['An item is a rule with a dot: what has been seen and what is hoped for.', 'Closure adds B → • γ for each nonterminal B after a dot.', 'Goto moves the dot over one symbol, then closes.', 'The item sets reachable from S\' → • S are the states of the LR(0) automaton.'] },
      { exercise: 'parse-ex-closure' },
      { exercise: 'parse-ex-goto' },
      { exercise: 'parse-ex-lr0-count' },
    ],
  });

  C.lesson({
    id: 'parse-l-lr0-slr', chapter: 'parse-ch-lr', title: 'The LR(0) and SLR(1) tables', minutes: 13,
    summary: 'Shift on the automaton\'s transitions, reduce on complete items; SLR(1) reduces only on FOLLOW.',
    blocks: [
      'The automaton becomes a table with two parts. **ACTION[s, a]** says what to do in state s with next terminal a: shift and go to a state (s5), reduce by rule k (r2), accept, or error. **GOTO[s, A]** says which state to enter after a reduction to A uncovers state s.',
      { steps: ['A transition from s to t on a terminal a: ACTION[s, a] = shift t.', 'A transition from s to t on a nonterminal A: GOTO[s, A] = t.', 'A complete item A → β • in s (not the start rule): reduce by A → β. In the LR(0) table, on every terminal and $.', 'S\' → S • in s: ACTION[s, $] = accept.'] },
      { topic: 'lr0-table', input: { g: 'E → E + T | T\nT → T * x | x' }, caption: 'LR(0) reduces on everything, so in the state holding E → T • and T → T • * x the reduce and the shift on * collide.' },
      { def: 'LR(0) grammar', text: 'one whose LR(0) table has at most one action in every cell: no state mixes a complete item with another complete item (reduce/reduce) or with a shift (shift/reduce).' },
      { h: 'SLR(1): reduce only when it could make sense' },
      'Reducing by A → β is only useful if the next terminal can follow A. So SLR(1) puts the reduce only under the terminals in FOLLOW(A). Many conflicts disappear.',
      { topic: 'slr-table', input: { g: 'E → E + T | T\nT → T * x | x' }, caption: 'The same grammar: FOLLOW(E) = {+, $} does not contain *, so E → T • no longer reduces on * and the conflict is gone.' },
      { predict: { q: 'Grammar S → K m, K → g K | ε. The start state holds K → • and shifts on g. Is this a conflict in the SLR(1) table?', options: ['Yes, shift/reduce on g', 'No: K → • reduces only on FOLLOW(K) = {m}'], answer: 1, explain: 'In the LR(0) table K → • reduces on g too, which clashes with the shift. SLR(1) reduces only on m, so the grammar is SLR(1) but not LR(0).' } },
      { warn: 'FOLLOW(A) is a property of the whole grammar, not of the state. A state may reduce A on a terminal that can follow A somewhere else, but not here. That is where SLR(1) runs out of power, and LR(1) begins.' },
      { list: ['ACTION has shifts, reduces, accept and errors; GOTO has the moves on nonterminals.', 'LR(0): a complete item reduces on every terminal.', 'SLR(1): a complete item A → β • reduces only on FOLLOW(A).', 'A grammar is LR(0) or SLR(1) when its table has no cell with two actions.'] },
      { exercise: 'parse-ex-lr0-table' },
      { exercise: 'parse-ex-slr-table' },
      { exercise: 'parse-ex-lr0-conflict' },
    ],
  });

  C.lesson({
    id: 'parse-l-lr-driver', chapter: 'parse-ch-lr', title: 'The LR driver: states on a stack', minutes: 10,
    summary: 'One small loop runs every LR table: look up ACTION, shift or reduce, consult GOTO.',
    blocks: [
      'Every LR method, from LR(0) to LR(1), uses the same driver. Only the table changes. The stack holds *states*, which remember everything the symbols would.',
      { steps: ['Start with state 0 on the stack.', 'Let s be the top state and a the next input symbol. Look up ACTION[s, a].', 'Shift t: push t and advance the input.', 'Reduce by A → β: pop |β| states, let u be the new top, push GOTO[u, A].', 'Accept: stop with success. Error: stop with an error.'] },
      { topic: 'lr-parse', input: { g: 'E → E + T | T\nT → x | ( E )', w: 'x+(x)' }, caption: 'The stack of states, with the symbols they stand for, beside the automaton. A reduction pops back to an older state and takes its GOTO edge.' },
      { predict: { q: 'The driver reduces by E → E + T. How many states does it pop?', options: ['1', '3', 'as many as the stack holds'], answer: 1, explain: 'One state per symbol of the right side: E, + and T, so three states are popped before GOTO[u, E] is pushed.' } },
      { topic: 'lr-parse', input: { g: 'E → E + T | T\nT → x | ( E )', w: 'x(' }, frame: 2, caption: 'An error: no state on the path can shift ( straight after x. The driver stops at the first symbol that cannot continue any sentence.' },
      { tip: 'The driver runs in linear time: every symbol is shifted once, and every reduction builds one node of the tree.' },
      { list: ['The stack holds states; the top state and the next symbol pick the action.', 'A reduction pops one state per symbol of the right side, then follows GOTO.', 'The same loop runs LR(0), SLR(1), LALR(1) and LR(1) tables.', 'Errors are found at the first symbol that cannot continue.'] },
      { exercise: 'parse-ex-lr-error' },
      { exercise: 'parse-ex-lr-pops' },
    ],
  });

  C.lesson({
    id: 'parse-l-lr1-lalr', chapter: 'parse-ch-lr', title: 'LR(1) lookaheads and LALR(1) merging', minutes: 14,
    summary: 'Carry the possible next terminal inside every item, then merge states with the same core to save space.',
    blocks: [
      'SLR(1) uses FOLLOW(A), the terminals that can follow A *anywhere*. A more precise parser remembers what can follow A *here*, in this particular context. It writes that terminal into the item.',
      { def: 'LR(1) item', text: '[A → α • β, a]: the LR(0) item A → α • β with a lookahead terminal a. When the dot reaches the end, reduce only if the next input symbol is a.' },
      'Closure now computes lookaheads too: from [A → α • B γ, a], each new item B → • δ gets every terminal in FIRST(γ a). Goto carries lookaheads along unchanged.',
      { topic: 'lr1-items', input: { g: 'S → c | A A\nA → B\nB → c' }, caption: 'Watch the lookaheads: the first A in A A is followed by another A (so by c), the second by the end of input ($). LR(0) cannot tell these apart; LR(1) can.' },
      { predict: { q: 'Grammar S → c A d | d A B | A c B, A → d, B → A. In the LR(1) state reached from the start on d, which lookahead does the complete item A → d • carry?', options: ['{c}', '{c, d, $}', '{d}'], answer: 0, explain: 'The item comes from S → • A c B in the start state, where A is followed by c. FOLLOW(A) = {c, d, $} is what SLR(1) would use, and d clashes with the shift on d in the same state.' } },
      { h: 'LALR(1): fewer states, nearly the same power' },
      'Canonical LR(1) automata can have many more states than LR(0), because states with the same items but different lookaheads are kept apart. **LALR(1)** merges every group of LR(1) states with the same *core* (the same LR(0) items) and unites their lookaheads. The result has exactly as many states as the LR(0) automaton.',
      { topic: 'lalr-merge', input: { g: 'S → c | A A\nA → B\nB → c' }, caption: 'Pairs of states with equal cores fold together; their lookaheads are united. Here no conflict appears.' },
      { topic: 'lalr-merge', input: { g: 'S → a X b | c Y b | a Y d | c X d\nX → e\nY → e' }, frame: 3, caption: 'Here merging creates a reduce/reduce conflict that the LR(1) automaton did not have.' },
      { warn: 'Merging can create reduce/reduce conflicts, but never a shift/reduce conflict: shifts depend only on the core, so a merged state that could shift and reduce on a would already do so in one of the states it came from.' },
      { list: ['An LR(1) item carries the terminal that may follow when it is complete.', 'Lookaheads of new items come from FIRST(γ a).', 'LALR(1) merges states with the same core; it has as many states as LR(0).', 'Merging can only add reduce/reduce conflicts.'] },
      { exercise: 'parse-ex-lr1-la' },
      { exercise: 'parse-ex-lalr-count' },
      { exercise: 'parse-ex-lalr-merge' },
    ],
  });

  C.lesson({
    id: 'parse-l-precedence', chapter: 'parse-ch-lr', title: 'Precedence and associativity settle conflicts', minutes: 11,
    summary: 'An ambiguous expression grammar plus a few declarations gives a small, fast table.',
    blocks: [
      'E → E + E | E * E | ( E ) | n is the shortest grammar for expressions, but it is ambiguous, so every LR table for it has conflicts. Instead of rewriting the grammar into layers, parser generators let you declare how operators bind and resolve the conflicts with that.',
      { def: 'Precedence declarations', text: '%left, %right and %nonassoc lines list operators from the loosest to the tightest binding. A rule takes the precedence of its last terminal. A shift/reduce conflict between a rule and a lookahead terminal is settled by comparing them.' },
      { steps: ['The lookahead binds tighter than the rule: shift.', 'The rule binds tighter: reduce.', 'Equal, and %left: reduce (group to the left). %right: shift (group to the right). %nonassoc: error.'] },
      { topic: 'lr-precedence', input: { g: '%left +\n%left *\nE → E + E | E * E | ( E ) | n', w: 'n+n*n+n' }, caption: 'With E + E on the stack and * next, the parser shifts: * binds tighter. With E * E on the stack and + next, it reduces.' },
      { predict: { q: 'With %left + and %left *, the stack holds E + E and the next input is +. Shift or reduce?', options: ['Shift: n + (n + n)', 'Reduce: (n + n) + n'], answer: 1, explain: 'Same precedence, left associative: reduce, so the earlier + groups first.' } },
      { topic: 'lr-precedence', input: { g: '%right +\n%left *\nE → E + E | E * E | ( E ) | n', w: 'n+n+n' }, frame: 5, caption: 'Declared %right, the same + groups to the right.' },
      { warn: 'With no declarations, parser generators settle a shift/reduce conflict by shifting. For E → E - E | n that silently groups n - n - n as n - (n - n), which is wrong for subtraction.' },
      { list: ['Declarations order operators from loose to tight; a rule takes its last terminal\'s level.', 'Higher lookahead: shift. Higher rule: reduce.', 'Equal: %left reduces, %right shifts, %nonassoc is an error.', 'Unresolved shift/reduce conflicts default to shift.'] },
      { exercise: 'parse-ex-prec-right' },
      { exercise: 'parse-ex-prec-nonassoc' },
      { exercise: 'parse-ex-prec-default' },
    ],
  });

  C.lesson({
    id: 'parse-l-classify', chapter: 'parse-ch-lr', title: 'Which method takes which grammar', minutes: 10,
    summary: 'LR(0) ⊂ SLR(1) ⊂ LALR(1) ⊂ LR(1): a grammar is placed by the first table with no conflicts.',
    blocks: [
      'The four LR methods form a ladder. Every LR(0) grammar is SLR(1), every SLR(1) grammar is LALR(1), and every LALR(1) grammar is LR(1). Each step is strict: there are grammars on each rung that fail the one below.',
      { table: [['method', 'states', 'a complete item reduces on'], ['LR(0)', 'LR(0) sets', 'every terminal'], ['SLR(1)', 'LR(0) sets', 'FOLLOW of its left side'], ['LALR(1)', 'LR(0) sets', 'merged LR(1) lookaheads'], ['LR(1)', 'LR(1) sets, often many more', 'its own lookahead']], caption: 'Same driver, four ways of filling the table.' },
      { topic: 'lr-classify', input: { g: 'S → c | A A\nA → B\nB → c' }, frame: 6, caption: 'All four tables are built; the grammar is placed on the lowest rung with no conflict.' },
      { predict: { q: 'Can an ambiguous grammar be LR(1)?', options: ['Yes, with enough lookahead states', 'No: an ambiguous grammar has a conflict in every LR table'], answer: 1, explain: 'A conflict-free LR table gives exactly one rightmost derivation per string. An ambiguous grammar has a string with two, so some cell must hold two actions.' } },
      { tip: 'Not LR(1) does not mean ambiguous. S → x S x | x is unambiguous, but the parser cannot know where the middle is without seeing the end.' },
      { topic: 'lr-classify', input: { g: 'S → a X b | c Y b | a Y d | c X d\nX → e\nY → e' }, frame: 6, caption: 'LR(1) but not LALR(1): merging the two states for e creates a reduce/reduce conflict.' },
      { list: ['LR(0) ⊂ SLR(1) ⊂ LALR(1) ⊂ LR(1), each step strict.', 'Ambiguous grammars are never LR(k).', 'Unambiguous grammars may still fail LR(1).', 'In practice LALR(1) is the sweet spot: LR(0)-sized tables, almost LR(1) power.'] },
      { exercise: 'parse-ex-class-1' },
      { exercise: 'parse-ex-class-2' },
      { exercise: 'parse-ex-class-3' },
      { exercise: 'parse-ex-class-4' },
      { exercise: 'parse-ex-class-5' },
      { exercise: 'parse-ex-class-ll' },
    ],
  });

  // ---- chapter 3 exercises ---------------------------------------------------------------------------------
  const GH = 'E -> E - P | P\nP -> q | [ E ]';
  ex({ id: 'parse-ex-handle-1', chapter: 'parse-ch-lr', title: 'Spot the handle', kind: 'choice', level: 1,
    text: ['Grammar:', show(GH), 'In the right sentential form E - q - q, which part is the handle?'],
    options: ['the first q, to be reduced by P → q', 'the second q, to be reduced by P → q', 'E - q', 'E'],
    answer: 0, why: 'Rightmost: E ⇒ E - P ⇒ E - q ⇒ E - P - q ⇒ E - q - q. The last step replaced the first q\'s P.',
    solution: 0, wrong: [1, 2],
    hints: H('Write the rightmost derivation of E - q - q.', 'In a rightmost derivation the last q is produced before the middle one.', 'The handle is the first q (P → q): reducing it gives E - P - q, the previous step.') });
  ex({ id: 'parse-ex-handle-2', chapter: 'parse-ch-lr', title: 'Spot the handle in brackets', kind: 'choice', level: 2,
    text: ['Same grammar:', show(GH), 'In the right sentential form E - [ P ], what is the handle?'],
    options: ['P, by E → P', '[ P ], by P → [ E ]', 'E - [ P ]', 'there is none'],
    answer: 0, why: 'E ⇒ E - P ⇒ E - [ E ] ⇒ E - [ P ]: the last step replaced E by P inside the brackets.',
    solution: 0, wrong: [1, 2],
    hints: H('P → [ E ] needs an E between the brackets, not a P.', 'So the P inside must first become an E.', 'The handle is P with E → P.') });
  ex({ id: 'parse-ex-sr-count', chapter: 'parse-ch-lr', title: 'Count the reductions', kind: 'number', level: 2,
    text: ['A shift-reduce parser for this grammar reads q-[q]. How many reductions does it make (not counting the final accept)?', show(GH)],
    answer: 6, solution: '6', wrong: ['5', '4'],
    hints: H('One reduction per interior node of the parse tree.', 'Draw the tree: E → E - P at the root; the left E is P → q; the right P is [ E ] with E → P → q inside.', 'P → q, E → P, P → q, E → P, P → [ E ], E → E - P: 6.') });
  ex({ id: 'parse-ex-closure', chapter: 'parse-ch-lr', title: 'Close an item set', kind: 'string', level: 2,
    text: ['Grammar:', show(GH), 'Write the closure of { P → [ • E ] }. Separate the items with semicolons, like P → • q; E → • P.'],
    placeholder: 'A → α • β; B → • γ', accept: itemsAccept(['P → [ • E ]', 'E → • E - P', 'E → • P', 'P → • q', 'P → • [ E ]']),
    answer: 'P → [ • E ]; E → • E - P; E → • P; P → • q; P → • [ E ]',
    solution: 'P -> [ . E ]; E -> . E - P; E -> . P; P -> . q; P -> . [ E ]',
    wrong: ['P → [ • E ]; E → • E - P; E → • P', 'P → [ • E ]; E → • E - P; E → • P; P → • q', 'P → [ E • ]; E → • E - P; E → • P; P → • q; P → • [ E ]'],
    hints: H('The dot is before E: add both rules of E with the dot at the start.', 'E → • P puts the dot before P: add both rules of P.', 'P → [ • E ]; E → • E - P; E → • P; P → • q; P → • [ E ].') });
  ex({ id: 'parse-ex-goto', chapter: 'parse-ch-lr', title: 'Move the dot', kind: 'string', level: 2,
    text: ['Same grammar. Let I be the closure of { P → [ • E ] } from the last exercise. Write goto(I, E), items separated by semicolons.', show(GH)],
    placeholder: 'A → α • β; B → • γ', accept: itemsAccept(['P → [ E • ]', 'E → E • - P']),
    answer: 'P → [ E • ]; E → E • - P', solution: 'E → E • - P; P → [ E • ]',
    wrong: ['P → [ E • ]', 'P → [ E • ]; E → E • - P; E → • P', 'E → E - • P; P → [ E • ]'],
    hints: H('Take the items with the dot just before E.', 'There are two: P → [ • E ] and E → • E - P. Move the dot over E.', 'P → [ E • ]; E → E • - P. Neither has a dot before a nonterminal, so closure adds nothing.') });
  ex({ id: 'parse-ex-lr0-count', chapter: 'parse-ch-lr', title: 'How many states?', kind: 'number', level: 3,
    text: ['How many states does the LR(0) automaton of this grammar have, counting the start state built from E\' → • E?', show(GH)],
    answer: 9, solution: '9', wrong: ['8', '10'],
    hints: H('Start: the closure of E\' → • E. Then goto on E, P, q and [.', 'The state after [ goes to the same states on P, q and [ as the start state does: they are not new.', '9: start, after E, after P, after q, after [, after E -, after [ E, after E - P, after [ E ].') });

  const LR0X = lrExercise('Z -> b Z | c', 'lr0');
  const lr0Wrong1 = Object.assign({}, LR0X.cells);
  for (const k of Object.keys(lr0Wrong1)) if (/^r/.test(lr0Wrong1[k]) && !/\|\$$/.test(k)) lr0Wrong1[k] = '';
  const lr0Wrong2 = Object.assign({}, LR0X.cells, { '0|Z': '' });
  ex({ id: 'parse-ex-lr0-table', chapter: 'parse-ch-lr', title: 'Fill an LR(0) table', kind: 'table', table: 'custom', level: 2,
    rows: LR0X.rows, cols: LR0X.cols, cells: LR0X.cells, corner: 'state',
    text: ['Rules, numbered:', { code: LR0X.rules, lang: 'grammar' }, 'The LR(0) states are:', { table: LR0X.states },
      'Fill in the LR(0) table. Write s3 for shift and go to state 3, r2 for reduce by rule 2, acc for accept, a state number in a GOTO column, and leave error cells empty.'],
    solution: LR0X.cells, wrong: [lr0Wrong1, lr0Wrong2],
    hints: H('Shifts come from the transitions on b and c; GOTO from the transitions on Z.', 'In LR(0) a complete item reduces on every terminal and on $.', 'State 0: s2 on b, s3 on c, GOTO 1 on Z. The accept is in state 1 under $. Each complete item Z → b Z • and Z → c • reduces under b, c and $ (r1 and r2).') });

  const SLRX = lrExercise(GA, 'slr');
  const LR0GA = lrExercise(GA, 'lr0');
  const slrWrong1 = Object.assign({}, SLRX.cells);
  for (const k of Object.keys(slrWrong1)) if (/^r/.test(LR0GA.cells[k] || '') && !slrWrong1[k]) slrWrong1[k] = LR0GA.cells[k];
  const slrWrong2 = Object.assign({}, SLRX.cells, { '1|$': '' });
  ex({ id: 'parse-ex-slr-table', chapter: 'parse-ch-lr', title: 'Fill an SLR(1) table', kind: 'table', table: 'custom', level: 3,
    rows: SLRX.rows, cols: SLRX.cols, cells: SLRX.cells, corner: 'state',
    text: ['Rules, numbered:', { code: SLRX.rules, lang: 'grammar' }, 'The LR(0) states are:', { table: SLRX.states },
      'Fill in the SLR(1) table (s3, r2, acc, GOTO numbers, empty for errors). FOLLOW(S) = {$} and FOLLOW(K) = {m}.'],
    solution: SLRX.cells, wrong: [slrWrong1, slrWrong2],
    hints: H('Transitions give the shifts and GOTOs, exactly as for LR(0).', 'A complete item reduces only under FOLLOW of its left side: K → • and K → g K • under m, S → K m • under $.', 'States 0 and 3 shift g and reduce K → ε (r3) on m only; state 2 shifts m; state 1 accepts on $; state 4 reduces r1 on $; state 5 reduces r2 on m. GOTO: 0 on S to 1, on K to 2; 3 on K to 5.') });
  ex({ id: 'parse-ex-lr0-conflict', chapter: 'parse-ch-lr', title: 'Find the LR(0) conflicts', kind: 'string', set: true, level: 2,
    text: ['Same grammar and states as the last exercise:', { table: LR0GA.states }, 'Which states have a conflict in the LR(0) table? Write the set of state numbers.'],
    answer: '{0, 3}', solution: '3, 0', wrong: ['{0}', '{3, 5}', '{2}'],
    hints: H('Look for a complete item together with a shift, or two complete items.', 'K → • is complete. Which states hold it, and do they also shift something?', 'States 0 and 3 hold K → • and shift on g: {0, 3}.') });

  ex({ id: 'parse-ex-lr-error', chapter: 'parse-ch-lr', title: 'Where the driver stops', kind: 'string', level: 2,
    text: ['An LR parser for this grammar reads q-[q-] . At which input symbol does it report the error?', show(GH)],
    answer: ']', solution: ']', wrong: ['-', '['],
    hints: H('Everything up to q-[q- can still be the start of a sentence.', 'After -, the grammar needs a P: a q or a [.', 'It stops at the final ], where a q or [ was expected.') });
  ex({ id: 'parse-ex-lr-pops', chapter: 'parse-ch-lr', title: 'Popping on a reduce', kind: 'number', level: 1,
    text: ['The LR driver reduces by P → [ E ]. How many states does it pop from its stack before it consults GOTO?'],
    answer: 3, solution: '3', wrong: ['1', '4'],
    hints: H('One state per symbol of the right side.', 'The right side is [ E ].', '3.') });

  const GL = 'S -> c A d | d A B | A c B\nA -> d\nB -> A';
  ex({ id: 'parse-ex-lr1-la', chapter: 'parse-ch-lr', title: 'A lookahead in context', kind: 'string', set: true, level: 3,
    text: ['Grammar:', show(GL), 'In the canonical LR(1) automaton, take the state reached from the start state on d. It holds the complete item A → d •. Which lookaheads does that item carry? Write a set.'],
    answer: '{c}', solution: 'c', wrong: ['{c, d, $}', '{d}', '{$}'],
    hints: H('In the start state, which items have the dot before A, and what follows A in them?', 'S → • A c B puts A → • d in the start state with lookahead c. Moving over d keeps it.', '{c}. (S → d • A B is in the same state, but its A has not been started yet.)') });
  ex({ id: 'parse-ex-lalr-count', chapter: 'parse-ch-lr', title: 'States after merging', kind: 'number', level: 2,
    text: ['The canonical LR(1) automaton of this grammar has 14 states. How many does the LALR(1) automaton have?', show(GL)],
    answer: 13, solution: '13', wrong: ['14', '7'],
    hints: H('LALR(1) has exactly as many states as the LR(0) automaton.', 'Only one pair of LR(1) states has the same core: two copies of A → d •, with lookaheads d and $.', '13.') });
  ex({ id: 'parse-ex-lalr-merge', chapter: 'parse-ch-lr', title: 'What merging can break', kind: 'choice', level: 2,
    text: 'An LR(1) table has no conflicts. After merging its states with equal cores into an LALR(1) table, which conflicts can appear?',
    options: ['reduce/reduce only', 'shift/reduce only', 'both kinds', 'none: merging never creates conflicts'],
    answer: 0, why: 'Shifts depend only on the core, so a shift/reduce clash in the merged state already exists in one of its parts.',
    solution: 0, wrong: [1, 2, 3],
    hints: H('What does a merged state shift on? Does that depend on the lookaheads?', 'It depends only on the core, which the merged states share.', 'Only reduce/reduce: two complete items whose lookahead sets were disjoint in each part can overlap after uniting.') });

  ex({ id: 'parse-ex-prec-right', chapter: 'parse-ch-lr', title: 'A right-associative power', kind: 'choice', level: 1,
    text: ['Declarations and grammar:', gram('%left *\n%right ^\nE → E * E | E ^ E | n'), 'The stack holds E ^ E and the next input is ^. What does the parser do?'],
    options: ['Shift: ^ groups to the right', 'Reduce: ^ groups to the left', 'Report an error'],
    answer: 0, solution: 0, wrong: [1, 2],
    hints: H('The rule E → E ^ E has the precedence of ^, the same as the lookahead.', 'Equal precedence: associativity decides.', '%right: shift, so n ^ n ^ n is n ^ (n ^ n).') });
  ex({ id: 'parse-ex-prec-nonassoc', chapter: 'parse-ch-lr', title: 'A comparison that does not chain', kind: 'choice', level: 2,
    text: ['Declarations and grammar:', gram('%nonassoc <\n%left +\nE → E < E | E + E | n'), 'What happens to n < n < n?'],
    options: ['It is an error', 'It parses as (n < n) < n', 'It parses as n < (n < n)'],
    answer: 0, solution: 0, wrong: [1, 2],
    hints: H('With E < E on the stack and < next, the rule and the lookahead have equal precedence.', '%nonassoc turns that cell into an error.', 'An error: a < b < c is refused.') });
  ex({ id: 'parse-ex-prec-default', chapter: 'parse-ch-lr', title: 'No declarations at all', kind: 'choice', level: 2,
    text: ['The grammar E → E - E | n has no precedence declarations. A parser generator resolves its shift/reduce conflicts the usual default way. How is n - n - n grouped?'],
    options: ['n - (n - n)', '(n - n) - n', 'It is rejected'],
    answer: 0, why: 'The default is to shift, which delays the first reduction and groups to the right.',
    solution: 0, wrong: [1, 2],
    hints: H('What is the default resolution of a shift/reduce conflict?', 'Shift. With E - E on the stack and - next, the parser shifts.', 'n - (n - n), which is the wrong grouping for subtraction.') });

  const CLASSES = ['LR(0)', 'SLR(1) but not LR(0)', 'LALR(1) but not SLR(1)', 'LR(1) but not LALR(1)', 'not LR(1)'];
  const classEx = (n, g, ans, level, hints, why) => ex({ id: 'parse-ex-class-' + n, chapter: 'parse-ch-lr', title: 'Which class? (' + n + ')', kind: 'choice', level,
    text: ['Place this grammar on the LR ladder: the lowest method whose table has no conflict.', gram(g)],
    options: CLASSES, answer: ans, why, solution: ans, wrong: [0, 1, 2, 3, 4].filter((i) => i !== ans).slice(0, 2), hints });
  classEx(1, 'R → R & t | t', 0, 1, H('Build the LR(0) states: how many hold a complete item?', 'Each complete item sits alone in its state, with nothing to shift.', 'LR(0). Left recursion is no problem for LR parsers.'), 'Every complete item is alone in its state.');
  classEx(2, 'S → K m\nK → g K | ε', 1, 2, H('The ε-rule gives a complete item K → • in a state that also shifts g.', 'FOLLOW(K) = {m}. Does that clash with g?', 'SLR(1) but not LR(0).'), 'K → • clashes with the shift on g in LR(0), but FOLLOW(K) = {m}.');
  classEx(3, GL.replace(/->/g, '→'), 2, 3, H('FOLLOW(A) = {c, d, $}. In the state after d from the start, A → d • and a shift on d meet.', 'In LR(1), that A → d • has lookahead c only.', 'LALR(1) but not SLR(1): merging the two A → d • states (lookaheads d and $) is harmless.'), 'SLR(1) reduces A → d • on d and clashes with a shift; the LR(1) lookahead is only c, and merging stays safe.');
  classEx(4, 'S → A B B | B a | a b B\nA → b\nB → b | A c', 3, 3, H('LALR(1) tables are much smaller here: the LR(1) automaton has 18 states, the LR(0) one 13.', 'After a b, two different contexts need A → b • and B → b • on different lookaheads; merging unites them.', 'LR(1) but not LALR(1): merging makes a reduce/reduce conflict.'), 'Merging the states with the cores A → b •, B → b • creates a reduce/reduce conflict.');
  classEx(5, 'S → x S x | x', 4, 2, H('The language is the odd-length strings of x\'s. Is the grammar ambiguous?', 'It is not, but after reading some x\'s the parser must decide where the middle is.', 'Not LR(1): one symbol of lookahead never tells the middle x from the others.'), 'The middle x cannot be found with one symbol of lookahead.');
  ex({ id: 'parse-ex-class-ll', chapter: 'parse-ch-lr', title: 'LL versus LR', kind: 'choice', level: 2,
    text: 'Which of these grammars are LR(1) but not LL(1)? Choose all.',
    options: ['R → R & t | t', 'S → u v | u w', 'S → K m, K → g K | ε', 'S → x S x | x'],
    answer: [0, 1], why: 'Left recursion and common prefixes stop LL(1) but not LR parsers, which wait until the whole right side is on the stack.',
    solution: [0, 1], wrong: [[0, 1, 2], [0, 1, 3]],
    hints: H('Left recursion and shared prefixes always break LL(1).', 'S → K m with K → g K | ε is LL(1) (check its table). S → x S x | x is not LR(1).', 'The first two: they are even LR(0).') });

  // =========================================================================================================
  // Chapter 4: CYK and Earley
  // =========================================================================================================
  C.lesson({
    id: 'parse-l-cyk', chapter: 'parse-ch-general', title: 'CYK: a pyramid of substrings', minutes: 12,
    summary: 'For every substring, the set of nonterminals that derive it, built from short to long.',
    blocks: [
      'LL and LR parsers are fast but fussy: they refuse ambiguous grammars and many others. Sometimes we need a parser that takes *any* context-free grammar, for natural language, for grammars still being designed, or to decide membership. CYK is the simplest.',
      'It needs the grammar in Chomsky normal form: every rule is A → B C or A → a. Then a substring of length 1 comes from a rule A → a, and a longer substring from A → B C, where B derives some first part and C the rest.',
      { def: 'CYK table', text: 'for each substring w[i .. i+ℓ), the set of nonterminals that derive it. Row ℓ = 1 comes from the rules A → a; a cell of length ℓ looks at every split into lengths k and ℓ − k and adds A for every rule A → B C with B in the first cell and C in the second. The word is in the language when the start symbol is in the top cell.' },
      { topic: 'cyk-fill', input: { g: 'S → E R | x\nE → E R | x\nR → P E\nP → +', w: 'x+x+x' }, caption: 'Each cell is filled from pairs of cells below it; arrows show which pair gave each entry. The top cell holds S: x+x+x is in the language.' },
      { predict: { q: 'A word of length 5 has how many cells in its CYK pyramid?', options: ['5', '10', '15', '25'], answer: 2, explain: '5 + 4 + 3 + 2 + 1 = 15: one cell for every substring.' } },
      'The table has about n²/2 cells and each cell tries up to n splits, so CYK takes time proportional to n³ times the size of the grammar.',
      { h: 'Trees from the table' },
      'Remember, for each entry, which split and which rule produced it. Starting at S in the top cell, follow those back-pointers down to the leaves. When an entry was produced in two ways, there are two trees.',
      { topic: 'cyk-tree', input: { g: 'S → E R | x\nE → E R | x\nR → P E\nP → +', w: 'x+x+x' }, frame: 12, caption: 'x+x+x has two trees: one groups the first two x\'s, the other the last two.' },
      { h: 'Try it yourself' },
      { sandbox: { kind: 'grammar', text: 'S → A T | A B\nT → M B\nM → A T | A B\nA → a\nB → b', input: 'aabb' }, caption: 'A grammar in Chomsky normal form for aⁿbⁿ. Try aaabbb, then abab.' },
      { list: ['CYK needs Chomsky normal form.', 'Cell (i, ℓ) holds every nonterminal deriving w[i .. i+ℓ).', 'Fill by length, trying every split: O(n³) time.', 'S in the top cell means accepted; back-pointers give every tree.'] },
      { exercise: 'parse-ex-cyk-1' },
      { exercise: 'parse-ex-cyk-2' },
      { exercise: 'parse-ex-cyk-3' },
      { exercise: 'parse-ex-cyk-trees' },
    ],
  });

  C.lesson({
    id: 'parse-l-earley', chapter: 'parse-ch-general', title: 'Earley: predict, scan, complete', minutes: 13,
    summary: 'A chart of dotted items with their start positions takes any grammar as written, left recursion and ε-rules included.',
    blocks: [
      'CYK needs the grammar converted first, and it fills every cell whether useful or not. **Earley\'s algorithm** works on the grammar as written and only considers items that could be part of a parse of the input so far.',
      { def: 'Earley item', text: '[A → α • β, j]: a rule with a dot, and the position j where this A started. Set k of the chart holds the items alive after reading k symbols.' },
      { steps: ['**Predict**: for [A → α • B β, j] in set k, add [B → • γ, k] for every rule of B.', '**Scan**: for [A → α • a β, j] in set k, if the next symbol is a, add [A → α a • β, j] to set k + 1.', '**Complete**: for [B → γ •, j] in set k, every [A → α • B β, i] in set j moves on: add [A → α B • β, i] to set k.', 'Accept when [S → γ •, 0] is in the last set.'] },
      { topic: 'earley-chart', input: { g: 'S → N V\nN → d n | n\nV → v N | v', w: 'dnvn' }, caption: 'Each column is one set. Scans move right one column; completions look back to the column where the finished item started.' },
      { predict: { q: 'Can Earley\'s algorithm handle the left-recursive grammar E → E + n | n?', options: ['No, it loops like recursive descent', 'Yes: predicting E twice in the same set adds nothing new'], answer: 1, explain: 'Items are kept in sets, so predicting E again in the same set finds the items already there and stops.' } },
      { topic: 'earley-chart', input: { g: 'E → E + n | n', w: 'n+n+n' }, caption: 'Left recursion: E → • E + n is predicted once per set, and completions climb back up through it.' },
      'Earley runs in O(n³) time in general, O(n²) for unambiguous grammars, and linear time for most LR(k) grammars. From the finished chart, the trees can be read off like in CYK.',
      { topic: 'earley-trees', input: { g: 'S → S + S | x', w: 'x+x+x' }, frame: 7, caption: 'One chart, two trees: the final item has two ways it was completed.' },
      { list: ['Items carry a dot and a start position.', 'Predict, scan and complete fill set after set.', 'Works on any grammar: ambiguous, left-recursive, with ε-rules.', 'Cubic in general, faster on friendly grammars.'] },
      { exercise: 'parse-ex-earley-set' },
      { exercise: 'parse-ex-earley-which' },
      { exercise: 'parse-ex-general-compare' },
    ],
  });

  const CY1 = 'S -> X Y | Y X\nX -> X Y | a\nY -> b';
  const CY2 = 'S -> L Q | L Z | S S\nZ -> S Q\nL -> (\nQ -> )';
  ex({ id: 'parse-ex-cyk-1', chapter: 'parse-ch-general', title: 'A small CYK pyramid', kind: 'table', table: 'cyk', grammar: CY1, word: 'abb',
    text: ['Fill in the CYK table for the word abb. The bottom row is single symbols; each row up is one symbol longer.', show(CY1)],
    solution: { '1,0': 'X', '1,1': 'Y', '1,2': 'Y', '2,0': 'S, X', '2,1': '', '3,0': 'S, X' },
    wrong: [{ '1,0': 'X', '1,1': 'Y', '1,2': 'Y', '2,0': 'S, X', '2,1': 'S', '3,0': 'S, X' }, { '1,0': 'X', '1,1': 'Y', '1,2': 'Y', '2,0': 'X', '2,1': '', '3,0': 'X' }],
    hints: H('Bottom row: a comes from X, b from Y.', 'ab is X Y, which both S and X derive. bb is Y Y, which nothing derives.', 'Bottom: X, Y, Y. Middle: S, X for ab; empty for bb. Top: abb splits as ab | b = X Y, giving S and X.') });
  ex({ id: 'parse-ex-cyk-2', chapter: 'parse-ch-general', title: 'Brackets in a pyramid', kind: 'table', table: 'cyk', grammar: CY2, word: '(())', level: 2,
    text: ['This grammar in Chomsky normal form describes balanced brackets. Fill in the CYK table for (()).', show(CY2)],
    solution: { '1,0': 'L', '1,1': 'L', '1,2': 'Q', '1,3': 'Q', '2,0': '', '2,1': 'S', '2,2': '', '3,0': '', '3,1': 'Z', '4,0': 'S' },
    wrong: [{ '1,0': 'L', '1,1': 'L', '1,2': 'Q', '1,3': 'Q', '2,0': '', '2,1': 'S', '2,2': '', '3,0': '', '3,1': 'Z', '4,0': '' }, { '1,0': 'L', '1,1': 'L', '1,2': 'Q', '1,3': 'Q', '2,0': '', '2,1': 'S', '2,2': '', '3,0': 'Z', '3,1': 'Z', '4,0': 'S' }],
    hints: H('Only () in the middle derives anything at length 2.', 'At length 3, ()) is S Q, which is Z.', 'Bottom: L, L, Q, Q. Length 2: nothing, S, nothing. Length 3: nothing, Z. Top: L Z gives S.') });
  ex({ id: 'parse-ex-cyk-3', chapter: 'parse-ch-general', title: 'A rejected word', kind: 'table', table: 'cyk', grammar: CY2, word: '())(', level: 2,
    text: ['Same grammar. Fill in the CYK table for ())( and see why it is rejected.', show(CY2)],
    solution: { '1,0': 'L', '1,1': 'Q', '1,2': 'Q', '1,3': 'L', '2,0': 'S', '2,1': '', '2,2': '', '3,0': 'Z', '3,1': '', '4,0': '' },
    wrong: [{ '1,0': 'L', '1,1': 'Q', '1,2': 'Q', '1,3': 'L', '2,0': 'S', '2,1': '', '2,2': '', '3,0': 'Z', '3,1': '', '4,0': 'S' }, { '1,0': 'L', '1,1': 'Q', '1,2': 'Q', '1,3': 'L', '2,0': 'S', '2,1': '', '2,2': '', '3,0': '', '3,1': '', '4,0': '' }],
    hints: H('() at the start gives S.', '()) is S Q, which is Z. Nothing else at lengths 2 and 3 derives anything.', 'The top cell would need L Q, L Z or S S over some split: none fits, so it is empty and the word is rejected.') });
  ex({ id: 'parse-ex-cyk-trees', chapter: 'parse-ch-general', title: 'Count the trees', kind: 'number', level: 3,
    text: ['How many parse trees does aaaa have in this grammar?', gram('S → S S | a')],
    answer: 5, solution: '5', wrong: ['4', '14', '3'],
    hints: H('Every tree is a full binary tree with four leaves.', 'Count by the top split: 1 + 3, 2 + 2, 3 + 1. A word of length 3 has 2 trees, length 2 has 1.', '2 + 1 + 2 = 5.') });
  const GE = 'S -> P o\nP -> P i | i';
  ex({ id: 'parse-ex-earley-set', chapter: 'parse-ch-general', title: 'One Earley set', kind: 'string', level: 2,
    text: ['Earley\'s algorithm runs on this grammar with the input iio. Write the items of set 1 (after reading the first i), each with its start position, separated by semicolons, like [P → • i, 0].', show(GE)],
    placeholder: '[A → α • β, 0]; …', accept: itemsAccept(['[P → i •, 0]', '[S → P • o, 0]', '[P → P • i, 0]']),
    answer: '[P → i •, 0]; [S → P • o, 0]; [P → P • i, 0]', solution: 'P -> i ., 0; S -> P . o, 0; P -> P . i, 0',
    wrong: ['[P → i •, 0]', '[P → i •, 0]; [S → P • o, 0]; [P → P • i, 0]; [P → • i, 1]', '[P → i •, 1]; [S → P • o, 0]; [P → P • i, 0]'],
    hints: H('Set 0 has [S → • P o, 0], [P → • P i, 0] and [P → • i, 0]. Scan i.', 'Scanning gives [P → i •, 0]. It is complete: which items in set 0 wait for a P?', '[P → i •, 0]; [S → P • o, 0]; [P → P • i, 0]. Nothing to predict: the dots stand before terminals.') });
  ex({ id: 'parse-ex-earley-which', chapter: 'parse-ch-general', title: 'Which parser takes it?', kind: 'choice', level: 1,
    text: ['Which of these parsers can parse with the grammar E → E + n | n as it is written, without rewriting it? Choose all.'],
    options: ['Earley', 'backtracking recursive descent', 'an LL(1) table', 'an LR(0) table'],
    answer: [0, 3], why: 'Left recursion stops both top-down methods; Earley and LR handle it.',
    solution: [0, 3], wrong: [[0], [0, 1, 3]],
    hints: H('The grammar is left-recursive.', 'Top-down methods cannot cope with left recursion; bottom-up and chart methods can.', 'Earley, and LR(0): the grammar is even LR(0).') });
  ex({ id: 'parse-ex-general-compare', chapter: 'parse-ch-general', title: 'CYK or Earley', kind: 'choice', level: 2,
    text: 'Which statements are true? Choose all.',
    options: ['CYK needs the grammar in Chomsky normal form; Earley takes it as written', 'Both find every parse tree of an ambiguous grammar', 'Earley runs in linear time on every grammar', 'Both take O(n³) time in the worst case'],
    answer: [0, 1, 3], solution: [0, 1, 3], wrong: [[0, 1, 2, 3], [0, 3]],
    hints: H('Recall what each algorithm requires of the grammar.', 'Earley is cubic in the worst case; linear only for many LR grammars.', 'All but the third.') });

  // =========================================================================================================
  // Chapter 5: operator precedence and the front end
  // =========================================================================================================
  C.lesson({
    id: 'parse-l-opp', chapter: 'parse-ch-front', title: 'Operator precedence: three relations between terminals', minutes: 13,
    summary: 'For expression grammars, comparing neighbouring operators is enough to find the handle.',
    blocks: [
      'In an expression, what decides the tree is how operators compare: * binds tighter than +, a ^ chain groups to the right. An **operator-precedence parser** uses nothing else. It looks only at terminals and three relations between them.',
      { def: 'Operator grammar', text: 'a grammar with no ε right sides and no right side with two nonterminals next to each other. Between any two nonterminals there is always an operator.' },
      { def: 'Precedence relations', text: 'a <· b: b\'s phrase starts inside, a handle begins at b. a ≐ b: a and b belong to the same handle, like ( and ). a ·> b: a\'s handle ends before b, so reduce.' },
      'They come from two sets per nonterminal: **LEADING(A)**, the first terminal of any string A derives (skipping one leading nonterminal), and **TRAILING(A)**, the last one. For a b in a right side: a ≐ b. For a A: a <· every terminal in LEADING(A). For A b: every terminal in TRAILING(A) ·> b.',
      { topic: 'opp-relations', input: { g: 'E → E + T | T\nT → T * P | P\nP → ( E ) | n' }, caption: 'LEADING and TRAILING first, then the relation table, filled one rule at a time.' },
      { predict: { q: 'In this grammar, how do + and * compare when + comes first, as in n + n * n?', options: ['+ <· *', '+ ·> *', '+ ≐ *'], answer: 0, explain: 'E → E + T puts + before T, and * ∈ LEADING(T): so + <· *. The * phrase is reduced first.' } },
      { h: 'The parse' },
      'The parser shifts while the top terminal on its stack is <· or ≐ the next input, and reduces when it is ·>. The handle runs back to the last <·.',
      { topic: 'opp-parse', input: { g: 'E → E + T | T\nT → T * P | P\nP → ( E ) | n', w: 'n+n*n' }, caption: 'Watch the relation between the top terminal and the next one. A ·> triggers a reduction of everything back to the last <·.' },
      { topic: 'opp-parse', input: { g: 'E → E - T | T\nT → F ^ T | F\nF → ( E ) | n', w: 'n^n^n' }, caption: 'A right-associative ^: ^ <· ^, so the parser keeps shifting and reduces from the right.' },
      { h: 'Precedence functions' },
      'The table can often be squeezed into two numbers per terminal, f and g, with a <· b exactly when f(a) < g(b), and so on. Not every table allows it: a cycle in the graph of relations means no functions exist.',
      { topic: 'opp-functions', input: { g: 'E → E + T | T\nT → T * P | P\nP → ( E ) | n', t: '' }, caption: 'Groups of equal values are merged, edges follow the relations, and the longest path from each node gives its value.' },
      { warn: 'Operator precedence parsing is small and quick, but it accepts some strings the grammar does not generate, and the same symbol cannot easily have two precedences (unary and binary minus).' },
      { list: ['Only operator grammars: no ε, no two nonterminals side by side.', 'Relations <·, ≐ and ·> between terminals come from LEADING and TRAILING.', 'Shift on <· and ≐, reduce on ·>, back to the last <·.', 'Precedence functions compress the table when its graph has no cycle.'] },
      { exercise: 'parse-ex-opp-table' },
      { exercise: 'parse-ex-opp-leading' },
      { exercise: 'parse-ex-opp-grammar' },
      { exercise: 'parse-ex-opp-first' },
      { exercise: 'parse-ex-opp-functions' },
    ],
  });

  C.lesson({
    id: 'parse-l-front-end', chapter: 'parse-ch-front', title: 'A tiny front end: lexer meets parser', minutes: 10,
    summary: 'Characters become tokens by longest match, and tokens become a tree by an LALR(1) parser with precedence.',
    blocks: [
      'A compiler does not parse characters. First a **lexer** cuts the source into tokens: names, numbers, operators. Then the parser works on tokens. The split pays off: tokens are regular, and a DFA handles them quickly; phrases need a grammar, and the parser handles them.',
      { def: 'Longest match', text: 'the lexer always takes the longest prefix of the remaining input that matches some token pattern; when two patterns match the same longest prefix, the one listed first wins.' },
      { code: 'id   = [a-z]+        num = [0-9]+\n=  +  *  (  )  ;     one token each\nspaces are skipped\n\nP → S | P S\nS → id = E ;\nE → E + E | E * E | ( E ) | id | num        with %left + and %left * (tighter)', lang: 'grammar' },
      { topic: 'front-end', input: { src: 'x = 12 + y*3;' }, caption: 'Characters at the bottom are grouped into tokens; tokens are shifted and reduced into the tree above them. * binds tighter, so y*3 becomes a node first.' },
      { predict: { q: 'How many tokens does the lexer make of ab=12;?', options: ['4', '6', '3'], answer: 0, explain: 'ab is one id (longest match), then =, then 12 as one num, then ;.' } },
      { topic: 'front-end', input: { src: 'x = 3 # 4;' }, frame: 15, caption: 'A lexical error: no pattern matches #. The lexer, not the parser, reports it.' },
      { topic: 'front-end', input: { src: 'x = 3 + ;' }, frame: 16, caption: 'A syntax error: every token is fine, but the parser has no action for ; straight after +.' },
      { h: 'Try it yourself' },
      { editor: { kind: 'regex', text: '(a|b)(a|b|0|1)*', tests: 'a\nab01\nb1\n-1a\n-\n-01' }, caption: 'A token pattern for names over a small alphabet: a letter, then letters or digits. The lexer is built from patterns like this one.' },
      { list: ['The lexer turns characters into tokens with a DFA, by longest match.', 'The parser turns tokens into a tree; here LALR(1) with precedence declarations.', 'Lexical errors are bad characters; syntax errors are bad orders of good tokens.', 'Regular languages for words, context-free for phrases.'] },
      { exercise: 'parse-ex-fe-tokens' },
      { exercise: 'parse-ex-fe-error' },
      { exercise: 'parse-ex-fe-regex' },
    ],
  });

  const OPG = 'E -> E ~ F | F\nF -> G @ F | G\nG -> n | ( E )';
  const OPR = T.opp.relationsFromGrammar(T.grammar.parse(OPG));
  const opTerms = ['~', '@', 'n', '(', ')', '$'];
  const opSol = {
    '~|~': '>', '~|@': '<', '~|n': '<', '~|(': '<', '~|)': '>', '~|$': '>',
    '@|~': '>', '@|@': '<', '@|n': '<', '@|(': '<', '@|)': '>', '@|$': '>',
    'n|~': '>', 'n|@': '>', 'n|)': '>', 'n|$': '>',
    '(|~': '<', '(|@': '<', '(|n': '<', '(|(': '<', '(|)': '=',
    ')|~': '>', ')|@': '>', ')|)': '>', ')|$': '>',
    '$|~': '<', '$|@': '<', '$|n': '<', '$|(': '<',
  };
  const opCells = {};
  for (const a of opTerms) for (const b of opTerms) opCells[a + '|' + b] = (OPR.rel[a] && OPR.rel[a][b]) || '';
  const opSolution = {};
  for (const k of Object.keys(opCells)) opSolution[k] = opSol[k] || '';
  ex({ id: 'parse-ex-opp-table', chapter: 'parse-ch-front', title: 'Fill a precedence table', kind: 'table', table: 'custom', level: 3,
    rows: opTerms, cols: opTerms, cells: opCells, corner: 'left \\ right',
    text: ['An operator grammar where ~ binds loosely and groups left, and @ binds tightly and groups right:', show(OPG),
      'Fill in the relation between the row terminal (on the left) and the column terminal (on the right): < for <·, = for ≐, > for ·>, and leave the cell empty when there is none.'],
    solution: opSolution,
    wrong: [Object.assign({}, opSolution, { '@|@': '>' }), Object.assign({}, opSolution, { '~|@': '>', '@|~': '<' }), Object.assign({}, opSolution, { '(|)': '' })],
    hints: H('LEADING(F) = {@, n, (} and TRAILING(F) = {@, n, )}; LEADING(E) adds ~, and so does TRAILING(E).', 'E → E ~ F: TRAILING(E) ·> ~ and ~ <· LEADING(F). F → G @ F: TRAILING(G) ·> @ and @ <· LEADING(F), which includes @ itself (right grouping).', 'Rows ~ and @: < on @, n, ( and > on ), $; ~ ·> ~, ~ <· @, @ ·> ~, @ <· @. Rows n and ): > on ~, @, ), $. Row (: < on ~, @, n, ( and = on ). Row $: < on ~, @, n, (.') });
  ex({ id: 'parse-ex-opp-leading', chapter: 'parse-ch-front', title: 'A LEADING set', kind: 'string', set: true, level: 2,
    text: ['Same grammar. What is LEADING(E)? Write a set.', show(OPG)],
    answer: '{~, @, n, (}', solution: '(, n, @, ~', wrong: ['{~}', '{n, (}', '{~, @, n, )}'],
    hints: H('E → E ~ F gives ~ (one leading nonterminal is skipped).', 'E → F brings in LEADING(F): @ from F → G @ F, and LEADING(G) through F → G.', '{~, @, n, (}.') });
  ex({ id: 'parse-ex-opp-grammar', chapter: 'parse-ch-front', title: 'Is it an operator grammar?', kind: 'choice', level: 1,
    text: 'Which of these are operator grammars? Choose all.',
    options: ['E → E ~ F | F, F → n', 'E → E O E | n, O → + | *', 'L → L ; x | x', 'S → a S | ε'],
    answer: [0, 2], why: 'E O E puts two nonterminals side by side, and S → ε is an ε right side.',
    solution: [0, 2], wrong: [[0, 1, 2], [0, 2, 3]],
    hints: H('Two conditions: no ε, and no two nonterminals next to each other.', 'E O E breaks the second; S → ε breaks the first.', 'The first and the third.') });
  ex({ id: 'parse-ex-opp-first', chapter: 'parse-ch-front', title: 'Which handle first?', kind: 'choice', level: 2,
    text: ['With the ~ and @ grammar, the operator-precedence parser reads n~n@n. After the first n is reduced, which operator\'s phrase is reduced next?', show(OPG)],
    options: ['@: n@n is reduced before ~', '~: n~n is reduced first', 'neither: the input is rejected'],
    answer: 0, solution: 0, wrong: [1, 2],
    hints: H('Compare ~ with @ when ~ comes first.', '~ <· @, so the parser shifts @ and its operand.', '@ first: the right operand of ~ is the whole n@n.') });
  ex({ id: 'parse-ex-opp-functions', chapter: 'parse-ch-front', title: 'When functions fail', kind: 'choice', level: 2,
    text: 'Precedence functions f and g replace a relation table when a <· b means f(a) < g(b), a ≐ b means f(a) = g(b) and a ·> b means f(a) > g(b). When do no such functions exist?',
    options: ['When the graph built from the relations has a cycle', 'When the table has an empty cell', 'When an operator is right-associative', 'When the grammar has parentheses'],
    answer: 0, solution: 0, wrong: [1, 2],
    hints: H('The values come from longest paths in a graph.', 'Longest paths exist only in a graph without cycles.', 'A cycle: then some value would have to be bigger than itself.') });

  ex({ id: 'parse-ex-fe-tokens', chapter: 'parse-ch-front', title: 'Count the tokens', kind: 'number', level: 1,
    text: ['The tiny front end has the tokens id = [a-z]+, num = [0-9]+, and one-character tokens = + * ( ) ;, with spaces skipped. How many tokens does it make of the line below?', { code: 'rate = r2*(10+x);', lang: 'grammar' }],
    answer: 11, solution: '11', wrong: ['10', '12', '9'],
    hints: H('Longest match: rate is one id, 10 is one num. What about r2?', 'r2 is the id r followed by the num 2: letters and digits are separate patterns here.', 'rate, =, r, 2, *, (, 10, +, x, ), ; : 11 tokens.') });
  ex({ id: 'parse-ex-fe-error', chapter: 'parse-ch-front', title: 'Lexical or syntax error?', kind: 'choice', level: 1,
    text: 'Which of these lines contain a syntax error, as opposed to a lexical one or none? Choose all.',
    options: ['x = 3 + ;', 'x = 3 # 4;', 'x = (y;', 'x = y*2;'],
    answer: [0, 2], why: 'Every token in x = 3 + ; and x = (y; is valid, but their order is not. # is not a token at all.',
    solution: [0, 2], wrong: [[0, 1, 2], [1]],
    hints: H('A lexical error is a character no token pattern matches.', '# is the only such character here.', 'The first and the third are syntax errors; the second is lexical; the fourth is fine.') });
  ex({ id: 'parse-ex-fe-regex', chapter: 'parse-ch-front', title: 'A token pattern', kind: 'regex', level: 1, alphabet: 'ab01',
    text: 'Write a regular expression over {a, b, 0, 1} for names: a letter (a or b) followed by any number of letters and digits.',
    ref: { member: (w) => /^[ab][ab01]*$/.test(w) }, solution: '(a|b)(a|b|0|1)*', wrong: ['(a|b|0|1)*', '(a|b)(a|b)*', '(a|b|0|1)(a|b|0|1)*'],
    hints: H('The first symbol is special: it must be a letter.', 'After that, anything goes, including nothing.', '(a|b)(a|b|0|1)*') });

  // ---- a guided tour and a course ------------------------------------------------------------------------------
  C.tour({
    id: 'parse-tour', title: 'A tour of the parsing part', blurb: 'From a grammar to its tables and a running parser, and where to try your own.',
    steps: [
      { route: 'topic=ll1-table', target: '#inputs', text: 'Every parsing topic takes a grammar you can type. One rule per line, alternatives with |, ε for the empty string. The chips below are ready-made examples.' },
      { target: '#stageWrap', text: 'The stage builds the LL(1) table cell by cell, from FIRST and FOLLOW. Conflicting cells are marked.' },
      { target: '#say', text: 'Each step is told in words, with the actual symbols: which rule went into which cell, and why.' },
      { target: '#timeline', text: 'Drag the timeline to jump to any step, or step with the arrow keys.' },
      { route: 'topic=lr0-items', target: '#stageWrap', text: 'Bottom up, the LR(0) automaton is built state by state: closure first, then goto on each symbol.' },
      { route: 'topic=lr-classify', target: '#inputs', text: 'Type any grammar here to see which of LR(0), SLR(1), LALR(1) and LR(1) take it, with the conflicts that stop the others.' },
      { route: 'topic=cyk-fill', target: '#stageWrap', text: 'CYK and Earley take every grammar, ambiguous ones too. Arrows show where each entry came from.' },
      { route: 'lesson=parse-l-ll1-table', target: '#main', text: 'Lessons explain one idea each, with the topic running inside and a question to answer before you read on.' },
      { route: 'exercise=parse-ex-ll1-2', target: '#answer', text: 'In table exercises you fill in the cells; each one is checked and wrong cells are marked in red. Hints come one at a time.' },
    ],
  });
  C.course({
    id: 'parse-course', title: 'Parsing, top down and bottom up', blurb: 'From guessing to tables: backtracking, LL(1), the LR family, the general algorithms, and a small front end.',
    steps: [
      { topic: 'rd-backtrack', note: 'Watch the parser re-enter A after it already succeeded: that is the cost of guessing.' },
      { topic: 'peg-packrat', note: 'The memo table fills each cell once; ordered choice commits to the first success.' },
      { lesson: 'parse-l-first', note: 'FIRST sets: the terminals that can start each phrase.' },
      { topic: 'first-sets', note: 'Rounds repeat until nothing changes; look past the symbols that can vanish.' },
      { topic: 'follow-sets', note: 'Watch FOLLOW flow from a left side into the last symbol of its right side.' },
      { topic: 'll1-table', note: 'Rules that read go under FIRST, ε-rules under FOLLOW.' },
      { topic: 'll1-conflict', note: 'Two rules in one cell: see which kind of conflict it is.' },
      { exercise: 'parse-ex-ll1-2', note: 'Fill a table of your own.' },
      { topic: 'll1-parse', note: 'The stack predicts; nothing is ever undone.' },
      { topic: 'left-recursion', note: 'The list keeps its language and changes the shape of its trees.' },
      { topic: 'left-factor', note: 'The shared prefix comes out first, then factoring repeats inside.' },
      { exercise: 'parse-ex-rw-list', note: 'Rewrite a grammar until it is LL(1).' },
      { topic: 'rd-codegen', note: 'Each procedure is a row of the table.' },
      { topic: 'll1-panic', note: 'Count the repairs: pops of missing terminals, pops at synchronising symbols, skips.' },
      { topic: 'shift-reduce', note: 'Reductions read backwards spell a rightmost derivation.' },
      { topic: 'lr0-items', note: 'Kernels first, then closure; equal item sets are one state.' },
      { topic: 'lr0-table', note: 'Find the state where a complete item meets a shift.' },
      { topic: 'slr-table', note: 'FOLLOW removes the reduce that caused the conflict.' },
      { topic: 'lr-parse', note: 'A reduction pops one state per symbol and follows GOTO.' },
      { topic: 'lr1-items', note: 'Lookaheads tell apart two places where the same rule is complete.' },
      { topic: 'lalr-merge', note: 'Equal cores fold together; once in a while that creates a reduce/reduce conflict.' },
      { topic: 'lr-precedence', note: 'Compare the rule with the lookahead: shift on higher, reduce on lower, associativity on equal.' },
      { topic: 'lr-classify', note: 'Place grammars on the ladder LR(0) ⊂ SLR(1) ⊂ LALR(1) ⊂ LR(1).' },
      { exercise: 'parse-ex-class-3', note: 'Classify a grammar yourself.' },
      { topic: 'cyk-fill', note: 'Every cell comes from a pair of cells below it.' },
      { topic: 'earley-chart', note: 'Predict, scan, complete; completions look back to where the item started.' },
      { topic: 'opp-parse', note: 'Shift on <· and ≐, reduce on ·>.' },
      { topic: 'front-end', note: 'Two machines in a row: a DFA for tokens, an LR automaton for phrases.' },
    ],
  });
})();
