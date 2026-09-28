// Part 2, finite automata and regular languages: the exercises. The chapters and lessons are in
// 20-regular.js, which loads first. Every exercise has a reference language (or answer), a worked
// solution, wrong answers the checker must turn down, and three hints, the last one a worked answer.
// Machines given in a question are shown as a little runnable figure, so the student can try strings.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;
  const H = (a, b, c) => [a, b, c];

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
  const ex = (x) => C.exercise(Object.assign({ level: 1 }, x, { text: Array.isArray(x.text) ? x.text.map(proseBlock) : prose(x.text), hints: x.hints.map(prose) }, x.options ? { options: x.options.map(prose) } : {}));
  const count = (w, c) => [...w].filter((x) => x === c).length;
  const bin = (w) => (w === '' ? 0 : parseInt(w, 2));
  // a machine shown inside a question, runnable on any string
  const shown = (text, input, caption) => ({ sandbox: { kind: 'fa', text, input: input || '' }, caption: caption || 'The machine in the question. Run it on a few strings before you answer.' });

  // =========================================================================================================
  // Chapter 1: finite automata
  // =========================================================================================================
  const A = 'reg-automata';

  ex({ id: 'reg-ex-dfa-ends-a', chapter: A, title: 'Ends in a', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} that accepts exactly the strings whose last symbol is a. The empty string has no last symbol, so it must be rejected.',
    ref: { regex: '(a|b)*a' }, member: (w) => w.endsWith('a'),
    solution: 'start n\naccept y\nn -a-> y\nn -b-> n\ny -a-> y\ny -b-> n',
    wrong: ['start n\naccept n\nn -a-> y\nn -b-> n\ny -a-> y\ny -b-> n', 'start n\naccept y\nn -a-> y\ny -b-> n', 'start y\naccept y\nn -a-> y\nn -b-> n\ny -a-> y\ny -b-> n'],
    hints: H('The machine only has to remember one thing: was the last symbol an a?', 'Two states: "last symbol was a" (accepting) and "anything else", which includes having read nothing yet.', 'start n, accept y; n -a-> y, n -b-> n, y -a-> y, y -b-> n.') });

  ex({ id: 'reg-ex-dfa-run-state', chapter: A, title: 'Where does the run end?', kind: 'string',
    text: ['This DFA keeps (number of a\'s − number of b\'s) mod 4 in its state. It starts in q0. In which state is it after reading aababbaa?',
      shown('start q0\naccept q0\nq0 -a-> q1\nq1 -a-> q2\nq2 -a-> q3\nq3 -a-> q0\nq0 -b-> q3\nq1 -b-> q0\nq2 -b-> q1\nq3 -b-> q2', '')],
    answer: ['q2'], solution: 'q2', wrong: ['q3', 'q1', 'q0'],
    hints: H('You do not need to trace eight moves: count instead.', 'aababbaa has 5 a\'s and 3 b\'s, so the difference is 2.', 'q2: 5 − 3 = 2, and 2 mod 4 = 2. Run the machine on aababbaa to watch it.') });

  ex({ id: 'reg-ex-dfa-count-moves', chapter: A, title: 'How many moves?', kind: 'number',
    text: 'A complete DFA has 7 states and the alphabet {0, 1, 2}. How many moves (arrows, counting each symbol separately) does it have?',
    answer: 21, solution: '21', wrong: ['7', '10', '14'],
    hints: H('Complete means every state has a move on every symbol.', 'Each state contributes one move per symbol.', '7 states × 3 symbols = 21 moves.') });

  ex({ id: 'reg-ex-dfa-facts', chapter: A, title: 'True about every DFA', kind: 'choice',
    text: 'Our DFAs may leave moves out: a missing move rejects. Which statements hold for every such DFA M?',
    options: ['M accepts ε exactly when its start state is accepting.', 'If M has no accepting state, it accepts no string at all.', 'If every state of M is accepting, M accepts every string over its alphabet.', 'A run of M on a string of length 5 lists 5 states.'],
    answer: [0, 1], solution: [0, 1], wrong: [[0, 1, 2], [0], [0, 1, 3]],
    hints: H('Reading ε makes no moves at all.', 'A missing move sends the run to a dead state, even when every drawn state accepts.', 'The first two. The third fails as soon as a move is missing, and a run on 5 symbols lists 6 states.') });

  ex({ id: 'reg-ex-dfa-two-b', chapter: A, title: 'At least two b\'s, in three states', kind: 'machine', machine: 'dfa', alphabet: 'ab', maxStates: 3,
    text: 'Build a DFA with at most 3 states for the strings over {a, b} that contain at least two b\'s.',
    member: (w) => count(w, 'b') >= 2,
    solution: 'start z\naccept t\nz -a-> z\nz -b-> o\no -a-> o\no -b-> t\nt -a,b-> t',
    wrong: ['start z\naccept t\nz -a-> z\nz -b-> o\no -a-> o\no -b-> t\nt -a-> t', 'start z\naccept t\nz -a-> z\nz -b-> o\no -a-> o\no -b-> t\nt -a,b-> t\nd -a,b-> d', 'start z\naccept o t\nz -a-> z\nz -b-> o\no -a-> o\no -b-> t\nt -a,b-> t'],
    hints: H('Count the b\'s, but stop counting at two: "two or more" is one state.', 'States: no b yet, one b, two or more. a never changes the count.', 'z -a-> z, z -b-> o, o -a-> o, o -b-> t, t -a,b-> t; start z, accept t.') });

  ex({ id: 'reg-ex-dfa-starts-ba', chapter: A, title: 'Starts with ba, complete', kind: 'machine', machine: 'dfa', alphabet: 'ab', complete: true,
    text: 'Build a complete DFA (a move from every state on every symbol) for the strings over {a, b} that start with ba.',
    member: (w) => w.startsWith('ba'),
    solution: 'start s\naccept ok\ns -b-> b1\ns -a-> dead\nb1 -a-> ok\nb1 -b-> dead\nok -a,b-> ok\ndead -a,b-> dead',
    wrong: ['start s\naccept ok\ns -b-> b1\nb1 -a-> ok\nok -a,b-> ok', 'start s\naccept ok\ns -b-> b1\ns -a-> dead\nb1 -a-> ok\nb1 -b-> dead\nok -a-> ok\nok -b-> dead\ndead -a,b-> dead', 'start s\naccept ok\ns -b-> b1\ns -a-> s\nb1 -a-> ok\nb1 -b-> s\nok -a,b-> ok\ndead -a,b-> dead'],
    hints: H('Once the string has gone wrong (it starts with a, or with bb) nothing can save it.', 'That hopeless situation is one state, the dead state, with a loop on both symbols.', 's -b-> b1, s -a-> dead, b1 -a-> ok, b1 -b-> dead, ok -a,b-> ok, dead -a,b-> dead.') });

  ex({ id: 'reg-ex-dfa-no-aaa', chapter: A, level: 2, title: 'Never three a\'s in a row', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} for the strings that never have three a\'s in a row (aa is fine, aaa is not).',
    member: (w) => !w.includes('aaa'),
    solution: 'start z\naccept z one two\nz -a-> one\nz -b-> z\none -a-> two\none -b-> z\ntwo -b-> z\ntwo -a-> dead\ndead -a,b-> dead',
    wrong: ['start z\naccept z one two\nz -a-> one\nz -b-> z\none -a-> two\none -b-> z\ntwo -b-> two\ntwo -a-> dead\ndead -a,b-> dead', 'start z\naccept z one\nz -a-> one\nz -b-> z\none -a-> two\none -b-> z\ntwo -b-> z\ntwo -a-> dead\ndead -a,b-> dead', 'start z\naccept z one two\nz -a-> one\nz -b-> z\none -a-> two\none -b-> z\ntwo -b-> z\ntwo -a-> z'],
    hints: H('Remember how many a\'s the string ends with: 0, 1 or 2. A third one is fatal.', 'A b resets the run of a\'s to 0, from every live state.', 'z -a-> one -a-> two -a-> dead, b from z, one, two back to z, dead loops; accept z, one, two.') });

  ex({ id: 'reg-ex-dfa-contains-bba', chapter: A, level: 2, title: 'Contains bba', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} for the strings that contain bba somewhere. Mind what happens on bbba.',
    member: (w) => w.includes('bba'),
    solution: 'start n\naccept got\nn -a-> n\nn -b-> b\nb -a-> n\nb -b-> bb\nbb -a-> got\nbb -b-> bb\ngot -a,b-> got',
    wrong: ['start n\naccept got\nn -a-> n\nn -b-> b\nb -a-> n\nb -b-> bb\nbb -a-> got\nbb -b-> n\ngot -a,b-> got', 'start n\naccept got\nn -a-> n\nn -b-> b\nb -a-> n\nb -b-> bb\nbb -a-> got\nbb -b-> b\ngot -a,b-> got', 'start n\naccept got\nn -a-> n\nn -b-> b\nb -a-> n\nb -b-> bb\nbb -a-> got\nbb -b-> bb\ngot -a-> got\ngot -b-> n'],
    hints: H('States for the progress: nothing, b, bb, and found.', 'After bb, another b leaves you with ...bb at the end: the progress stays at bb, it does not fall back.', 'n -a-> n, n -b-> b, b -a-> n, b -b-> bb, bb -b-> bb, bb -a-> got, got -a,b-> got.') });

  ex({ id: 'reg-ex-dfa-table', chapter: A, level: 2, title: 'Fill in the moves for "contains aab"', kind: 'table', table: 'custom',
    text: 'A DFA for the strings over {a, b} that contain aab has four states. N means no progress, A means the input ends in a (but not aa), AA means it ends in aa, and AAB means aab has been seen. Fill in where each move goes.',
    rows: ['N', 'A', 'AA', 'AAB'], cols: ['a', 'b'], corner: 'δ',
    cells: { 'N|a': 'A', 'N|b': 'N', 'A|a': 'AA', 'A|b': 'N', 'AA|a': 'AA', 'AA|b': 'AAB', 'AAB|a': 'AAB', 'AAB|b': 'AAB' },
    solution: { 'N|a': 'A', 'N|b': 'N', 'A|a': 'AA', 'A|b': 'N', 'AA|a': 'AA', 'AA|b': 'AAB', 'AAB|a': 'AAB', 'AAB|b': 'AAB' },
    wrong: [{ 'N|a': 'A', 'N|b': 'N', 'A|a': 'AA', 'A|b': 'N', 'AA|a': 'N', 'AA|b': 'AAB', 'AAB|a': 'AAB', 'AAB|b': 'AAB' }, { 'N|a': 'A', 'N|b': 'N', 'A|a': 'AA', 'A|b': 'A', 'AA|a': 'AA', 'AA|b': 'AAB', 'AAB|a': 'AAB', 'AAB|b': 'AAB' }],
    hints: H('For each cell, write down what the input ends with after the new symbol, and keep the longest end that starts aab.', 'aa followed by a ends in aaa, whose longest useful end is aa again. ab ends in b, which starts nothing.', 'N: a→A, b→N. A: a→AA, b→N. AA: a→AA, b→AAB. AAB: both stay in AAB.') });

  ex({ id: 'reg-ex-dfa-mod3-two', chapter: A, level: 2, title: 'Binary numbers that leave 2', kind: 'machine', machine: 'dfa', alphabet: '01',
    text: 'Build a DFA over {0, 1} for the binary numerals (read from the most significant bit, leading zeros allowed) whose value leaves remainder 2 when divided by 3. The empty numeral counts as 0.',
    member: (w) => bin(w) % 3 === 2,
    solution: 'start r0\naccept r2\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r0\nr2 -0-> r1\nr2 -1-> r2',
    wrong: ['start r0\naccept r1\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r0\nr2 -0-> r1\nr2 -1-> r2', 'start r0\naccept r2\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r0\nr2 -0-> r1\nr2 -1-> r0', 'start r0\naccept r2\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r1\nr1 -1-> r2\nr2 -0-> r2\nr2 -1-> r0'],
    hints: H('Reading a bit b turns the value v into 2v + b.', 'So the remainder r becomes (2r + b) mod 3: three states r0, r1, r2 are enough.', 'r0: 0→r0, 1→r1; r1: 0→r2, 1→r0; r2: 0→r1, 1→r2; start r0, accept r2.') });

  ex({ id: 'reg-ex-dfa-runs-even', chapter: A, level: 3, title: 'Every run of a\'s is even', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} for the strings in which every maximal block of consecutive a\'s has even length. So bb, aab and baaaab are in; ab and baaab are not.',
    member: (w) => w.split('b').every((r) => r.length % 2 === 0), ref: { regex: '(b|aa)*' },
    solution: 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> dead\ndead -a,b-> dead',
    wrong: ['start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> e', 'start e\naccept e o\ne -a-> o\no -a-> e\ne -b-> e\no -b-> dead\ndead -a,b-> dead', 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o'],
    hints: H('While inside a block of a\'s, track its parity.', 'A b closes the block: fine if the block was even, fatal if it was odd. The end of the input closes the last block too.', 'e -a-> o, o -a-> e, e -b-> e, o -b-> dead; accept only e. The language is (b|aa)*.') });

  ex({ id: 'reg-ex-dfa-bin5', chapter: A, level: 3, title: 'Multiples of 5 in binary', kind: 'machine', machine: 'dfa', alphabet: '01', maxStates: 5,
    text: 'Build a DFA with at most 5 states for the binary numerals (most significant bit first, leading zeros allowed, ε counts as 0) whose value is a multiple of 5.',
    member: (w) => bin(w) % 5 === 0,
    solution: 'start r0\naccept r0\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r3\nr2 -0-> r4\nr2 -1-> r0\nr3 -0-> r1\nr3 -1-> r2\nr4 -0-> r3\nr4 -1-> r4',
    wrong: ['start r0\naccept r0\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r3\nr2 -0-> r4\nr2 -1-> r0\nr3 -0-> r1\nr3 -1-> r2\nr4 -0-> r4\nr4 -1-> r3', 'start r0\naccept r0\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r3\nr2 -0-> r3\nr2 -1-> r4\nr3 -0-> r4\nr3 -1-> r0\nr4 -0-> r0\nr4 -1-> r1'],
    hints: H('Keep the remainder mod 5. A new bit b maps remainder r to (2r + b) mod 5.', 'For example r3 with a 1: 2·3 + 1 = 7, and 7 mod 5 = 2.', 'r0: 0→r0, 1→r1; r1: 0→r2, 1→r3; r2: 0→r4, 1→r0; r3: 0→r1, 1→r2; r4: 0→r3, 1→r4; accept r0.') });

  // ---- NFAs ----------------------------------------------------------------------------------------------------
  ex({ id: 'reg-ex-nfa-ends-bab', chapter: A, title: 'An NFA for "ends in bab"', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Build an NFA over {a, b} for the strings that end in bab. Let the machine guess where the last three symbols begin.',
    member: (w) => w.endsWith('bab'),
    solution: 'start p\naccept s\np -a,b-> p\np -b-> q\nq -a-> r\nr -b-> s',
    wrong: ['start p\naccept s\np -b-> q\nq -a-> r\nr -b-> s', 'start p\naccept s\np -a,b-> p\np -b-> q\nq -a-> r\nr -b-> s\ns -a,b-> s', 'start p\naccept s\np -a,b-> p\np -a-> q\nq -b-> r\nr -a-> s'],
    hints: H('The start state loops on everything: it waits.', 'At some b it guesses "this is the start of the final bab" and walks a three-arrow path.', 'p -a,b-> p, p -b-> q, q -a-> r, r -b-> s, accept s (with no moves out of s).') });

  ex({ id: 'reg-ex-nfa-aa-or-bb', chapter: A, title: 'A double letter somewhere', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Build an NFA over {a, b} for the strings that contain aa or bb (or both).',
    member: (w) => w.includes('aa') || w.includes('bb'),
    solution: 'start p\naccept f\np -a,b-> p\np -a-> x\nx -a-> f\np -b-> y\ny -b-> f\nf -a,b-> f',
    wrong: ['start p\naccept f\np -a,b-> p\np -a-> x\nx -a-> f\np -b-> y\ny -b-> f', 'start p\naccept f\np -a,b-> p\np -a-> x\nx -a-> f\nf -a,b-> f', 'start p\naccept f\np -a-> x\nx -a-> f\np -b-> y\ny -b-> f\nf -a,b-> f'],
    hints: H('Wait in the start state, then guess where the double letter is.', 'Two branches out of the waiting state, one for aa and one for bb, meeting in an accepting state that keeps everything.', 'p -a,b-> p, p -a-> x -a-> f, p -b-> y -b-> f, f -a,b-> f.') });

  ex({ id: 'reg-ex-nfa-lit', chapter: A, title: 'Which states are lit?', kind: 'string', set: true,
    text: ['This NFA accepts the strings containing aba. It starts in p. Which states are lit after it reads aaba? Write them as a set, like {p, q}.',
      shown('start p\naccept s\np -a,b-> p\np -a-> q\nq -b-> r\nr -a-> s\ns -a,b-> s', 'aaba')],
    answer: '{p, q, s}', solution: 'p, q, s', wrong: ['{s}', '{p, s}', '{p, q, r, s}'],
    hints: H('Start with {p} and apply one symbol at a time to every lit state.', 'After a: {p, q}. After a again: {p, q}. After b: {p, r}.', 'The last a takes p to p and q, and r to s: {p, q, s}.') });

  ex({ id: 'reg-ex-nfa-accepts', chapter: A, title: 'What does this NFA accept?', kind: 'choice',
    text: ['Which of these strings does the NFA accept?', shown('start p\naccept q\np -a,b-> p\np -a-> q\nq -b-> q', 'abba')],
    options: ['ab', 'ba', 'bbb', 'abba', 'ε'], answer: [0, 1, 3], solution: [0, 1, 3], wrong: [[0, 3], [0, 1, 2, 3], [0, 1, 3, 4]],
    hints: H('A string is accepted if at least one run ends in q.', 'To reach q the machine must read an a with p -a-> q, and after that only b\'s.', 'The language is (a|b)*ab*: an a followed only by b\'s. That is ab, ba and abba.') });

  ex({ id: 'reg-ex-nfa-eclosure', chapter: A, title: 'An ε-closure', kind: 'string', set: true,
    text: ['What is the ε-closure of u in this ε-NFA, the set of states reachable from u by ε-moves alone (u included)?',
      shown('start s\naccept w\ns -ε-> t\nt -ε-> u\nu -ε-> t\nt -a-> v\nv -ε-> w\nw -ε-> s\nu -b-> w', 'a')],
    answer: '{t, u}', solution: '{u, t}', wrong: ['{s, t, u}', '{u}', '{t, u, w}'],
    hints: H('Follow only arrows labelled ε, and only forwards.', 'From u the only ε-arrow goes to t; from t it goes back to u.', '{t, u}. s points to t, but nothing points from t or u back to s with ε.') });

  ex({ id: 'reg-ex-enfa-build', chapter: A, level: 2, title: 'a\'s then b\'s, or the other way round', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Build an NFA over {a, b}, ε-moves allowed, for the strings that are some a\'s followed by some b\'s, or some b\'s followed by some a\'s. Any of the blocks may be empty.',
    member: (w) => /^(a*b*|b*a*)$/.test(w),
    solution: 'start s\naccept x2 y2\ns -ε-> x1\ns -ε-> y1\nx1 -a-> x1\nx1 -ε-> x2\nx2 -b-> x2\ny1 -b-> y1\ny1 -ε-> y2\ny2 -a-> y2',
    wrong: ['start x1\naccept x2\nx1 -a-> x1\nx1 -ε-> x2\nx2 -b-> x2', 'start s\naccept s\ns -a,b-> s', 'start s\naccept x2 y2\ns -ε-> x1\ns -ε-> y1\nx1 -a-> x1\nx1 -b-> x2\nx2 -b-> x2\ny1 -b-> y1\ny1 -a-> y2\ny2 -a-> y2'],
    hints: H('Build a machine for a*b* and one for b*a*, then let a new start state choose between them.', 'For a*b*: loop on a, an ε-move to a second state, loop on b there.', 's -ε-> x1, s -ε-> y1, x1 loops a, x1 -ε-> x2, x2 loops b; y1 loops b, y1 -ε-> y2, y2 loops a; accept x2 and y2.') });

  ex({ id: 'reg-ex-nfa-len-2-or-3', chapter: A, level: 2, title: 'Length divisible by 2 or by 3', kind: 'machine', machine: 'nfa', alphabet: 'ab', maxStates: 6,
    text: 'Build an NFA with at most 6 states for the strings over {a, b} whose length is divisible by 2 or by 3 (or both). ε-moves are allowed.',
    member: (w) => w.length % 2 === 0 || w.length % 3 === 0,
    solution: 'start s\naccept e0 t0\ns -ε-> e0\ns -ε-> t0\ne0 -a,b-> e1\ne1 -a,b-> e0\nt0 -a,b-> t1\nt1 -a,b-> t2\nt2 -a,b-> t0',
    wrong: ['start z0\naccept z0\nz0 -a,b-> z1\nz1 -a,b-> z2\nz2 -a,b-> z3\nz3 -a,b-> z4\nz4 -a,b-> z5\nz5 -a,b-> z0', 'start e0\naccept e0 t0\ne0 -a,b-> e1\ne1 -a,b-> e0\nt0 -a,b-> t1\nt1 -a,b-> t2\nt2 -a,b-> t0', 'start s\naccept e0 t0\ns -ε-> e0\ns -ε-> t0\ne0 -a,b-> e1\ne1 -a,b-> e0\nt0 -a,b-> t1\nt1 -a,b-> t2\nt2 -a,b-> t0\nx -a-> x'],
    hints: H('A 2-cycle counts length mod 2; a 3-cycle counts length mod 3.', 'Put them side by side and let a new start state jump into either with ε. That is 1 + 2 + 3 states.', 's -ε-> e0, s -ε-> t0; e0 ⇄ e1 on a, b; t0 → t1 → t2 → t0 on a, b; accept e0 and t0.') });

  // ---- subset construction --------------------------------------------------------------------------------------
  ex({ id: 'reg-ex-subset-table', chapter: A, level: 2, title: 'The subset table', kind: 'table', table: 'custom', cellKind: 'set',
    text: ['Run the subset construction on this NFA (start x, accepting z). The reachable subsets are the rows. Fill in where each subset goes on a and on b.',
      shown('start x\naccept z\nx -a,b-> x\nx -b-> y\ny -b-> z\nz -a-> z', 'abba')],
    rows: ['{x}', '{x, y}', '{x, y, z}', '{x, z}'], cols: ['a', 'b'], corner: 'subset',
    cells: { '{x}|a': 'x', '{x}|b': 'x, y', '{x, y}|a': 'x', '{x, y}|b': 'x, y, z', '{x, y, z}|a': 'x, z', '{x, y, z}|b': 'x, y, z', '{x, z}|a': 'x, z', '{x, z}|b': 'x, y' },
    solution: { '{x}|a': '{x}', '{x}|b': '{x, y}', '{x, y}|a': '{x}', '{x, y}|b': '{x, y, z}', '{x, y, z}|a': '{x, z}', '{x, y, z}|b': '{x, y, z}', '{x, z}|a': '{x, z}', '{x, z}|b': '{y, x}' },
    wrong: [{ '{x}|a': 'x', '{x}|b': 'x, y', '{x, y}|a': 'x', '{x, y}|b': 'x, y, z', '{x, y, z}|a': 'x, y, z', '{x, y, z}|b': 'x, y, z', '{x, z}|a': 'x, z', '{x, z}|b': 'x, y' }, { '{x}|a': 'x', '{x}|b': 'y', '{x, y}|a': 'x', '{x, y}|b': 'y, z', '{x, y, z}|a': 'z', '{x, y, z}|b': 'y, z', '{x, z}|a': 'z', '{x, z}|b': 'y' }],
    hints: H('A cell is the union of the moves of every state in the row\'s subset.', 'x always stays lit, because x loops on both symbols. z keeps itself on a, and has no move on b.', '{x}: a→{x}, b→{x,y}. {x,y}: a→{x}, b→{x,y,z}. {x,y,z}: a→{x,z}, b→{x,y,z}. {x,z}: a→{x,z}, b→{x,y}.') });

  ex({ id: 'reg-ex-subset-count', chapter: A, level: 2, title: 'How many subsets are reachable?', kind: 'number',
    text: ['This NFA has 4 states, so its subset construction could produce up to 16 subsets. How many are reachable from the start subset {p}? (Count the empty subset only if it is reachable.)',
      shown('start p\naccept s\np -a,b-> p\np -a-> q\nq -b-> r\nr -a-> s\ns -a,b-> s', 'abab')],
    answer: 6, solution: '6', wrong: ['4', '16', '5'],
    hints: H('p is lit forever (it loops on both symbols), so every reachable subset contains p.', 'Explore: {p}, then {p, q} on a, {p, r} after ab, {p, q, s} after aba ...', '{p}, {p,q}, {p,r}, {p,q,s}, {p,r,s}, {p,s}: 6 subsets.') });

  ex({ id: 'reg-ex-subset-dfa', chapter: A, level: 2, title: 'Determinise it', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: ['Build a DFA for the language of this NFA, the strings that end in bb. Use the subset construction.', shown('start p\naccept r\np -a,b-> p\np -b-> q\nq -b-> r', 'abb')],
    ref: 'start p\naccept r\np -a,b-> p\np -b-> q\nq -b-> r',
    solution: 'start P\naccept PQR\nP -a-> P\nP -b-> PQ\nPQ -a-> P\nPQ -b-> PQR\nPQR -a-> P\nPQR -b-> PQR',
    wrong: ['start p\naccept r\np -a,b-> p\np -b-> q\nq -b-> r', 'start P\naccept PQR\nP -a-> P\nP -b-> PQ\nPQ -a-> P\nPQ -b-> PQR\nPQR -a-> PQR\nPQR -b-> PQR', 'start P\naccept PQ PQR\nP -a-> P\nP -b-> PQ\nPQ -a-> P\nPQ -b-> PQR\nPQR -a-> P\nPQR -b-> PQR'],
    hints: H('Start from {p}. On b it goes to {p, q}.', 'From {p, q}, b gives {p, q, r}; from any subset, a gives back {p}. A subset accepts when it holds r.', 'Three DFA states, P = {p}, PQ = {p,q}, PQR = {p,q,r}: a always → P; b: P→PQ→PQR→PQR; accept PQR.') });

  ex({ id: 'reg-ex-enfa-step', chapter: A, level: 2, title: 'One step of an ε-NFA', kind: 'string', set: true,
    text: ['In the subset construction for this ε-NFA, the start subset is the ε-closure of s. Which subset does the DFA move to on a?',
      shown('start s\naccept v\ns -ε-> t\nt -ε-> u\nu -a-> v\ns -b-> v\nv -ε-> s', 'a')],
    answer: '{s, t, u, v}', solution: 's, t, u, v', wrong: ['{v}', '{s, t, u}', '{u, v}'],
    hints: H('First find the start subset: the ε-closure of s.', 'The start subset is {s, t, u}. Reading a from it: only u has an a-move, to v.', 'Then take the ε-closure of {v}: v → s → t → u. The answer is {s, t, u, v}.') });

  ex({ id: 'reg-ex-blowup-number', chapter: A, level: 2, title: 'The fifth symbol from the end', kind: 'number',
    text: 'An NFA with 6 states accepts the strings over {a, b} whose fifth symbol from the end is a. How many states does the smallest DFA for this language have (dead states included, if any)?',
    answer: 32, solution: '32', wrong: ['6', '10', '64'],
    hints: H('A DFA reading left to right must remember the last five symbols, since any of them might turn out to be the fifth from the end.', 'Two different five-symbol endings can always be told apart by some continuation.', '2⁵ = 32 states, one for each possible ending of length five.') });

  ex({ id: 'reg-ex-nfa-fourth-last', chapter: A, level: 2, title: 'The fourth symbol from the end, in five states', kind: 'machine', machine: 'nfa', alphabet: 'ab', maxStates: 5,
    text: 'Build an NFA with at most 5 states for the strings over {a, b} whose fourth symbol from the end is b.',
    member: (w) => w.length >= 4 && w[w.length - 4] === 'b',
    solution: 'start p\naccept t\np -a,b-> p\np -b-> q\nq -a,b-> r\nr -a,b-> s\ns -a,b-> t',
    wrong: ['start p\naccept t\np -a,b-> p\np -a-> q\nq -a,b-> r\nr -a,b-> s\ns -a,b-> t', 'start p\naccept s\np -a,b-> p\np -b-> q\nq -a,b-> r\nr -a,b-> s', 'start p\naccept t\np -a,b-> p\np -b-> q\nq -a,b-> r\nr -a,b-> s\ns -a,b-> t\nu -a-> u'],
    hints: H('Guess that this b is the fourth from the end.', 'After the guess, exactly three more symbols must follow, then the input must end.', 'p loops on a, b; p -b-> q; then q, r, s each move on a, b to the next; accept t.') });

  ex({ id: 'reg-ex-nfa-facts', chapter: A, level: 2, title: 'NFAs and DFAs', kind: 'choice',
    text: 'Which statements are true?',
    options: ['Every NFA has a DFA that accepts the same language.', 'For some languages the smallest DFA is exponentially bigger than an NFA for them.', 'Some languages have an NFA but no DFA.', 'An NFA accepts a string only when every one of its runs ends in an accepting state.', 'ε-moves can be removed from an NFA without adding states.'],
    answer: [0, 1, 4], solution: [0, 1, 4], wrong: [[0, 1], [0, 1, 2, 4], [0, 1, 3, 4]],
    hints: H('The subset construction always works; the only cost is size.', 'One accepting run is enough. And to remove ε-moves, give each state the moves of its ε-closure.', 'True: the first, second and fifth.') });

  // =========================================================================================================
  // Chapter 2: closure properties
  // =========================================================================================================
  const B = 'reg-closure';

  ex({ id: 'reg-ex-complement-dfa', chapter: B, title: 'Does not end in ab', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} for the strings that do not end in ab. (ε and a are in, aab is not.) Start from a complete DFA for "ends in ab".',
    member: (w) => !w.endsWith('ab'),
    solution: 'start x\naccept x y\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x',
    wrong: ['start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x', 'start x\naccept x\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x', 'start x\naccept x y\nx -a-> y\ny -b-> z'],
    hints: H('A complete DFA for "ends in ab" has states for "no progress", "ends in a" and "ends in ab".', 'Its complement is the same machine with accepting and non-accepting swapped.', 'x -a-> y, x -b-> x, y -a-> y, y -b-> z, z -a-> y, z -b-> x; accept x and y.') });

  ex({ id: 'reg-ex-complement-trap', chapter: B, title: 'Flipping a machine with holes', kind: 'choice',
    text: ['This DFA for a(ba)* has missing moves. If we only swap accepting and non-accepting states (s becomes accepting, t not), what does the new machine accept?',
      shown('start s\naccept t\ns -a-> t\nt -b-> s', 'ab')],
    options: ['Exactly the strings not in a(ba)*', 'Only (ab)*: strings such as b or aa still fall into the missing moves and are rejected', 'Every string over {a, b}', 'Nothing at all'],
    answer: 1, solution: 1, wrong: [0, 2],
    hints: H('What happens to the string b in the flipped machine?', 'b has no move from s, so it is rejected, although b is not in a(ba)* and should be accepted by a true complement.', 'Only (ab)*. Complete the machine with a dead state first, then flip.') });

  ex({ id: 'reg-ex-product-dfa', chapter: B, level: 2, title: 'Odd a\'s and at least one b', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} for the strings with an odd number of a\'s and at least one b. A product of two small machines does it.',
    member: (w) => count(w, 'a') % 2 === 1 && w.includes('b'),
    solution: 'start e0\naccept o1\ne0 -a-> o0\ne0 -b-> e1\no0 -a-> e0\no0 -b-> o1\ne1 -a-> o1\ne1 -b-> e1\no1 -a-> e1\no1 -b-> o1',
    wrong: ['start e0\naccept o0 o1\ne0 -a-> o0\ne0 -b-> e1\no0 -a-> e0\no0 -b-> o1\ne1 -a-> o1\ne1 -b-> e1\no1 -a-> e1\no1 -b-> o1', 'start e0\naccept o1 e1\ne0 -a-> o0\ne0 -b-> e1\no0 -a-> e0\no0 -b-> o1\ne1 -a-> o1\ne1 -b-> e1\no1 -a-> e1\no1 -b-> o1', 'start e0\naccept o1\ne0 -a-> o0\ne0 -b-> e1\no0 -a-> e0\no0 -b-> o1\ne1 -a-> o1\ne1 -b-> e1\no1 -a-> o1\no1 -b-> o1'],
    hints: H('One machine tracks the parity of the a\'s (2 states), the other whether a b has been seen (2 states).', 'A product state is a pair, (parity, seen b?). a flips the first part; b sets the second part to "yes".', 'States e0, o0, e1, o1; a: e↔o; b: 0→1, 1 stays; start e0, accept o1 only.') });

  ex({ id: 'reg-ex-product-states', chapter: B, title: 'The size of a product', kind: 'number',
    text: 'One complete DFA has 3 states, another has 4, over the same alphabet. How many states does their product construction have, counting every pair, reachable or not?',
    answer: 12, solution: '12', wrong: ['7', '4', '81'],
    hints: H('A state of the product is a pair: one state of each machine.', 'Count the pairs.', '3 × 4 = 12 pairs.') });

  ex({ id: 'reg-ex-difference-dfa', chapter: B, level: 3, title: 'aa but never bb', kind: 'machine', machine: 'dfa', alphabet: 'ab',
    text: 'Build a DFA over {a, b} for the strings that contain aa but do not contain bb.',
    member: (w) => w.includes('aa') && !w.includes('bb'),
    solution: 'start n\naccept A B\nn -a-> a\nn -b-> b\na -a-> A\na -b-> b\nb -a-> a\nb -b-> dead\nA -a-> A\nA -b-> B\nB -a-> A\nB -b-> dead\ndead -a,b-> dead',
    wrong: ['start n\naccept A B\nn -a-> a\nn -b-> b\na -a-> A\na -b-> b\nb -a-> a\nb -b-> dead\nA -a-> A\nA -b-> B\nB -a-> A\nB -b-> B\ndead -a,b-> dead', 'start n\naccept A B\nn -a-> a\nn -b-> b\na -a-> A\na -b-> b\nb -a-> a\nb -b-> A\nA -a-> A\nA -b-> B\nB -a-> A\nB -b-> A', 'start n\naccept A\nn -a-> a\nn -b-> b\na -a-> A\na -b-> b\nb -a-> a\nb -b-> dead\nA -a-> A\nA -b-> B\nB -a-> A\nB -b-> dead\ndead -a,b-> dead'],
    hints: H('This is "contains aa" intersected with the complement of "contains bb". Both need to know the last symbol.', 'Track: has aa appeared yet, and what was the last symbol. A second b in a row is fatal at any time, even after aa.', 'Before aa: n, a (last a), b (last b). After aa: A (last a), B (last b). b after b → dead; a after a → A. Accept A and B.') });

  ex({ id: 'reg-ex-union-nfa', chapter: B, level: 2, title: 'Starts with ab or ends with ba', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Build an NFA over {a, b} (ε-moves allowed) for the strings that start with ab or end with ba.',
    member: (w) => w.startsWith('ab') || w.endsWith('ba'),
    solution: 'start s\naccept x2 y2\ns -ε-> x0\ns -ε-> y0\nx0 -a-> x1\nx1 -b-> x2\nx2 -a,b-> x2\ny0 -a,b-> y0\ny0 -b-> y1\ny1 -a-> y2',
    wrong: ['start s\naccept x2 y2\ns -ε-> x0\ns -ε-> y0\nx0 -a-> x1\nx1 -b-> x2\ny0 -a,b-> y0\ny0 -b-> y1\ny1 -a-> y2', 'start x0\naccept y2\nx0 -a-> x1\nx1 -b-> x2\nx2 -a,b-> x2\nx2 -ε-> y0\ny0 -a,b-> y0\ny0 -b-> y1\ny1 -a-> y2', 'start s\naccept x2 y2\ns -ε-> x0\ns -ε-> y0\nx0 -a-> x1\nx1 -b-> x2\nx2 -a,b-> x2\ny0 -a,b-> y0\ny0 -a-> y1\ny1 -b-> y2'],
    hints: H('Build a small machine for each half, then join them with a new start state.', 'Starts with ab: a, b, then loop on everything. Ends with ba: loop on everything, then guess b, a.', 's -ε-> x0 and y0; x0 -a-> x1 -b-> x2 looping on a, b; y0 loops on a, b, y0 -b-> y1 -a-> y2; accept x2, y2.') });

  ex({ id: 'reg-ex-star-nfa', chapter: B, level: 2, title: 'The star of {aab, b}', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Build an NFA over {a, b} for (aab|b)*: any number of the blocks aab and b, one after another, including none.',
    ref: { regex: '(aab|b)*' }, member: (w) => /^(aab|b)*$/.test(w),
    solution: 'start s\naccept s\ns -b-> s\ns -a-> t\nt -a-> u\nu -b-> s',
    wrong: ['start s\naccept f\ns -b-> f\ns -a-> t\nt -a-> u\nu -b-> f\nf -ε-> s', 'start s\naccept s\ns -a,b-> s', 'start s\naccept s\ns -b-> s\ns -a-> t\nt -a-> u\nu -b-> s\nu -a-> u'],
    hints: H('ε must be accepted: zero blocks.', 'Make one state that is both the start and accepting, and return to it after each block.', 's loops on b; s -a-> t -a-> u -b-> s; start and accept s.') });

  ex({ id: 'reg-ex-reverse', chapter: B, level: 2, title: 'Reverse a language', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: ['This DFA accepts the strings whose second symbol is b. Build an NFA for the reversal of its language: every accepted string written backwards.', shown('start p\naccept r\np -a,b-> q\nq -b-> r\nr -a,b-> r', 'ab')],
    member: (w) => w.length >= 2 && w[w.length - 2] === 'b', ref: { regex: '(a|b)*b(a|b)' },
    solution: 'start p\naccept r\np -a,b-> p\np -b-> q\nq -a,b-> r',
    wrong: ['start p\naccept r\np -a,b-> q\nq -b-> r\nr -a,b-> r', 'start p\naccept q\np -a,b-> p\np -b-> q', 'start p\naccept r\np -a,b-> p\np -a-> q\nq -a,b-> r'],
    hints: H('Written backwards, "the second symbol" becomes "the second symbol from the end".', 'Or mechanically: turn every arrow round, make r the start and p the accepting state.', 'Strings whose second symbol from the end is b: p loops on a, b; p -b-> q; q -a,b-> r; accept r.') });

  ex({ id: 'reg-ex-hom-regex', chapter: B, level: 2, title: 'The image under a homomorphism', kind: 'regex', alphabet: '01',
    text: 'Let h(a) = 10 and h(b) = 0. Write a regular expression for h(L) where L = a*b.',
    ref: '(10)*0', solution: '(10)*0', wrong: ['(01)*0', '1*0*0', '(10)*'],
    hints: H('Apply h symbol by symbol to an expression for L.', 'h(a*) = (10)* and h(b) = 0.', '(10)*0.') });

  ex({ id: 'reg-ex-invhom', chapter: B, level: 3, title: 'An inverse image', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Let h(a) = 00 and h(b) = 1, and let L be the binary strings whose length is a multiple of 3. Build an automaton for h⁻¹(L): the strings w over {a, b} with h(w) in L.',
    member: (w) => (2 * count(w, 'a') + count(w, 'b')) % 3 === 0,
    solution: 'start m0\naccept m0\nm0 -a-> m2\nm0 -b-> m1\nm1 -a-> m0\nm1 -b-> m2\nm2 -a-> m1\nm2 -b-> m0',
    wrong: ['start m0\naccept m0\nm0 -a,b-> m1\nm1 -a,b-> m2\nm2 -a,b-> m0', 'start m0\naccept m1\nm0 -a-> m2\nm0 -b-> m1\nm1 -a-> m0\nm1 -b-> m2\nm2 -a-> m1\nm2 -b-> m0', 'start m0\naccept m2\nm0 -a-> m2\nm0 -b-> m1\nm1 -a-> m0\nm1 -b-> m2\nm2 -a-> m1\nm2 -b-> m0'],
    hints: H('The DFA for L counts length mod 3. Reading a symbol x of w means reading all of h(x) in that DFA.', 'a adds 2 to the length of h(w), b adds 1.', 'States m0, m1, m2 for |h(w)| mod 3; a: +2, b: +1; accept m0.') });

  ex({ id: 'reg-ex-quotient', chapter: B, level: 3, title: 'A right quotient', kind: 'regex', alphabet: 'ab',
    text: 'Let L = (aab)* and M = b*. The right quotient L / M is the set of strings x for which some y in M makes xy a string of L. Write a regular expression for it.',
    ref: '(aab)*(ε|aa)', solution: '(aab)*(aa)?', wrong: ['(aab)*', '(aab)*(a|aa|ε)', '(aab)*aa'],
    hints: H('Try each y in b*: y = ε, y = b, y = bb, ...', 'y = ε gives L itself. y = b needs xb in (aab)*, so x is (aab)* followed by aa. Two or more b\'s never fit.', '(aab)*(ε|aa).') });

  ex({ id: 'reg-ex-closure-choice', chapter: B, level: 2, title: 'What must stay regular?', kind: 'choice',
    text: 'L is a regular language over {a, b}. Which of these must be regular too?',
    options: ['The complement of L', 'L written backwards', 'L ∩ {aⁿbⁿ : n ≥ 0}', 'Any subset of L', 'h⁻¹(L), for any homomorphism h', 'The union of infinitely many regular languages'],
    answer: [0, 1, 4], solution: [0, 1, 4], wrong: [[0, 1, 2, 4], [0, 1], [0, 1, 3, 4]],
    hints: H('Closure under an operation means: regular in, regular out, always.', 'Take L = a*b*: the third option is then aⁿbⁿ. Any language over {a, b} is a subset of (a|b)*, and a union of single-string languages.', 'The complement, the reversal and the inverse homomorphism.') });

  // =========================================================================================================
  // Chapter 3: regular expressions
  // =========================================================================================================
  const R = 'reg-regex';

  ex({ id: 'reg-ex-rx-precedence', chapter: R, title: 'Which operator binds first?', kind: 'choice',
    text: 'How is the expression ab*|c grouped?',
    options: ['((ab)*)|c', 'a(b*|c)', '(a(b*))|c', 'a((b|c)*)'], answer: 2, solution: 2, wrong: [0, 1],
    hints: H('Star binds tightest, union loosest.', 'So the star applies to b alone, and the union splits the whole expression in two.', '(a(b*))|c: either an a followed by b\'s, or a single c.') });

  ex({ id: 'reg-ex-rx-match', chapter: R, title: 'Which strings match?', kind: 'choice',
    text: 'Which of these strings match (a|ba)*b? ?',
    options: ['ε', 'bab', 'abba', 'baab', 'bb'], answer: [0, 1, 3], solution: [0, 1, 3], wrong: [[0, 1], [1, 3], [0, 1, 3, 4]],
    hints: H('(a|ba)* makes blocks a and ba; then one optional b at the end.', 'In the blocks every b is followed by an a. So two b\'s in a row can only happen if... they cannot, except the very last b.', 'ε, bab (ba · b) and baab (ba · a · b). abba and bb would need a b followed by b inside the blocks.') });

  ex({ id: 'reg-ex-rx-even-len', chapter: R, title: 'Even length', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression over {a, b} for the strings of even length (ε included).',
    member: (w) => w.length % 2 === 0, ref: { regex: '((a|b)(a|b))*' },
    solution: '((a|b)(a|b))*', wrong: ['(a|b)(a|b)*', '(aa|bb)*', '(ab|ba)*'],
    hints: H('Even length means the string splits into pairs.', 'A pair is any symbol followed by any symbol.', '((a|b)(a|b))*.') });

  ex({ id: 'reg-ex-rx-same-ends', chapter: R, title: 'Same first and last symbol', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the non-empty strings over {a, b} that begin and end with the same symbol. A single symbol counts: its first and last symbol are the same one.',
    member: (w) => w.length > 0 && w[0] === w[w.length - 1],
    solution: 'a|b|a(a|b)*a|b(a|b)*b', wrong: ['a(a|b)*a|b(a|b)*b', '(a|b)*', 'a|b|a(a|b)*a|b(a|b)*b|ε'],
    hints: H('Split into cases by the first symbol.', 'Starting with a: either just a, or a, anything, a.', 'a|b|a(a|b)*a|b(a|b)*b.') });

  ex({ id: 'reg-ex-rx-at-most-two-b', chapter: R, title: 'At most two b\'s', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} with at most two b\'s.',
    member: (w) => count(w, 'b') <= 2,
    solution: 'a*(b|ε)a*(b|ε)a*', wrong: ['a*ba*ba*', 'a*b?a*', '(a|b)*b(a|b)*'],
    hints: H('Between and around the b\'s there can be any number of a\'s.', 'Each of the two b\'s is optional.', 'a*(b|ε)a*(b|ε)a*, or a*b?a*b?a*.') });

  ex({ id: 'reg-ex-rx-no-ab', chapter: R, title: 'Never ab', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} that do not contain ab.',
    member: (w) => !w.includes('ab'),
    solution: 'b*a*', wrong: ['a*b*', '(a|b)*', 'b*a*b*'],
    hints: H('Once an a has appeared, what may follow it?', 'Only more a\'s: any b after an a would make ab somewhere.', 'b*a*: some b\'s, then some a\'s.') });

  ex({ id: 'reg-ex-rx-third-last-b', chapter: R, title: 'Third from the end', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} whose third symbol from the end is b.',
    member: (w) => w.length >= 3 && w[w.length - 3] === 'b',
    solution: '(a|b)*b(a|b)(a|b)', wrong: ['b(a|b)(a|b)', '(a|b)*b(a|b)*', '(a|b)*bb(a|b)'],
    hints: H('Anything first, then the b, then exactly two more symbols.', 'Exactly two symbols is (a|b)(a|b).', '(a|b)*b(a|b)(a|b).') });

  ex({ id: 'reg-ex-rx-a-then-bb', chapter: R, level: 2, title: 'Every a is followed by bb', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} in which every a is immediately followed by at least two b\'s.',
    member: (w) => [...w].every((c, i) => c !== 'a' || (w[i + 1] === 'b' && w[i + 2] === 'b')),
    solution: '(b|abb)*', wrong: ['(abb)*', '(b|ab)*', 'b*(abb)*'],
    hints: H('Cut the string into blocks: each a must start a block abb.', 'Other b\'s can stand alone.', '(b|abb)*.') });

  ex({ id: 'reg-ex-rx-odd-a', chapter: R, level: 2, title: 'An odd number of a\'s', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} with an odd number of a\'s.',
    member: (w) => count(w, 'a') % 2 === 1,
    solution: 'b*a(b*ab*a)*b*', wrong: ['b*(ab*a)*b*', '(a|b)*a(a|b)*', 'a(aa)*'],
    hints: H('Take the first a on its own; after it, a\'s come in pairs.', 'A pair of a\'s with b\'s around and between: b*ab*a.', 'b*a(b*ab*a)*b*.') });

  ex({ id: 'reg-ex-rx-a-mod3', chapter: R, level: 2, title: 'a\'s leave remainder 1', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} whose number of a\'s leaves remainder 1 when divided by 3 (1, 4, 7, ... a\'s).',
    member: (w) => count(w, 'a') % 3 === 1,
    solution: 'b*ab*(ab*ab*ab*)*', wrong: ['b*ab*(ab*ab*)*', 'a(aaa)*', 'b*ab*'],
    hints: H('One a, then the rest come in groups of three.', 'b\'s may appear anywhere between them.', 'b*ab*(ab*ab*ab*)*.') });

  ex({ id: 'reg-ex-rx-bin-mult4', chapter: R, level: 2, title: 'Multiples of 4 without leading zeros', kind: 'regex', alphabet: '01',
    text: 'Write a regular expression over {0, 1} for the binary numerals with no leading zeros whose value is a multiple of 4. The numeral 0 itself is allowed; 00 and ε are not.',
    member: (w) => w === '0' || (w[0] === '1' && w.endsWith('00')),
    solution: '0|1(0|1)*00', wrong: ['(0|1)*00', '1(0|1)*00', '0|1(0|1)*0'],
    hints: H('A binary numeral is a multiple of 4 exactly when its last two bits are 00.', 'No leading zeros: either the numeral is 0, or it starts with 1.', '0|1(0|1)*00.') });

  ex({ id: 'reg-ex-rx-short-both', chapter: R, level: 2, title: 'An a and a b, briefly', kind: 'regex', alphabet: 'ab', maxSize: 17,
    text: 'Write an expression with at most 17 parts (symbols and operators, the hidden concatenations included) for the strings over {a, b} that contain at least one a and at least one b.',
    member: (w) => w.includes('a') && w.includes('b'),
    solution: '(a|b)*(ab|ba)(a|b)*', wrong: ['(a|b)*a(a|b)*b(a|b)*|(a|b)*b(a|b)*a(a|b)*', '(a|b)*a(a|b)*b(a|b)*', 'a+b+|b+a+'],
    hints: H('Somewhere an a and a b must stand next to each other.', 'Look for the place where the symbol first changes: ab or ba.', '(a|b)*(ab|ba)(a|b)*, 17 parts.') });

  ex({ id: 'reg-ex-rx-even-even', chapter: R, level: 3, title: 'Even a\'s and even b\'s', kind: 'regex', alphabet: 'ab',
    text: 'Write a regular expression for the strings over {a, b} with an even number of a\'s and an even number of b\'s.',
    member: (w) => count(w, 'a') % 2 === 0 && count(w, 'b') % 2 === 0,
    solution: '(aa|bb|(ab|ba)(aa|bb)*(ab|ba))*', wrong: ['(aa|bb)*', '(aa|bb|ab|ba)*', '((a|b)(a|b))*'],
    hints: H('Read the string in pairs. aa and bb keep both parities as they were; ab and ba flip both.', 'So after a mixed pair, you need some same pairs and then another mixed pair to get back.', '(aa|bb|(ab|ba)(aa|bb)*(ab|ba))*.') });

  ex({ id: 'reg-ex-nfa-from-regex', chapter: R, title: 'An automaton for an expression', kind: 'machine', machine: 'nfa', alphabet: 'ab',
    text: 'Build a finite automaton (an NFA is fine) for (ab|ba)*a.',
    ref: { regex: '(ab|ba)*a' },
    solution: 'start s\naccept f\ns -a-> x\nx -b-> s\ns -b-> y\ny -a-> s\ns -a-> f',
    wrong: ['start s\naccept s\ns -a-> x\nx -b-> s\ns -b-> y\ny -a-> s', 'start s\naccept f\ns -a-> x\nx -b-> s\ns -b-> y\ny -a-> s\ns -a-> f\nf -a,b-> f', 'start s\naccept f\ns -a-> x\nx -b-> f\ns -b-> y\ny -a-> f\nf -a-> f'],
    hints: H('One state s is the "between blocks" state, and the start.', 'From s, the block ab goes out and back through one state, ba through another. The final a leaves to an accepting state.', 's -a-> x -b-> s, s -b-> y -a-> s, s -a-> f; accept f.') });

  ex({ id: 'reg-ex-glushkov-count', chapter: R, level: 2, title: 'States of the position automaton', kind: 'number',
    text: 'The position automaton of an expression has one state for every occurrence of a symbol in it, plus a start state. How many states does it have for (ab|b)*a(a|b)?',
    answer: 7, solution: '7', wrong: ['6', '12', '5'],
    hints: H('Count occurrences, not distinct symbols.', 'The occurrences are a, b, b, a, a, b.', '6 positions + 1 start state = 7.') });

  ex({ id: 'reg-ex-derivative', chapter: R, level: 2, title: 'A derivative', kind: 'regex', alphabet: 'ab',
    text: 'The derivative of an expression R by a symbol c describes { w : cw matches R }. Write an expression for the derivative of (a|ba)*b by b.',
    ref: 'a(a|ba)*b|ε', solution: 'a(a|ba)*b|ε', wrong: ['(a|ba)*b', 'a(a|ba)*b', 'ε'],
    hints: H('A leading b can come from the block ba, or be the final b with zero blocks before it.', 'If the b starts a block ba, what remains is a, then more blocks, then the final b. If it is the final b, nothing remains.', 'a(a|ba)*b | ε.') });

  ex({ id: 'reg-ex-derivative-2', chapter: R, level: 3, title: 'A derivative by two symbols', kind: 'regex', alphabet: 'ab',
    text: 'Write an expression for the derivative of (a|b)*abb by the string ab, that is, { w : abw matches (a|b)*abb }.',
    ref: '(a|b)*abb|b', solution: 'b|(a|b)*abb', wrong: ['(a|b)*abb', 'b', '(a|b)*bb'],
    hints: H('Either the ab you removed belongs to the (a|b)* part, or it is the start of the final abb.', 'In the second case only b is left.', '(a|b)*abb | b.') });

  ex({ id: 'reg-ex-elim-label', chapter: R, level: 2, title: 'Eliminate one state', kind: 'regex', alphabet: 'ab',
    text: ['State elimination removes m from this automaton. Write the expression that labels the arrow from p to r afterwards (it must cover the old direct arrow too).',
      shown('start p\naccept r\np -a-> m\nm -b-> m\nm -a-> r\np -b-> r', 'aba')],
    ref: 'b|ab*a', solution: 'b|ab*a', wrong: ['ab*a', 'b|aba', 'b|a(a|b)*a'],
    hints: H('A path through m: in on a, loop on b any number of times, out on a.', 'That gives ab*a. The direct arrow p -b-> r still exists.', 'b | ab*a.') });

  ex({ id: 'reg-ex-rx-from-dfa', chapter: R, level: 2, title: 'From a DFA to an expression', kind: 'regex', alphabet: 'ab',
    text: ['Write a regular expression for the language of this DFA.', shown('start 1\naccept 2\n1 -a-> 2\n1 -b-> 1\n2 -a-> 3\n2 -b-> 1\n3 -a,b-> 3', 'bab')],
    ref: { machine: 'start 1\naccept 2\n1 -a-> 2\n1 -b-> 1\n2 -a-> 3\n2 -b-> 1\n3 -a,b-> 3' },
    solution: '(b|ab)*a', wrong: ['(b|ab)*', '(a|b)*a', 'b*a'],
    hints: H('State 3 is dead: once aa is read, nothing is accepted. So the language has no aa.', 'Coming back to state 1 takes b or ab. Then a final a moves to the accepting state 2.', '(b|ab)*a: no two a\'s in a row, and ends in a.') });

  ex({ id: 'reg-ex-rx-from-nfa', chapter: R, level: 3, title: 'From an automaton with two loops', kind: 'regex', alphabet: 'ab',
    text: ['Write a regular expression for the language of this automaton. Eliminating x first, then y, works well.', shown('start x\naccept z\nx -a-> y\ny -b-> x\ny -a-> z\nz -b-> z\nz -a-> y', 'aa')],
    ref: { machine: 'start x\naccept z\nx -a-> y\ny -b-> x\ny -a-> z\nz -b-> z\nz -a-> y' },
    solution: 'a(ba)*a(b|a(ba)*a)*', wrong: ['a(ba)*a', '(ab|aa)*', 'a(ba)*ab*'],
    hints: H('Eliminating x: the path y → x → y becomes a loop ba on y, and the start reaches y on a.', 'Eliminating y: start → z is a(ba)*a, and z → y → z is a(ba)*a too, beside z\'s own loop b.', 'a(ba)*a(b|a(ba)*a)*.') });

  ex({ id: 'reg-ex-simplify', chapter: R, level: 2, title: 'Simplify', kind: 'regex', alphabet: 'ab', maxSize: 5,
    text: 'Write an expression with at most 5 parts that means the same as (ε|a)(a*)*(ε|b)b*.',
    ref: '(ε|a)(a*)*(ε|b)b*', solution: 'a*b*', wrong: ['(ε|a)(a*)*(ε|b)b*', 'a*b+', '(a|b)*'],
    hints: H('(a*)* is a*, and (ε|a)a* is still a*.', 'Likewise (ε|b)b* is b*.', 'a*b*.') });

  ex({ id: 'reg-ex-simplify-2', chapter: R, level: 3, title: 'Simplify further', kind: 'regex', alphabet: 'ab', maxSize: 4,
    text: 'Write an expression with at most 4 parts that means the same as (a|b)*a(a|b)*|b*.',
    ref: '(a|b)*a(a|b)*|b*', solution: '(a|b)*', wrong: ['b*', '(a|b)*a(a|b)*', 'a*b*'],
    hints: H('What does the left side describe? And the right side?', 'Left: strings with at least one a. Right: strings with no a at all.', 'Together they cover every string: (a|b)*.') });

  ex({ id: 'reg-ex-equiv-choice', chapter: R, level: 2, title: 'Equal or not?', kind: 'choice',
    text: 'Which of these pairs of expressions describe the same language?',
    options: ['(a|b)* and (a*b)*a*', 'a(ba)* and (ab)*a', '(ab)* and a*b*', 'a*|b* and (a|b)*', '(a*b*)* and (a|b)*'],
    answer: [0, 1, 4], solution: [0, 1, 4], wrong: [[0, 1], [0, 1, 3, 4], [1, 4]],
    hints: H('For each pair, look for a short string that one matches and the other does not.', 'a*b* matches aab; (ab)* does not. (a|b)* matches ab; a*|b* does not.', 'The first, second and fifth pairs are equal.') });

  ex({ id: 'reg-ex-counterexample', chapter: R, level: 2, title: 'Tell them apart', kind: 'string',
    text: 'The expressions (ab|ba)* and ((a|b)(a|b))* are not equal. Give a shortest string that one of them matches and the other does not.',
    accept: (w) => /^[ab]*$/.test(w) && /^(ab|ba)*$/.test(w) !== /^((a|b)(a|b))*$/.test(w) && w.length === 2,
    solution: 'aa', wrong: ['ab', 'aab', 'ε'],
    hints: H('Both only match strings of even length.', 'Every pair of the first expression is mixed; the second allows any pair.', 'aa (or bb): the second matches it, the first does not.') });

  // =========================================================================================================
  // Chapter 4: beyond regular
  // =========================================================================================================
  const N = 'reg-limits';

  ex({ id: 'reg-ex-pump-dfa-y', chapter: N, title: 'Find the loop', kind: 'string',
    text: ['This DFA counts b\'s mod 3. Run it on bbab and find the first state that repeats. The symbols read between its two visits are y. What is y?',
      shown('start b0\naccept b0\nb0 -a-> b0\nb0 -b-> b1\nb1 -a-> b1\nb1 -b-> b2\nb2 -a-> b2\nb2 -b-> b0', 'bbab')],
    answer: 'a', solution: 'a', wrong: ['bba', 'b', 'bb'],
    hints: H('Write the run: the state before and after each symbol.', 'b0, b1, b2, b2, b0: the first repeat is b2, right after bb.', 'y = a (with x = bb and z = b). Pumping a keeps the number of b\'s.') });

  ex({ id: 'reg-ex-pump-a-lt-b', chapter: N, level: 2, title: 'Fewer a\'s than b\'s', kind: 'pumping', lang: 'a-lt-b',
    text: 'Show that { aⁿbᵐ : n < m } is not regular by winning the pumping game: choose s, let the computer split it, then choose i.',
    solution: { s: 'aaaabbbbb', i: 2 }, wrong: [{ s: 'aaaabbbbb', i: 0 }, { s: 'abbbb', i: 2 }, { s: 'aaaabbbbb', i: 1 }],
    hints: H('Put the a\'s at the front so that y can only be a\'s.', 'Make the gap as small as it can be: one more b than a\'s. Then adding a\'s breaks the rule.', 's = aᵖbᵖ⁺¹ (aaaabbbbb for p = 4) and i = 2: there are now at least as many a\'s as b\'s.') });

  ex({ id: 'reg-ex-pump-pal', chapter: N, level: 2, title: 'Palindromes', kind: 'pumping', lang: 'pal',
    text: 'Show that the palindromes over {a, b} are not regular by winning the pumping game.',
    solution: { s: 'aaaabaaaa', i: 0 }, wrong: [{ s: 'abba', i: 0 }, { s: 'aaaa', i: 2 }, { s: 'aaaabaaaa', i: 1 }],
    hints: H('A string of a\'s only stays a palindrome whatever you pump. Put a b in it.', 'With s = aᵖbaᵖ, y lies in the first block of a\'s.', 's = aᵖbaᵖ (aaaabaaaa) and i = 0: the left block gets shorter than the right one.') });

  ex({ id: 'reg-ex-pump-equal', chapter: N, level: 2, title: 'As many a\'s as b\'s', kind: 'pumping', lang: 'equal-ab',
    text: 'Show that the strings with as many a\'s as b\'s (in any order) are not regular by winning the pumping game.',
    solution: { s: 'aaaabbbb', i: 0 }, wrong: [{ s: 'abababab', i: 0 }, { s: 'aabb', i: 2 }, { s: 'aaaabbbb', i: 1 }],
    hints: H('ababab... lets the computer pump ab, which keeps the balance.', 'Choose s so that the first p symbols are all a\'s.', 's = aᵖbᵖ (aaaabbbb) and i = 0 (or 2): the a\'s and b\'s no longer balance.') });

  ex({ id: 'reg-ex-pump-anb2n', chapter: N, level: 2, title: 'Twice as many b\'s', kind: 'pumping', lang: 'anb2n',
    text: 'Show that { aⁿb²ⁿ : n ≥ 0 } is not regular by winning the pumping game.',
    solution: { s: 'aaaabbbbbbbb', i: 2 }, wrong: [{ s: 'aaaabbbb', i: 2 }, { s: 'aaaabbbbbbbb', i: 1 }],
    hints: H('The string must be in the language: twice as many b\'s as a\'s.', 'With p a\'s at the front, y is a\'s only.', 's = aᵖb²ᵖ (aaaabbbbbbbb) and i = 2 (or 0).') });

  ex({ id: 'reg-ex-pump-parens', chapter: N, level: 2, title: 'Balanced brackets', kind: 'pumping', lang: 'parens',
    text: 'Show that the well-nested strings of brackets ( and ) are not regular by winning the pumping game.',
    solution: { s: '(((())))', i: 0 }, wrong: [{ s: '()()()()', i: 2 }, { s: '(((())))', i: 1 }, { s: '((((', i: 0 }],
    hints: H('()()() lets the computer pump a whole pair.', 'Open p brackets first, then close them all.', 's = (ᵖ)ᵖ, that is (((()))) for p = 4, and i = 0: some opening brackets are lost.') });

  ex({ id: 'reg-ex-pump-a-gt-b', chapter: N, level: 3, title: 'More a\'s than b\'s: pump down', kind: 'pumping', lang: 'a-gt-b',
    text: 'Show that { aⁿbᵐ : n > m } is not regular. Careful: pumping up only adds a\'s, which keeps the string in.',
    solution: { s: 'aaaaabbbb', i: 0 }, wrong: [{ s: 'aaaaabbbb', i: 2 }, { s: 'aaaabbbb', i: 0 }, { s: 'aaaaaaaabbbb', i: 0 }],
    hints: H('Adding a\'s never hurts here. Removing them can.', 'Make the a\'s win by exactly one, so that losing any a\'s is fatal.', 's = aᵖ⁺¹bᵖ (aaaaabbbb for p = 4) and i = 0.') });

  ex({ id: 'reg-ex-pump-ww', chapter: N, level: 3, title: 'A string written twice', kind: 'pumping', lang: 'ww',
    text: 'Show that { ww : w ∈ {a, b}* } is not regular by winning the pumping game.',
    solution: { s: 'aaaabaaaab', i: 0 }, wrong: [{ s: 'abab', i: 2 }, { s: 'aaaaaaaa', i: 2 }, { s: 'aaaabaaaab', i: 1 }],
    hints: H('Strings of a\'s only, or short repeating strings, let the computer pump in step with the copy.', 'Mark the middle with a b in each half: aᵖb aᵖb.', 's = aᵖbaᵖb (aaaabaaaab) and i = 0: the first half loses a\'s, the second does not.') });

  ex({ id: 'reg-ex-pump-square', chapter: N, level: 3, title: 'Square numbers of a\'s', kind: 'pumping', lang: 'square',
    text: 'Show that { a^(n²) : n ≥ 0 } is not regular by winning the pumping game.',
    solution: { s: 'aaaaaaaaaaaaaaaa', i: 2 }, wrong: [{ s: 'aaaaaaaaaaaaaaaa', i: 1 }, { s: 'aaaaaaaaaa', i: 2 }],
    hints: H('Choose a square length at least p: for p = 4 that is 16.', 'y has 1 to 4 a\'s. Pumping once more gives a length between 17 and 20.', 's = a¹⁶ and i = 2: 17 to 20 lie strictly between the squares 16 and 25.') });

  ex({ id: 'reg-ex-pump-prime', chapter: N, level: 3, title: 'A prime number of a\'s', kind: 'pumping', lang: 'prime',
    text: 'Show that { aⁿ : n is prime } is not regular. A large i helps.',
    solution: { s: 'aaaaa', i: 6 }, wrong: [{ s: 'aaaaa', i: 2 }, { s: 'aaaaaa', i: 6 }, { s: 'aaaaa', i: 1 }],
    hints: H('Take s of prime length q ≥ p, say q = 5.', 'Pumping with i gives length q + (i − 1)·|y|. Choose i so that this has a factor you know.', 's = a⁵ and i = 6: the length is 5 + 5|y| = 5(1 + |y|), not prime.') });

  ex({ id: 'reg-ex-pump-meaning', chapter: N, level: 2, title: 'When you cannot win', kind: 'choice',
    text: 'You play the pumping game on "no two b\'s in a row" and the computer survives every time. What does that show?',
    options: ['That the language is regular', 'Nothing by itself: some non-regular languages survive the game too. To show a language is regular, build a machine for it', 'That you should have chosen a larger i', 'That p was too small'],
    answer: 1, solution: 1, wrong: [0, 2],
    hints: H('The pumping lemma says: regular ⇒ pumpable. Does it say the reverse?', 'There are non-regular languages in which every long string can be pumped.', 'Nothing by itself. This language is regular, but the proof is a DFA, not a lost game.') });

  ex({ id: 'reg-ex-nerode-classes', chapter: N, level: 2, title: 'Count the classes', kind: 'number',
    text: 'How many Myhill–Nerode classes does the language of strings over {a, b} that end in aba have? (Equivalently, how many states has its smallest complete DFA?)',
    answer: 4, solution: '4', wrong: ['3', '5', '8'],
    hints: H('A class is "what the future needs to know". Here: how much of aba the input ends with.', 'The possibilities are nothing, a, ab and aba.', '4 classes.') });

  ex({ id: 'reg-ex-nerode-distinguish', chapter: N, level: 2, title: 'A distinguishing suffix', kind: 'string',
    text: 'L is the set of strings over {a, b} whose number of a\'s minus number of b\'s is a multiple of 3. Give a string z such that exactly one of aabz and baz is in L.',
    accept: (z) => { if (!/^[ab]*$/.test(z)) return false; const inL = (w) => ((count(w, 'a') - count(w, 'b')) % 3 + 3) % 3 === 0; return inL('aab' + z) !== inL('ba' + z); },
    solution: 'ε', wrong: ['a', 'aaaa', 'aab'],
    hints: H('Work out the difference for aab and for ba.', 'aab has difference 1, ba has 0. A suffix with difference d adds d to both.', 'Any z whose difference is not 1 mod 3 works; ε is the simplest: ba is in L, aab is not.') });

  ex({ id: 'reg-ex-nerode-infinite', chapter: N, level: 2, title: 'Infinitely many classes', kind: 'choice',
    text: 'To show with Myhill–Nerode that { aⁿbⁿ : n ≥ 0 } is not regular, you need infinitely many strings that are pairwise distinguishable. Which set works?',
    options: ['a, aa, aaa, aaaa, ...', 'b, bb, bbb, bbbb, ...', 'ab, aabb, aaabbb, ...', 'ε, ab, ba'], answer: 0, solution: 0, wrong: [1, 2],
    hints: H('Two strings are distinguishable if some suffix sends one into L and the other out.', 'b, bb, ... can never be completed, so they all behave alike. ab, aabb, ... are all in L and accept only ε as a suffix.', 'aⁱ and aʲ with i ≠ j: the suffix bⁱ tells them apart.') });

  ex({ id: 'reg-ex-which-regular', chapter: N, level: 2, title: 'Regular or not?', kind: 'choice',
    text: 'Which of these languages are regular?',
    options: ['aⁿbⁿ with n ≤ 1000', 'Strings with as many ab\'s as ba\'s (as substrings)', 'aⁿbᵐ with n, m ≥ 0', 'aⁿbⁿ with n ≥ 0', 'Palindromes over {a, b}', 'Binary numerals divisible by 7'],
    answer: [0, 1, 2, 5], solution: [0, 1, 2, 5], wrong: [[0, 2, 5], [0, 1, 2, 3, 5], [2, 5]],
    hints: H('Every finite language is regular.', 'The number of ab\'s and ba\'s differ by at most one, and they are equal exactly when the first and last symbols match.', 'All but aⁿbⁿ and the palindromes.') });

  // =========================================================================================================
  // Chapter 5: minimisation and decisions
  // =========================================================================================================
  const M = 'reg-minimise';
  const DIFF6 = 'start d0\naccept d0 d3\nd0 -a-> d1\nd1 -a-> d2\nd2 -a-> d3\nd3 -a-> d4\nd4 -a-> d5\nd5 -a-> d0\nd0 -b-> d5\nd1 -b-> d0\nd2 -b-> d1\nd3 -b-> d2\nd4 -b-> d3\nd5 -b-> d4';
  const BB6 = 'start A\naccept E F\nA -a-> B\nA -b-> C\nB -a-> A\nB -b-> D\nC -a-> B\nC -b-> E\nD -a-> A\nD -b-> F\nE -a,b-> F\nF -a,b-> E';
  const LEN2 = 'start A\naccept D E\nA -a-> B\nA -b-> C\nB -a-> D\nB -b-> E\nC -a-> E\nC -b-> D\nD -a,b-> D\nE -a,b-> D';

  ex({ id: 'reg-ex-min-dfa', chapter: M, level: 2, title: 'Shrink a six-state DFA', kind: 'machine', machine: 'dfa', alphabet: 'ab', maxStates: 3,
    text: ['This DFA keeps (number of a\'s − number of b\'s) mod 6 and accepts at 0 and 3. Build an equivalent DFA with at most 3 states.', shown(DIFF6, 'aab')],
    ref: DIFF6,
    solution: 'start e0\naccept e0\ne0 -a-> e1\ne0 -b-> e2\ne1 -a-> e2\ne1 -b-> e0\ne2 -a-> e0\ne2 -b-> e1',
    wrong: [DIFF6, 'start e0\naccept e1\ne0 -a-> e1\ne0 -b-> e2\ne1 -a-> e2\ne1 -b-> e0\ne2 -a-> e0\ne2 -b-> e1', 'start e0\naccept e0\ne0 -a-> e1\ne0 -b-> e1\ne1 -a-> e0\ne1 -b-> e0'],
    hints: H('Accepting at 0 and 3 mod 6 means: the difference is a multiple of 3.', 'So d0 and d3 behave alike, and so do d1 and d4, and d2 and d5.', 'Three states for the difference mod 3: a adds 1, b subtracts 1; accept e0.') });

  ex({ id: 'reg-ex-min-number', chapter: M, level: 2, title: 'How small can it get?', kind: 'number',
    text: ['How many states has the smallest DFA equivalent to this one?', shown(BB6, 'abb')],
    answer: 3, solution: '3', wrong: ['6', '2', '4'],
    hints: H('First find the language. E and F accept and only lead to each other.', 'The machine accepts the strings that contain bb. A and B both mean "no progress"; C and D both mean "just read one b".', '3: {A, B}, {C, D}, {E, F}.') });

  ex({ id: 'reg-ex-min-table', chapter: M, level: 2, title: 'Fill the distinguishability table', kind: 'table', table: 'custom',
    text: ['Fill the table-filling table for this DFA: put x in a cell when its two states are distinguishable, and leave it empty when they are equivalent.', shown(LEN2, 'ab')],
    rows: ['B', 'C', 'D', 'E'], cols: ['A', 'B', 'C', 'D'], corner: '',
    cells: { 'B|A': 'x', 'C|A': 'x', 'C|B': '', 'D|A': 'x', 'D|B': 'x', 'D|C': 'x', 'E|A': 'x', 'E|B': 'x', 'E|C': 'x', 'E|D': '' },
    solution: { 'B|A': 'x', 'C|A': 'x', 'C|B': '', 'D|A': 'x', 'D|B': 'x', 'D|C': 'x', 'E|A': 'x', 'E|B': 'x', 'E|C': 'x', 'E|D': '' },
    wrong: [{ 'B|A': '', 'C|A': '', 'C|B': '', 'D|A': 'x', 'D|B': 'x', 'D|C': 'x', 'E|A': 'x', 'E|B': 'x', 'E|C': 'x', 'E|D': '' }, { 'B|A': 'x', 'C|A': 'x', 'C|B': 'x', 'D|A': 'x', 'D|B': 'x', 'D|C': 'x', 'E|A': 'x', 'E|B': 'x', 'E|C': 'x', 'E|D': 'x' }],
    hints: H('Round 0: mark every pair of one accepting and one non-accepting state.', 'Round 1: A and B are both non-accepting, but on a, A goes to B and B goes to D, a pair already marked.', 'Marked: every pair except {B, C} and {D, E}. The language is "length at least 2", with 3 states.') });

  ex({ id: 'reg-ex-min-unique', chapter: M, level: 2, title: 'What is unique?', kind: 'choice',
    text: 'Two students each build a smallest possible DFA (complete, no unreachable states) for the same language. What can you say?',
    options: ['They may have different numbers of states', 'They have the same number of states, but may be wired differently', 'They are the same machine up to renaming the states', 'They are the same only if both used table filling'],
    answer: 2, solution: 2, wrong: [0, 1],
    hints: H('Each state of a minimal DFA is one Myhill–Nerode class.', 'Classes are fixed by the language, and so are the moves between them.', 'They are identical up to the names of the states.') });

  ex({ id: 'reg-ex-decide-empty', chapter: M, title: 'Is anything accepted?', kind: 'choice',
    text: ['Is the language of this automaton empty?', shown('start p\naccept r\np -a-> q\nq -b-> p\nq -a-> q\nr -a,b-> p', 'aba')],
    options: ['Yes, it is empty: r cannot be reached from p', 'No: aba is accepted', 'No: it has an accepting state', 'This cannot be decided'], answer: 0, solution: 0, wrong: [1, 2, 3],
    hints: H('Emptiness is reachability: can the start reach an accepting state?', 'From p you reach q, and from q only p and q. Arrows leave r, but none arrive.', 'Empty. r exists but no path leads to it from p.') });

  ex({ id: 'reg-ex-decide-finite', chapter: M, level: 2, title: 'Count the language', kind: 'number',
    text: ['This DFA accepts a finite language. How many strings does it accept?', shown('start s\naccept x y z\ns -a-> x\ns -b-> y\nx -a,b-> z\ny -a-> z\ny -b-> d\nz -a,b-> d\nd -a,b-> d', 'ab')],
    answer: 5, solution: '5', wrong: ['4', '6', '3'],
    hints: H('The only loop is on the dead state d, so the language is finite. List the paths to accepting states.', 'Length 1: a, b. Length 2: aa, ab, ba (bb goes to d).', '5: a, b, aa, ab, ba.') });

  ex({ id: 'reg-ex-decide-count', chapter: M, level: 2, title: 'Strings of length six', kind: 'number',
    text: 'How many strings of length 7 over {a, b} contain no aaa? (Count with a DFA: how many ways to be in each state after each step.)',
    answer: 81, solution: '81', wrong: ['128', '68', '44'],
    hints: H('Use a DFA with states "ends in 0, 1 or 2 a\'s". Count strings by state, length by length.', 'Totals by length: 1, 2, 4, 7, 13, 24, 44, ... from length 3 on, each is the sum of the three before it.', '13 + 24 + 44 = 81.') });

  ex({ id: 'reg-ex-decide-counterex', chapter: M, level: 2, title: 'A shortest difference', kind: 'string',
    text: 'Machine A accepts the strings with an even number of a\'s; machine B accepts the strings of even length. Give a shortest string on which they disagree.',
    accept: (w) => /^[ab]*$/.test(w) && w.length === 1 && (count(w, 'a') % 2 === 0) !== (w.length % 2 === 0),
    solution: 'b', wrong: ['a', 'ab', 'ε'],
    hints: H('Try strings in order of length: ε first.', 'ε: both accept. a: both reject.', 'b: A accepts (no a\'s), B rejects (odd length).') });

  ex({ id: 'reg-ex-decide-inclusion', chapter: M, level: 2, title: 'Deciding inclusion', kind: 'choice',
    text: 'To decide whether L(A) ⊆ L(B) for two DFAs, it is enough to build a product automaton and check one language for emptiness. Which one?',
    options: ['L(A) ∩ complement of L(B)', 'L(A) ∩ L(B)', 'complement of L(A) ∩ L(B)', 'L(A) ∪ L(B)'], answer: 0, solution: 0, wrong: [1, 2],
    hints: H('L(A) ⊆ L(B) fails exactly when some string is in A but not in B.', 'Strings in A and not in B form L(A) minus L(B).', 'L(A) ∩ complement of L(B) must be empty.') });

  // =========================================================================================================
  // Chapter 6: machines that do more
  // =========================================================================================================
  const D = 'reg-beyond';

  ex({ id: 'reg-ex-moore-output', chapter: D, title: 'A Moore machine prints', kind: 'string',
    text: ['A Moore machine has states c0, c1, c2 that print 0, 1 and 2. Reading 1 moves from cᵢ to cᵢ₊₁ (c2 goes back to c0); reading 0 stays put. It starts in c0. What does it print on input 11011?', { table: [['state', 'prints', 'on 0', 'on 1'], ['c0', '0', 'c0', 'c1'], ['c1', '1', 'c1', 'c2'], ['c2', '2', 'c2', 'c0']] }],
    answer: '012201', solution: '012201', wrong: ['12201', '01201', '0122011'],
    hints: H('A Moore machine prints when it is in a state, including the start state before any input.', 'So the output has one more symbol than the input.', 'States c0, c1, c2, c2, c0, c1 print 012201.') });

  ex({ id: 'reg-ex-mealy-output', chapter: D, title: 'A Mealy machine prints', kind: 'string',
    text: 'A Mealy machine over {a, b} prints 1 when the symbol it reads equals the previous one, and 0 otherwise (the first symbol prints 0). What does it print on aabbba?',
    answer: '010110', solution: '010110', wrong: ['10110', '0101100', '011110'],
    hints: H('A Mealy machine prints on each move, so the output is as long as the input.', 'Compare each symbol with the one before: a (first), a = a, b ≠ a, ...', '0 1 0 1 1 0.') });

  ex({ id: 'reg-ex-mealy-build', chapter: D, title: 'Build the repeat spotter', kind: 'transducer', machine: 'mealy', alphabet: 'ab', level: 2,
    text: 'Build the Mealy machine of the last exercise: over {a, b}, it prints 1 when the symbol it reads equals the previous one, and 0 otherwise. The first symbol has nothing before it, so it prints 0. Write each move as q -a/0-> r.',
    output: (w) => [...w].map((c, i) => (i > 0 && c === w[i - 1] ? '1' : '0')).join(''),
    solution: 'mealy\nstart s\ns -a/0-> A\ns -b/0-> B\nA -a/1-> A\nA -b/0-> B\nB -a/0-> A\nB -b/1-> B',
    wrong: ['mealy\nstart A\nA -a/1-> A\nA -b/0-> B\nB -a/0-> A\nB -b/1-> B', 'mealy\nstart s\ns -a/0-> A\ns -b/0-> B\nA -a/0-> A\nA -b/1-> B\nB -a/1-> A\nB -b/0-> B', 'mealy\nstart s\ns -a/0-> A\ns -b/0-> B\nA -a/1-> A\nA -b/0-> B\nB -b/1-> B'],
    hints: H('The machine must remember the last symbol it read, and also whether it has read anything at all.', 'Three states: a start state, one for "last was a" and one for "last was b". Every move on a goes to the a-state, every move on b to the b-state.', 's -a/0-> A, s -b/0-> B, A -a/1-> A, A -b/0-> B, B -a/0-> A, B -b/1-> B.') });

  ex({ id: 'reg-ex-moore-length', chapter: D, title: 'How long is the output?', kind: 'number',
    text: 'A Moore machine reads an input of length 7. How many symbols does it print?',
    answer: 8, solution: '8', wrong: ['7', '6'],
    hints: H('A Moore machine prints once in every state it is in.', 'A run on 7 symbols passes through 8 states, the start included.', '8.') });

  ex({ id: 'reg-ex-twoway-power', chapter: D, level: 2, title: 'What two-way machines can do', kind: 'choice',
    text: 'A two-way DFA may move its head left as well as right over the input (between end markers), but cannot write. Which is true?',
    options: ['It accepts exactly the regular languages', 'It can accept aⁿbⁿ by walking back and forth', 'It is as powerful as a Turing machine', 'It always halts'], answer: 0, solution: 0, wrong: [1, 3],
    hints: H('Without writing, what can a back-and-forth walk remember?', 'Only its state. Every two-way DFA can be turned into an ordinary DFA, possibly much bigger. And a two-way machine may loop for ever.', 'It accepts exactly the regular languages.') });

  ex({ id: 'reg-ex-kmp-failure', chapter: D, level: 2, title: 'The failure function', kind: 'table', table: 'custom',
    text: 'For the pattern abaab, fill in the border of each prefix: the length of the longest proper beginning that is also an ending.',
    rows: ['border'], cols: ['a', 'ab', 'aba', 'abaa', 'abaab'], corner: 'prefix',
    cells: { 'border|a': '0', 'border|ab': '0', 'border|aba': '1', 'border|abaa': '1', 'border|abaab': '2' },
    solution: { 'border|a': '0', 'border|ab': '0', 'border|aba': '1', 'border|abaa': '1', 'border|abaab': '2' },
    wrong: [{ 'border|a': '0', 'border|ab': '0', 'border|aba': '1', 'border|abaa': '1', 'border|abaab': '3' }, { 'border|a': '1', 'border|ab': '0', 'border|aba': '1', 'border|abaa': '2', 'border|abaab': '2' }],
    hints: H('Proper means shorter than the prefix itself, so a has border 0.', 'aba begins and ends with a. abaa begins and ends with a, but not with aa.', '0, 0, 1, 1, 2: abaab begins and ends with ab.') });

  ex({ id: 'reg-ex-kmp-dfa', chapter: D, level: 2, title: 'A search DFA for abab', kind: 'machine', machine: 'dfa', alphabet: 'ab', maxStates: 5,
    text: 'Build a DFA with at most 5 states for the strings over {a, b} that end with abab. Matches can overlap: ababab ends with abab too.',
    member: (w) => w.endsWith('abab'),
    solution: 'start s0\naccept s4\ns0 -a-> s1\ns0 -b-> s0\ns1 -a-> s1\ns1 -b-> s2\ns2 -a-> s3\ns2 -b-> s0\ns3 -a-> s1\ns3 -b-> s4\ns4 -a-> s3\ns4 -b-> s0',
    wrong: ['start s0\naccept s4\ns0 -a-> s1\ns0 -b-> s0\ns1 -a-> s1\ns1 -b-> s2\ns2 -a-> s3\ns2 -b-> s0\ns3 -a-> s1\ns3 -b-> s4\ns4 -a-> s1\ns4 -b-> s0', 'start s0\naccept s4\ns0 -a-> s1\ns0 -b-> s0\ns1 -a-> s1\ns1 -b-> s2\ns2 -a-> s3\ns2 -b-> s0\ns3 -a-> s0\ns3 -b-> s4\ns4 -a-> s3\ns4 -b-> s0'],
    hints: H('States 0 to 4: how much of abab the input ends with.', 'After a full match, an a leaves the input ending in ...aba: state 3, not 1.', 's0: a→s1, b→s0; s1: a→s1, b→s2; s2: a→s3, b→s0; s3: a→s1, b→s4; s4: a→s3, b→s0; accept s4.') });

  ex({ id: 'reg-ex-kmp-count', chapter: D, title: 'Overlapping matches', kind: 'number',
    text: 'How many times does aba occur in abababa, counting overlapping occurrences?',
    answer: 3, solution: '3', wrong: ['2', '4'],
    hints: H('Check every starting position.', 'aba starts at positions 1, 3 and 5.', '3.') });

  ex({ id: 'reg-ex-lexer-longest', chapter: D, title: 'Longest match', kind: 'choice',
    text: 'A lexer has two rules, in this order: IF for the word if, and ID for any run of letters. It reads iffy. What does it produce?',
    options: ['One ID token, iffy', 'IF, then ID fy', 'IF, then an error', 'One IF token'], answer: 0, solution: 0, wrong: [1, 3],
    hints: H('A lexer takes the longest prefix that some rule matches.', 'IF matches if, but ID matches all of iffy, which is longer.', 'One ID token, iffy. Rule order only breaks ties between matches of the same length.') });

  ex({ id: 'reg-ex-lexer-tie', chapter: D, title: 'A tie', kind: 'choice',
    text: 'With the same two rules, IF listed before ID, the lexer reads if followed by a space. Both rules match if, two characters long. Which token is produced?',
    options: ['IF, because it is listed first', 'ID, because it is more general', 'Both', 'An error, because the match is ambiguous'], answer: 0, solution: 0, wrong: [1, 3],
    hints: H('Longest match does not decide here: both matches have length 2.', 'The tie is broken by the order of the rules.', 'IF, listed first. That is why keywords come before identifiers.') });

  ex({ id: 'reg-ex-lexer-id', chapter: D, title: 'An identifier token', kind: 'regex', alphabet: 'ab01',
    text: 'Over the alphabet {a, b, 0, 1}, an identifier is a letter (a or b) followed by any number of letters and digits. Write a regular expression for identifiers.',
    member: (w) => /^[ab][ab01]*$/.test(w),
    solution: '(a|b)(a|b|0|1)*', wrong: ['(a|b|0|1)*', '(a|b)+(0|1)*', '(a|b|0|1)(a|b)*'],
    hints: H('The first symbol is special; the rest are free.', 'Any letter or digit: (a|b|0|1).', '(a|b)(a|b|0|1)*.') });

  ex({ id: 'reg-ex-lexer-num', chapter: D, level: 2, title: 'A number token', kind: 'regex', alphabet: '012',
    text: 'Over the digits {0, 1, 2}, a number token has no leading zeros: either 0 alone, or a non-zero digit followed by any digits. Write a regular expression for it.',
    member: (w) => w === '0' || /^[12][012]*$/.test(w),
    solution: '0|(1|2)(0|1|2)*', wrong: ['(0|1|2)+', '(1|2)(0|1|2)*', '0*(1|2)(0|1|2)*'],
    hints: H('Two cases: the numeral 0, or a numeral starting with 1 or 2.', 'After the first digit anything goes.', '0|(1|2)(0|1|2)*.') });
})();
