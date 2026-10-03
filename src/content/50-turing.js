// Part 5 lessons: Turing machines and other models. Six chapters in teaching order: the machine itself,
// building machines from parts, the variants (tapes, nondeterminism, enumerators), the other models
// (registers, counters, LBAs, unrestricted grammars, the hierarchy), recursive functions and λ, and
// encodings with the universal machine, busy beavers and the Church–Turing thesis. The exercises are in
// 51-turing-ex.js; a guided tour and a course close the file.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const C = T.Content;

  // ---- chapters ---------------------------------------------------------------------------------------------
  C.chapter({ id: 'tur-machines', part: 'turing', n: 1, title: 'The Turing machine', blurb: 'A tape, a head that reads, writes and moves, and a finite table of rules. Configurations, deciders and recognisers, machines that compute, and how to design them.' });
  C.chapter({ id: 'tur-building', part: 'turing', n: 2, title: 'Building machines from parts', blurb: 'Statements that expand into states, subroutines pasted in, and whole machines run one after another.' });
  C.chapter({ id: 'tur-variants', part: 'turing', n: 3, title: 'Variants, all equally strong', blurb: 'More tapes, a one-way tape, a grid, nondeterminism, enumerators and dovetailing: each one simulated by the plain machine.' });
  C.chapter({ id: 'tur-models', part: 'turing', n: 4, title: 'Other models of computation', blurb: 'Register machines, counter machines, linear-bounded automata, unrestricted grammars, and the Chomsky hierarchy that ties grammars to machines.' });
  C.chapter({ id: 'tur-functions', part: 'turing', n: 5, title: 'Recursive functions and λ', blurb: 'Functions built from zero and successor, the unbounded search μ, Ackermann\'s function, and computing by substitution alone.' });
  C.chapter({ id: 'tur-universal', part: 'turing', n: 6, title: 'Encodings and the universal machine', blurb: 'Machines written as strings of bits, one machine that runs them all, busy beavers, and the Church–Turing thesis.' });

  const L = (x) => C.lesson(x);
  const INC = 'start: right\naccept: done\nright, 0 -> right, 0, R\nright, 1 -> right, 1, R\nright, _ -> carry, _, L\ncarry, 1 -> carry, 0, L\ncarry, 0 -> done, 1, S\ncarry, _ -> done, 1, S';

  // =========================================================================================================
  // Chapter 1: the Turing machine
  // =========================================================================================================
  L({
    id: 'tur-l-tape', chapter: 'tur-machines', title: 'A head on a tape', minutes: 12,
    summary: 'A finite automaton reads once, left to right, and forgets. Give it a tape it can write on and a head that moves both ways, and you have the most powerful machine anyone has found.',
    blocks: [
      'Every machine so far has had a weakness you could put your finger on. A finite automaton remembers only its state. A pushdown automaton adds a stack, but it can only look at the top, and once it pops a symbol the symbol is gone. Neither can check that a string has the form aⁿbⁿcⁿ, or compare the two halves of ww.',
      'Now imagine doing those tasks yourself with pencil and paper. You would *mark* symbols as you use them, walk back and forth along the string, and scribble notes in the margin. A **Turing machine** is exactly that: a finite control (the "mind") plus a tape it can read, write and walk along in both directions.',
      { def: 'Turing machine', text: 'a machine M = (Q, Σ, Γ, δ, q₀, q_acc, q_rej). Q is a finite set of states; Σ the input alphabet; Γ ⊇ Σ ∪ {⊔} the tape alphabet, where ⊔ is the blank; δ : Q × Γ → Q × Γ × {L, R, S} the transition function; q₀ the start state; q_acc and q_rej the halting states.' },
      'The tape is a row of cells that goes on for ever. At the start, the input sits in cells 0, 1, 2, …, every other cell holds a blank, the head is on cell 0, and the state is q₀. Each **step** looks at the state and the symbol under the head, and δ says three things: what to write in that cell, which way to move (L, R, or S to stay), and which state to enter. The machine halts when it enters q_acc or q_rej, or when δ has no rule for the current state and symbol (we treat that as rejecting).',
      { h: 'Watch it run' },
      { topic: 'tm-run', input: { w: '1011' }, caption: 'Adding one in binary. The head runs right to the blank, then turns round and carries: each 1 becomes 0 until a 0 (or a blank) takes the 1. Watch the state name change when the head turns.' },
      { predict: { q: 'The same machine runs on 111. How long is the number it leaves on the tape?', options: ['3 symbols: 000', '4 symbols: 1000', '3 symbols: 111, since there is nowhere to carry'], answer: 1, explain: 'The carry turns all three 1s into 0s and then reaches the blank left of the input. The rule carry, ⊔ → done, 1 writes the new leading 1 there. The tape is infinite in both directions, so there is always room.' } },
      { h: 'Reading the rules' },
      'In the text format a rule is written `state, read -> next, write, move`, and `_` stands for the blank. So `carry, 1 -> carry, 0, L` says: in state carry, reading 1, write 0, move left, stay in carry.',
      { code: INC, lang: 'machine' },
      { tip: 'A missing rule is a rule too: the machine halts and rejects. You only need to write the rules you mean to use.' },
      { h: 'Try one' },
      { sandbox: { kind: 'tm', text: 'start: even\naccept: yes\neven, 0 -> even, 0, R\neven, 1 -> odd, 1, R\nodd, 0 -> odd, 0, R\nodd, 1 -> even, 1, R\neven, _ -> yes, _, S', input: '1101' }, caption: 'This machine never writes anything new: it walks right, keeping the parity of the 1s in its state. Run it on 1101, 11 and ε. Which strings does it accept?' },
      'That last machine is really a finite automaton in disguise. The power of a Turing machine comes from writing and from moving left, which the next lessons put to work.',
      { warn: 'A Turing machine need not halt. A rule like `s, _ -> s, _, R` walks right over blanks for ever. That is not a bug in the model: it is the price of its power, and Part 6 shows it cannot be avoided.' },
      { h: 'What to take away' },
      { list: ['A finite set of states, and a tape that is infinite in both directions.', 'Each step reads one cell, writes it, moves one cell, and changes state.', 'The machine halts in q_acc or q_rej, or when no rule applies; it may also run for ever.', 'The text format: `state, read -> next, write, move`, with `_` for the blank.'] },
      { exercise: 'tur-x-starts-b' },
      { exercise: 'tur-x-odd-ones' },
      { exercise: 'tur-x-len3' },
      { exercise: 'tur-x-times2' },
    ],
  });

  L({
    id: 'tur-l-configs', chapter: 'tur-machines', title: 'Configurations: a snapshot in three parts', minutes: 10,
    summary: 'Everything a Turing machine will ever do depends on three things: its state, its tape, and where its head is. Write them as u q v and a whole run becomes a list of strings.',
    blocks: [
      'Pause a Turing machine in the middle of a run and ask: what would you need to write down so that someone else could carry on exactly where it stopped? The rules are fixed, so you need the state, the contents of the tape, and the position of the head. That snapshot is called a **configuration**.',
      { def: 'Configuration', text: 'a string u q v, where q is the current state, uv is the non-blank part of the tape (with any blanks between it and the head), and the head is on the first symbol of v. If v is empty, the head is on a blank.' },
      'So `Xa q bY` means: state q, the tape holds XabY, and the head is on the b. The start configuration on input w is `q₀ w`.',
      { h: 'One step, on strings' },
      'A step turns one configuration into the next, and the change is always local: only the symbols right next to q move.',
      { math: 'u c q a v  ⊢  u q′ c b v    when δ(q, a) = (q′, b, L)\nu q a v  ⊢  u b q′ v    when δ(q, a) = (q′, b, R)\nu q a v  ⊢  u q′ b v    when δ(q, a) = (q′, b, S)' },
      { topic: 'tm-configs', input: { w: 'aabb' }, caption: 'A machine for aⁿbⁿ, with every configuration written underneath. Watch how the state name slides along the string as the head moves, and how X and Y mark the a\'s and b\'s already paired.' },
      { predict: { q: 'The machine is in configuration `X q1 aYb`, and δ(q1, a) = (q1, a, R). What is the next configuration?', options: ['`Xa q1 Yb`', '`X q1 Yb`', '`Xq1 aYb`, unchanged: it only read the a'], answer: 0, explain: 'Moving right, the state slides past the symbol it just wrote. Here it wrote a back, so the tape is unchanged and q1 now sits before the Y.' } },
      'A run is a sequence C₀ ⊢ C₁ ⊢ C₂ ⊢ … . A machine **accepts** w when this sequence reaches a configuration in q_acc; it **rejects** when it reaches q_rej or gets stuck; otherwise it **loops**. This view, with whole runs written as strings, is what later lets us prove things about machines with other machines and with grammars.',
      { tip: 'If the same configuration ever appears twice in a run, the machine is in a loop for ever: it is deterministic, so the future repeats too. The player and the checker both use this to report "runs forever" instead of waiting.' },
      { h: 'Trace one yourself' },
      { sandbox: { kind: 'tm', text: 'start: q0\naccept: q2\nq0, a -> q1, a, R\nq1, a -> q0, b, R\nq0, b -> q0, b, R\nq1, b -> q1, a, R\nq0, _ -> q2, _, L', input: 'aab' }, caption: 'Before you press play, write down the configurations after steps 1, 2 and 3 on aab. Then step through and compare.' },
      { list: ['A configuration u q v is a complete snapshot: state, tape and head.', 'One step changes only the symbols beside q.', 'Accept, reject and loop are properties of the sequence of configurations.', 'A repeated configuration means the run never ends.'] },
      { exercise: 'tur-x-cfg-inc' },
      { exercise: 'tur-x-cfg-mark' },
      { exercise: 'tur-x-cfg-table' },
      { exercise: 'tur-x-steps-inc' },
    ],
  });

  L({
    id: 'tur-l-decide', chapter: 'tur-machines', title: 'Deciders and recognisers', minutes: 10,
    summary: 'A machine that always halts gives you an answer. A machine that may run for ever gives you an answer only when the answer is yes. The difference is the heart of computability.',
    blocks: [
      'A finite automaton always finishes: it reads the last symbol and stops. A Turing machine has no such guarantee. On some inputs it may accept, on others reject, and on others run for ever. So "the language of M" needs care.',
      { def: 'Language of a machine', text: 'L(M) is the set of strings M accepts. Strings it rejects and strings on which it runs for ever are both outside L(M).' },
      { def: 'Recognisable', text: 'L is Turing-recognisable when L = L(M) for some machine M. M must accept every string in L; on a string outside L it may reject or loop.' },
      { def: 'Decidable', text: 'L is decidable when some machine M with L(M) = L halts on every input. Such an M is a decider: it always answers yes or no.' },
      'Every decider is a recogniser, so every decidable language is recognisable. The reverse fails, and Part 6 shows a language (the halting problem) that is recognisable but not decidable. Here we just look at what the difference feels like.',
      { topic: 'tm-decide', input: { pair: 'aa', w: 'bab' }, caption: 'Two machines for "contains aa". The decider rejects bab when it reaches the blank. The recogniser accepts the same strings, but on bab it never stops. From outside, you cannot tell whether it is still thinking or lost for ever.' },
      { predict: { q: 'You run the recogniser on a string and it has not halted after a million steps. What do you know?', options: ['The string is not in the language', 'Nothing yet: it may still accept later', 'The machine is broken'], answer: 1, explain: 'A recogniser can take as long as it likes before accepting. Waiting can confirm a yes, never a no. That is why deciders are so valuable.' } },
      { warn: 'Do not confuse "rejects" with "does not accept". A machine that loops on w does not accept w, but it does not reject it either. Only a decider turns every "not accept" into a real "reject".' },
      { h: 'Make a recogniser into a decider' },
      'Here is a recogniser for "contains aa" that wanders off when it fails. Add one rule so that it rejects instead of looping on every string without aa.',
      { editor: { kind: 'tm', text: 'start: s\naccept: yes\ns, a -> sa, a, R\ns, b -> s, b, R\nsa, a -> yes, a, S\nsa, b -> s, b, R\ns, _ -> s, _, R\nsa, _ -> s, _, R', tests: 'aa\nbaab\n-bab\n-ε\n-a' }, caption: 'Press Test: the rejected strings show no answer, because the machine walks right over blanks for ever. Delete the two rules that read _ (a missing rule rejects), and test again.' },
      { list: ['L(M) is what M accepts; rejecting and looping both leave a string out.', 'Recognisable: some machine accepts exactly L. Decidable: some machine accepts exactly L and always halts.', 'Waiting on a recogniser can confirm yes but never no.'] },
      { exercise: 'tur-x-ch-decider' },
      { exercise: 'tur-x-ch-loop-reject' },
      { exercise: 'tur-x-bab' },
      { exercise: 'tur-x-same-ends' },
    ],
  });

  L({
    id: 'tur-l-transducer', chapter: 'tur-machines', title: 'Machines that compute functions', minutes: 9,
    summary: 'A Turing machine does not only say yes or no: what it leaves on the tape is an answer too. That is how a machine adds, copies and sorts.',
    blocks: [
      'So far we have asked only "accept or reject?". But a machine writes on its tape, and when it halts the tape holds something. Reading that as an output turns a Turing machine into a computer of functions.',
      { def: 'Computes', text: 'M computes the function f when, started on input w, it halts in an accepting state with exactly f(w) on the tape (blanks at the two ends do not count). If M does not halt on w, f(w) is undefined. A function computed by some machine is called computable; if the machine halts on every input, f is total.' },
      'Numbers need a way to be written down. **Unary** writes n as n 1s, which makes arithmetic easy for a machine and long for us; **binary** is short but needs carries.',
      { topic: 'tm-transducer', input: { f: 'add', w: '11+1' }, caption: 'Unary addition: 11+1 becomes 111. The trick is to turn the + into a 1 and then remove one 1 from the end. No counting at all.' },
      { predict: { q: 'The same adding machine runs on +11 (that is, 0 + 2). What should it leave?', options: ['11', '111', '+11', 'nothing: it gets stuck on the +'], answer: 0, explain: 'The + becomes 1, giving 111, and then one 1 is removed from the end: 11. Edge cases like an empty number are where machines usually go wrong, so try them.' } },
      { topic: 'tm-transducer', input: { f: 'copy', w: 'ab' }, caption: 'Copying ab into ab#ab. Each round marks one symbol, carries it in the state to the far end, and comes back. Notice the marked symbols being restored at the end.' },
      { h: 'Your turn' },
      { sandbox: { kind: 'tm', text: 'start: s\naccept: done\ns, a -> ca, _, R\ns, b -> cb, _, R\ns, _ -> done, _, S\nca, a -> ca, a, R\nca, b -> ca, b, R\nca, _ -> done, a, S\ncb, a -> cb, a, R\ncb, b -> cb, b, R\ncb, _ -> done, b, S', input: 'abb' }, caption: 'This machine moves the first symbol to the end. The symbol travels in the state: ca means "carrying an a".' },
      { tip: 'The state is the only thing a head carries. To move a symbol from one place to another, make one state for each symbol you might carry.' },
      { list: ['A machine computes f by halting with f(w) on its tape.', 'Undefined where it does not halt: computable functions may be partial.', 'Carry symbols in the state; mark cells you have dealt with.', 'Always try ε and the smallest inputs.'] },
      { exercise: 'tur-x-ch-transducer' },
      { exercise: 'tur-x-unary-succ' },
      { exercise: 'tur-x-rotate' },
      { exercise: 'tur-x-bin-dec' },
      { exercise: 'tur-x-unary-double' },
    ],
  });

  L({
    id: 'tur-l-design', chapter: 'tur-machines', title: 'Design techniques: mark, sweep and zig-zag', minutes: 14,
    summary: 'Most Turing machines are built from a handful of tricks: checking the shape first, crossing symbols off in matched groups, and zig-zagging between the two ends.',
    blocks: [
      'Writing a Turing machine from scratch feels like programming with your hands tied. It helps to know that almost every machine you will need is built from three or four ideas, used again and again.',
      { steps: ['**Check the shape** with a first pass that behaves like a finite automaton (are the a\'s before the b\'s?). Then come back to the left end.', '**Cross off in groups**: replace one symbol of each kind by a marker (X, Y, Z) per round, so the tape itself counts.', '**Zig-zag**: compare the two ends of the input, erasing or marking them, and move inwards.', '**Carry in the state**: to move or compare a symbol, remember it in the state while the head travels.'] },
      { h: 'Crossing off: aⁿbⁿcⁿ' },
      'No pushdown automaton can recognise aⁿbⁿcⁿ, because its stack can match the a\'s with the b\'s but then has nothing left to match the c\'s. A Turing machine never forgets: it can cross off one a, one b and one c per round.',
      { topic: 'tm-anbncn', input: { w: 'aabbcc' }, caption: 'Each round crosses off one a, one b and one c, then returns to the left. Watch the final check: when no a is left, only crossed-off symbols may remain.' },
      { predict: { q: 'Run the same idea on abcabc, which has two of each letter but in the wrong order. Where should it fail?', options: ['Right after the first round: with no a left before the crossed symbols, it checks that only crossed symbols remain, and meets an a', 'Only at the very end, when it compares the counts', 'It does not fail: the counts are equal'], answer: 0, explain: 'After one round the tape is XYZabc. The next round starts on Y, which means "no a left", so the machine checks that only crossed-off symbols follow, and the a stops it. Counting alone is not enough: abcabc has equal counts but the wrong shape.' } },
      { h: 'Zig-zag: palindromes' },
      { topic: 'tm-palindrome', input: { w: 'abba' }, caption: 'Erase the first symbol, carry it in the state to the far end, compare with the last symbol, erase that too, and come back. The table in the definition shows the cost: about n²/2 steps.' },
      'That quadratic cost is not an accident. With one tape, every comparison of the two ends needs a walk across the middle. Chapter 3 shows that a second tape brings it down to linear time, without being able to compute anything new.',
      { h: 'Design one' },
      { editor: { kind: 'tm', text: 'start: s\naccept: yes\ns, 0 -> r, X, R\ns, Y -> chk, Y, R\ns, _ -> yes, _, S\nr, 0 -> r, 0, R\nr, Y -> r, Y, R\nr, 1 -> l, Y, L\nl, 0 -> l, 0, L\nl, Y -> l, Y, L\nl, X -> s, X, R\nchk, Y -> chk, Y, R', tests: 'ε\n01\n0011\n-0\n-011\n-10\n-0101' }, caption: 'A machine for 0ⁿ1ⁿ that crosses off one 0 (as X) and one 1 (as Y) per round. One rule is missing, so it rejects 01 and 0011. Find it (what should chk do when it reaches the blank?) and make every test pass.' },
      { warn: 'The two most common mistakes: forgetting that the empty string (and other tiny inputs) needs a rule, and forgetting to step over the markers you wrote in an earlier round.' },
      { list: ['Check the shape first, then count.', 'Markers turn the tape into a counter you can never lose.', 'Zig-zag between the ends to compare; it costs about n² steps on one tape.', 'Carry symbols in the state.'] },
      { exercise: 'tur-x-anban' },
      { exercise: 'tur-x-pal01' },
      { exercise: 'tur-x-equal-ab' },
      { exercise: 'tur-x-reverse-hash' },
      { exercise: 'tur-x-sum-ab-c' },
      { exercise: 'tur-x-sort' },
      { exercise: 'tur-x-stutter' },
      { exercise: 'tur-x-drop-b' },
    ],
  });

  // =========================================================================================================
  // Chapter 2: building machines from parts
  // =========================================================================================================
  L({
    id: 'tur-l-macro', chapter: 'tur-building', title: 'A macro language for machines', minutes: 12,
    summary: 'Nobody writes a big transition table by hand. A few statements, each expanding into states and rules, let you write machines the way you write programs.',
    blocks: [
      'The machine for "u#v with v the reverse of u" already needs twenty rules, and most of them say the same thing: "keep moving right until you see a blank". Programmers would call that a loop and give it a name. We can do the same, as long as every statement turns back into ordinary states and rules.',
      { table: [['statement', 'what it does', 'becomes'], ['`left`, `right`', 'move one cell', 'one state, one rule per symbol'], ['`write s`', 'write s, stay', 'one state'], ['`map a:b b:a`', 'rewrite by a table', 'one state'], ['`seek R _`', 'move right until a blank', 'one state that loops on every other symbol'], ['`if b goto L`', 'branch on the symbol', 'one state with two exits'], ['`call name`', 'run a subroutine or a library machine', 'a fresh copy of its states']], caption: 'The statements of the macro language, and what each one compiles to.' },
      { topic: 'tm-macro', input: { w: 'aab' }, caption: 'Five lines that decide "ends in b". Each line becomes one state; seek R _ becomes a state that loops on a and b. The counter shows how many plain rules the program turns into.' },
      { predict: { q: 'A program has 6 statements and the tape alphabet has 4 symbols (a, b, X and the blank). Roughly how many plain rules can it compile to?', options: ['6', 'about 24: up to one rule per statement per symbol', 'about 4⁶'], answer: 1, explain: 'Each statement becomes a state with a rule for every symbol it may read. That is the hidden cost of a macro: small to write, wide underneath.' } },
      { h: 'Subroutines are pasted in' },
      'A call does not jump into shared code and come back, because a Turing machine has nowhere to keep a return address except its state. Instead, every call site gets its *own copy* of the subroutine\'s states, whose exits lead to the statement after that call. This is also why a subroutine may not call itself: the copies would never end.',
      { topic: 'tm-macro', input: { p: 'alphabet: 0 1\n  call tm:bin-inc\n  call tm:bin-inc\n  accept', w: '101' }, caption: 'Calling a library machine twice adds two. Look at the state names: the two copies of bin-inc get different prefixes.' },
      { tip: 'In the exercises, type a program on one line with ; between statements, like `alphabet: a b; seek R _; left; if b accept; reject`.' },
      { list: ['Each statement compiles to one state (or a few) with a rule per symbol.', 'seek and if replace the most common loops and branches.', 'A call pastes in a fresh copy, so there is no recursion.', 'The result is an ordinary machine: nothing was added to the model.'] },
      { exercise: 'tur-x-macro-ends-ab' },
      { exercise: 'tur-x-macro-swap' },
      { exercise: 'tur-x-ch-macro-cost' },
    ],
  });

  L({
    id: 'tur-l-combine', chapter: 'tur-building', title: 'Running machines one after another', minutes: 8,
    summary: 'If one machine flips bits and another adds one, gluing the first\'s halt to the second\'s start gives a machine that negates. Composition is the first tool of every proof that something is computable.',
    blocks: [
      'Big programs are built from small ones. For Turing machines the simplest glue is "run M₁, then run M₂ on whatever M₁ left on the tape".',
      { def: 'Sequential composition', text: 'rename the states of M₁ and M₂ apart; every rule of M₁ that enters an accepting state of M₁ enters M₂\'s start state instead; M₁\'s rejecting states stay rejecting; M₂\'s rules are kept as they are. The start state is M₁\'s.' },
      'One detail matters: where M₁ leaves its head. M₂ expects to start on the first symbol of its input, so a well-behaved part returns its head to the left end before it halts.',
      { topic: 'tm-combine', input: { pair: 'neg', w: '0110' }, caption: 'Flip every bit, then add one: in two\'s complement, 0110 (six) becomes 1010 (minus six). The colours show which part of the combined machine is running.' },
      { predict: { q: 'Negate 0000 with the same pair. What is left on the tape?', options: ['0000, with the carry falling off the left end', '10000', '1111'], answer: 1, explain: 'Flipping gives 1111, and adding one carries all the way: 10000. A fixed-width machine would drop the leading 1; ours has an infinite tape, so it keeps it. Edge cases tell you what a machine really does.' } },
      { topic: 'tm-combine', input: { pair: 'odd', w: '11' }, caption: 'Double, then add one: 2n + 1. Pause on the step where the first machine hands over and check where its head is.' },
      'Composition is how Part 6 builds its machines: "first check the input has the right form, then run this, then that". Each part is a machine you already trust.',
      { list: ['Send M₁\'s accept into M₂\'s start; keep the reject.', 'Leave the head where the next machine expects it.', 'Composition never adds power, only convenience.'] },
      { exercise: 'tur-x-macro-plus3' },
      { exercise: 'tur-x-combine-count' },
    ],
  });

  // =========================================================================================================
  // Chapter 3: variants
  // =========================================================================================================
  L({
    id: 'tur-l-multitape', chapter: 'tur-variants', title: 'More tapes, same power', minutes: 13,
    summary: 'A machine with three tapes is far easier to program than a machine with one. It is faster too. But it cannot compute anything the one-tape machine cannot.',
    blocks: [
      'The palindrome machine wore itself out walking from end to end. With a second tape it could copy the input once, then read one copy forwards and the other backwards at the same time.',
      { def: 'k-tape machine', text: 'a machine with k tapes, each with its own head. δ : Q × Γᵏ → Q × Γᵏ × {L, R, S}ᵏ reads all k heads at once, writes on all k tapes, and moves each head its own way. The input starts on tape 1; the others start blank.' },
      { topic: 'tm-multitape', input: { m: 'pal', w: 'abba' }, caption: 'Palindromes with two tapes: copy, rewind one head, then compare while the heads move in opposite directions. The step count grows linearly with the length, not quadratically.' },
      { h: 'Simulating k tapes on one' },
      'Here is why the extra tapes add no power. Give each cell of a single tape 2k **tracks**: track 2i − 1 holds the contents of tape i, and track 2i holds a mark under the cell where head i is. A combined symbol is just a tuple, so the tape alphabet grows but stays finite.',
      { steps: ['Sweep right over the used part of the tape, collecting in the state the k symbols under the k marks.', 'Now the state knows everything δ needs: look up the rule.', 'Sweep left, writing the new symbols under the marks and moving each mark one cell left or right.'] },
      { topic: 'tm-ksim', input: { m: 'pal', w: 'aba' }, frame: 20, caption: 'One tape simulating the two-tape palindrome machine. The marks on the even tracks are the two heads. Compare the two step counters as the run goes on.' },
      { predict: { q: 'After t steps the two-tape machine has used at most about t cells. How many single-tape steps does the whole simulation take, roughly?', options: ['about t', 'about t²', 'about 2ᵗ'], answer: 1, explain: 'Each simulated step is two sweeps over at most about t cells, so t steps cost about t · t. A quadratic slowdown: worth knowing for Part 7, harmless for computability.' } },
      { tip: 'Multi-head machines (several heads on one tape) are simulated the same way: one mark track per head.' },
      { list: ['k tapes make programs simpler and faster.', 'One tape with 2k tracks simulates them, step for step.', 'The cost is quadratic, never more: same languages, same functions.'] },
      { exercise: 'tur-x-ch-ktape-power' },
      { exercise: 'tur-x-tracks' },
      { exercise: 'tur-x-ktape-alpha' },
    ],
  });

  L({
    id: 'tur-l-tapes', chapter: 'tur-variants', title: 'One-way tapes and two-dimensional tapes', minutes: 11,
    summary: 'Cut the tape off on the left, or spread it out into a grid: either way, the machine can do exactly what it could before. Folding and numbering are the two tricks.',
    blocks: [
      'Our tapes go on for ever in both directions. Many presentations use a tape with a left end instead. And one could imagine a sheet of squared paper rather than a strip. Do these choices matter?',
      { h: 'Folding a two-way tape' },
      'A one-way tape can hold a two-way tape by folding it at cell 0, like a strip of paper bent back on itself: give each cell two tracks, the upper for the cells 0, 1, 2, … and the lower for −1, −2, … . A marker in the first cell tells the machine it has reached the fold.',
      { math: 'cell p ≥ 0  ↦  folded cell p + 1, upper track\ncell p < 0  ↦  folded cell −p, lower track\nstates (q, up) and (q, down): on the lower track, L and R swap' },
      { topic: 'tm-oneway', input: { m: 'inc', w: '111' }, caption: 'Binary increment on 111 needs one cell left of the input. On the folded tape that cell is on the lower track: watch the head cross the fold, where left and right swap.' },
      { predict: { q: 'The two-way machine moves left while on cell −2. Which way does the folded machine\'s head move?', options: ['Left, to folded cell 1', 'Right, to folded cell 3', 'It stays and switches track'], answer: 1, explain: 'Cell −2 is folded cell 2 (lower track), and cell −3 is folded cell 3. Moving left on the negative side means moving right on the fold.' } },
      { h: 'A grid' },
      'A 2-D machine can also move up and down. To put a grid on a strip, number its cells: walk the diagonals x + y = 0, 1, 2, …, giving (x, y) the number π(x, y) = (x + y)(x + y + 1)/2 + y. Moving up, down, left or right becomes "go to another number", which a one-tape machine can work out and walk to.',
      { topic: 'tm-2d', input: { w: 'abba' }, caption: 'A machine that drops a shadow under its input row, moving D and U as well as L and R. Every move is local, which is what makes the simulation possible.' },
      { list: ['A one-way tape simulates a two-way tape by folding; the cost is a constant factor.', 'A grid is laid out on a strip by numbering its cells along diagonals.', 'Neither changes what can be computed.'] },
      { exercise: 'tur-x-fold' },
      { exercise: 'tur-x-pairing' },
    ],
  });

  L({
    id: 'tur-l-ntm', chapter: 'tur-variants', title: 'Nondeterministic machines and their simulation', minutes: 13,
    summary: 'A nondeterministic machine may have several moves at once and accepts if any branch does. A deterministic machine can search the whole tree of branches, breadth first, and find that branch if it exists.',
    blocks: [
      'Nondeterminism made finite automata easier to design and no stronger. For Turing machines the story ends the same way, but the simulation has a twist: some branches never end.',
      { def: 'Nondeterministic TM', text: 'a machine whose δ gives a set of moves: δ : Q × Γ → 𝒫(Q × Γ × {L, R, S}). Its runs on w form a tree; it accepts w when some branch reaches q_acc.' },
      'Guessing is the point. To check that some letter occurs twice, a nondeterministic machine guesses the first position, remembers the letter, and guesses the second.',
      { topic: 'tm-ntm-tree', input: { m: 'rep', w: 'abca' }, frame: 15, caption: 'The computation tree on abca. Each node is a configuration; children are the choices. One branch guesses both a\'s and accepts; the rest die. Accepting needs only one.' },
      { predict: { q: 'A deterministic simulator explores the tree depth first, always taking the first child. Is that safe?', options: ['Yes: every branch is eventually visited', 'No: if the first branch is infinite, the search never comes back', 'Yes, as long as the machine is a decider'], answer: 1, explain: 'Depth first can be swallowed by one endless branch while an accepting branch sits next to it. Breadth first visits every node at depth d after finitely many others, so it finds any accepting leaf.' } },
      { topic: 'tm-ntm-tree', input: { m: 'ab', w: 'bab' }, frame: 9, caption: 'This machine has a branch that runs for ever. Breadth-first search still finds the accepting branch, because it never commits to one path.' },
      { h: 'Addresses on a third tape' },
      'A deterministic machine can do the breadth-first search with three tapes. Tape 1 keeps the input. Tape 3 holds an **address**, a string over {1, …, b} where b is the most choices any configuration has. For each address in shortlex order, copy the input to tape 2 and run the machine, taking choice number d at each step from the next digit of the address.',
      { topic: 'tm-ntm-address', input: { m: 'rep', w: 'aba' }, frame: 14, caption: 'Addresses ε, 1, 2, 11, 12, … each pick one path from the root. Shortlex order is breadth first: all short paths before any longer one.' },
      { warn: 'The simulation can be very slow: a tree of depth t has up to bᵗ nodes. Whether that exponential cost can be avoided in general is the P versus NP question of Part 7.' },
      { list: ['Nondeterministic: a tree of runs; accept if any branch accepts.', 'Search the tree breadth first, never depth first.', 'Addresses in shortlex order do the search deterministically.', 'Same power, possibly exponential cost.'] },
      { exercise: 'tur-x-ch-ntm' },
      { exercise: 'tur-x-addresses' },
    ],
  });

  L({
    id: 'tur-l-enum', chapter: 'tur-variants', title: 'Enumerators and dovetailing', minutes: 12,
    summary: 'A language is recognisable exactly when a machine can print it, one string after another. Turning a recogniser into a printer needs one clever idea: never wait too long on any one string.',
    blocks: [
      'Instead of answering questions about strings, a machine could simply print the strings of a language, one by one, on a printer that only goes forward. Such a machine is an **enumerator**.',
      { def: 'Enumerator', text: 'a Turing machine with an output printer. It starts on a blank tape; from time to time it prints a string. The language it enumerates is the set of strings it ever prints, in any order, possibly with repeats.' },
      { topic: 'tm-enumerator', input: { m: 'anbn', n: 4 }, frame: 28, caption: 'An enumerator for aⁿbⁿ prints ε, ab, aabb, aaabbb, … . It never stops, and every string of the language appears after finitely many steps.' },
      'From an enumerator to a recogniser is easy: on input w, run the enumerator and accept if it ever prints w. The other way is harder, and it is where many people go wrong.',
      { predict: { q: 'You have a recogniser R. Your plan: for each string s₁, s₂, s₃, … in shortlex order, run R on it, and print it if R accepts. What goes wrong?', options: ['Nothing', 'If R loops on s₁, nothing after s₁ is ever printed', 'It prints strings outside the language'], answer: 1, explain: 'R may run for ever on a string it does not accept. Running the strings one at a time, you get stuck on the first such string.' } },
      { h: 'Dovetailing' },
      'The fix is to share time out fairly. In round n, run R for n steps on each of s₁, …, sₙ, starting each run afresh. A string that R accepts in k steps is printed in round max(i, k) at the latest, where i is its position. Every pair (string, step count) comes up after finitely many others, so no loop can stall the whole schedule.',
      { topic: 'tm-dovetail', input: { m: 'aa', order: 'zig' }, frame: 30, caption: 'The zig-zag schedule over (string, steps) pairs. Strings without aa make R spin, but each only gets a bounded slice of each round, so the strings with aa keep coming out.' },
      { topic: 'tm-dovetail', input: { m: 'aa', order: 'one' }, frame: 8, caption: 'The same recogniser, one string at a time. It gets stuck on ε, which has no aa, and prints nothing at all.' },
      { tip: 'Dovetailing is a general tool: whenever you must run infinitely many computations, any of which may loop, interleave them along the diagonals.' },
      { list: ['L is recognisable exactly when some enumerator prints L.', 'Enumerator → recogniser: wait for w to be printed.', 'Recogniser → enumerator: dovetail over strings and step counts.', 'An enumerator that prints in shortlex order gives a decider.'] },
      { exercise: 'tur-x-ch-enum' },
      { exercise: 'tur-x-dovetail' },
    ],
  });

  // =========================================================================================================
  // Chapter 4: other models
  // =========================================================================================================
  L({
    id: 'tur-l-ram', chapter: 'tur-models', title: 'Register machines and RAMs', minutes: 12,
    summary: 'Forget tapes. A handful of registers holding whole numbers, and five instructions, already compute everything a Turing machine can.',
    blocks: [
      'Real computers do not have tapes: they have memory cells with addresses, and instructions that work on numbers. A **register machine** keeps just the essentials of that.',
      { def: 'Register machine', text: 'a numbered list of instructions over registers r0, r1, r2, …, each holding a whole number ≥ 0. The core instructions are inc r, dec r (never below 0), jz r label (jump if r is zero), jmp label and halt. The input is in r1, r2, …, the output is r0, and every other register starts at 0.' },
      'With only those five, you cannot even copy a register without destroying it: to read r1 you must count it down to zero. That is why programs keep a spare register to put things back.',
      { topic: 'ram-run', input: { r: 'r1=2, r2=3' }, caption: 'Multiplication: for each unit of r1, move r2 into r0 one at a time while saving it in r3, then move r3 back. Watch r2 empty and refill in every round.' },
      { predict: { q: 'Running the multiplication program with r1 = 0 and r2 = 5, what is r0 at the end, and what is r2?', options: ['r0 = 0 and r2 = 5', 'r0 = 5 and r2 = 0', 'r0 = 0 and r2 = 0'], answer: 0, explain: 'The outer loop finds r1 = 0 at once and halts. r2 is never touched, so it is still 5.' } },
      { h: 'RAM extras' },
      'A **RAM** adds instructions that real machines have: set r k, copy, add, sub, and indirect addressing, load r s (r := R[R[s]]) and store. These make programs short, but each can be written with the core five, so they add speed and no power. Open [the topic](#topic=ram-run) and choose the preset that sums an array to see indirect addressing at work.',
      { h: 'Why registers are enough' },
      'A register machine can simulate a Turing machine: split the tape at the head, read each half as a number in base |Γ|, and keep the two numbers in two registers. Moving the head is multiplying or dividing by |Γ|, and the symbol under the head is a remainder. And a Turing machine can simulate a register machine by writing the registers on its tape. Each model computes what the other does.',
      { tip: 'In the exercises, type a program on one line: `loop: jz r1 done; dec r1; inc r0; jmp loop; done: halt`.' },
      { list: ['Registers hold unbounded whole numbers; five instructions suffice.', 'Reading a register destroys it unless you copy it to a spare.', 'RAM instructions (indirect addressing too) add speed, not power.', 'Register machines and Turing machines simulate each other.'] },
      { exercise: 'tur-x-ram-trace' },
      { exercise: 'tur-x-ram-plus2' },
      { exercise: 'tur-x-ram-triple' },
      { exercise: 'tur-x-ram-mod3' },
      { exercise: 'tur-x-ram-add' },
    ],
  });

  L({
    id: 'tur-l-counter', chapter: 'tur-models', title: 'Two counters are enough', minutes: 10,
    summary: 'A machine with two counters that can only go up, go down, and test for zero can simulate a Turing machine. The secret is to pack many numbers into one with prime powers.',
    blocks: [
      'A **counter machine** is a register machine stripped further: a few counters, and instructions that add one, take one away, or branch when a counter is zero. That is less than a pushdown automaton with a one-letter stack per counter. Surely two of them are weak?',
      { def: 'Counter machine', text: 'labelled lines of three kinds: q: inc C next; q: dec C next ifzero (if C > 0, take one and go to next, otherwise go to ifzero); q: halt.' },
      { topic: 'counter-run', input: { p: 'double', a: 3 }, caption: 'Doubling with two counters: move A into B two at a time, then move B back into A. The second counter is pure scratch space.' },
      { h: 'Many counters in one' },
      'Here is the surprise. Three counters c₁, c₂, c₃ can live in one number N = 2^c₁ · 3^c₂ · 5^c₃. Adding one to c₂ is multiplying N by 3; testing c₃ = 0 is checking that 5 does not divide N. With a second counter as scratch, each of those is a loop of incs and decs.',
      { predict: { q: 'N = 2^c₁ · 3^c₂ · 5^c₃ = 90. What are the counters?', options: ['c₁ = 1, c₂ = 2, c₃ = 1', 'c₁ = 2, c₂ = 1, c₃ = 1', 'c₁ = 1, c₂ = 1, c₃ = 2'], answer: 0, explain: '90 = 2 · 9 · 5 = 2¹ · 3² · 5¹.' } },
      { topic: 'counter-run', input: { p: 'prime-powers', a: 12 }, caption: 'A = 2^x · 3^y becomes 2^(x+y): the counter machine moves a hidden counter into another, dividing and multiplying as it goes. 12 = 2² · 3 becomes 2³ = 8.' },
      'Since a Turing machine can be simulated with two stacks, and each stack (a string over a finite alphabet) is a number, and any number of counters fit into two, **two-counter machines are as powerful as Turing machines**, if their input and output are coded as powers of 2. With one counter, by contrast, you get much less.',
      { list: ['Counters only inc, dec and test zero.', 'Prime powers pack many counters into one number.', 'Two counters simulate any Turing machine, with the input coded as 2ⁿ.'] },
      { exercise: 'tur-x-counter-run' },
      { exercise: 'tur-x-godel-counters' },
      { exercise: 'tur-x-godel-inc' },
    ],
  });

  L({
    id: 'tur-l-lba', chapter: 'tur-models', title: 'Linear-bounded automata and unrestricted grammars', minutes: 13,
    summary: 'Fence a Turing machine in so it may only use the cells of its input, and you get the linear-bounded automaton. Let grammar rules rewrite whole groups of symbols, and you get grammars as strong as Turing machines.',
    blocks: [
      'Between pushdown automata and Turing machines there is a natural stop: a Turing machine that may read and write as it likes, but **never leaves the cells of its input**.',
      { def: 'Linear-bounded automaton (LBA)', text: 'a nondeterministic Turing machine whose input is written between two endmarkers it can read but never cross or overwrite. All its work happens in the n cells of the input.' },
      { topic: 'lba-run', input: { m: 'abc', w: 'aabbcc' }, caption: 'aⁿbⁿcⁿ fits in the input\'s own cells: cross off one of each per round, never stepping past the walls.' },
      'Because its space is fenced in, an LBA on input w has only finitely many configurations: q states times n + 2 head positions times gⁿ tape contents. Any run longer than that repeats a configuration and so loops for ever. So a decider can simulate an LBA, counting steps, and reject once the count passes the bound.',
      { topic: 'lba-run', input: { m: 'bounce', w: 'ab' }, caption: 'A machine that bounces between the walls for ever. The simulator sees a configuration repeat and stops with a reject: the loop has been decided.' },
      { predict: { q: 'An LBA has 4 states and 3 tape symbols. How many configurations can it have on an input of length 2?', options: ['4 · 4 · 9 = 144', '4 · 2 · 9 = 72', '4 · 3 · 2 = 24'], answer: 0, explain: 'States 4, head positions 2 + 2 = 4 (the cells and the two endmarkers), tape contents 3² = 9.' } },
      { h: 'Grammars that rewrite groups' },
      'In a context-free rule, the left side is one variable. Allow any non-empty string on the left, α → β, and grammars become **unrestricted**. A rule like `cB → Bc` lets a B travel left through the c\'s, which is how a grammar moves information around, much as a head does.',
      { topic: 'ugrammar-derive', input: { w: 'aabbcc' }, frame: 11, caption: 'A grammar for aⁿbⁿcⁿ. It makes the right numbers of a, B and c first, then lets each B slide left past the c\'s to meet the b\'s. Every rule keeps the string the same length or longer.' },
      { def: 'Context-sensitive grammar', text: 'an unrestricted grammar whose rules never shrink the string (|α| ≤ |β|), except S → ε when S appears on no right side. Context-sensitive grammars generate exactly the languages of LBAs.' },
      'Unrestricted grammars, with rules that may shrink the string, generate exactly the Turing-recognisable languages: a derivation is a computation run backwards, and a machine can search for derivations.',
      { topic: 'ugrammar-derive', input: { g: 'S -> LaR\nL -> LD\nDa -> aaD\nDR -> R\nL -> ε\nR -> ε', w: 'aaaa' }, frame: 21, caption: 'A doubling grammar: each D walks right through the a\'s, doubling each one. The rules DR → R and L → ε shrink the string, so this grammar is unrestricted, not context-sensitive.' },
      { list: ['An LBA works only inside its input.', 'Finitely many configurations, so its acceptance is decidable.', 'Noncontracting grammars ↔ LBAs (context-sensitive languages).', 'Unrestricted grammars ↔ Turing machines (recognisable languages).'] },
      { exercise: 'tur-x-lba-bound' },
      { exercise: 'tur-x-ch-lba' },
      { exercise: 'tur-x-ugrammar-lengths' },
      { exercise: 'tur-x-ugrammar-equal' },
    ],
  });

  L({
    id: 'tur-l-chomsky', chapter: 'tur-models', title: 'The Chomsky hierarchy', minutes: 9,
    summary: 'Four kinds of grammar, four kinds of machine, four classes of language, each strictly inside the next. Here is the whole map in one picture.',
    blocks: [
      'We now have grammars and machines at four levels. They line up perfectly.',
      { table: [['type', 'grammar rules', 'machine', 'languages'], ['3', 'A → a B or A → a', 'finite automaton', 'regular'], ['2', 'A → γ', 'pushdown automaton', 'context-free'], ['1', 'α → β with |α| ≤ |β|', 'linear-bounded automaton', 'context-sensitive'], ['0', 'α → β', 'Turing machine', 'recognisable']], caption: 'The four levels. Each kind of grammar is a special case of the one below it.' },
      { topic: 'chomsky-map', input: { focus: 'l4' }, frame: 6, caption: 'Where does aⁿbⁿcⁿ live? Not in the context-free circle, since the pumping lemma breaks it; inside the context-sensitive one, since an LBA decides it.' },
      'Every inclusion is strict, and each has a witness: (ab)* is regular; aⁿbⁿ is context-free but not regular; aⁿbⁿcⁿ is context-sensitive but not context-free; some decidable languages are not context-sensitive; and the halting problem is recognisable but not decidable.',
      { predict: { q: 'Where does the language ww (any string written twice) go?', options: ['Regular', 'Context-free but not regular', 'Context-sensitive but not context-free', 'Recognisable but not decidable'], answer: 2, explain: 'A stack would reverse the first half, which suits wwᴿ, not ww. An LBA can mark and compare the halves in place.' } },
      { topic: 'chomsky-map', input: { focus: 'l7' }, frame: 6, caption: 'The complement of the halting problem lies outside every circle: not even recognisable.' },
      { list: ['Type 3 ⊂ type 2 ⊂ type 1 ⊂ decidable ⊂ type 0: each strictly.', 'Each grammar type matches one kind of machine.', 'Witnesses: (ab)*, aⁿbⁿ, aⁿbⁿcⁿ, the halting problem.'] },
      { exercise: 'tur-x-ch-chomsky' },
      { exercise: 'tur-x-ch-hierarchy' },
    ],
  });

  // =========================================================================================================
  // Chapter 5: recursive functions and λ
  // =========================================================================================================
  L({
    id: 'tur-l-primrec', chapter: 'tur-functions', title: 'Primitive recursive functions', minutes: 13,
    summary: 'Start with zero, add one, and pick an argument. Allow composition and recursion on a counter. You can build addition, multiplication, powers and much more, and every function you build halts.',
    blocks: [
      'Turing machines describe computing as a process. There is another way in, through functions defined from smaller functions, the way a mathematician would. It turns out to reach the same place.',
      { def: 'Basic functions', text: 'zero Z(x̄) = 0; successor S(x) = x + 1; projections P(i, n)(x₁, …, xₙ) = xᵢ.' },
      { def: 'Composition', text: 'C(f; g₁, …, gₘ)(x̄) = f(g₁(x̄), …, gₘ(x̄)).' },
      { def: 'Primitive recursion', text: 'h = R(f, g) is defined by h(x̄, 0) = f(x̄) and h(x̄, y + 1) = g(x̄, y, h(x̄, y)). The last argument counts down; g gets the previous value.' },
      'The **primitive recursive** functions are the ones built from the basic functions by composition and primitive recursion, as many times as you like. Here is addition: add(x, 0) = x, and add(x, y + 1) = S(add(x, y)).',
      { math: 'add = R(P(1,1), C(S; P(3,3)))\nmult = R(Z, C(add; P(1,3), P(3,3)))' },
      { topic: 'primrec-tree', input: { f: 'add', a: '2, 3' }, caption: 'add(2, 3) unfolds into add(2, 2), add(2, 1), add(2, 0), then climbs back up adding one at each level. The recursion is a loop that runs exactly y times.' },
      { predict: { q: 'mult(2, 3) is defined through add. How many calls of add does it make?', options: ['2', '3', '6'], answer: 1, explain: 'mult(x, y + 1) = add(x, mult(x, y)): one add per step of y, so 3 calls (each of which makes its own steps inside).' } },
      { topic: 'primrec-tree', input: { f: 'pred', a: '3' }, caption: 'The predecessor is a recursion that simply returns the counter: pred(y + 1) = y. Subtraction, comparisons and tests are all built from tricks like this.' },
      'Every primitive recursive function is total: each recursion runs a known number of times, fixed before it starts. In programming terms, these are the functions you can write with **for-loops only**, where each loop\'s count is known when it begins.',
      { warn: 'Total sounds good, but it is a limit. Chapter 6\'s universal machine and the next lesson\'s Ackermann function show computable, total functions that no fixed nesting of for-loops can reach.' },
      { list: ['Start from Z, S and P(i, n).', 'Build with composition C and primitive recursion R.', 'Every primitive recursive function halts on every input.', 'R is a for-loop whose count is fixed in advance.'] },
      { exercise: 'tur-x-pr-eval' },
      { exercise: 'tur-x-pr-eval2' },
      { exercise: 'tur-x-pr-write-plus2' },
      { exercise: 'tur-x-pr-write-xyx' },
      { exercise: 'tur-x-pr-write-pow3' },
    ],
  });

  L({
    id: 'tur-l-mu', chapter: 'tur-functions', title: 'Unbounded search, and a function that outgrows every loop', minutes: 13,
    summary: 'Add one operator, "the least z such that…", and functions may fail to halt, just like machines. Then meet Ackermann\'s function, total and computable, which climbs faster than any for-loop program can.',
    blocks: [
      'Primitive recursion only has for-loops. Programs also have while-loops, which run until a condition comes true, if it ever does. In the world of functions that is the **μ operator**.',
      { def: 'Minimisation', text: 'μf(x̄) is the least z such that f(x̄, z) = 0 and f(x̄, z′) is defined for every z′ < z. If there is no such z, μf(x̄) is undefined.' },
      'The **μ-recursive** (or partial recursive) functions are those built from the basic functions with composition, primitive recursion and μ. They are exactly the functions Turing machines compute, partial ones included.',
      { topic: 'mu-search', input: { f: 'div', a: '7, 2' }, caption: 'Division as a search: try z = 0, 1, 2, … until (z + 1) · 2 > 7. The answer is 3, found on the fourth try.' },
      { predict: { q: 'The same search runs on div(5, 0). What happens?', options: ['It returns 0', 'It returns 5', 'It never stops: no z makes (z + 1) · 0 > 5'], answer: 2, explain: 'The condition is never met, so the search runs for ever: div(5, 0) is undefined. Partiality came in with μ, exactly as looping came in with Turing machines.' } },
      { topic: 'mu-search', input: { f: 'div', a: '5, 0' }, frame: 13, caption: 'The search that never ends. The player gives up after a budget, as any simulator must.' },
      { h: 'Ackermann\'s function' },
      'Is μ really needed for total functions, or could clever for-loops do everything that always halts? Ackermann\'s function settles it.',
      { math: 'A(0, n) = n + 1\nA(m + 1, 0) = A(m, 1)\nA(m + 1, n + 1) = A(m, A(m + 1, n))' },
      { topic: 'ackermann', input: { m: 2, n: 1 }, caption: 'A(2, 1) = 5 already needs 14 calls. Watch the stack of pending calls grow and shrink: each row of A is a loop over the row above.' },
      'Row by row: A(1, n) = n + 2, A(2, n) = 2n + 3, A(3, n) = 2ⁿ⁺³ − 3, and A(4, n) is a tower of 2s. Each row iterates the one above, so each new row needs one more nested loop. A primitive recursive function has a fixed nesting depth, so some row of A eventually beats it, and the diagonal A(n, n) beats them all.',
      { predict: { q: 'Is A computable?', options: ['No: it grows too fast for any machine', 'Yes: the recursion always ends, so a program can just follow it', 'Only for m ≤ 3'], answer: 1, explain: 'Each call is on a smaller pair in dictionary order, so the recursion ends. A is total and computable, yet not primitive recursive.' } },
      { list: ['μ is unbounded search: the least z with f(x̄, z) = 0.', 'μ-recursive = Turing-computable, partial functions included.', 'Ackermann\'s function is total and computable but not primitive recursive.', 'For-loops alone cannot reach every total computable function.'] },
      { exercise: 'tur-x-mu-eval' },
      { exercise: 'tur-x-ch-mu' },
      { exercise: 'tur-x-ack-value' },
      { exercise: 'tur-x-ack-table' },
      { exercise: 'tur-x-ch-ack' },
    ],
  });

  L({
    id: 'tur-l-lambda', chapter: 'tur-functions', title: 'The λ-calculus: computing by substitution', minutes: 14,
    summary: 'No tape, no numbers, no instructions: only functions applied to functions, and one rule that substitutes an argument for a variable. It computes everything a Turing machine can.',
    blocks: [
      'The λ-calculus has just three kinds of term: a variable x, a function λx. M that takes x and gives back M, and an application M N that feeds N to M.',
      { def: 'β-reduction', text: '(λx. M) N  →  M[x := N]: replace the free occurrences of x in M by N, first renaming bound variables of M so that no free variable of N is captured. A term with no redex (λx. M) N left anywhere is in normal form.' },
      'Computing means reducing until no redex is left. The order matters: **normal order** always reduces the leftmost outermost redex first.',
      { topic: 'lambda-reduce', input: { t: 'SUCC 2' }, caption: 'Numbers are functions too: the Church numeral n is λf x. f (f (… (f x))), with n f\'s. SUCC 2 reduces to 3. Each step names the redex it reduces.' },
      { predict: { q: 'What is the normal form of (λx. x x) (λy. y)?', options: ['(λy. y) (λy. y)', 'λy. y', 'x x', 'There is none'], answer: 1, explain: 'One step gives (λy. y) (λy. y), which is still a redex; one more gives λy. y.' } },
      { h: 'Order matters' },
      'Ω = (λx. x x) (λx. x x) reduces to itself, for ever: it has no normal form, the λ-calculus\'s version of a loop. Now feed Ω to a function that ignores its argument.',
      { topic: 'lambda-reduce', input: { t: '(λx y. x) (λz. z) ((λx. x x) (λx. x x))' }, caption: 'Normal order reduces the outer redex first, which throws Ω away, and finishes in two steps. Reducing the argument first would spin for ever.' },
      { warn: 'Substitution must not capture. In (λx. λy. x y) y, the y passed in is free; substituting it straight into λy. … would make it bound. Rename first: λz. y z.' },
      { topic: 'lambda-reduce', input: { t: 'PLUS 2 1' }, caption: 'Arithmetic with Church numerals: PLUS m n = λf x. m f (n f x) applies f n times, then m more.' },
      'Booleans are functions that choose (TRUE = λt f. t, FALSE = λt f. f), pairs are functions that hold two things, and recursion comes from a fixed-point combinator. Every μ-recursive function can be written this way, and a Turing machine can carry out β-reduction, so the λ-calculus computes exactly the Turing-computable functions.',
      { list: ['Terms: variables, λx. M, and M N.', 'One rule: β-reduction, with renaming to avoid capture.', 'Normal order finds a normal form whenever one exists.', 'Church numerals, booleans and recursion make it as strong as a Turing machine.'] },
      { exercise: 'tur-x-lam-id' },
      { exercise: 'tur-x-lam-twice' },
      { exercise: 'tur-x-lam-capture' },
      { exercise: 'tur-x-lam-succ' },
      { exercise: 'tur-x-lam-k' },
      { exercise: 'tur-x-ch-normal-order' },
    ],
  });

  // =========================================================================================================
  // Chapter 6: encodings and the universal machine
  // =========================================================================================================
  L({
    id: 'tur-l-encode', chapter: 'tur-universal', title: 'A machine as a string of bits', minutes: 12,
    summary: 'A Turing machine is a finite list of rules, and a finite list can be written down. Once machines are strings, machines can read other machines.',
    blocks: [
      'Everything a Turing machine is fits on a postcard: its states, its symbols and its rules. Give each a number, write each number in a way that can be read back, and the machine becomes a string. We write ⟨M⟩ for the string of M.',
      { h: 'One convention' },
      { math: 'states  q1 (start), q2 (accept), q3 (reject), q4, …\nsymbols  1 (blank), 2, 3, …       moves  L = 1, R = 2, S = 3\nδ(qi, j) = (qk, l, m)  ↦  0^i 1 0^j 1 0^k 1 0^l 1 0^m\nrules joined by 11;  ⟨M, w⟩ = ⟨M⟩ 111 ⟨w⟩' },
      'Every number is a run of 0s, at least one long, so a single 1 separates fields, 11 separates rules, and 111 separates the machine from its input. Nothing is ambiguous.',
      { topic: 'tm-encode', input: { m: 'flip', w: '10' }, caption: 'The bit-flipping machine has three rules, so its code has three blocks joined by 11. Each block is five runs of 0s: state, symbol, next state, symbol written, move.' },
      { predict: { q: 'How is the move R written?', options: ['0', '00', '000', '1'], answer: 1, explain: 'L = 1, R = 2, S = 3, and a number n is a run of n 0s: R is 00.' } },
      { h: 'Reading it back' },
      'Decoding splits at 11 into rules, splits each rule at 1 into five runs, and counts. Not every bit string is a machine: a field might be empty, there might be 111 inside, or two rules for the same state and symbol. A decoder checks all of that.',
      { topic: 'tm-decode', input: { c: '010010100100110100010000100010011000010010100100110000100010010001000' }, frame: 5, caption: 'Four rules come out of this code. Read them off the table: the machine accepts strings that contain 11.' },
      { topic: 'tm-decode', input: { c: '010100100100111010' }, frame: 3, caption: 'A string with 111 inside the machine part is not a machine. Many conventions simply say: an invalid string stands for a machine that rejects everything.' },
      { tip: 'Since every machine is a string, the machines can be listed in order M₁, M₂, M₃, … . There are only countably many of them, but uncountably many languages, so most languages have no machine at all.' },
      { list: ['Number states, symbols and moves; write numbers as runs of 0s.', '1 separates fields, 11 rules, 111 the machine from its input.', 'Decoding checks validity; invalid strings can stand for a trivial machine.', 'Machines are countable, languages are not.'] },
      { exercise: 'tur-x-enc-rule' },
      { exercise: 'tur-x-dec-rule' },
      { exercise: 'tur-x-enc-word' },
      { exercise: 'tur-x-enc-machine' },
      { exercise: 'tur-x-dec-machine' },
      { exercise: 'tur-x-dec-count' },
      { exercise: 'tur-x-unpair' },
    ],
  });

  L({
    id: 'tur-l-utm', chapter: 'tur-universal', title: 'One machine that runs them all', minutes: 11,
    summary: 'A single, fixed Turing machine, given the code of any machine M and an input w, does whatever M would do on w. It is the idea behind every stored-program computer.',
    blocks: [
      'Until now each machine did one job. But if a machine is a string, then a machine could read that string and *follow* it. That machine is the **universal Turing machine** U.',
      { def: 'Universal machine', text: 'U on input ⟨M, w⟩ accepts if M accepts w, rejects if M rejects w, and runs for ever if M runs for ever on w.' },
      { steps: ['Tape 1 holds ⟨M⟩ and is only read.', 'Tape 2 holds M\'s tape, each symbol written as its run of 0s.', 'Tape 3 holds M\'s current state, as a run of 0s.', 'Each simulated step: read the state on tape 3 and the symbol under the simulated head on tape 2; scan tape 1 for the rule that starts with those two fields; rewrite the symbol, move the simulated head, and replace the state.', 'Stop when the state is q2 (accept) or q3 (reject).'] },
      { topic: 'utm-run', input: { m: 'c11', w: '0110' }, caption: 'U running "contains 11" on 0110. Watch the head on tape 1 scan from rule to rule until it finds the one that matches tape 3 and the block under tape 2\'s head.' },
      { predict: { q: 'M has 50 states. How many states does U need to run it?', options: ['At least 50', 'The same fixed number as for any other M', 'It depends on the input w'], answer: 1, explain: 'U keeps M\'s state as a string on tape 3, not in its own states. One machine, of one fixed size, runs every machine there is.' } },
      { topic: 'utm-run', input: { m: 'flip', w: '101' }, caption: 'The same U runs a different machine, the bit flipper, without a single change. Only the data on tape 1 is different.' },
      'This is the idea of a stored-program computer: a program is just data that a fixed machine interprets. It is also the key to Part 6, where a machine that receives machines as input is fed its own description.',
      { list: ['U(⟨M, w⟩) behaves exactly like M on w.', 'U has fixed size: M\'s state is data on a tape.', 'Each step scans ⟨M⟩ for the matching rule.', 'Programs are data.'] },
      { exercise: 'tur-x-ch-utm' },
      { exercise: 'tur-x-utm-steps' },
    ],
  });

  L({
    id: 'tur-l-thesis', chapter: 'tur-universal', title: 'Busy beavers and the Church–Turing thesis', minutes: 12,
    summary: 'How long can a small machine run before it halts? The record grows faster than anything computable. And every model in this part computes the same functions, which is the evidence for the thesis that ties them all to "computable".',
    blocks: [
      'Take all machines with n states and two symbols, start each on a blank tape, and look at the ones that halt. The **busy beaver** is the one that runs longest. Its step count is S(n), and the most 1s any of them leaves is Σ(n).',
      { topic: 'tm-busy-beaver', input: { m: 'bb2' }, caption: 'The 2-state champion: 6 steps, four 1s. Small machines can be surprisingly busy.' },
      { topic: 'tm-busy-beaver', input: { m: 'bb4' }, frame: 108, caption: 'The 4-state champion runs 107 steps and leaves thirteen 1s. Five states already give a record in the tens of millions.' },
      { predict: { q: 'Suppose a program could compute S(n). What could you do with it?', options: ['Nothing new', 'Decide whether any n-state machine halts on a blank tape: run it S(n) steps and see', 'Compute every function'], answer: 1, explain: 'If the machine has not halted after S(n) steps, it never will. That would decide a halting problem, which Part 6 shows is impossible. So S grows faster than every computable function.' } },
      { h: 'Many models, one class' },
      'Look back at this part: tapes, many tapes, nondeterminism, registers, two counters, μ-recursive functions, the λ-calculus, unrestricted grammars. Each was proved to compute exactly the same functions as the plain Turing machine. No one has ever found a reasonable model that computes more.',
      { topic: 'tm-church-turing', input: { f: 'add', a: '2, 3' }, frame: 12, caption: 'add(2, 3) computed five ways: by a Turing machine, a register machine, a counter machine, a μ-recursive definition and a λ-term. Different steps, the same answer.' },
      { def: 'Church–Turing thesis', text: 'every function that is effectively calculable, by any mechanical procedure a person could in principle follow, is computable by a Turing machine.' },
      'The thesis is not a theorem and cannot be one, because "effectively calculable" is an intuitive idea, not a definition. The equivalences of the models are theorems, and they are the evidence. In practice, the thesis is what lets us describe an algorithm in plain steps and know a Turing machine could carry it out.',
      { warn: 'The thesis is about what can be computed at all, not how fast. Nondeterminism, for example, adds no power, but may add an exponential amount of speed. Speed is the subject of Part 7.' },
      { list: ['S(n), the busy beaver step count, outgrows every computable function.', 'Every reasonable model computes the same functions.', 'The thesis links the intuitive idea of an algorithm to Turing machines; it is evidence, not proof.'] },
      { exercise: 'tur-x-bb2' },
      { exercise: 'tur-x-bb-ones' },
      { exercise: 'tur-x-ch-bb' },
      { exercise: 'tur-x-ch-thesis' },
      { exercise: 'tur-x-ch-models-equal' },
    ],
  });

  // ---- a guided tour -----------------------------------------------------------------------------------------
  C.tour({
    id: 'tur-tour', title: 'Tour: Turing machines', blurb: 'Where the tape, the rules and the variants are, and how to build and test your own machine.',
    steps: [
      { route: 'part=turing', text: 'Part 5 gathers the Turing machine, its variants, the other models of computation, recursive functions and λ, and the universal machine. Every card here is a family of topics you can run.' },
      { route: 'topic=tm-run', target: '#stageWrap', text: 'The stage shows the tape, with the head under one cell and the state above it, and the machine\'s diagram. The cell under the head is the only one the machine can see.' },
      { target: '#inputs', text: 'Change the tape here, or press Edit machine to draw your own rules. Presets give interesting inputs, including the edge cases.' },
      { target: '#btnPlay', text: 'Play runs the machine step by step; the timeline below lets you go back to any step. Every step is told in words, with the rule that fired.' },
      { target: '#btnDrawer', text: 'The definition shows the machine as a tuple and its δ as a table, with the rule in use lit up.' },
      { route: 'topic=tm-ksim', target: '#stageWrap', text: 'The variants are shown by simulation. Here one tape with four tracks runs a two-tape machine; the two step counters show the price.' },
      { route: 'sandbox', target: '#sbKinds', text: 'In the sandbox, choose Turing machine to build your own. Rules are typed as state, read -> next, write, move, with _ for the blank.', before: () => { const b = document.querySelector('#sbKinds [data-kind="tm"]'); if (b) b.click(); } },
      { target: '#sbRunCard', text: 'Run it on any input, and test it on a whole list of strings at once: a − in front of a string means it should be rejected.' },
      { route: 'learn', target: '[data-chapter="tur-machines"]', text: 'The lessons of Part 5 start here, and each ends with exercises. Machines you build are checked on every short input, with a step limit, so a machine that loops is caught.' },
    ],
  });

  // ---- a course --------------------------------------------------------------------------------------------------
  C.course({
    id: 'tur-course', title: 'Turing machines and other models', blurb: 'From one tape and a head to the universal machine: build machines, see why the variants are no stronger, meet the other models, and end at the Church–Turing thesis.',
    steps: [
      { topic: 'tm-run', note: 'Follow the head: it reads one cell, writes it, moves, and changes state.' },
      { lesson: 'tur-l-tape', note: 'The definition, and a first machine to run.' },
      { topic: 'tm-configs', note: 'Watch the state name slide through the configuration string as the head moves.' },
      { topic: 'tm-decide', note: 'Same language, two machines: one always halts, one spins on the strings it does not accept.' },
      { exercise: 'tur-x-bab', note: 'Build your first decider.' },
      { topic: 'tm-transducer', note: 'Read the tape at the end as the output: unary addition without any counting.' },
      { topic: 'tm-anbncn', note: 'Crossing off one a, one b and one c per round: the tape counts for you.' },
      { topic: 'tm-palindrome', note: 'The zig-zag: about n²/2 steps on one tape. Look at the cost table.' },
      { exercise: 'tur-x-equal-ab', note: 'Cross symbols off in pairs, in any order.' },
      { topic: 'tm-macro', note: 'Each statement becomes a state; count the plain rules it compiles to.' },
      { topic: 'tm-combine', note: 'Where does the first machine leave its head when it hands over?' },
      { topic: 'tm-multitape', note: 'Two tapes make the palindrome check linear.' },
      { topic: 'tm-ksim', note: 'One tape with tracks simulates two tapes; compare the two step counters.' },
      { topic: 'tm-oneway', note: 'Watch the head cross the fold onto the lower track.' },
      { topic: 'tm-2d', note: 'Moves up and down as well; every move is still local.' },
      { topic: 'tm-ntm-tree', note: 'One accepting branch is enough; the others may die or run for ever.' },
      { topic: 'tm-ntm-address', note: 'Addresses in shortlex order explore the tree breadth first.' },
      { topic: 'tm-enumerator', note: 'A machine that prints its language and never stops.' },
      { topic: 'tm-dovetail', note: 'Compare the zig-zag schedule with one string at a time: only one of them gets past a loop.' },
      { topic: 'ram-run', note: 'Reading a register destroys it: watch the spare register put r2 back.' },
      { topic: 'counter-run', note: 'Two counters: one holds the number, the other is scratch.' },
      { topic: 'lba-run', note: 'Fenced in by endmarkers: finitely many configurations, so loops are caught.' },
      { topic: 'ugrammar-derive', note: 'A B slides left through the c\'s: grammar rules moving information like a head.' },
      { topic: 'chomsky-map', note: 'Four circles, one inside the next; find the witness for each gap.' },
      { topic: 'primrec-tree', note: 'Recursion that counts down a known number of times.' },
      { topic: 'mu-search', note: 'Unbounded search: try div(5, 0) and see it never end.' },
      { topic: 'ackermann', note: 'A small input, a huge number of calls.' },
      { topic: 'lambda-reduce', note: 'Only substitution, yet SUCC 2 becomes 3. Try the Ω presets.' },
      { topic: 'tm-encode', note: 'Each rule becomes five runs of 0s; 11 between rules.' },
      { topic: 'tm-decode', note: 'Read a bit string back as a machine, or find why it is not one.' },
      { topic: 'utm-run', note: 'One fixed machine scanning another machine\'s rules.' },
      { topic: 'tm-busy-beaver', note: 'Tiny machines that run a long time before they halt.' },
      { topic: 'tm-church-turing', note: 'Five models, one answer.' },
      { lesson: 'tur-l-thesis', note: 'Why the thesis can be believed but not proved.' },
    ],
  });
})();
