// A library of our own Turing machines, each with a JavaScript oracle the tests check it against.
// kind: decider (oracle w -> bool), transducer (oracle w -> output, on inputs where domain(w) holds),
// beaver (blank tape; known steps and ones), nondet (oracle w -> bool), enumerator (first prints).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const lib = [];
  const def = (id, title, kind, alphabet, text, oracle, extra = {}) => lib.push(Object.assign({ id, title, kind, alphabet, text, oracle }, extra));
  const count = (w, c) => [...w].filter((x) => x === c).length;
  const val = (b) => (b ? parseInt(b, 2) : 0);

  // ---------- deciders ----------
  def('even-length', 'Even length', 'decider', ['a', 'b'], `
input: a b
q0, a|b -> q1, *, R
q1, a|b -> q0, *, R
q0, _ -> qa, _, S
q1, _ -> qr, _, S`, (w) => w.length % 2 === 0, { blurb: 'Two states remember the parity of what has been read.' });

  def('contains-11', 'Contains 11', 'decider', ['0', '1'], `
input: 0 1
q0, 0 -> q0, 0, R
q0, 1 -> q1, 1, R
q1, 0 -> q0, 0, R
q1, 1 -> qa, 1, R
q0, _ -> qr, _, S
q1, _ -> qr, _, S`, (w) => w.includes('11'), { blurb: 'A finite automaton in disguise: the head only moves right.' });

  def('div3', 'Binary multiple of 3', 'decider', ['0', '1'], `
input: 0 1
r0, 0 -> r0, 0, R
r0, 1 -> r1, 1, R
r1, 0 -> r2, 0, R
r1, 1 -> r0, 1, R
r2, 0 -> r1, 0, R
r2, 1 -> r2, 1, R
r0, _ -> qa, _, S
r1, _ -> qr, _, S
r2, _ -> qr, _, S`, (w) => val(w) % 3 === 0, { blurb: 'The state is the remainder so far; reading bit b sends r to (2r + b) mod 3. The empty string counts as 0.' });

  def('anbn', 'aⁿbⁿ', 'decider', ['a', 'b'], `
input: a b
q0, a -> q1, X, R
q0, Y -> q3, Y, R
q0, _ -> qa, _, S
q1, a|Y -> q1, *, R
q1, b -> q2, Y, L
q2, a|Y -> q2, *, L
q2, X -> q0, X, R
q3, Y -> q3, Y, R
q3, _ -> qa, _, S`, (w) => /^a*b*$/.test(w) && count(w, 'a') === count(w, 'b'), { blurb: 'Cross off an a, then the first b, and come back; finish when only crossed b\'s remain.' });

  def('anb2n', 'aⁿb²ⁿ', 'decider', ['a', 'b'], `
input: a b
q0, a -> q1, X, R
q0, Y -> q4, Y, R
q0, _ -> qa, _, S
q1, a|Y -> q1, *, R
q1, b -> q2, Y, R
q2, b -> q3, Y, L
q3, a|b|Y -> q3, *, L
q3, X -> q0, X, R
q4, Y -> q4, Y, R
q4, _ -> qa, _, S`, (w) => /^a*b*$/.test(w) && 2 * count(w, 'a') === count(w, 'b'), { blurb: 'Every a pays for two b\'s.' });

  def('anbncn', 'aⁿbⁿcⁿ', 'decider', ['a', 'b', 'c'], `
input: a b c
q0, a -> q1, X, R
q0, Y -> q4, Y, R
q0, _ -> qa, _, S
q1, a|Y -> q1, *, R
q1, b -> q2, Y, R
q2, b|Z -> q2, *, R
q2, c -> q3, Z, L
q3, a|b|Y|Z -> q3, *, L
q3, X -> q0, X, R
q4, Y -> q4, Y, R
q4, Z -> q5, Z, R
q5, Z -> q5, Z, R
q5, _ -> qa, _, S`, (w) => /^a*b*c*$/.test(w) && count(w, 'a') === count(w, 'b') && count(w, 'b') === count(w, 'c'), { blurb: 'One a, one b and one c are crossed off per round, so the counts must agree: not context-free, but easy for a TM.' });

  def('anbmcn', 'aⁿbᵐcⁿ', 'decider', ['a', 'b', 'c'], `
input: a b c
f0, a -> f0, a, R
f0, b -> f1, b, R
f0, c -> f2, c, R
f0, _ -> g, _, L
f1, b -> f1, b, R
f1, c -> f2, c, R
f1, _ -> g, _, L
f2, c -> f2, c, R
f2, _ -> g, _, L
g, a|b|c -> g, *, L
g, _ -> q0, _, R
q0, X -> q0, X, R
q0, a -> q1, X, R
q0, b|Z|_ -> q4, *, S
q1, a|b|Z -> q1, *, R
q1, c -> q2, Z, L
q2, a|b|Z -> q2, *, L
q2, X -> q0, X, R
q4, b|Z -> q4, *, R
q4, _ -> qa, _, S`, (w) => /^a*b*c*$/.test(w) && count(w, 'a') === count(w, 'c'), { blurb: 'First a pass checks the shape a*b*c*, then each a is matched with a c across the b\'s.' });

  def('palindrome', 'Palindromes', 'decider', ['a', 'b'], `
input: a b
q0, a -> pa, _, R
q0, b -> pb, _, R
q0, _ -> qa, _, S
pa, a|b -> pa, *, R
pa, _ -> ta, _, L
ta, a -> back, _, L
ta, _ -> qa, _, S
pb, a|b -> pb, *, R
pb, _ -> tb, _, L
tb, b -> back, _, L
tb, _ -> qa, _, S
back, a|b -> back, *, L
back, _ -> q0, _, R`, (w) => w === [...w].reverse().join(''), { blurb: 'Erase the first symbol, remember it in the state, and check the last symbol matches.' });

  def('ww', 'ww (a string twice)', 'decider', ['a', 'b'], `
input: a b
p0, _ -> qa, _, S
p0, a -> p1, A, R
p0, b -> p1, B, R
p0, A|B -> r0, *, L
p1, a|b -> p1, *, R
p1, _|A|B -> p2, *, L
p2, a -> p3, A, L
p2, b -> p3, B, L
p3, a|b -> p3, *, L
p3, A|B -> p0, *, R
r0, A -> r0, a, L
r0, B -> r0, b, L
r0, _ -> c0, _, R
c0, x -> c0, x, R
c0, a -> ca, x, R
c0, b -> cb, x, R
c0, y -> fin, y, R
ca, a|b|y -> ca, *, R
ca, A -> bk, y, L
cb, a|b|y -> cb, *, R
cb, B -> bk, y, L
bk, a|b|y -> bk, *, L
bk, x -> c0, x, R
fin, y -> fin, y, R
fin, _ -> qa, _, S`, (w) => w.length % 2 === 0 && w.slice(0, w.length / 2) === w.slice(w.length / 2), { blurb: 'Find the middle by marking from both ends in turn, then match the halves symbol by symbol.' });

  def('swap-halves', 'u#v with v the a↔b swap of u', 'decider', ['a', 'b', '#'], `
input: a b #
q0, a -> pa, x, R
q0, b -> pb, x, R
q0, # -> f0, #, R
pa, a|b -> pa, *, R
pa, # -> sa, #, R
sa, x -> sa, x, R
sa, b -> bk, x, L
pb, a|b -> pb, *, R
pb, # -> sb, #, R
sb, x -> sb, x, R
sb, a -> bk, x, L
bk, a|b|x -> bk, *, L
bk, # -> bl, #, L
bl, a|b -> bl, *, L
bl, x -> q0, x, R
f0, x -> f0, x, R
f0, _ -> qa, _, S`, (w) => { const p = w.split('#'); return p.length === 2 && p[1] === [...p[0]].map((c) => (c === 'a' ? 'b' : 'a')).join(''); }, { blurb: 'Zig-zag across the # comparing each symbol with its partner, which must be the other letter.' });

  def('brackets', 'Balanced brackets', 'decider', ['(', ')'], `
input: ( )
q0, (|X -> q0, *, R
q0, ) -> q1, X, L
q0, _ -> q2, _, L
q1, X -> q1, X, L
q1, ( -> q0, X, R
q1, _ -> qr, _, S
q2, X -> q2, X, L
q2, ( -> qr, (, S
q2, _ -> qa, _, S`, (w) => { let d = 0; for (const c of w) { d += c === '(' ? 1 : -1; if (d < 0) return false; } return d === 0; }, { blurb: 'Each ) is matched with the nearest open ( to its left; leftover brackets of either kind mean reject.' });

  def('equal-ab', 'As many a\'s as b\'s', 'decider', ['a', 'b'], `
input: a b
q0, X -> q0, X, R
q0, a -> q1, X, R
q0, b -> q2, X, R
q0, _ -> qa, _, S
q1, a|X -> q1, *, R
q1, b -> q3, X, L
q2, b|X -> q2, *, R
q2, a -> q3, X, L
q3, a|b|X -> q3, *, L
q3, _ -> q0, _, R`, (w) => count(w, 'a') === count(w, 'b'), { blurb: 'Cross off the first symbol and some partner of the other letter; an a without a partner b means reject.' });

  def('more-a', 'More a\'s than b\'s', 'decider', ['a', 'b'], `
input: a b
q0, X -> q0, X, R
q0, a -> q1, X, R
q0, b -> q2, X, R
q0, _ -> qr, _, S
q1, a|X -> q1, *, R
q1, b -> q3, X, L
q1, _ -> qa, _, S
q2, b|X -> q2, *, R
q2, a -> q3, X, L
q2, _ -> qr, _, S
q3, a|b|X -> q3, *, L
q3, _ -> q0, _, R`, (w) => count(w, 'a') > count(w, 'b'), { blurb: 'Pairs cancel; whichever letter finds no partner first is in the majority.' });

  def('unary-le', '1ᵐ#1ⁿ with m ≤ n', 'decider', ['1', '#'], `
input: 1 #
q0, x -> q0, x, R
q0, 1 -> q1, x, R
q0, # -> c0, #, R
q1, 1 -> q1, 1, R
q1, # -> q2, #, R
q2, y -> q2, y, R
q2, 1 -> q3, y, L
q3, y|#|1 -> q3, *, L
q3, x -> q0, x, R
c0, y|1 -> c0, *, R
c0, _ -> qa, _, S`, (w) => /^1*#1*$/.test(w) && w.indexOf('#') <= w.length - 1 - w.indexOf('#'), { blurb: 'Each 1 on the left needs a partner on the right.' });

  def('unary-sum', '1ˣ+1ʸ=1ᶻ with x + y = z', 'decider', ['1', '+', '='], `
input: 1 + =
f0, 1 -> f0, 1, R
f0, + -> f1, +, R
f1, 1 -> f1, 1, R
f1, = -> f2, =, R
f2, 1 -> f2, 1, R
f2, _ -> g0, _, L
g0, 1|+|= -> g0, *, L
g0, _ -> m0, _, R
m0, x|+ -> m0, *, R
m0, 1 -> m1, x, R
m0, = -> c0, =, R
m1, 1|+ -> m1, *, R
m1, = -> m2, =, R
m2, y -> m2, y, R
m2, 1 -> m3, y, L
m3, 1|+|=|x|y -> m3, *, L
m3, _ -> m0, _, R
c0, y -> c0, y, R
c0, _ -> qa, _, S`, (w) => { const m = /^(1*)\+(1*)=(1*)$/.exec(w); return !!m && m[1].length + m[2].length === m[3].length; }, { blurb: 'Check the shape, then match every 1 before the = with one after it.' });

  // binary x#y (same length), accept when x < y; three copies of the states remember equal / less / greater so far
  const ltText = (() => {
    const L = ['input: 0 1 #'];
    for (const m of ['e', 'l', 'g']) {
      L.push(`a${m}, X -> a${m}, X, R`, `a${m}, 0 -> c0${m}, X, R`, `a${m}, 1 -> c1${m}, X, R`, `a${m}, # -> z${m}, #, R`);
      for (const b of ['0', '1']) {
        L.push(`c${b}${m}, 0|1 -> c${b}${m}, *, R`, `c${b}${m}, # -> d${b}${m}, #, R`, `d${b}${m}, X -> d${b}${m}, X, R`);
        for (const c of ['0', '1']) { const n = m !== 'e' ? m : b < c ? 'l' : b > c ? 'g' : 'e'; L.push(`d${b}${m}, ${c} -> b${n}, X, L`); }
      }
      L.push(`b${m}, X|0|1|# -> b${m}, *, L`, `b${m}, _ -> a${m}, _, R`, `z${m}, X -> z${m}, X, R`, `z${m}, _ -> ${m === 'l' ? 'qa' : 'qr'}, _, S`);
    }
    return 'start: ae\n' + L.join('\n');
  })();
  def('bin-less', 'Binary x#y with x < y', 'decider', ['0', '1', '#'], ltText, (w) => { const m = /^([01]*)#([01]*)$/.exec(w); return !!m && m[1].length === m[2].length && val(m[1]) < val(m[2]); }, { blurb: 'Compare bit by bit from the left; the first difference decides, and the lengths must agree.' });

  def('anbn-oneway', 'aⁿbⁿ on a one-way tape', 'decider', ['a', 'b'], `
mode: oneway
input: a b
q0, X -> q0, X, R
q0, a -> q1, X, R
q0, Y -> q3, Y, R
q0, _ -> qa, _, S
q1, a|Y -> q1, *, R
q1, b -> q2, Y, L
q2, a|X|Y -> q2, *, L
q2, > -> q0, >, R
q3, Y -> q3, Y, R
q3, _ -> qa, _, S`, (w) => /^a*b*$/.test(w) && count(w, 'a') === count(w, 'b'), { blurb: 'The tape ends on the left at the marker >, which the machine uses to find its way home.' });

  def('anbncn-lba', 'aⁿbⁿcⁿ as a linear-bounded automaton', 'decider', ['a', 'b', 'c'], `
mode: lba
input: a b c
q0, a -> q1, X, R
q0, Y -> q4, Y, R
q0, > -> qa, >, S
q1, a|Y -> q1, *, R
q1, b -> q2, Y, R
q2, b|Z -> q2, *, R
q2, c -> q3, Z, L
q3, a|b|Y|Z -> q3, *, L
q3, X -> q0, X, R
q4, Y -> q4, Y, R
q4, Z -> q5, Z, R
q5, Z -> q5, Z, R
q5, > -> qa, >, S`, (w) => /^a*b*c*$/.test(w) && count(w, 'a') === count(w, 'b') && count(w, 'b') === count(w, 'c'), { blurb: 'The input sits between < and >, and the machine never leaves that space.' });

  def('aa-recogniser', 'Contains aa (a recogniser that loops otherwise)', 'recogniser', ['a', 'b'], `
input: a b
q0, a -> q1, a, R
q0, b -> q0, b, R
q1, a -> qa, a, S
q1, b -> q0, b, R
q0, _ -> q0, _, S
q1, _ -> q1, _, S`, (w) => w.includes('aa'), { blurb: 'Accepts its members; on any other string it stops moving and spins forever instead of rejecting.' });

  // ---------- transducers ----------
  def('unary-inc', 'Unary successor', 'transducer', ['1'], `
output: tape
input: 1
q0, 1 -> q0, 1, R
q0, _ -> halt, 1, S`, (w) => w + '1');

  def('bin-inc', 'Binary increment', 'transducer', ['0', '1'], `
output: tape
input: 0 1
q0, 0|1 -> q0, *, R
q0, _ -> q1, _, L
q1, 1 -> q1, 0, L
q1, 0|_ -> halt, 1, S`, (w) => { const n = val(w) + 1; const s = n.toString(2); return s.length > w.length ? s : s.padStart(w.length, '0'); }, { blurb: 'Carry from the right: 1s turn to 0s until a 0 (or the blank) takes the 1. The width is kept.' });

  def('bin-dec', 'Binary decrement (0 stays 0)', 'transducer', ['0', '1'], `
output: tape
input: 0 1
q0, 0 -> q0, 0, R
q0, 1 -> q1, 1, R
q0, _ -> halt, _, S
q1, 0|1 -> q1, *, R
q1, _ -> q2, _, L
q2, 0 -> q2, 1, L
q2, 1 -> halt, 0, S`, (w) => { const n = val(w); return n === 0 ? w : (n - 1).toString(2).padStart(w.length, '0'); }, { blurb: 'First make sure there is a 1 to borrow from, then borrow from the right.' });

  def('unary-add', 'Unary addition', 'transducer', ['1', '+'], `
output: tape
input: 1 +
q0, 1 -> q0, 1, R
q0, + -> q1, 1, R
q1, 1 -> q1, 1, R
q1, _ -> q2, _, L
q2, 1 -> halt, _, S`, (w) => '1'.repeat(w.length - 1), { domain: (w) => /^1*\+1*$/.test(w), blurb: 'Fill the + with a 1 and erase one 1 at the end.' });

  def('unary-monus', 'Unary subtraction (stops at 0)', 'transducer', ['1', '-'], `
output: tape
input: 1 -
q0, 1|- -> q0, *, R
q0, _ -> q1, _, L
q1, 1 -> q2, _, L
q1, - -> halt, _, S
q2, 1|- -> q2, *, L
q2, _ -> q3, _, R
q3, 1 -> q0, _, R
q3, - -> q4, _, R
q4, 1 -> q4, _, R
q4, _ -> halt, _, S`, (w) => { const [a, b] = w.split('-'); return '1'.repeat(Math.max(0, a.length - b.length)); }, { domain: (w) => /^1*-1*$/.test(w), blurb: 'Erase a 1 from each end in turn until one side runs out.' });

  def('unary-mul', 'Unary multiplication', 'transducer', ['1', '*'], `
output: tape
input: 1 *
s0, 1|* -> s0, *, R
s0, _ -> s1, =, L
s1, 1|* -> s1, *, L
s1, _ -> a0, _, R
a0, x -> a0, x, R
a0, 1 -> a1, x, R
a0, * -> e1, _, L
a1, 1 -> a1, 1, R
a1, * -> b0, *, R
b0, y -> b0, y, R
b0, 1 -> b1, y, R
b0, = -> r0, =, L
b1, 1|= -> b1, *, R
b1, _ -> b2, 1, L
b2, 1|= -> b2, *, L
b2, y -> b0, y, R
r0, y -> r0, 1, L
r0, * -> r1, *, L
r1, 1|x -> r1, *, L
r1, _ -> a0, _, R
e1, x -> e1, _, L
e1, _ -> e2, _, R
e2, _|1 -> e2, _, R
e2, = -> halt, _, R`, (w) => { const [a, b] = w.split('*'); return '1'.repeat(a.length * b.length); }, { domain: (w) => /^1*\*1*$/.test(w), blurb: 'For every 1 of the first factor, copy the second factor to the end; then clear away the factors.' });

  def('unary-double', 'Unary doubling', 'transducer', ['1'], `
output: tape
input: 1
q0, x -> q0, x, R
q0, 1 -> q1, x, R
q0, y|_ -> q3, *, L
q1, 1|y -> q1, *, R
q1, _ -> q2, y, L
q2, 1|y -> q2, *, L
q2, x -> q0, x, R
q3, x|y -> q3, *, L
q3, _ -> q4, _, R
q4, x|y -> q4, 1, R
q4, _ -> halt, _, S`, (w) => w + w);

  def('unary-half', 'Unary halving (rounded down)', 'transducer', ['1'], `
output: tape
input: 1
q0, 1 -> q1, _, R
q0, x|_ -> q4, *, S
q1, 1 -> q2, _, R
q1, x|_ -> q4, *, S
q2, 1|x -> q2, *, R
q2, _ -> q3, x, L
q3, 1|x -> q3, *, L
q3, _ -> q0, _, R
q4, x -> q4, 1, R
q4, _ -> halt, _, S`, (w) => '1'.repeat(w.length >> 1));

  def('unary-mod3', 'Unary remainder mod 3', 'transducer', ['1'], `
output: tape
input: 1
q0, 1 -> q1, _, R
q1, 1 -> q2, _, R
q2, 1 -> q0, _, R
q0, _ -> halt, _, S
q1, _ -> halt, 1, S
q2, _ -> w1, 1, L
w1, _ -> halt, 1, S`, (w) => '1'.repeat(w.length % 3));

  def('bin-add', 'Binary addition by counting down', 'transducer', ['0', '1', '+'], `
output: tape
input: 0 1 +
s0, 0|1 -> s0, *, R
s0, + -> z0, +, R
z0, 0 -> z0, 0, R
z0, 1 -> z1, 1, R
z0, _ -> c0, _, L
z1, 0|1 -> z1, *, R
z1, _ -> d0, _, L
d0, 0 -> d0, 1, L
d0, 1 -> i0, 0, L
i0, 0|1 -> i0, *, L
i0, + -> i1, +, L
i1, 1 -> i1, 0, L
i1, 0|_ -> r0, 1, R
r0, 0|1 -> r0, *, R
r0, + -> z0, +, R
c0, 0 -> c0, _, L
c0, + -> halt, _, L`, (w) => {
    const [x, y] = w.split('+');
    if (val(y) === 0) return x;
    const s = (val(x) + val(y)).toString(2);
    return s.length >= x.length ? s : s.padStart(x.length, '0');
  }, { domain: (w) => /^[01]*\+[01]*$/.test(w), maxSteps: 200000, blurb: 'While y is not zero: take 1 from y and add 1 to x. Slow (exponential in the length of y) but simple.' });

  def('copy', 'Copy: w to w#w', 'transducer', ['a', 'b'], `
output: tape
input: a b
s0, a|b -> s0, *, R
s0, _ -> s1, #, L
s1, a|b -> s1, *, L
s1, _ -> m0, _, R
m0, A|B -> m0, *, R
m0, a -> ma, A, R
m0, b -> mb, B, R
m0, # -> f0, #, L
ma, a|b|# -> ma, *, R
ma, _ -> back, a, L
mb, a|b|# -> mb, *, R
mb, _ -> back, b, L
back, a|b|# -> back, *, L
back, A|B -> m0, *, R
f0, A -> f0, a, L
f0, B -> f0, b, L
f0, _ -> halt, _, R`, (w) => w + '#' + w, { blurb: 'Mark a symbol, carry it in the state to the end, write it, come back for the next.' });

  def('reverse', 'Reverse', 'transducer', ['a', 'b'], `
output: tape
input: a b
s0, a|b -> s0, *, R
s0, _ -> s1, #, L
s1, A|B -> s1, *, L
s1, a -> ta, A, R
s1, b -> tb, B, R
s1, _ -> e0, _, R
ta, A|B|#|a|b -> ta, *, R
ta, _ -> u0, a, L
tb, A|B|#|a|b -> tb, *, R
tb, _ -> u0, b, L
u0, a|b -> u0, *, L
u0, # -> s1, #, L
e0, A|B -> e0, _, R
e0, # -> halt, _, R`, (w) => [...w].reverse().join(''), { blurb: 'Take symbols from the right end of w and append them after a #, then erase w.' });

  def('bin-to-unary', 'Binary to unary', 'transducer', ['0', '1'], `
output: tape
input: 0 1
s0, 0|1 -> s0, *, R
s0, _ -> k0, #, L
k0, 0 -> k0, 0, L
k0, 1 -> k1, 1, R
k0, _ -> c0, _, R
k1, 0|1 -> k1, *, R
k1, # -> d0, #, L
d0, 0 -> d0, 1, L
d0, 1 -> a0, 0, R
a0, 0|1|# -> a0, *, R
a0, _ -> b0, 1, L
b0, 1 -> b0, 1, L
b0, # -> k0, #, L
c0, 0 -> c0, _, R
c0, # -> halt, _, R`, (w) => '1'.repeat(val(w)), { maxSteps: 100000, blurb: 'Count down in binary, adding a 1 on the right each time.' });

  def('unary-to-bin', 'Unary to binary', 'transducer', ['1'], `
output: tape
input: 1
s0, 1|_ -> s1, *, L
s1, _ -> s2, #, L
s2, _ -> s3, 0, R
s3, # -> e0, #, R
e0, 1 -> e0, 1, R
e0, _ -> e1, _, L
e1, 1 -> g0, _, L
e1, # -> halt, _, L
g0, 1 -> g0, 1, L
g0, # -> i0, #, L
i0, 1 -> i0, 0, L
i0, 0|_ -> j0, 1, R
j0, 0|1 -> j0, *, R
j0, # -> e0, #, R`, (w) => w.length.toString(2), { blurb: 'A binary counter grows to the left while the 1s are used up on the right.' });

  def('sort-bits', 'Sort a binary string', 'transducer', ['0', '1'], `
output: tape
input: 0 1
q0, 0 -> q0, 0, R
q0, 1 -> q1, 1, R
q0, _ -> halt, _, L
q1, 1 -> q1, 1, R
q1, 0 -> q2, 1, L
q1, _ -> halt, _, L
q2, 1 -> q3, 0, L
q3, 0|1 -> q3, *, L
q3, _ -> q0, _, R`, (w) => [...w].sort().join(''), { blurb: 'Find a 1 followed by a 0, swap them, start again: bubble sort on a tape.' });

  def('complement', 'Flip every bit', 'transducer', ['0', '1'], `
output: tape
input: 0 1
q0, 0 -> q0, 1, R
q0, 1 -> q0, 0, R
q0, _ -> halt, _, S`, (w) => [...w].map((c) => (c === '0' ? '1' : '0')).join(''));

  def('unary-max', 'Maximum of two unary numbers', 'transducer', ['1', '#'], `
output: tape
input: 1 #
p0, x -> p0, x, R
p0, 1 -> p1, x, R
p0, # -> L0, #, R
p1, 1 -> p1, 1, R
p1, # -> p2, #, R
p2, y -> p2, y, R
p2, 1 -> p3, y, L
p2, _ -> R0, _, L
p3, y|#|1|x -> p3, *, L
p3, _ -> p0, _, R
L0, y|1 -> L0, 1, R
L0, _ -> L1, _, L
L1, 1 -> L1, 1, L
L1, # -> L2, _, L
L2, x -> L2, _, L
L2, _ -> halt, _, R
R0, y -> R0, _, L
R0, # -> R1, _, L
R1, x|1 -> R1, 1, L
R1, _ -> halt, _, R`, (w) => { const [a, b] = w.split('#'); return '1'.repeat(Math.max(a.length, b.length)); }, { domain: (w) => /^1*#1*$/.test(w), blurb: 'Pair off 1s; the side that still has 1s when the other runs out is the larger, and it is kept.' });

  def('unary-compare', 'Compare two unary numbers', 'transducer', ['1', '#'], `
output: tape
input: 1 #
tape: < = >
q0, 1 -> q1, _, R
q0, # -> c0, _, R
q1, 1|# -> q1, *, R
q1, _ -> q2, _, L
q2, 1 -> q3, _, L
q2, # -> g0, _, L
g0, 1 -> g0, _, L
g0, _ -> halt, >, S
q3, 1|# -> q3, *, L
q3, _ -> q0, _, R
c0, 1 -> c1, _, R
c0, _ -> halt, =, S
c1, 1 -> c1, _, R
c1, _ -> halt, <, S`, (w) => { const [a, b] = w.split('#'); return a.length < b.length ? '<' : a.length > b.length ? '>' : '='; }, { domain: (w) => /^1*#1*$/.test(w), blurb: 'Erase a 1 from each end until a side runs out, then write the verdict.' });

  def('drop-a', 'Delete every a', 'transducer', ['a', 'b'], `
output: tape
input: a b
s0, a|b -> s0, *, R
s0, _ -> s1, #, L
s1, a|b -> s1, *, L
s1, _ -> m0, _, R
m0, a -> m0, _, R
m0, b -> mb, _, R
m0, # -> halt, _, R
mb, a|b|# -> mb, *, R
mb, _ -> bk, b, L
bk, a|b|# -> bk, *, L
bk, _ -> m0, _, R`, (w) => w.replace(/a/g, ''), { blurb: 'Erase the input from the left, writing each b again after a #.' });

  // ---------- busy beavers (blank tape 0, ones count) ----------
  def('bb2', 'Busy beaver, 2 states', 'beaver', ['1'], `
blank: 0
input: 1
start: A
halt: H
A, 0 -> B, 1, R
A, 1 -> B, 1, L
B, 0 -> A, 1, L
B, 1 -> H, 1, R`, null, { steps: 6, ones: 4, blurb: 'The most ones (4) and the most steps (6) any halting 2-state, 2-symbol machine can manage.' });

  def('bb3', 'Busy beaver, 3 states (most steps)', 'beaver', ['1'], `
blank: 0
input: 1
start: A
halt: H
A, 0 -> B, 1, R
A, 1 -> H, 1, L
B, 0 -> B, 1, L
B, 1 -> C, 0, R
C, 0 -> C, 1, L
C, 1 -> A, 1, L`, null, { steps: 21, ones: 5, blurb: '21 steps is the most for any halting 3-state, 2-symbol machine; the most ones any such machine leaves is 6.' });

  def('bb3-ones', 'Busy beaver, 3 states (most ones)', 'beaver', ['1'], `
blank: 0
input: 1
start: A
halt: H
A, 0 -> B, 1, R
A, 1 -> C, 1, L
B, 0 -> A, 1, L
B, 1 -> B, 1, R
C, 0 -> B, 1, L
C, 1 -> H, 1, L`, null, { steps: 13, ones: 6, blurb: 'Leaves 6 ones, the most for 3 states.' });

  def('bb4', 'Busy beaver, 4 states', 'beaver', ['1'], `
blank: 0
input: 1
start: A
halt: H
A, 0 -> B, 1, R
A, 1 -> B, 1, L
B, 0 -> A, 1, L
B, 1 -> C, 0, L
C, 0 -> H, 1, R
C, 1 -> D, 1, L
D, 0 -> D, 1, R
D, 1 -> A, 0, R`, null, { steps: 107, ones: 13, blurb: 'The 4-state champion: 107 steps and 13 ones, both the maximum for 4 states.' });

  // ---------- k tapes, several heads, 2-D ----------
  def('pal-2tape', 'Palindromes with two tapes', 'decider', ['a', 'b'], `
tapes: 2
input: a b
q0, a, _ -> q0, a, a, R, R
q0, b, _ -> q0, b, b, R, R
q0, _, _ -> q1, _, _, L, L
q1, a|b, * -> q1, *, *, L, S
q1, _, * -> q2, _, *, R, S
q2, a, a -> q2, a, a, R, L
q2, b, b -> q2, b, b, R, L
q2, _, * -> qa, _, *, S, S`, (w) => w === [...w].reverse().join(''), { blurb: 'Copy, rewind one head, then read forwards and backwards at once: linear time.' });

  def('anbncn-2tape', 'aⁿbⁿcⁿ with two tapes', 'decider', ['a', 'b', 'c'], `
tapes: 2
input: a b c
s, _, _ -> qa, _, _, S, S
s, a, _ -> q0, a, _, S, S
q0, a, _ -> q0, a, x, R, R
q0, b, _ -> q1, b, _, S, L
q1, b, x -> q1, b, x, R, L
q1, c, _ -> q2, c, _, S, R
q2, c, x -> q2, c, x, R, R
q2, _, _ -> qa, _, _, S, S`, (w) => /^a*b*c*$/.test(w) && count(w, 'a') === count(w, 'b') && count(w, 'b') === count(w, 'c'), { blurb: 'Count the a\'s on tape 2, count down with the b\'s, count up again with the c\'s.' });

  def('copy-2tape', 'Copy w to ww with two tapes', 'transducer', ['a', 'b'], `
tapes: 2
output: tape
input: a b
q0, a, _ -> q0, a, a, R, R
q0, b, _ -> q0, b, b, R, R
q0, _, _ -> q1, _, _, S, L
q1, _, a|b -> q1, _, *, S, L
q1, _, _ -> q2, _, _, S, R
q2, _, a -> q2, a, a, R, R
q2, _, b -> q2, b, b, R, R
q2, _, _ -> halt, _, _, S, S`, (w) => w + w);

  const addText = (() => {
    const L = ['tapes: 3', 'output: tape 3', 'input: 0 1 +', 's0, 0|1, *, * -> s0, *, *, *, R, S, S', 's0, +, *, * -> s1, +, *, *, R, S, S',
      's1, 0, _, * -> s1, _, 0, *, R, R, S', 's1, 1, _, * -> s1, _, 1, *, R, R, S', 's1, _, _, * -> s2, _, _, *, L, L, S',
      's2, _, *, * -> s2, _, *, *, L, S, S', 's2, +, *, * -> c0, _, *, *, L, S, S'];
    const B = ['0', '1', '_'], v = (s) => (s === '1' ? 1 : 0);
    for (const c of [0, 1]) for (const a of B) for (const b of B) {
      if (a === '_' && b === '_') { L.push(`c${c}, _, _, _ -> halt, _, _, ${c ? '1' : '_'}, S, S, S`); continue; }
      const s = v(a) + v(b) + c;
      L.push(`c${c}, ${a}, ${b}, _ -> c${s >> 1}, ${a}, ${b}, ${s & 1}, L, L, L`);
    }
    return L.join('\n');
  })();
  def('bin-add-3tape', 'Binary addition with three tapes', 'transducer', ['0', '1', '+'], addText, (w) => {
    const [x, y] = w.split('+'), wd = Math.max(x.length, y.length);
    if (!wd) return '';
    const s = (val(x) + val(y)).toString(2);
    return s.length >= wd ? s : s.padStart(wd, '0');
  }, { domain: (w) => /^[01]*\+[01]*$/.test(w), blurb: 'Move y to tape 2, then add right to left with a carry, writing the sum on tape 3.' });

  def('pal-2head', 'Palindromes with two heads on one tape', 'decider', ['a', 'b'], `
heads: 2
input: a b
q0, *, a|b -> q0, *, *, S, R
q0, *, _ -> q1, *, _, S, L
q1, a, a -> q1, a, a, R, L
q1, b, b -> q1, b, b, R, L
q1, _, _ -> qa, _, _, S, S`, (w) => w === [...w].reverse().join(''), { blurb: 'One head runs to the end; then the heads walk towards each other comparing.' });

  def('copy-down-2d', 'Copy row 0 into row 1 (2-D tape)', 'grid', ['a', 'b'], `
mode: 2d
input: a b
q0, a -> pa, a, D
q0, b -> pb, b, D
pa, _ -> up, a, U
pb, _ -> up, b, U
up, a|b -> q0, *, R
q0, _ -> halt, _, S`, null, { blurb: 'Each symbol is carried one row down.' });

  def('ant-2d', 'Langton\'s ant (2-D tape)', 'grid', ['#'], `
mode: 2d
input: #
N, _ -> E, #, R
N, # -> W, _, L
E, _ -> S, #, D
E, # -> N, _, U
S, _ -> W, #, L
S, # -> E, _, R
W, _ -> N, #, U
W, # -> S, _, D`, null, { blurb: 'The state is the heading: on white turn right, on black turn left, flipping the cell. It never halts.' });

  // ---------- nondeterministic ----------
  def('ntm-repeat', 'Some letter occurs twice (guess where)', 'nondet', ['a', 'b', 'c'], `
nondet: yes
input: a b c
q0, a|b|c -> q0, *, R
q0, a -> pa, a, R
q0, b -> pb, b, R
q0, c -> pc, c, R
pa, a|b|c -> pa, *, R
pa, a -> qa, a, S
pb, a|b|c -> pb, *, R
pb, b -> qa, b, S
pc, a|b|c -> pc, *, R
pc, c -> qa, c, S`, (w) => new Set(w).size < w.length, { blurb: 'Guess the first occurrence, remember its letter, guess the second.' });

  def('ntm-ww', 'ww by guessing the middle', 'nondet', ['a', 'b'], `
nondet: yes
input: a b
s, _ -> qa, _, S
s, a|b -> g, *, S
g, a|b -> g, *, R
g, a -> u, A, R
g, b -> u, B, R
u, a -> u, A, R
u, b -> u, B, R
u, _ -> r1, _, L
r1, a|b|A|B -> r1, *, L
r1, _ -> c0, _, R
c0, x -> c0, x, R
c0, a -> ca, x, R
c0, b -> cb, x, R
c0, y -> fin, y, R
ca, a|b|y -> ca, *, R
ca, A -> bk, y, L
cb, a|b|y -> cb, *, R
cb, B -> bk, y, L
bk, a|b|y -> bk, *, L
bk, x -> c0, x, R
fin, y -> fin, y, R
fin, _ -> qa, _, S`, (w) => w.length % 2 === 0 && w.slice(0, w.length / 2) === w.slice(w.length / 2), { blurb: 'Guess where the second half starts, upper-case it, then check the halves agree.' });

  def('ntm-substring', 'x#y with x a substring of y (two tapes, guess the start)', 'nondet', ['a', 'b', '#'], `
nondet: yes
tapes: 2
input: a b #
c0, a, _ -> c0, a, a, R, R
c0, b, _ -> c0, b, b, R, R
c0, #, _ -> c1, #, _, R, L
c1, *, a|b -> c1, *, *, S, L
c1, *, _ -> g, *, _, S, R
g, a|b|#, * -> g, *, *, R, S
g, *, * -> m, *, *, S, S
m, a, a -> m, a, a, R, R
m, b, b -> m, b, b, R, R
m, *, _ -> qa, *, _, S, S`, (w) => { const i = w.indexOf('#'); return i >= 0 && w.slice(i + 1).includes(w.slice(0, i)); }, { blurb: 'Copy x to tape 2, then guess where in y it begins and compare.' });

  // ---------- enumerators ----------
  def('enum-even-a', 'Enumerator: even numbers of a\'s', 'enumerator', ['a'], `
print: pr
start: pr
input: a
pr, _ -> w1, a, R
w1, _ -> pr, a, R`, null, { prints: (i) => 'a'.repeat(2 * i), blurb: 'Print, add two a\'s, print again, forever.' });

  def('enum-binary', 'Enumerator: every binary string in shortlex order', 'enumerator', ['0', '1'], `
print: pr
start: pr
input: 0 1
pr, 0|1 -> pr, *, R
pr, _ -> c, _, L
c, 1 -> c, 0, L
c, 0 -> b, 1, L
c, _ -> b, 0, L
b, 0|1 -> b, *, L
b, _ -> pr, _, R`, null, { prints: (i) => T.tm.strings(['0', '1'], 12)[i], blurb: 'The shortlex successor: from the right, 1s become 0s until a 0 becomes 1, or the string grows.' });

  // compile lazily so one bad entry cannot stop the page
  const cache = new Map();
  function get(id) {
    if (!cache.has(id)) { const e = lib.find((x) => x.id === id); if (!e) throw new Error('no library machine ' + id); cache.set(id, T.tm.compile(e.text, { name: id })); }
    return cache.get(id);
  }
  T.tmLib = { list: lib, get, entry: (id) => lib.find((x) => x.id === id) };
})();
