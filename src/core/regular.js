// Around regular languages: the pumping-lemma game with a catalogue of languages, Moore and Mealy
// machines, two-way DFAs, KMP pattern search as a DFA, and a lexer generator. Each returns its result
// with a trace of { kind, say, ...data } steps.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const FA = T.FA, RE = T.RE;
  const chars = (w) => Array.from(w);
  const showW = (w) => (w === '' ? 'ε' : w);
  const count = (w, c) => { let n = 0; for (const x of w) if (x === c) n++; return n; };
  const rep = (s, n) => s.repeat(Math.max(0, n));
  const isPrime = (n) => { if (n < 2) return false; for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; };
  const nextPrime = (n) => { while (!isPrime(n)) n++; return n; };
  const fact = (n) => (n <= 1 ? 1 : n * fact(n - 1));
  // a^i b^j c^k ... in this exact block order: returns the counts, or null if the shape is wrong
  const blocks = (w, letters) => {
    const m = w.match(new RegExp('^' + letters.map((c) => `(${c}*)`).join('') + '$'));
    return m ? m.slice(1).map((x) => x.length) : null;
  };

  // ---------------------------------------------------------------- the catalogue

  // Our own languages for the pumping game and the distinguisher game. Non-regular entries carry a
  // winning string for the student (witness(p)); regular ones carry a regex or DFA text from which
  // the adversary's pumping length comes.
  const L = [
    // non-regular
    { id: 'anbn', name: 'aⁿbⁿ', desc: 'some a\'s followed by the same number of b\'s', alphabet: ['a', 'b'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b']); return !!b && b[0] === b[1]; }, witness: (p) => rep('a', p) + rep('b', p),
      hint: 'Take aᵖbᵖ: y lies inside the a\'s, so pumping changes only the a\'s.' },
    { id: 'equal-ab', name: '#a = #b', desc: 'as many a\'s as b\'s, in any order', alphabet: ['a', 'b'], regular: false,
      member: (w) => count(w, 'a') === count(w, 'b'), witness: (p) => rep('a', p) + rep('b', p),
      hint: 'aᵖbᵖ again: y is all a\'s, and i = 2 adds a\'s only.' },
    { id: 'pal', name: 'palindromes', desc: 'strings over {a, b} that read the same backwards', alphabet: ['a', 'b'], regular: false,
      member: (w) => w === chars(w).reverse().join(''), witness: (p) => rep('a', p) + 'b' + rep('a', p),
      hint: 'aᵖbaᵖ: pumping changes the a\'s before the b only.' },
    { id: 'ww', name: 'ww', desc: 'a string written twice', alphabet: ['a', 'b'], regular: false,
      member: (w) => w.length % 2 === 0 && w.slice(0, w.length / 2) === w.slice(w.length / 2), witness: (p) => rep('a', p) + 'b' + rep('a', p) + 'b',
      hint: 'aᵖbaᵖb: pump down (i = 0) and the halves no longer match.' },
    { id: 'square', name: 'a^(n²)', desc: 'a\'s, and their number is a perfect square', alphabet: ['a'], regular: false,
      member: (w) => /^a*$/.test(w) && Number.isInteger(Math.sqrt(w.length)), witness: (p) => rep('a', p * p),
      hint: 'a^(p²) and i = 2: the length lands strictly between p² and (p+1)².' },
    { id: 'prime', name: 'a^prime', desc: 'a\'s, and their number is prime', alphabet: ['a'], regular: false,
      member: (w) => /^a*$/.test(w) && isPrime(w.length), witness: (p) => rep('a', nextPrime(p + 2)),
      hint: 'aᵠ for a prime q ≥ p + 2, and i = q + 1: the length becomes q(1 + |y|).' },
    { id: 'pow2', name: 'a^(2ⁿ)', desc: 'a\'s, and their number is a power of two', alphabet: ['a'], regular: false,
      member: (w) => /^a*$/.test(w) && w.length > 0 && (w.length & (w.length - 1)) === 0, witness: (p) => { let n = 1; while (n < p) n *= 2; return rep('a', n); },
      hint: 'The first power of two 2ᵏ ≥ p, and i = 2: the length lands between 2ᵏ and 2ᵏ⁺¹.' },
    { id: 'a-lt-b', name: 'aⁿbᵐ, n < m', desc: 'a\'s then b\'s, fewer a\'s than b\'s', alphabet: ['a', 'b'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b']); return !!b && b[0] < b[1]; }, witness: (p) => rep('a', p) + rep('b', p + 1),
      hint: 'aᵖbᵖ⁺¹ and pump up (i = 2).' },
    { id: 'a-gt-b', name: 'aⁿbᵐ, n > m', desc: 'a\'s then b\'s, more a\'s than b\'s', alphabet: ['a', 'b'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b']); return !!b && b[0] > b[1]; }, witness: (p) => rep('a', p + 1) + rep('b', p),
      hint: 'aᵖ⁺¹bᵖ and pump down (i = 0).' },
    { id: 'a-le-b', name: 'aⁿbᵐ, n ≤ m', desc: 'a\'s then b\'s, no more a\'s than b\'s', alphabet: ['a', 'b'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b']); return !!b && b[0] <= b[1]; }, witness: (p) => rep('a', p) + rep('b', p),
      hint: 'aᵖbᵖ and pump up.' },
    { id: 'a-ne-b', name: 'aⁿbᵐ, n ≠ m', desc: 'a\'s then b\'s, unequal numbers', alphabet: ['a', 'b'], regular: false, maxP: 5,
      member: (w) => { const b = blocks(w, ['a', 'b']); return !!b && b[0] !== b[1]; }, witness: (p) => rep('a', p) + rep('b', p + fact(p)),
      hint: 'aᵖbᵖ⁺ᵖ! : whatever |y| = k ≤ p is, pumping i = p!/k + 1 times makes the counts equal. (Closure is quicker: complement and intersect with a*b*.)' },
    { id: 'parens', name: 'balanced ( )', desc: 'well-nested parentheses', alphabet: ['(', ')'], regular: false,
      member: (w) => { let d = 0; for (const c of w) { d += c === '(' ? 1 : -1; if (d < 0) return false; } return d === 0; }, witness: (p) => rep('(', p) + rep(')', p),
      hint: '(ᵖ)ᵖ: y is all opening brackets.' },
    { id: 'anbncn', name: 'aⁿbⁿcⁿ', desc: 'equal blocks of a\'s, b\'s and c\'s', alphabet: ['a', 'b', 'c'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b', 'c']); return !!b && b[0] === b[1] && b[1] === b[2]; }, witness: (p) => rep('a', p) + rep('b', p) + rep('c', p),
      hint: 'aᵖbᵖcᵖ: only the a\'s change.' },
    { id: 'anb2n', name: 'aⁿb²ⁿ', desc: 'a\'s then twice as many b\'s', alphabet: ['a', 'b'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b']); return !!b && 2 * b[0] === b[1]; }, witness: (p) => rep('a', p) + rep('b', 2 * p),
      hint: 'aᵖb²ᵖ and any i ≠ 1.' },
    { id: 'more-a', name: '#a > #b', desc: 'more a\'s than b\'s, in any order', alphabet: ['a', 'b'], regular: false,
      member: (w) => count(w, 'a') > count(w, 'b'), witness: (p) => rep('b', p) + rep('a', p + 1),
      hint: 'bᵖaᵖ⁺¹: y is all b\'s, so pump up.' },
    { id: 'anban', name: 'aⁿbaⁿ', desc: 'a single b with equal runs of a\'s around it', alphabet: ['a', 'b'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b', 'a']); return !!b && b[1] === 1 && b[0] === b[2]; }, witness: (p) => rep('a', p) + 'b' + rep('a', p),
      hint: 'aᵖbaᵖ: pumping unbalances the two sides.' },
    { id: 'wwr', name: 'wwᴿ', desc: 'even-length palindromes', alphabet: ['a', 'b'], regular: false,
      member: (w) => w.length % 2 === 0 && w === chars(w).reverse().join(''), witness: (p) => rep('a', p) + 'bb' + rep('a', p),
      hint: 'aᵖbbaᵖ.' },
    { id: 'anbmcnm', name: 'aⁿbᵐcⁿ⁺ᵐ', desc: 'the c\'s count the a\'s and b\'s together', alphabet: ['a', 'b', 'c'], regular: false,
      member: (w) => { const b = blocks(w, ['a', 'b', 'c']); return !!b && b[0] + b[1] === b[2]; }, witness: (p) => rep('a', p) + 'b' + rep('c', p + 1),
      hint: 'aᵖbcᵖ⁺¹ and i = 0.' },
    // regular
    { id: 'even-a', name: 'even #a', desc: 'an even number of a\'s', alphabet: ['a', 'b'], regular: true, regex: 'b*(ab*ab*)*', member: (w) => /^[ab]*$/.test(w) && count(w, 'a') % 2 === 0 },
    { id: 'has-aba', name: 'contains aba', desc: 'aba appears somewhere', alphabet: ['a', 'b'], regular: true, regex: '(a|b)*aba(a|b)*', member: (w) => /^[ab]*$/.test(w) && w.includes('aba') },
    { id: 'ends-bb', name: 'ends in bb', desc: 'the last two symbols are b', alphabet: ['a', 'b'], regular: true, regex: '(a|b)*bb', member: (w) => /^[ab]*bb$/.test(w) },
    { id: 'a-then-b', name: 'a*b*', desc: 'no a after a b', alphabet: ['a', 'b'], regular: true, regex: 'a*b*', member: (w) => /^a*b*$/.test(w) },
    { id: 'len3', name: '|w| divisible by 3', desc: 'length a multiple of three', alphabet: ['a', 'b'], regular: true, regex: '((a|b)(a|b)(a|b))*', member: (w) => /^[ab]*$/.test(w) && w.length % 3 === 0 },
    { id: 'div3', name: 'binary divisible by 3', desc: 'binary numerals (ε counts as 0) whose value is a multiple of 3', alphabet: ['0', '1'], regular: true, regex: '(0|1(01*0)*1)*',
      member: (w) => { if (!/^[01]*$/.test(w)) return false; let r = 0; for (const c of w) r = (2 * r + +c) % 3; return r === 0; } },
    { id: 'no-bb', name: 'no bb', desc: 'never two b\'s in a row', alphabet: ['a', 'b'], regular: true, regex: '(a|ba)*(b|ε)', member: (w) => /^[ab]*$/.test(w) && !w.includes('bb') },
    { id: 'anbn-small', name: 'aⁿbⁿ, n ≤ 3', desc: 'looks like aⁿbⁿ but is finite', alphabet: ['a', 'b'], regular: true, regex: 'ε|ab|aabb|aaabbb', member: (w) => ['', 'ab', 'aabb', 'aaabbb'].includes(w),
      note: 'Finite, so regular: the pumping length can exceed every string in it.' },
    { id: 'ab-ba', name: '#ab = #ba', desc: 'as many ab\'s as ba\'s as substrings', alphabet: ['a', 'b'], regular: true, regex: 'ε|a|b|a(a|b)*a|b(a|b)*b',
      member: (w) => { if (!/^[ab]*$/.test(w)) return false; let x = 0, y = 0; for (let i = 0; i + 1 < w.length; i++) { if (w[i] === 'a' && w[i + 1] === 'b') x++; if (w[i] === 'b' && w[i + 1] === 'a') y++; } return x === y; },
      note: 'It looks like counting, but it only says the first and last symbols agree.' },
    { id: 'diff3', name: '#a − #b ≡ 0 (mod 3)', desc: 'the a\'s and b\'s differ by a multiple of three', alphabet: ['a', 'b'], regular: true,
      dfa: 'start r0\naccept r0\nr0 -a-> r1\nr1 -a-> r2\nr2 -a-> r0\nr0 -b-> r2\nr2 -b-> r1\nr1 -b-> r0', member: (w) => /^[ab]*$/.test(w) && (count(w, 'a') - count(w, 'b')) % 3 === 0 },
    { id: 'aa-star', name: '(aa)*', desc: 'an even number of a\'s and nothing else', alphabet: ['a'], regular: true, regex: '(aa)*', member: (w) => /^(aa)*$/.test(w) },
    { id: 'third-last-a', name: 'third from last is a', desc: 'the third symbol from the end is a', alphabet: ['a', 'b'], regular: true, regex: '(a|b)*a(a|b)(a|b)', member: (w) => /^[ab]*a[ab][ab]$/.test(w),
      note: 'An NFA needs 4 states; the smallest DFA needs 8.' },
  ];
  const Pump = T.Pump = { catalogue: L };
  Pump.get = (id) => (typeof id === 'string' ? L.find((x) => x.id === id) : id);

  // The minimal DFA of a regular catalogue entry (memoised), and its pumping length: the number of its
  // useful states, since a string of L never visits the dead state.
  Pump.dfa = function (lang) {
    lang = Pump.get(lang);
    if (!lang.regular) return null;
    if (!lang._dfa) {
      const m = lang.dfa ? FA.parse(lang.dfa).fa : RE.derivativeDFA(lang.regex, { alphabet: lang.alphabet }).fa;
      lang._dfa = FA.canonical(FA.minimizeHopcroft(FA.make({ ...m, alphabet: lang.alphabet })).fa);
    }
    return lang._dfa;
  };
  Pump.lengthFor = function (lang) {
    const d = Pump.dfa(lang);
    return d ? Math.max(1, FA.trim(d).fa.states.length) : null;
  };

  // All splits s = xyz with |xy| ≤ p and |y| ≥ 1, and for each the pump counts i ∈ [0, maxI] that leave L.
  Pump.splits = function (lang, p, s, maxI) {
    lang = Pump.get(lang);
    const w = chars(s), out = [];
    for (let i = 0; i < Math.min(p, w.length); i++) for (let j = i + 1; j <= Math.min(p, w.length); j++) {
      const x = w.slice(0, i).join(''), y = w.slice(i, j).join(''), z = w.slice(j).join('');
      const failing = [];
      for (let k = 0; k <= maxI; k++) if (!lang.member(x + y.repeat(k) + z)) failing.push(k);
      out.push({ x, y, z, failing });
    }
    return out;
  };
  const defaultMaxI = (s) => Math.min(Math.max(8, chars(s).length + 2), 400);

  // The game. Moves happen in order: adversary picks p, student picks s, adversary splits, student
  // picks i. Each move returns { ok, say, ... } and appends to g.trace.
  Pump.game = function (lang, opts = {}) {
    lang = Pump.get(lang);
    if (!lang) throw new Error('Unknown language.');
    const g = { lang, p: null, s: null, split: null, i: null, winner: null, trace: [] };
    const log = (step) => { g.trace.push(step); return step; };
    g.pickP = function (p) {
      if (p === undefined) p = lang.regular ? Pump.lengthFor(lang) : Math.min(opts.p || 4, lang.maxP || Infinity);
      g.p = p;
      return log({ kind: 'p', ok: true, p, say: lang.regular ? `I pick p = ${p}: my smallest DFA for this language has ${p} useful state${p === 1 ? '' : 's'}.` : `I pick p = ${p}.` });
    };
    g.pickString = function (s) {
      if (g.p === null) g.pickP();
      if (chars(s).some((c) => !lang.alphabet.includes(c))) return log({ kind: 's', ok: false, say: `${showW(s)} uses symbols outside {${lang.alphabet.join(', ')}}.` });
      if (!lang.member(s)) return log({ kind: 's', ok: false, say: `${showW(s)} is not in the language: you must pick a string of L.` });
      if (chars(s).length < g.p) return log({ kind: 's', ok: false, say: `${showW(s)} has length ${chars(s).length}, shorter than p = ${g.p}.` });
      g.s = s;
      return log({ kind: 's', ok: true, s, say: `You pick s = ${s} (length ${chars(s).length}).` });
    };
    // The adversary tries every legal split and keeps the one that is hardest for the student: one
    // that survives every i up to the bound if possible, else the one with the fewest losing i's
    // (and among those, the latest first losing i).
    g.pickSplit = function () {
      if (g.s === null) return log({ kind: 'split', ok: false, say: 'The string must be chosen first.' });
      const maxI = opts.maxI || defaultMaxI(g.s);
      let all = Pump.splits(lang, g.p, g.s, maxI), best;
      if (lang.regular) {
        // the DFA's own split (from the first repeated state) always survives
        const d = Pump.dfa(lang), r = FA.pumpSplit(d, g.s);
        if (r.ok && chars(r.x + r.y).length <= g.p) best = all.find((c) => c.x === r.x && c.y === r.y);
      }
      if (!best) best = all.slice().sort((a, b) => a.failing.length - b.failing.length || (b.failing[0] ?? Infinity) - (a.failing[0] ?? Infinity))[0];
      g.split = best;
      const survives = best.failing.length === 0;
      return log({ kind: 'split', ok: true, x: best.x, y: best.y, z: best.z, survives, maxI, considered: all.length, failing: best.failing,
        say: `I split s as x = ${showW(best.x)}, y = ${best.y}, z = ${showW(best.z)}${survives ? `; every xyⁱz with i ≤ ${maxI} stays in the language.` : '.'}` });
    };
    g.pickI = function (i) {
      if (!g.split) return log({ kind: 'i', ok: false, say: 'The split must be chosen first.' });
      const { x, y, z } = g.split, w = x + y.repeat(i) + z, inL = lang.member(w);
      g.i = i; g.winner = inL ? 'adversary' : 'student';
      const shown = chars(w).length > 60 ? `a string of length ${chars(w).length}` : showW(w);
      return log({ kind: 'i', ok: true, i, pumped: w, inL, winner: g.winner,
        say: inL ? `xy${i === 1 ? '' : supNum(i)}z = ${shown} is still in the language: I survive this round.` : `xy${supNum(i)}z = ${shown} is not in the language: you win, and this split is defeated.` });
    };
    // A winning i for the current split, if the bound finds one.
    g.winningI = () => (g.split && g.split.failing.length ? g.split.failing[0] : null);
    return g;
  };
  const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
  const supNum = (n) => String(n).split('').map((d) => SUP[d]).join('');

  // Does s defeat every split? (Then the student wins whatever the adversary does.)
  Pump.wins = function (lang, p, s, maxI) {
    const all = Pump.splits(lang, p, s, maxI || defaultMaxI(s));
    return { wins: all.every((c) => c.failing.length > 0), splits: all };
  };
  // Look for a winning string by brute force among strings of L with length p .. p + extra.
  Pump.findWinningString = function (lang, p, extra = 4) {
    lang = Pump.get(lang);
    let found = null;
    T.Found.eachString(lang.alphabet, p + extra, (w) => {
      if (chars(w).length < p || !lang.member(w)) return true;
      if (Pump.wins(lang, p, w).wins) { found = w; return false; }
      return true;
    });
    return found;
  };

  // ---------------------------------------------------------------- Moore and Mealy machines

  // Moore: { states, inputs, start, trans: [{from, sym, to}], out: { state: output } }; output after each
  // state entered, starting with the start state's (so |output| = |input| + 1).
  // Mealy: { states, inputs, start, trans: [{from, sym, to, out}] }; one output per move (|output| = |input|).
  const Tr = T.Transducer = {};
  const moveMap = (m) => { const d = new Map(); for (const e of m.trans) d.set(e.from + '\u0000' + e.sym, e); return d; };
  Tr.runMoore = function (m, w) {
    const d = moveMap(m), trace = [];
    let q = m.start, out = String(m.out[q] ?? '');
    trace.push({ kind: 'start', state: q, out: m.out[q], say: `Start in ${q}, which outputs ${showW(String(m.out[q] ?? ''))}.` });
    for (const a of chars(w)) {
      const e = d.get(q + '\u0000' + a);
      if (!e) { trace.push({ kind: 'stuck', state: q, sym: a, say: `${q} has no move on ${a}: the machine stops.` }); return { output: out, complete: false, trace }; }
      q = e.to; out += m.out[q] ?? '';
      trace.push({ kind: 'move', from: e.from, sym: a, to: q, out: m.out[q], say: `Read ${a}: go to ${q}, output ${showW(String(m.out[q] ?? ''))}.` });
    }
    return { output: out, complete: true, trace };
  };
  Tr.runMealy = function (m, w) {
    const d = moveMap(m), trace = [];
    let q = m.start, out = '';
    trace.push({ kind: 'start', state: q, say: `Start in ${q}; a Mealy machine outputs on its moves.` });
    for (const a of chars(w)) {
      const e = d.get(q + '\u0000' + a);
      if (!e) { trace.push({ kind: 'stuck', state: q, sym: a, say: `${q} has no move on ${a}: the machine stops.` }); return { output: out, complete: false, trace }; }
      q = e.to; out += e.out;
      trace.push({ kind: 'move', from: e.from, sym: a, to: q, out: e.out, say: `Read ${a}: go to ${q}, output ${showW(e.out)}.` });
    }
    return { output: out, complete: true, trace };
  };
  // Moore → Mealy: each move outputs what its target state would. The Mealy output is the Moore output
  // without the start state's first symbol.
  Tr.mooreToMealy = function (m) {
    const trace = m.trans.map((e) => ({ kind: 'edge', edge: e, out: m.out[e.to], say: `${e.from} -${e.sym}-> ${e.to} outputs ${showW(String(m.out[e.to] ?? ''))}, the output of ${e.to}.` }));
    trace.push({ kind: 'note', say: `The Mealy machine skips the initial output ${showW(String(m.out[m.start] ?? ''))} of the start state; otherwise the outputs agree.` });
    return { mealy: { states: m.states.slice(), inputs: m.inputs.slice(), start: m.start, trans: m.trans.map((e) => ({ ...e, out: String(m.out[e.to] ?? '') })) }, trace };
  };
  // Mealy → Moore: split each state by the output on the move that enters it: state "q/o" means "in q,
  // having just output o". The start gets the initial output (default: the first output symbol used).
  Tr.mealyToMoore = function (m, initial) {
    const outs = [...new Set(m.trans.map((e) => e.out))];
    if (initial === undefined) initial = outs[0] ?? '';
    const name = (q, o) => `${q}/${o === '' ? 'ε' : o}`;
    const d = moveMap(m), trace = [], seen = new Map(), queue = [[m.start, initial]], trans = [];
    seen.set(name(m.start, initial), [m.start, initial]);
    trace.push({ kind: 'state', state: name(m.start, initial), say: `Start in ${name(m.start, initial)}: state ${m.start}, showing the initial output ${showW(initial)}.` });
    while (queue.length) {
      const [q, o] = queue.shift();
      for (const a of m.inputs) {
        const e = d.get(q + '\u0000' + a);
        if (!e) continue;
        const n2 = name(e.to, e.out);
        if (!seen.has(n2)) { seen.set(n2, [e.to, e.out]); queue.push([e.to, e.out]); trace.push({ kind: 'state', state: n2, say: `New state ${n2}: ${e.to} entered with output ${showW(e.out)}.` }); }
        trans.push({ from: name(q, o), sym: a, to: n2 });
      }
    }
    const out = {};
    for (const [n, [, o]] of seen) out[n] = o;
    return { moore: { states: [...seen.keys()], inputs: m.inputs.slice(), start: name(m.start, initial), trans, out }, trace };
  };

  // ---------------------------------------------------------------- two-way DFA

  // { states, alphabet, start, accept, reject, delta: [{from, sym, to, move: 'L' | 'R'}] }. The tape is
  // ⊢ w ⊣; the machine halts on entering accept or reject. A missing move or falling off the tape
  // rejects; a repeated configuration (state, head) means it loops forever, which also rejects.
  const TW = T.TwoWay = { LEFT: '⊢', RIGHT: '⊣' };
  TW.run = function (m, w, maxSteps = 10000) {
    const tape = [TW.LEFT, ...chars(w), TW.RIGHT], d = new Map(), trace = [];
    for (const e of m.delta) d.set(e.from + '\u0000' + e.sym, e);
    let q = m.start, h = 0;
    const seen = new Set();
    const end = (accepted, why, extra = {}) => { trace.push({ kind: 'halt', state: q, head: h, accepted, ...extra, say: why }); return { accepted, steps: trace.length - 1, trace, tape }; };
    trace.push({ kind: 'start', state: q, head: 0, tape, say: `Start in ${q} on ⊢, the left end marker.` });
    for (let step = 0; step < maxSteps; step++) {
      if (q === m.accept) return end(true, `${q} is the accepting state: accept.`);
      if (q === m.reject) return end(false, `${q} is the rejecting state: reject.`);
      const c = q + '\u0000' + h;
      if (seen.has(c)) return end(false, `The machine is in ${q} at cell ${h} again: it will loop forever, so it does not accept.`, { loop: true });
      seen.add(c);
      const e = d.get(q + '\u0000' + tape[h]);
      if (!e) return end(false, `${q} has no move on ${tape[h]}: halt and reject.`);
      const from = q, at = h;
      q = e.to; h += e.move === 'L' ? -1 : 1;
      if (h < 0 || h >= tape.length) return end(false, `The head falls off the ${h < 0 ? 'left' : 'right'} end: reject.`);
      trace.push({ kind: 'move', from, to: q, head: h, was: at, sym: tape[at], dir: e.move, say: `${from} reads ${tape[at]}, goes to ${q} and moves ${e.move === 'L' ? 'left' : 'right'}.` });
    }
    return end(false, `Stopped after ${maxSteps} steps.`, { limit: true });
  };
  TW.examples = {
    // walk to the right end, then step back three cells and look
    thirdFromEnd: { name: 'third symbol from the end is a', states: ['go', 'c1', 'c2', 'c3', 'yes', 'no'], alphabet: ['a', 'b'], start: 'go', accept: 'yes', reject: 'no',
      delta: [
        { from: 'go', sym: '⊢', to: 'go', move: 'R' }, { from: 'go', sym: 'a', to: 'go', move: 'R' }, { from: 'go', sym: 'b', to: 'go', move: 'R' }, { from: 'go', sym: '⊣', to: 'c1', move: 'L' },
        { from: 'c1', sym: 'a', to: 'c2', move: 'L' }, { from: 'c1', sym: 'b', to: 'c2', move: 'L' }, { from: 'c1', sym: '⊢', to: 'no', move: 'R' },
        { from: 'c2', sym: 'a', to: 'c3', move: 'L' }, { from: 'c2', sym: 'b', to: 'c3', move: 'L' }, { from: 'c2', sym: '⊢', to: 'no', move: 'R' },
        { from: 'c3', sym: 'a', to: 'yes', move: 'R' }, { from: 'c3', sym: 'b', to: 'no', move: 'R' }, { from: 'c3', sym: '⊢', to: 'no', move: 'R' },
      ], member: (w) => /^[ab]*a[ab][ab]$/.test(w) },
    // two passes: check the a's are even going right, come back, check the b's are odd going right
    twoPass: { name: 'even number of a\'s and odd number of b\'s, checked in two passes', states: ['e', 'o', 'back', 'E', 'O', 'yes', 'no'], alphabet: ['a', 'b'], start: 'e', accept: 'yes', reject: 'no',
      delta: [
        { from: 'e', sym: '⊢', to: 'e', move: 'R' }, { from: 'e', sym: 'a', to: 'o', move: 'R' }, { from: 'e', sym: 'b', to: 'e', move: 'R' }, { from: 'e', sym: '⊣', to: 'back', move: 'L' },
        { from: 'o', sym: 'a', to: 'e', move: 'R' }, { from: 'o', sym: 'b', to: 'o', move: 'R' }, { from: 'o', sym: '⊣', to: 'no', move: 'L' },
        { from: 'back', sym: 'a', to: 'back', move: 'L' }, { from: 'back', sym: 'b', to: 'back', move: 'L' }, { from: 'back', sym: '⊢', to: 'E', move: 'R' },
        { from: 'E', sym: 'a', to: 'E', move: 'R' }, { from: 'E', sym: 'b', to: 'O', move: 'R' }, { from: 'E', sym: '⊣', to: 'no', move: 'L' },
        { from: 'O', sym: 'a', to: 'O', move: 'R' }, { from: 'O', sym: 'b', to: 'E', move: 'R' }, { from: 'O', sym: '⊣', to: 'yes', move: 'L' },
      ], member: (w) => /^[ab]*$/.test(w) && count(w, 'a') % 2 === 0 && count(w, 'b') % 2 === 1 },
  };

  // ---------------------------------------------------------------- KMP

  const KMP = T.KMP = {};
  // fail[j] = length of the longest proper border (prefix that is also a suffix) of pattern[0..j].
  KMP.failure = function (pattern) {
    const p = chars(pattern), fail = new Array(p.length).fill(0), trace = [];
    let k = 0;
    for (let j = 1; j < p.length; j++) {
      while (k > 0 && p[j] !== p[k]) {
        trace.push({ kind: 'fallback', j, k, to: fail[k - 1], say: `${p[j]} ≠ ${p[k]}: fall back from border ${k} to ${fail[k - 1]}.` });
        k = fail[k - 1];
      }
      if (p[j] === p[k]) k++;
      fail[j] = k;
      trace.push({ kind: 'set', j, value: k, say: `fail(${p.slice(0, j + 1).join('')}) = ${k}${k ? `: ${p.slice(0, k).join('')} is both a prefix and a suffix` : ''}.` });
    }
    return { fail, trace };
  };
  // The DFA that has just read text ending in the longest possible prefix of the pattern. State names
  // are the prefixes (ε for none); the full pattern accepts, and keeps going so overlaps are found.
  KMP.dfa = function (pattern, alphabet) {
    const p = chars(pattern), n = p.length;
    if (!n) throw new Error('The pattern is empty.');
    alphabet = alphabet || [...new Set(p)].sort();
    const { fail } = KMP.failure(pattern);
    const name = (j) => (j === 0 ? 'ε' : p.slice(0, j).join(''));
    const delta = [], trans = [], trace = [];
    for (let j = 0; j <= n; j++) {
      delta.push({});
      for (const c of alphabet) {
        let to;
        if (j < n && p[j] === c) { to = j + 1; trace.push({ kind: 'forward', from: name(j), sym: c, to: name(to), say: `${name(j)} on ${c}: the match grows to ${name(to)}.` }); }
        else {
          const b = j === 0 ? 0 : fail[j - 1];
          to = j === 0 ? 0 : delta[b][c];
          trace.push({ kind: 'back', from: name(j), sym: c, via: name(b), to: name(to), say: j === 0 ? `ε on ${c}: still nothing matched.` : `${name(j)} on ${c}: behave like the border ${name(b)} would, reaching ${name(to)}.` });
        }
        delta[j][c] = to;
        trans.push({ from: name(j), sym: c, to: name(to) });
      }
    }
    return { fa: FA.make({ states: p.map((_, j) => name(j)).concat([name(n)]), alphabet, start: 'ε', accept: [name(n)], trans }), fail, trace };
  };
  // Search text for pattern: positions (0-based) where a match starts.
  KMP.search = function (pattern, text) {
    const n = chars(pattern).length, alphabet = [...new Set([...chars(pattern), ...chars(text)])].sort();
    const { fa } = KMP.dfa(pattern, alphabet), del = FA._deltaMap(fa), t = chars(text), trace = [], matches = [];
    let q = fa.start;
    t.forEach((c, i) => {
      const to = del.get(q).get(c);
      const hit = to === fa.accept[0];
      if (hit) matches.push(i - n + 1);
      trace.push({ kind: 'read', pos: i, sym: c, from: q, to, match: hit, say: hit ? `Read ${c}: the whole pattern matched, starting at ${i - n + 1}.` : `Read ${c}: ${q} → ${to}.` });
      q = to;
    });
    return { matches, trace };
  };

  // ---------------------------------------------------------------- lexer generator

  // Moore refinement on a partial DFA whose accepting states carry token names: start from blocks of
  // equal tags, split by where each symbol leads (a missing move counts as its own block).
  function minimizeTagged(d, tag) {
    const del = FA._deltaMap(d);
    let blockOf = new Map(d.states.map((q) => [q, tag[q] || '']));
    for (let size = -1; ;) {
      const sig = new Map(), next = new Map();
      for (const q of d.states) {
        const k = blockOf.get(q) + '\u0000' + d.alphabet.map((a) => { const t = del.get(q).get(a); return t === undefined ? '-' : blockOf.get(t); }).join('\u0001');
        if (!sig.has(k)) sig.set(k, String(sig.size));
        next.set(q, sig.get(k));
      }
      blockOf = next;
      if (sig.size === size) break;
      size = sig.size;
    }
    const rep = new Map();
    for (const q of d.states) if (!rep.has(blockOf.get(q))) rep.set(blockOf.get(q), q);
    // name blocks L0, L1, ... in breadth-first order from the start
    const name = new Map(), queue = [d.start];
    name.set(blockOf.get(d.start), 'L0');
    while (queue.length) {
      const q = queue.shift();
      for (const a of d.alphabet) { const t = del.get(q).get(a); if (t !== undefined && !name.has(blockOf.get(t))) { name.set(blockOf.get(t), 'L' + name.size); queue.push(t); } }
    }
    const trans = [], token = {};
    for (const [b, q] of rep) {
      if (!name.has(b)) continue;
      if (tag[q]) token[name.get(b)] = tag[q];
      for (const a of d.alphabet) { const t = del.get(q).get(a); if (t !== undefined) trans.push({ from: name.get(b), sym: a, to: name.get(blockOf.get(t)) }); }
    }
    const states = [...name.values()].sort((x, y) => +x.slice(1) - +y.slice(1));
    return { dfa: FA.make({ states, alphabet: d.alphabet, start: 'L0', accept: Object.keys(token), trans }), token };
  }

  // rules: [{ name, regex, skip }]. Builds one DFA for all of them; each accepting DFA state carries the
  // first-listed rule it accepts (priority). Tokenising takes the longest match at each position.
  const Lexer = T.Lexer = {};
  Lexer.build = function (rules, opts = {}) {
    const trace = [], asts = rules.map((r) => (typeof r.regex === 'string' ? RE.parse(r.regex, opts) : r.regex));
    asts.forEach((a, i) => { if (RE.nullable(a)) throw new Error(`Rule ${rules[i].name} matches the empty string, so the lexer would never move.`); });
    const sigma = [...new Set(asts.flatMap((a) => RE.alphabet(a)).concat(opts.alphabet || []))].sort();
    const states = ['S'], trans = [], accept = [], ruleOf = new Map();
    asts.forEach((a, i) => {
      const t = RE.thompson(a).fa, ren = (q) => `${i}:${q}`;
      states.push(...t.states.map(ren));
      trans.push({ from: 'S', sym: '', to: ren(t.start) }, ...t.trans.map((e) => ({ from: ren(e.from), sym: e.sym, to: ren(e.to) })));
      for (const f of t.accept) { accept.push(ren(f)); ruleOf.set(ren(f), i); }
      trace.push({ kind: 'rule', rule: rules[i].name, regex: RE.show(a), states: t.states.length, say: `${rules[i].name} = ${RE.show(a)}: a Thompson NFA with ${t.states.length} states, joined to a common start by ε.` });
    });
    const nfa = FA.make({ states, alphabet: sigma, start: 'S', accept, trans });
    const sub = FA.subset(nfa, { dropEmpty: true });
    trace.push({ kind: 'subset', states: sub.fa.states.length, say: `The subset construction gives one DFA with ${sub.fa.states.length} states.` });
    // rename DFA states L0, L1, ... and tag the accepting ones with their winning rule
    const ren = new Map(sub.fa.states.map((q, i) => [q, 'L' + i])), token = {};
    for (const q of sub.fa.accept) {
      const rs = [...new Set(sub.sets[q].filter((x) => ruleOf.has(x)).map((x) => ruleOf.get(x)))].sort((a, b) => a - b);
      token[ren.get(q)] = rules[rs[0]].name;
      trace.push({ kind: 'tag', state: ren.get(q), rules: rs.map((i) => rules[i].name), token: rules[rs[0]].name,
        say: rs.length > 1 ? `${ren.get(q)} ends ${rs.map((i) => rules[i].name).join(' and ')}; ${rules[rs[0]].name} wins because it is listed first.` : `${ren.get(q)} ends the token ${rules[rs[0]].name}.` });
    }
    const big = FA.make({ states: sub.fa.states.map((q) => ren.get(q)), alphabet: sigma, start: ren.get(sub.fa.start), accept: sub.fa.accept.map((q) => ren.get(q)), trans: sub.fa.trans.map((e) => ({ from: ren.get(e.from), sym: e.sym, to: ren.get(e.to) })) });
    const { dfa, token: tok } = minimizeTagged(big, token);
    trace.push({ kind: 'minimize', states: dfa.states.length, say: `Merging states that end the same token and behave alike leaves ${dfa.states.length}.` });
    for (const k of Object.keys(token)) delete token[k];
    Object.assign(token, tok);
    const del = FA._deltaMap(dfa), skip = new Set(rules.filter((r) => r.skip).map((r) => r.name));
    const lex = { dfa, token, trace, rules };
    // Longest match: run the DFA as far as it goes, remembering the last accepting position, then back
    // up to it. Characters no rule can start are reported and skipped one at a time.
    lex.tokenize = function (input) {
      const s = chars(input), tokens = [], errors = [], steps = [];
      let pos = 0;
      while (pos < s.length) {
        let q = dfa.start, i = pos, last = null;
        while (i < s.length) {
          const to = del.get(q) && del.get(q).get(s[i]);
          if (to === undefined) break;
          q = to; i++;
          if (token[q]) last = { end: i, name: token[q], state: q };
        }
        if (!last) {
          errors.push({ pos, ch: s[pos] });
          steps.push({ kind: 'error', pos, ch: s[pos], say: `No token can start with ${s[pos]} at position ${pos}: report it and skip it.` });
          pos++;
          continue;
        }
        const text = s.slice(pos, last.end).join('');
        const backed = i - last.end;
        if (!skip.has(last.name)) tokens.push({ name: last.name, text, start: pos, end: last.end });
        steps.push({ kind: skip.has(last.name) ? 'skip' : 'token', name: last.name, text, start: pos, end: last.end, scanned: i,
          say: `${skip.has(last.name) ? 'Skip' : 'Token'} ${last.name} "${text}"${backed ? `: the scan reached position ${i} but the longest match ends at ${last.end}, so back up ${backed}` : ''}.` });
        pos = last.end;
      }
      return { tokens, errors, trace: steps };
    };
    return lex;
  };
})();
