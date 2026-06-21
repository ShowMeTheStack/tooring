// The pumping lemma for context-free languages as a two-player game, a catalogue of languages to play it
// on, and the closure constructions (union, concatenation, star, intersection with a regular language)
// with the demonstration that two context-free languages can meet in a non-context-free one.
//
// THE GAME. For a context-free L there is a p such that every s in L with |s| ≥ p splits as s = uvxyz
// with |vxy| ≤ p and |vy| ≥ 1 so that u vⁱ x yⁱ z is in L for every i ≥ 0. To show L is not context-free
// the student plays against an adversary who claims it is: the adversary names p, the student picks s,
// the adversary splits it, the student picks i. The student wins if the pumped word leaves L. The
// computer adversary tries every legal split and keeps one that survives all i in a range; if none does,
// it says so: the student's word defeats every split.
// Words here are plain strings of one-character symbols.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const show = (w) => (w === '' ? 'ε' : w);
  const count = (w, c) => { let k = 0; for (const x of w) if (x === c) k++; return k; };
  // w = a^i b^j c^k ... in this exact block order (blocks may be empty); returns the counts or null
  const blocks = (w, letters) => {
    const out = []; let i = 0;
    for (const L of letters) { let k = 0; while (w[i] === L) { k++; i++; } out.push(k); }
    return i === w.length ? out : null;
  };
  const isPrime = (n) => { if (n < 2) return false; for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; };
  const isSquare = (n) => { const r = Math.round(Math.sqrt(n)); return r * r === n; };
  const isPow2 = (n) => n >= 1 && (n & (n - 1)) === 0;
  const rev = (w) => [...w].reverse().join('');
  const R = (c, n) => c.repeat(n);

  // ---------- the catalogue ----------
  // { id, name, notation, alphabet, cf, member, sample(p) (a word in L of length ≥ p, the natural choice
  //   for the game), why, grammar (text, for the context-free ones), pMin (smallest p the adversary may
  //   use for a context-free one), iMax(s) (pumping range needed, default 3) }
  const catalogue = [
    { id: 'anbn', name: 'equal blocks', notation: 'aⁿbⁿ', alphabet: ['a', 'b'], cf: true,
      member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] === b[1]; }, sample: (p) => R('a', p) + R('b', p),
      grammar: 'S -> a S b | ε', why: 'Pump one a together with one b around the middle.' },
    { id: 'anbncn', name: 'three equal blocks', notation: 'aⁿbⁿcⁿ', alphabet: ['a', 'b', 'c'], cf: false,
      member: (w) => { const b = blocks(w, 'abc'); return !!b && b[0] === b[1] && b[1] === b[2]; }, sample: (p) => R('a', p) + R('b', p) + R('c', p),
      why: 'vxy is at most p long, so it touches at most two of the three blocks; pumping changes those and leaves the third behind.' },
    { id: 'evenpal', name: 'even palindromes', notation: 'w wᴿ', alphabet: ['a', 'b'], cf: true,
      member: (w) => w.length % 2 === 0 && w === rev(w), sample: (p) => R('a', p) + R('b', 2) + R('a', p),
      grammar: 'S -> a S a | b S b | ε', why: 'Pump matching symbols on both sides of the centre.' },
    { id: 'ww', name: 'doubled words', notation: 'w w', alphabet: ['a', 'b'], cf: false,
      member: (w) => w.length % 2 === 0 && w.slice(0, w.length / 2) === w.slice(w.length / 2), sample: (p) => R('a', p) + R('b', p) + R('a', p) + R('b', p),
      why: 'In aᵖbᵖaᵖbᵖ the window vxy is too short to change matching parts of both halves; pumping down breaks the copy.' },
    { id: 'ijk-or', name: 'two of three agree', notation: 'aⁱbʲcᵏ with i = j or j = k', alphabet: ['a', 'b', 'c'], cf: true,
      member: (w) => { const b = blocks(w, 'abc'); return !!b && (b[0] === b[1] || b[1] === b[2]); }, sample: (p) => R('a', p) + R('b', p) + R('c', p),
      grammar: 'S -> X C | A Y\nX -> a X b | ε\nC -> c C | ε\nA -> a A | ε\nY -> b Y c | ε', why: 'Context-free (a union of two easy ones) but inherently ambiguous: aⁿbⁿcⁿ always has two trees.' },
    { id: 'anb2n', name: 'twice as many b', notation: 'aⁿb²ⁿ', alphabet: ['a', 'b'], cf: true, pMin: 3,
      member: (w) => { const b = blocks(w, 'ab'); return !!b && b[1] === 2 * b[0]; }, sample: (p) => R('a', p) + R('b', 2 * p),
      grammar: 'S -> a S b b | ε', why: 'Pump one a with two b.' },
    { id: 'squares', name: 'square lengths', notation: 'a^(n²)', alphabet: ['a'], cf: false,
      member: (w) => count(w, 'a') === w.length && isSquare(w.length), sample: (p) => R('a', p * p),
      why: 'From p² pumping once adds at most p symbols, landing strictly between p² and (p+1)².' },
    { id: 'primes', name: 'prime lengths', notation: 'aᵖ, p prime', alphabet: ['a'], cf: false,
      member: (w) => count(w, 'a') === w.length && isPrime(w.length), sample: (p) => { let q = Math.max(p, 2) + 2; while (!isPrime(q)) q++; return R('a', q); },
      iMax: (s) => s.length + 1, why: 'With |s| = q prime, pumping with i = q + 1 gives length q(1 + |vy|), which is not prime.' },
    { id: 'abcd-cross', name: 'crossed counts', notation: 'aⁿbᵐcⁿdᵐ', alphabet: ['a', 'b', 'c', 'd'], cf: false,
      member: (w) => { const b = blocks(w, 'abcd'); return !!b && b[0] === b[2] && b[1] === b[3]; }, sample: (p) => R('a', p) + R('b', p) + R('c', p) + R('d', p),
      why: 'The matched pairs cross; a window of length p cannot reach both a and c, or both b and d.' },
    { id: 'abcd-nest', name: 'nested counts', notation: 'aⁿbᵐcᵐdⁿ', alphabet: ['a', 'b', 'c', 'd'], cf: true,
      member: (w) => { const b = blocks(w, 'abcd'); return !!b && b[0] === b[3] && b[1] === b[2]; }, sample: (p) => R('a', p) + R('b', p) + R('c', p) + R('d', p),
      grammar: 'S -> a S d | B\nB -> b B c | ε', why: 'The pairs nest, as a stack likes; pump b with c in the middle.' },
    { id: 'eqabc', name: 'equal letter counts', notation: '#a = #b = #c', alphabet: ['a', 'b', 'c'], cf: false,
      member: (w) => count(w, 'a') === count(w, 'b') && count(w, 'b') === count(w, 'c'), sample: (p) => R('a', p) + R('b', p) + R('c', p),
      why: 'Choose aᵖbᵖcᵖ; the window misses one letter entirely, so pumping unbalances the counts.' },
    { id: 'eqab', name: 'as many a as b', notation: '#a = #b', alphabet: ['a', 'b'], cf: true,
      member: (w) => count(w, 'a') === count(w, 'b'), sample: (p) => R('a', p) + R('b', p),
      grammar: 'S -> a S b S | b S a S | ε', why: 'Pump an a with a b next to the boundary.' },
    { id: 'ijk-lt', name: 'strictly growing blocks', notation: 'aⁱbʲcᵏ with i < j < k', alphabet: ['a', 'b', 'c'], cf: false,
      member: (w) => { const b = blocks(w, 'abc'); return !!b && b[0] < b[1] && b[1] < b[2]; }, sample: (p) => R('a', p) + R('b', p + 1) + R('c', p + 2),
      why: 'Pumping up a block with a or b in it catches the next block; pumping down one with c in it falls behind.' },
    { id: 'bounded-ratio', name: 'between one and two b per a', notation: 'aⁱbʲ with i ≤ j ≤ 2i', alphabet: ['a', 'b'], cf: true,
      member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] <= b[1] && b[1] <= 2 * b[0]; }, sample: (p) => R('a', p) + R('b', p + Math.ceil(p / 2)),
      grammar: 'S -> a S b | a S b b | ε', why: 'Each a brings one or two b; pump an a with one b.' },
    { id: 'aba-n', name: 'a sandwich', notation: 'aⁿbⁿaⁿ', alphabet: ['a', 'b'], cf: false,
      member: (w) => { const b = blocks(w, 'aba'); return !!b && b[0] === b[1] && b[1] === b[2]; }, sample: (p) => R('a', p) + R('b', p) + R('a', p),
      why: 'Like three equal blocks: the window cannot touch both outer blocks.' },
    { id: 'twoab', name: 'twice as many a as b', notation: '#a = 2·#b', alphabet: ['a', 'b'], cf: true,
      member: (w) => count(w, 'a') === 2 * count(w, 'b'), sample: (p) => R('a', 2 * p) + R('b', p),
      grammar: 'S -> a S a S b S | a S b S a S | b S a S a S | ε', why: 'Pump two a with one b near the boundary.' },
    { id: 'unequal', name: 'unequal blocks', notation: 'aᵐbⁿ with m ≠ n', alphabet: ['a', 'b'], cf: true, pMin: 3,
      member: (w) => { const b = blocks(w, 'ab'); return !!b && b[0] !== b[1]; }, sample: (p) => R('a', p) + R('b', p + 1),
      grammar: 'S -> a S b | A | B\nA -> a A | a\nB -> b B | b', why: 'Pump an a with a b, keeping the surplus.' },
    { id: 'pow2', name: 'power-of-two lengths', notation: 'a^(2ⁿ)', alphabet: ['a'], cf: false,
      member: (w) => count(w, 'a') === w.length && isPow2(w.length), sample: (p) => { let m = 1; while (m <= p) m *= 2; return R('a', m); },
      why: 'From 2ᵐ > p pumping once adds at most p < 2ᵐ symbols, falling short of 2ᵐ⁺¹.' },
    { id: 'abc-lecap', name: 'c capped by equal blocks', notation: 'aⁿbⁿcᵐ with m ≤ n', alphabet: ['a', 'b', 'c'], cf: false,
      member: (w) => { const b = blocks(w, 'abc'); return !!b && b[0] === b[1] && b[2] <= b[0]; }, sample: (p) => R('a', p) + R('b', p) + R('c', p),
      why: 'Pumping the c up breaks the cap; pumping a and b down falls under the c.' },
    { id: 'mirror-c', name: 'mirror around c', notation: 'w c wᴿ', alphabet: ['a', 'b', 'c'], cf: true,
      member: (w) => { const i = w.indexOf('c'); return i >= 0 && w.lastIndexOf('c') === i && w.slice(i + 1) === rev(w.slice(0, i)); }, sample: (p) => R('a', p) + 'c' + R('a', p),
      grammar: 'S -> a S a | b S b | c', why: 'Pump matching symbols on both sides of c.' },
    { id: 'copy-c', name: 'copy around c', notation: 'w c w', alphabet: ['a', 'b', 'c'], cf: false,
      member: (w) => { const i = w.indexOf('c'); return i >= 0 && w.lastIndexOf('c') === i && w.slice(i + 1) === w.slice(0, i); }, sample: (p) => R('a', p) + R('b', p) + 'c' + R('a', p) + R('b', p),
      why: 'A short window cannot change both copies the same way.' },
    { id: 'sum', name: 'c counts the rest', notation: 'aⁱbʲcᵏ with k = i + j', alphabet: ['a', 'b', 'c'], cf: true,
      member: (w) => { const b = blocks(w, 'abc'); return !!b && b[2] === b[0] + b[1]; }, sample: (p) => R('a', p) + R('b', p) + R('c', 2 * p),
      grammar: 'S -> a S c | B\nB -> b B c | ε', why: 'Pump a b with a c.' },
    { id: 'product', name: 'c counts a times b', notation: 'aⁱbʲcᵏ with k = i·j', alphabet: ['a', 'b', 'c'], cf: false,
      member: (w) => { const b = blocks(w, 'abc'); return !!b && b[2] === b[0] * b[1]; }, sample: (p) => R('a', p) + R('b', p) + R('c', p * p),
      why: 'Changing a or b by a little changes the product by about p, more than the window can add to c.' },
    { id: 'middle-a', name: 'a in the middle', notation: 'odd length, middle symbol a', alphabet: ['a', 'b'], cf: true,
      member: (w) => w.length % 2 === 1 && w[(w.length - 1) / 2] === 'a', sample: (p) => R('b', p) + 'a' + R('b', p),
      grammar: 'S -> X S X | a\nX -> a | b', why: 'Pump one symbol on each side of the middle.' },
    { id: 'brackets', name: 'balanced brackets', notation: 'balanced ( and )', alphabet: ['(', ')'], cf: true,
      member: (w) => { let d = 0; for (const c of w) { d += c === '(' ? 1 : -1; if (d < 0) return false; } return d === 0; }, sample: (p) => R('(', p) + R(')', p),
      grammar: "S -> ( S ) S | ε", why: 'Pump an opening bracket with its partner.' },
  ];
  const byId = (id) => (typeof id === 'string' ? catalogue.find((L) => L.id === id) : id);

  // ---------- splits ----------
  // Every legal split of s for the constant p: |vxy| ≤ p and |vy| ≥ 1, as index tuples and strings.
  function* splits(s, p) {
    const n = s.length;
    for (let a = 0; a <= n; a++)                       // u = s[0..a)
      for (let lv = 0; lv <= p && a + lv <= n; lv++)
        for (let lx = 0; lv + lx <= p && a + lv + lx <= n; lx++)
          for (let ly = 0; lv + lx + ly <= p && a + lv + lx + ly <= n; ly++) {
            if (lv + ly === 0) continue;
            const b = a + lv, c = b + lx, d = c + ly;
            yield { u: s.slice(0, a), v: s.slice(a, b), x: s.slice(b, c), y: s.slice(c, d), z: s.slice(d), at: [a, b, c, d] };
          }
  }
  const pump = (dec, i) => dec.u + dec.v.repeat(i) + dec.x + dec.y.repeat(i) + dec.z;
  function validSplit(s, p, dec) {
    if (dec.u + dec.v + dec.x + dec.y + dec.z !== s) return { ok: false, say: 'u v x y z must spell the word ' + show(s) + ' exactly.' };
    if ((dec.v + dec.x + dec.y).length > p) return { ok: false, say: '|vxy| = ' + (dec.v + dec.x + dec.y).length + ' is more than p = ' + p + '.' };
    if (!(dec.v + dec.y).length) return { ok: false, say: 'v and y cannot both be empty.' };
    return { ok: true, say: 'A legal split.' };
  }
  const iRange = (L, s, opts) => { const top = (opts && opts.iMax) || (L.iMax ? L.iMax(s) : 3); const r = []; for (let i = 0; i <= top; i++) if (i !== 1) r.push(i); return r; };
  // The i that knocks the split out of L, or null if it survives every i in the range.
  function refute(L, dec, range) { for (const i of range) if (!L.member(pump(dec, i))) return i; return null; }
  const showSplit = (d) => 'u = ' + show(d.u) + ', v = ' + show(d.v) + ', x = ' + show(d.x) + ', y = ' + show(d.y) + ', z = ' + show(d.z);

  // The computer as adversary: look for a split of s that survives every i in the range.
  function adversarySplit(L0, s, p, opts) {
    const L = byId(L0), range = iRange(L, s, opts), trace = [];
    const limit = (opts && opts.traceLimit) || 60;
    let tried = 0;
    for (const d of splits(s, p)) {
      tried++;
      const i = refute(L, d, range);
      if (i === null) {
        trace.push({ kind: 'survivor', split: d, say: 'Split ' + showSplit(d) + ' stays in the language for every i in ' + range.join(', ') + '.' });
        return { split: d, survives: true, tried, range, trace };
      }
      if (trace.length < limit) trace.push({ kind: 'try', split: d, i, pumped: pump(d, i), say: showSplit(d) + ' fails at i = ' + i + ': ' + show(pump(d, i)) + ' is not in the language.' });
    }
    trace.push({ kind: 'none', tried, say: 'All ' + tried + ' legal splits of ' + show(s) + ' leave the language for some i: the adversary has no answer, so the student wins.' });
    return { split: null, survives: false, tried, range, trace };
  }
  // The computer as challenger (the student defends a context-free language): find an i that breaks a split.
  function challengerI(L0, s, dec, p, opts) {
    const L = byId(L0), v = validSplit(s, p, dec);
    if (!v.ok) return { i: null, legal: false, say: v.say };
    const range = iRange(L, s, opts), i = refute(L, dec, range);
    return i === null ? { i: null, legal: true, survives: true, range, say: 'Every i in ' + range.join(', ') + ' keeps the word in the language: the split holds.' }
      : { i, legal: true, survives: false, pumped: pump(dec, i), say: 'i = ' + i + ' gives ' + show(pump(dec, i)) + ', which is not in the language.' };
  }

  // A game as a small state machine: adversary picks p → student picks s → adversary splits → student picks i.
  function game(L0, opts) {
    const L = byId(L0);
    opts = opts || {};
    const g = { lang: L, p: opts.p || (L.pMin ? Math.max(L.pMin, 3) : 3), word: null, split: null, i: null, over: false, studentWins: null, trace: [] };
    g.trace.push({ kind: 'p', p: g.p, say: 'The adversary claims ' + L.notation + ' is context-free with pumping constant p = ' + g.p + '.' });
    g.chooseWord = (s) => {
      if (!L.member(s)) return { ok: false, say: show(s) + ' is not in the language.' };
      if (s.length < g.p) return { ok: false, say: show(s) + ' is shorter than p = ' + g.p + '.' };
      g.word = s; g.trace.push({ kind: 'word', word: s, say: 'The student picks s = ' + show(s) + ' (length ' + s.length + ').' });
      return { ok: true, say: 'Accepted.' };
    };
    g.adversaryMove = () => {
      const r = adversarySplit(L, g.word, g.p, opts);
      g.search = r;
      if (r.survives) { g.split = r.split; g.trace.push({ kind: 'split', split: r.split, say: 'The adversary splits: ' + showSplit(r.split) + '.' }); }
      else {
        // no split survives; show the first one anyway so the student can finish the round
        g.split = splits(g.word, g.p).next().value;
        g.trace.push({ kind: 'cornered', split: g.split, tried: r.tried, say: 'No split survives every i; the adversary is cornered and offers ' + showSplit(g.split) + '.' });
      }
      return g.split;
    };
    g.setSplit = (dec) => { const v = validSplit(g.word, g.p, dec); if (v.ok) { g.split = dec; g.trace.push({ kind: 'split', split: dec, say: 'Split: ' + showSplit(dec) + '.' }); } return v; };
    g.chooseI = (i) => {
      const w = pump(g.split, i), inL = L.member(w);
      g.i = i; g.over = true; g.studentWins = !inL;
      g.trace.push({ kind: 'pump', i, pumped: w, inL, say: 'With i = ' + i + ': u v' + i + ' x y' + i + ' z = ' + show(w) + (inL ? ' is still in the language; the adversary survives this round.' : ' is not in the language; the student wins.') });
      return { pumped: w, inL, studentWins: !inL };
    };
    if (opts.word) g.chooseWord(opts.word);
    return g;
  }

  // ---------- closure constructions ----------
  // Rename every nonterminal of each grammar apart (suffixes 1 and 2), so the two sets do not mix.
  function renameApart(G, tag, avoid) {
    const map = new Map();
    for (const A of G.nonterminals) {
      let nm = A + tag;
      while (avoid.has(nm)) nm += tag;
      avoid.add(nm); map.set(A, nm);
    }
    const ren = (s) => (map.has(s) ? map.get(s) : s);
    return { map, prods: G.productions.map((p) => [ren(p.A), p.rhs.map(ren)]), start: map.get(G.start) };
  }
  function combine(kind, G1, G2) {
    const g = T.grammar, trace = [];
    const avoid = new Set([...G1.terminals, ...(G2 ? G2.terminals : []), ...G1.nonterminals, ...(G2 ? G2.nonterminals : [])]);
    const a = renameApart(G1, '1', avoid), b = G2 ? renameApart(G2, '2', avoid) : null;
    trace.push({ kind: 'rename', map: [...a.map].concat(b ? [...b.map] : []), say: 'Rename nonterminals apart: ' + [...a.map].concat(b ? [...b.map] : []).map(([x, y]) => x + '→' + y).join(', ') + ', so no rule of one grammar can be used inside the other.' });
    let S = 'S'; while (avoid.has(S)) S += "'";
    const prods = [];
    if (kind === 'union') { prods.push([S, [a.start]], [S, [b.start]]); trace.push({ kind: 'start', say: 'New start ' + S + ' → ' + a.start + ' | ' + b.start + ': derive from either grammar.' }); }
    if (kind === 'concat') { prods.push([S, [a.start, b.start]]); trace.push({ kind: 'start', say: 'New start ' + S + ' → ' + a.start + ' ' + b.start + ': a word of the first followed by a word of the second.' }); }
    if (kind === 'star') { prods.push([S, [a.start, S]], [S, []]); trace.push({ kind: 'start', say: 'New start ' + S + ' → ' + a.start + ' ' + S + ' | ε: any number of words of the language in a row.' }); }
    prods.push(...a.prods, ...(b ? b.prods : []));
    const terms = [...new Set([...G1.terminals, ...(G2 ? G2.terminals : [])])];
    const G = g.make(S, prods, { nonterminals: [S, ...a.map.values(), ...(b ? b.map.values() : [])], terminals: terms, tokens: terms });
    trace.push({ kind: 'done', say: 'The new grammar has ' + G.productions.length + ' rules.' });
    return { grammar: G, trace };
  }
  const union = (G1, G2) => combine('union', G1, G2);
  const concat = (G1, G2) => combine('concat', G1, G2);
  const star = (G) => combine('star', G, null);
  // Intersection with a regular language: grammar → top-down PDA → product with the DFA (and back to a
  // grammar when asked). Context-free languages are closed under this, though not under intersection.
  function intersectRegular(G, D, opts) {
    const P = T.pda, trace = [];
    const a = P.fromCFGTopDown(G);
    trace.push({ kind: 'pda', say: 'Turn the grammar into a PDA (top-down construction).' }, ...a.trace.map((s) => Object.assign({ sub: 'cfg-to-pda' }, s)));
    const b = P.productDFA(a.pda, D);
    trace.push({ kind: 'product', say: 'Run the PDA and the DFA side by side.' }, ...b.trace.map((s) => Object.assign({ sub: 'product' }, s)));
    const out = { pda: b.pda, trace };
    if (opts && opts.grammar) { const c = P.toCFG(b.pda); out.grammar = c.grammar; trace.push({ kind: 'grammar', say: 'Convert the product PDA back to a grammar.' }); }
    return out;
  }
  // Two context-free languages whose intersection aⁿbⁿcⁿ is not context-free.
  function intersectionDemo(n, p) {
    const g = T.grammar, trace = [];
    n = n || 9;
    const G1 = g.parse('S -> X C\nX -> a X b | ε\nC -> c C | ε'), G2 = g.parse('S -> A Y\nA -> a A | ε\nY -> b Y c | ε');
    const w1 = g.language(G1, n).map((w) => w.join('')), w2 = g.language(G2, n).map((w) => w.join(''));
    const s2 = new Set(w2), both = w1.filter((w) => s2.has(w));
    trace.push({ kind: 'first', grammar: G1, words: w1, say: 'L1 = aⁿbⁿcᵐ (as many a as b, any c) is context-free: ' + g.toString(G1).replace(/\n/g, '; ') + '.' });
    trace.push({ kind: 'second', grammar: G2, words: w2, say: 'L2 = aᵐbⁿcⁿ (any a, as many b as c) is context-free: ' + g.toString(G2).replace(/\n/g, '; ') + '.' });
    trace.push({ kind: 'both', words: both, say: 'Words in both up to length ' + n + ': ' + both.map(show).join(', ') + ', exactly aⁿbⁿcⁿ.' });
    const G = game('anbncn', { p: p || 3 });
    G.chooseWord(byId('anbncn').sample(G.p));
    const r = adversarySplit('anbncn', G.word, G.p);
    trace.push({ kind: 'game', word: G.word, tried: r.tried, say: 'The pumping game on ' + show(G.word) + ' with p = ' + G.p + ': none of the ' + r.tried + ' splits survives, so aⁿbⁿcⁿ is not context-free, and context-free languages are not closed under intersection.' });
    return { G1, G2, words1: w1, words2: w2, both, game: r, trace };
  }

  T.cfpump = { catalogue, byId, splits, pump, validSplit, refute, adversarySplit, challengerI, game,
    renameApart, union, concat, star, intersectRegular, intersectionDemo, blocks };
})();
