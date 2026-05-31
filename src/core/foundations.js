// Foundations: strings over an alphabet, finite languages, relations and their closures, partitions,
// the diagonal argument, pigeonhole and induction. Everything is finite and exact, so a scene can show
// every element; the infinite objects (Σ*, L*) are explored up to a length bound the caller chooses.
// Every construction returns its result and a trace of steps { kind, say, ...data }.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const F = T.Found = {};

  // Symbols are single characters (code points), so a string is a JS string and Array.from splits it.
  const chars = F.chars = (w) => Array.from(w);
  const show = F.show = (w) => (w === '' ? 'ε' : w);
  const showSet = F.showSet = (xs) => (xs.length ? '{' + xs.map(show).join(', ') + '}' : '∅');

  // A seeded generator for presets and tests (xorshift32): the same seed gives the same sequence.
  F.rng = function (seed) {
    let s = (seed >>> 0) || 1;
    const r = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
    r.int = (n) => Math.floor(r() * n);
    r.pick = (a) => a[Math.floor(r() * a.length)];
    return r;
  };

  // ---------------------------------------------------------------- strings

  F.str = {
    length: (w) => chars(w).length,
    reverse: (w) => chars(w).reverse().join(''),
    power: (w, n) => w.repeat(n),
    count: (w, a) => chars(w).filter((c) => c === a).length,
    prefixes: (w) => { const c = chars(w); return c.map((_, i) => c.slice(0, i).join('')).concat([w]); },
    suffixes: (w) => { const c = chars(w); return c.map((_, i) => c.slice(i).join('')).concat(['']); },
    // all distinct substrings in shortlex order (ε first)
    substrings: (w) => {
      const c = chars(w), out = new Set(['']);
      for (let i = 0; i < c.length; i++) for (let j = i + 1; j <= c.length; j++) out.add(c.slice(i, j).join(''));
      return [...out].sort(shortlexCmp);
    },
    isPrefix: (u, w) => w.startsWith(u),
    isSuffix: (u, w) => w.endsWith(u),
    isSubstring: (u, w) => w.includes(u),
    // subsequence: u's symbols appear in w in order, not necessarily together
    isSubsequence: (u, w) => { const a = chars(u); let i = 0; for (const c of chars(w)) if (i < a.length && a[i] === c) i++; return i === a.length; },
    isPalindrome: (w) => { const c = chars(w); return c.join('') === c.slice().reverse().join(''); },
  };

  // ---------------------------------------------------------------- shortlex order on Σ*

  // Shortlex: shorter strings first, equal lengths in dictionary order of the alphabet as given.
  function shortlexCmp(a, b, order) {
    const x = chars(a), y = chars(b);
    if (x.length !== y.length) return x.length - y.length;
    for (let i = 0; i < x.length; i++) {
      if (x[i] === y[i]) continue;
      if (order) return order.indexOf(x[i]) - order.indexOf(y[i]);
      return x[i] < y[i] ? -1 : 1;
    }
    return 0;
  }
  F.shortlexCmp = shortlexCmp;
  F.sortShortlex = (ws, order) => ws.slice().sort((a, b) => shortlexCmp(a, b, order));

  // Every string over the alphabet of length at most maxLen, in shortlex order.
  F.sigmaStar = function (alphabet, maxLen) {
    const out = [''];
    let level = [''];
    for (let n = 1; n <= maxLen; n++) {
      const next = [];
      for (const w of level) for (const a of alphabet) next.push(w + a);
      for (const w of next) out.push(w);
      level = next;
    }
    return out;
  };
  // Lazy version for large bounds: calls fn(w) for each string; stop early by returning false.
  F.eachString = function (alphabet, maxLen, fn) {
    const k = alphabet.length, idx = [];
    for (let n = 0; n <= maxLen; n++) {
      idx.length = n; idx.fill(0);
      for (;;) {
        if (fn(idx.map((i) => alphabet[i]).join('')) === false) return false;
        let p = n - 1;
        while (p >= 0 && idx[p] === k - 1) idx[p--] = 0;
        if (p < 0) break;
        idx[p]++;
      }
      if (k === 0) break; // over the empty alphabet only ε exists
    }
    return true;
  };
  // The n-th string (from 0) in shortlex order, and back: bijective base-k numbering.
  F.nthString = function (alphabet, n) {
    const k = alphabet.length, out = [];
    if (k === 0) { if (n !== 0) throw new Error('over the empty alphabet only ε exists'); return ''; }
    while (n > 0) { n -= 1; out.push(alphabet[n % k]); n = Math.floor(n / k); }
    return out.reverse().join('');
  };
  F.indexOfString = function (alphabet, w) {
    const k = alphabet.length;
    let n = 0;
    for (const c of chars(w)) {
      const d = alphabet.indexOf(c);
      if (d < 0) throw new Error(`symbol ${c} is not in the alphabet`);
      n = n * k + d + 1;
    }
    return n;
  };
  // How many strings of length exactly n, and of length at most n (BigInt, as these grow fast).
  F.countStrings = (k, n) => BigInt(k) ** BigInt(n);
  F.countUpTo = (k, n) => { let s = 0n; for (let i = 0; i <= n; i++) s += BigInt(k) ** BigInt(i); return s; };

  // ---------------------------------------------------------------- finite languages

  // A finite language is an array of strings; results are deduplicated and in shortlex order.
  const lang = (xs) => F.sortShortlex([...new Set(xs)]);
  F.lang = lang;
  F.union = (A, B) => lang([...A, ...B]);
  F.intersect = (A, B) => { const b = new Set(B); return lang(A.filter((w) => b.has(w))); };
  F.minus = (A, B) => { const b = new Set(B); return lang(A.filter((w) => !b.has(w))); };
  F.reverseLang = (A) => lang(A.map(F.str.reverse));
  // complement relative to Σ^{≤n}
  F.complementUpTo = (A, alphabet, n) => F.minus(F.sigmaStar(alphabet, n), A);

  // Concatenation AB = { xy : x ∈ A, y ∈ B }, tracing each pair (a scene can draw the grid).
  F.concat = function (A, B, maxLen = Infinity) {
    const trace = [], out = new Set();
    for (const x of A) for (const y of B) {
      const w = x + y;
      if (chars(w).length > maxLen) continue;
      const fresh = !out.has(w);
      out.add(w);
      trace.push({ kind: 'pair', x, y, w, fresh, say: `${show(x)} · ${show(y)} = ${show(w)}${fresh ? '' : ' (already there)'}` });
    }
    const result = lang([...out]);
    trace.push({ kind: 'done', result, say: `The concatenation has ${result.length} string${result.length === 1 ? '' : 's'}.` });
    return { result, trace };
  };

  // A^n: A^0 = {ε}, A^{k+1} = A^k A.
  F.power = function (A, n, maxLen = Infinity) {
    let cur = [''];
    const trace = [{ kind: 'power', k: 0, set: cur, say: 'A⁰ = {ε}: the only way to concatenate zero strings is the empty string.' }];
    for (let k = 1; k <= n; k++) {
      cur = F.concat(cur, A, maxLen).result;
      trace.push({ kind: 'power', k, set: cur, say: `A^${k} = A^${k - 1} · A has ${cur.length} string${cur.length === 1 ? '' : 's'}.` });
    }
    return { result: cur, trace };
  };

  // A* cut at length maxLen: A⁰ ∪ A¹ ∪ ... until no new string of length ≤ maxLen appears.
  // (If A contains only ε or nothing, A* = {ε}: the loop stops at once.)
  F.star = function (A, maxLen) {
    const all = new Set(['']);
    const trace = [{ kind: 'power', k: 0, added: [''], say: 'Start with A⁰ = {ε}; ε is in every star.' }];
    let cur = [''];
    const nonEmpty = A.filter((w) => w !== '');
    for (let k = 1; cur.length; k++) {
      const next = F.concat(cur, nonEmpty, maxLen).result;
      const added = next.filter((w) => !all.has(w));
      added.forEach((w) => all.add(w));
      trace.push({ kind: 'power', k, added, say: added.length ? `Concatenating ${k} pieces adds ${showSet(added.slice(0, 8))}${added.length > 8 ? ' …' : ''}.` : `Concatenating ${k} pieces adds nothing new of length ≤ ${maxLen}.` });
      cur = added;
    }
    return { result: lang([...all]), trace };
  };
  F.plus = (A, maxLen) => { const s = F.concat(A, F.star(A, maxLen).result, maxLen); return { result: s.result, trace: s.trace }; };

  // ---------------------------------------------------------------- relations

  // A relation on a finite domain is an array of pairs [x, y]. Keys use JSON so any values work.
  const pk = (x, y) => JSON.stringify([x, y]);
  const relSet = (R) => new Set(R.map(([x, y]) => pk(x, y)));
  const fromSet = (domain, S) => {
    const out = [];
    for (const x of domain) for (const y of domain) if (S.has(pk(x, y))) out.push([x, y]);
    return out;
  };
  F.rel = {
    has: (R, x, y) => R.some((p) => p[0] === x && p[1] === y),
    isReflexive: (D, R) => { const S = relSet(R); return D.every((x) => S.has(pk(x, x))); },
    isIrreflexive: (D, R) => { const S = relSet(R); return D.every((x) => !S.has(pk(x, x))); },
    isSymmetric: (D, R) => { const S = relSet(R); return R.every(([x, y]) => S.has(pk(y, x))); },
    isAntisymmetric: (D, R) => { const S = relSet(R); return R.every(([x, y]) => x === y || !S.has(pk(y, x))); },
    isTransitive: (D, R) => { const S = relSet(R); return R.every(([x, y]) => R.every(([y2, z]) => y2 !== y || S.has(pk(x, z)))); },
  };
  F.rel.isEquivalence = (D, R) => F.rel.isReflexive(D, R) && F.rel.isSymmetric(D, R) && F.rel.isTransitive(D, R);
  F.rel.isPartialOrder = (D, R) => F.rel.isReflexive(D, R) && F.rel.isAntisymmetric(D, R) && F.rel.isTransitive(D, R);
  // Report which property fails and the pairs that witness it, for the "is it an equivalence?" quiz.
  F.rel.why = function (D, R) {
    const S = relSet(R), out = [];
    for (const x of D) if (!S.has(pk(x, x))) { out.push({ prop: 'reflexive', pairs: [[x, x]], say: `Not reflexive: (${x}, ${x}) is missing.` }); break; }
    for (const [x, y] of R) if (!S.has(pk(y, x))) { out.push({ prop: 'symmetric', pairs: [[x, y]], say: `Not symmetric: (${x}, ${y}) is there but (${y}, ${x}) is not.` }); break; }
    outer: for (const [x, y] of R) for (const [y2, z] of R) if (y2 === y && !S.has(pk(x, z))) { out.push({ prop: 'transitive', pairs: [[x, y], [y, z]], say: `Not transitive: (${x}, ${y}) and (${y}, ${z}) are there but (${x}, ${z}) is not.` }); break outer; }
    return out;
  };

  F.reflexiveClosure = function (D, R) {
    const S = relSet(R), trace = [];
    for (const x of D) if (!S.has(pk(x, x))) { S.add(pk(x, x)); trace.push({ kind: 'add', pair: [x, x], say: `Add (${x}, ${x}): every element must be related to itself.` }); }
    return { result: fromSet(D, S), trace };
  };
  F.symmetricClosure = function (D, R) {
    const S = relSet(R), trace = [];
    for (const [x, y] of R) if (!S.has(pk(y, x))) { S.add(pk(y, x)); trace.push({ kind: 'add', pair: [y, x], because: [x, y], say: `Add (${y}, ${x}) to mirror (${x}, ${y}).` }); }
    return { result: fromSet(D, S), trace };
  };
  // Warshall: after round k, (i, j) is in the relation when j is reachable from i through intermediate
  // elements among the first k. Each added pair records the two pairs through k that justify it.
  F.transitiveClosure = function (D, R) {
    const n = D.length, ix = new Map(D.map((x, i) => [JSON.stringify(x), i]));
    const M = D.map(() => new Array(n).fill(false));
    for (const [x, y] of R) M[ix.get(JSON.stringify(x))][ix.get(JSON.stringify(y))] = true;
    const trace = [{ kind: 'matrix', k: -1, matrix: M.map((r) => r.slice()), say: 'Start from the matrix of the relation itself.' }];
    for (let k = 0; k < n; k++) {
      const added = [];
      for (let i = 0; i < n; i++) if (M[i][k]) for (let j = 0; j < n; j++) if (M[k][j] && !M[i][j]) {
        M[i][j] = true;
        added.push([D[i], D[j]]);
        trace.push({ kind: 'add', k: D[k], pair: [D[i], D[j]], via: [[D[i], D[k]], [D[k], D[j]]], say: `Through ${D[k]}: (${D[i]}, ${D[k]}) and (${D[k]}, ${D[j]}) give (${D[i]}, ${D[j]}).` });
      }
      trace.push({ kind: 'matrix', k: D[k], added, matrix: M.map((r) => r.slice()), say: added.length ? `Round ${k + 1} (paths may pass through ${D[k]}) added ${added.length} pair${added.length === 1 ? '' : 's'}.` : `Round ${k + 1} (through ${D[k]}) adds nothing.` });
    }
    const out = [];
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (M[i][j]) out.push([D[i], D[j]]);
    return { result: out, trace };
  };
  // Reflexive-transitive closure R*, and the smallest equivalence containing R.
  F.reflexiveTransitiveClosure = (D, R) => {
    const a = F.reflexiveClosure(D, R), b = F.transitiveClosure(D, a.result);
    return { result: b.result, trace: a.trace.concat(b.trace) };
  };
  F.equivalenceClosure = (D, R) => {
    const a = F.reflexiveClosure(D, R), b = F.symmetricClosure(D, a.result), c = F.transitiveClosure(D, b.result);
    return { result: c.result, trace: a.trace.concat(b.trace, c.trace) };
  };
  // Composition R∘S = { (x, z) : (x, y) ∈ R and (y, z) ∈ S } (R first, then S).
  F.compose = (R, S) => {
    const out = new Map();
    for (const [x, y] of R) for (const [y2, z] of S) if (y === y2) out.set(pk(x, z), [x, z]);
    return [...out.values()];
  };

  // ---------------------------------------------------------------- partitions

  // The classes of an equivalence relation, each in domain order. Throws if R is not an equivalence.
  F.classes = function (D, R) {
    if (!F.rel.isEquivalence(D, R)) throw new Error(F.rel.why(D, R).map((w) => w.say).join(' ') || 'not an equivalence relation');
    const S = relSet(R), seen = new Set(), out = [], trace = [];
    for (const x of D) {
      if (seen.has(JSON.stringify(x))) continue;
      const cls = D.filter((y) => S.has(pk(x, y)));
      cls.forEach((y) => seen.add(JSON.stringify(y)));
      out.push(cls);
      trace.push({ kind: 'class', rep: x, members: cls, say: `[${x}] = {${cls.join(', ')}}` });
    }
    return { result: out, trace };
  };
  // Classes of the kernel of a function: x ~ y when key(x) = key(y).
  F.classesBy = function (D, key) {
    const m = new Map();
    for (const x of D) { const k = JSON.stringify(key(x)); if (!m.has(k)) m.set(k, []); m.get(k).push(x); }
    return [...m.values()];
  };
  F.partitionToRelation = (P) => P.flatMap((b) => b.flatMap((x) => b.map((y) => [x, y])));
  F.isPartition = (D, P) => {
    const seen = new Set();
    for (const b of P) { if (!b.length) return false; for (const x of b) { const k = JSON.stringify(x); if (seen.has(k)) return false; seen.add(k); } }
    return seen.size === D.length && D.every((x) => seen.has(JSON.stringify(x)));
  };
  // P refines Q when every block of P lies inside one block of Q.
  F.refines = (P, Q) => P.every((b) => Q.some((c) => b.every((x) => c.includes(x))));
  // Number of partitions of an n-set (Bell numbers), for the "how many equivalences" question.
  F.bell = (n) => {
    let row = [1n];
    for (let i = 0; i < n; i++) { const next = [row[row.length - 1]]; for (const v of row) next.push(next[next.length - 1] + v); row = next; }
    return row[0];
  };

  // ---------------------------------------------------------------- functions

  F.fn = {
    isInjective: (D, f) => new Set(D.map((x) => JSON.stringify(f(x)))).size === D.length,
    isSurjective: (D, C, f) => { const img = new Set(D.map((x) => JSON.stringify(f(x)))); return C.every((y) => img.has(JSON.stringify(y))); },
  };
  F.fn.isBijective = (D, C, f) => F.fn.isInjective(D, f) && F.fn.isSurjective(D, C, f);
  F.powerset = (S) => {
    const out = [[]];
    for (const x of S) { const n = out.length; for (let i = 0; i < n; i++) out.push(out[i].concat([x])); }
    const key = (b) => b.map((x) => S.indexOf(x));
    return out.sort((a, b) => {
      if (a.length !== b.length) return a.length - b.length;
      const x = key(a), y = key(b);
      for (let i = 0; i < x.length; i++) if (x[i] !== y[i]) return x[i] - y[i];
      return 0;
    });
  };

  // ---------------------------------------------------------------- diagonalisation

  // rows: an enumeration of sequences, each an array or a function i -> value. The diagonal sequence
  // takes row i's i-th entry and changes it, so it differs from row i at position i, whatever the rows.
  // flip(v) must return something different from v (default: 0 ↔ 1, and for digits 5 ↔ 4).
  F.diagonal = function (rows, n, flip) {
    flip = flip || ((v) => (v === 0 ? 1 : v === 1 ? 0 : v === 5 ? 4 : typeof v === 'number' ? 5 : v === 'a' ? 'b' : 'a'));
    const at = (r, i) => (typeof r === 'function' ? r(i) : r[i]);
    n = Math.min(n === undefined ? rows.length : n, rows.length);
    const diag = [], trace = [];
    for (let i = 0; i < n; i++) {
      const v = at(rows[i], i), d = flip(v);
      if (d === v) throw new Error('flip must change the value');
      diag.push(d);
      trace.push({ kind: 'diag', row: i, col: i, was: v, now: d, say: `Row ${i} has ${v} at position ${i}; the diagonal sequence puts ${d} there, so it is not row ${i}.` });
    }
    trace.push({ kind: 'done', diag, say: `The diagonal sequence ${diag.join('')}… differs from each listed row on the diagonal, so the list missed it.` });
    // differsAt[i] = i for every row: the witness position
    return { diag, differsAt: diag.map((_, i) => i), trace };
  };

  // Cantor for sets: given f : A → P(A) (as a function to arrays), D = { x : x ∉ f(x) } differs from
  // every f(x) on the element x itself.
  F.cantorSet = function (A, f) {
    const trace = [], D = [];
    for (const x of A) {
      const fx = f(x), inside = fx.includes(x);
      if (!inside) D.push(x);
      trace.push({ kind: 'diag', x, fx, inside, say: inside ? `${x} ∈ f(${x}), so leave ${x} out of D; then D ≠ f(${x}).` : `${x} ∉ f(${x}), so put ${x} into D; then D ≠ f(${x}).` });
    }
    trace.push({ kind: 'done', D, say: `D = {${D.join(', ')}} is no f(x): f is not onto the power set.` });
    return { D, trace };
  };

  // ---------------------------------------------------------------- pigeonhole and induction

  // Place items in holes by hole(item); report the first collision (two items in one hole). With more
  // items than holes a collision is certain; the trace shows each placement.
  F.pigeonhole = function (items, hole) {
    const where = new Map(), trace = [];
    for (let i = 0; i < items.length; i++) {
      const h = JSON.stringify(hole(items[i]));
      if (where.has(h)) {
        const j = where.get(h);
        trace.push({ kind: 'collide', item: items[i], other: items[j], hole: hole(items[i]), say: `${items[i]} lands in hole ${hole(items[i])}, where ${items[j]} already sits.` });
        return { found: true, pair: [items[j], items[i]], indices: [j, i], hole: hole(items[i]), trace };
      }
      where.set(h, i);
      trace.push({ kind: 'place', item: items[i], hole: hole(items[i]), say: `${items[i]} goes into hole ${hole(items[i])}.` });
    }
    return { found: false, trace };
  };
  // Generalised pigeonhole: n items in k holes force some hole to hold at least ⌈n/k⌉.
  F.pigeonBound = (n, k) => Math.ceil(n / k);

  // Check an induction proof numerically: P(n) must hold for the base cases, and for each k in range the
  // step "P(k) (and earlier, for strong induction) implies P(k+1)" is checked by evaluating P.
  // A failed step names the first k where the claim breaks, which is what a student needs to see.
  F.induction = function ({ P, base = 0, bases = 1, upto = 20, strong = false, say }) {
    const trace = [], name = say || ((n) => `P(${n})`);
    for (let n = base; n < base + bases; n++) {
      const ok = !!P(n);
      trace.push({ kind: 'base', n, ok, say: `Base case: ${name(n)} is ${ok ? 'true' : 'false'}.` });
      if (!ok) return { ok: false, failAt: n, trace };
    }
    for (let k = base + bases - 1; k < upto; k++) {
      const ok = !!P(k + 1);
      trace.push({ kind: 'step', from: strong ? [base, k] : [k, k], to: k + 1, ok, say: ok ? `From ${strong ? `${name(base)} … ${name(k)}` : name(k)} we reach ${name(k + 1)}: it holds.` : `${name(k + 1)} fails, so the step from ${k} to ${k + 1} cannot be proved.` });
      if (!ok) return { ok: false, failAt: k + 1, trace };
    }
    trace.push({ kind: 'done', say: `Checked up to n = ${upto}; induction extends this to every n ≥ ${base}.` });
    return { ok: true, trace };
  };
})();
