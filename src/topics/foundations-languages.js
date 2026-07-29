// Languages: sets of strings. Union, intersection and difference sort strings by membership; concatenation
// is a grid of every x from A followed by every y from B (with repeats found and ∅, {ε} as the edge
// cases); and the star is built level by level, A⁰ = {ε}, A¹, A², …, cut at a length so it fits.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found, Geo = T.geom;
  const H = K.rel;

  T.family({ id: 'found-languages', part: 'foundations', order: 90, title: 'Languages and their operations', blurb: 'A language is any set of strings. Besides the set operations there are two of its own: concatenation glues a string of one to a string of the other, and the star glues any number of pieces.' });

  const show = F.show;
  const setText = (xs) => (xs.length ? '{' + xs.map(show).join(', ') + '}' : '∅');
  const chipW = (w) => Math.max(40, Geo.textWidth(show(w), 15, { mono: true }) + 16);
  /** A row of chips (one per string), with a label in front; returns items and the width */
  const chips = (P, list, x0, y, o) => {
    o = o || {};
    const items = [];
    let x = x0;
    if (!list.length && o.emptyKey !== false) items.push({ key: P + ':empty', kind: 'cell', x, y, w: 40, h: 34, text: '∅', cls: 'empty', size: 15 });
    list.forEach((w, i) => {
      const cw = chipW(w);
      items.push(Object.assign({ key: P + ':' + (w === '' ? 'ε' : w), kind: 'cell', x, y, w: cw, h: 34, text: show(w), cls: 'mono ' + ((o.cls && o.cls(w, i)) || ''), size: 15, rx: 17, pick: !!o.pick }, o.extra ? o.extra(w, i) : {}));
      x += cw + 8;
    });
    return { items, w: x - x0 };
  };
  const lbl = (key, x, y, text) => ({ key, kind: 'text', x, y: y + 22, text, anchor: 'end', cls: 'strong', size: 16 });
  const listCheck = (label) => (v) => (new Set(v).size !== v.length ? label + ': a string is listed twice' : v.some((w) => [...w].length > 4) ? label + ': at most 4 symbols per string' : null);

  const OPS = {
    concat: { label: 'concatenation AB' },
    union: { label: 'union A ∪ B' },
    inter: { label: 'intersection A ∩ B' },
    minus: { label: 'difference A − B' },
  };
  T.topic({
    id: 'lang-ops', family: 'found-languages', order: 10, title: 'Operations on languages',
    blurb: 'Union, intersection and difference treat languages as plain sets. Concatenation AB fills a grid with every x from A followed by every y from B, and repeats collapse.',
    inputs: [
      { id: 'A', kind: 'list', label: 'A', def: ['a', 'ab'], max: 4, check: listCheck('A') },
      { id: 'B', kind: 'list', label: 'B', def: ['b', 'ε'], max: 4, check: listCheck('B') },
      { id: 'op', kind: 'choice', label: 'Operation', def: 'concat', options: Object.entries(OPS).map(([value, o]) => ({ value, label: o.label })) },
    ],
    presets: [
      { label: '{a, ab} · {b, ε}: a repeat', values: { A: ['a', 'ab'], B: ['b', ''], op: 'concat' } },
      { label: '{0, 1} · {0, 1}', values: { A: ['0', '1'], B: ['0', '1'], op: 'concat' } },
      { label: 'A · ∅ = ∅', values: { A: ['a', 'b'], B: [], op: 'concat' } },
      { label: '{ε} · B = B', values: { A: [''], B: ['ab', 'b'], op: 'concat' } },
      { label: 'Union', values: { A: ['a', 'ab', 'ε'], B: ['ab', 'b'], op: 'union' } },
      { label: 'Difference', values: { A: ['a', 'ab', 'ε'], B: ['ab', 'b'], op: 'minus' } },
    ],
    counters: [{ id: 'pairs', label: 'pairs tried' }, { id: 'size', label: 'strings in the result' }],
    run(inp) {
      const A = F.lang(inp.A), B = F.lang(inp.B), op = inp.op;
      const F2 = new T.Frames(['pairs', 'size']);
      if (op !== 'concat') {
        const all = F.union(A, B);
        const res = op === 'union' ? F.union(A, B) : op === 'inter' ? F.intersect(A, B) : F.minus(A, B);
        const decided = new Map();
        const scene = (hot) => {
          const a = chips('A', A, 0, 0, { cls: (w) => (w === hot ? 'hot' : decided.has(w) ? (decided.get(w) ? 'good' : 'gone') : 'part-x') });
          const b = chips('B', B, 0, 56, { cls: (w) => (w === hot ? 'hot' : decided.has(w) ? (decided.get(w) ? 'good' : 'gone') : 'part-z') });
          const r = chips('R', all.filter((w) => decided.get(w)), 0, 140, { extra: (w) => ({ enter: 'from', src: A.includes(w) ? 'A:' + (w === '' ? 'ε' : w) : 'B:' + (w === '' ? 'ε' : w) }), cls: () => 'good' });
          return a.items.concat(b.items, r.items, [lbl('la', -14, 0, 'A'), lbl('lb', -14, 56, 'B'), lbl('lr', -14, 140, OPS[op].label.split(' ').slice(1).join(' '))]);
        };
        F2.add({ items: scene(), say: 'A = ' + setText(A) + ' and B = ' + setText(B) + '. ' + OPS[op].label.split(' ')[0].replace(/^./, (c) => c.toUpperCase()) + ' keeps each string according to which of them it is in.', hl: { def: ['0', '1'] } });
        for (const w of all) {
          const inA = A.includes(w), inB = B.includes(w), keep = res.includes(w);
          decided.set(w, keep);
          if (keep) F2.count('size');
          F2.add({ items: scene(w), say: show(w) + ' is ' + (inA && inB ? 'in both' : inA ? 'only in A' : 'only in B') + ', so it is ' + (keep ? 'kept.' : 'left out.') + (w === '' ? ' (ε is a string like any other here; a language may or may not contain it.)' : ''), hl: { def: ['2'] } });
        }
        F2.add({ items: scene(), say: OPS[op].label.split(' ').slice(1).join(' ') + ' = ' + setText(res) + '.', hl: { def: ['2'] }, mark: 'result' });
        return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The languages', text: ['A = ' + setText(A), 'B = ' + setText(B), op === 'union' ? 'A ∪ B = {w : w ∈ A or w ∈ B}' : op === 'inter' ? 'A ∩ B = {w : w ∈ A and w ∈ B}' : 'A − B = {w : w ∈ A, w ∉ B}'].join('\n') }] } };
      }
      // concatenation: a grid of A (rows) by B (columns)
      const cw = Math.max(64, ...A.flatMap((x) => B.map((y) => chipW(x + y) + 10)));
      const made = new Map(), seen = new Set();
      const narrow = H.narrow();
      const grid = (hot) => {
        const rows = A.length && B.length ? A.map((x) => B.map((y) => show(x + y))) : [[]];
        const t = K.table.draw({ rows, rowHead: A.length ? A.map(show) : [' '], colHead: B.length ? B.map(show) : [' '], corner: 'x · y', cw, ch: 42, mono: true, size: 16, prefix: 'cg', skip: (r, c) => !A.length || !B.length || !made.has(r + ',' + c), cls: (r, c) => ((hot && hot[0] === r && hot[1] === c ? 'hot ' : '') + (made.get(r + ',' + c) === 'dup' ? 'gone' : 'good')) });
        for (const it of t.items) if (/^cg:\d+,\d+$/.test(it.key)) { const [r, c] = it.key.slice(3).split(',').map(Number); it.enter = 'from'; it.src = ['cg:rh:' + r, 'cg:ch:' + c]; }
        return t;
      };
      const t0 = grid();
      const ry = narrow ? t0.box.y + t0.box.h + 40 : t0.box.y + 40;
      const rx = narrow ? 50 : t0.box.x + t0.box.w + 90;
      const result = () => {
        const list = F.lang([...seen]);
        const c = chips('AB', list, rx, ry, { cls: () => 'good', extra: (w) => { const r = A.findIndex((x) => B.some((y) => x + y === w)), cc = B.findIndex((y) => A[r] + y === w); return { enter: 'from', src: 'cg:' + r + ',' + cc }; } });
        return c.items.concat([{ key: 'lab', kind: 'text', x: rx, y: ry - 14, text: 'AB = ' + (list.length ? '' : '∅'), cls: 'strong', size: 16 }]);
      };
      F2.add({ items: grid().items.concat(result()), say: 'A = ' + setText(A) + ' labels the rows and B = ' + setText(B) + ' the columns. The cell in row x, column y will hold xy.', hl: { def: ['0', '1'] }, meta: { count: F.concat(A, B).result.length, cells: A.length * B.length } });
      if (!A.length || !B.length) {
        F2.add({ items: grid().items.concat(result()), say: (A.length ? 'B' : 'A') + ' is empty, so there is no ' + (A.length ? 'column' : 'row') + ' and no pair at all: the concatenation with ∅ is ∅. (Not {ε}: ∅ has no string to contribute.)', hl: { def: ['2'] }, mark: 'empty' });
      } else {
        A.forEach((x, r) => B.forEach((y, c) => {
          const w = x + y, dup = seen.has(w);
          made.set(r + ',' + c, dup ? 'dup' : 'new');
          seen.add(w);
          F2.count('pairs').set('size', seen.size);
          F2.add({ items: grid([r, c]).items.concat(result()), say: show(x) + ' · ' + show(y) + ' = ' + show(w) + (dup ? ': already in AB, and a set holds it only once.' : '.') + (y === '' ? ' Gluing on ε changes nothing.' : x === '' ? ' ε in front changes nothing.' : ''), hl: { def: ['2'] } });
        }));
        const n = seen.size, cells = A.length * B.length;
        F2.add({ items: grid().items.concat(result()), say: 'AB = ' + setText(F.lang([...seen])) + ': ' + n + ' string' + (n === 1 ? '' : 's') + ' from ' + cells + ' pairs' + (n < cells ? ', fewer because different pairs glued into the same string.' : '.') + (A.length === 1 && A[0] === '' ? ' With A = {ε}, AB = B.' : B.includes('') ? ' Since ε ∈ B, every string of A is in AB.' : ''), hl: { def: ['3'] }, mark: 'result' });
      }
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Concatenation', text: ['A = ' + setText(A), 'B = ' + setText(B), 'AB = { xy : x ∈ A, y ∈ B }', '|AB| ≤ |A| · |B|,  A∅ = ∅,  A{ε} = A'].join('\n') }] } };
    },
    predict: [
      { at: (f, i, fr, inp) => i === 0 && inp.op === 'concat' && f.meta.cells > 0, pick: 'option', options: (fr) => [...new Set([fr[0].meta.count, fr[0].meta.cells, fr[0].meta.cells + 1, Math.max(1, fr[0].meta.count - 1)])].sort((a, b) => a - b).map(String), ask: 'How many strings will AB have?', answer: (fr) => String(fr[0].meta.count), explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr, inp) => i === 0 && inp.op === 'concat' && f.meta.cells === 0, pick: 'option', options: ['∅', '{ε}', 'A'], ask: 'What is the concatenation with the empty language?', answer: () => '∅', explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr, inp) => i === 0 && inp.op !== 'concat', pick: 'option', options: (fr) => { const v = fr[fr.length - 1].counters.size; return [...new Set([Math.max(0, v - 1), v, v + 1, v + 2])].map(String); }, ask: 'How many strings will the result have?', answer: (fr) => String(fr[fr.length - 1].counters.size), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What is {a, b} · ∅?', options: ['{a, b}', '{ε}', '∅', '{a, b, ε}'], answer: 2, why: 'A string of AB needs a piece from each, and ∅ has none.' },
      { q: 'What is {ε} · {a, b}?', options: ['{a, b}', '{ε, a, b}', '∅'], answer: 0, why: '{ε} is the identity for concatenation of languages.' },
      { q: '|A| = 3 and |B| = 2. How many strings can AB have?', options: ['Exactly 6', 'At most 6, maybe fewer', 'Exactly 5', 'At least 6'], answer: 1, why: 'Six pairs, but two pairs may glue into the same string, like a · bc and ab · c.' },
      { q: 'Is AB = BA for languages?', options: ['Always', 'Not in general: {a}{b} = {ab} but {b}{a} = {ba}'], answer: 1, why: 'Concatenation of strings is not commutative, so neither is that of languages.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // The star, level by level
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'lang-star', family: 'found-languages', order: 20, title: 'The star, built level by level',
    blurb: 'A* glues together any number of strings of A, zero included: A⁰ = {ε}, then A¹, A², … Watch each level grow from the one before, and see why ∅* = {ε}.',
    inputs: [
      { id: 'A', kind: 'list', label: 'A', def: ['a', 'ba'], max: 4, check: listCheck('A') },
      { id: 'n', kind: 'number', label: 'Up to length', def: 4, min: 1, max: 6 },
    ],
    presets: [
      { label: '{a, ba} up to length 4', values: { A: ['a', 'ba'], n: 4 } },
      { label: '{aa, aaa}: every length but 1', values: { A: ['aa', 'aaa'], n: 6 } },
      { label: '{0, 1}: everything', values: { A: ['0', '1'], n: 3 } },
      { label: '{a, ab, b}: repeats appear', values: { A: ['a', 'ab', 'b'], n: 2 } },
      { label: '∅* = {ε}', values: { A: [], n: 3 } },
      { label: '{ε}* = {ε}', values: { A: [''], n: 3 } },
    ],
    counters: [{ id: 'level', label: 'pieces glued' }, { id: 'size', label: 'strings in A* so far' }],
    run(inp) {
      const A = F.lang(inp.A), n = inp.n;
      const F2 = new T.Frames(['level', 'size']);
      const narrow = H.narrow();
      const per = narrow ? 5 : 8;
      const levels = [];
      const seen = new Set();
      let cur = [''];
      const from = new Map([['', null]]);
      levels.push({ k: 0, list: [''], fresh: [''] });
      seen.add('');
      for (let k = 1; k <= n + 1; k++) {
        const next = [];
        for (const x of cur) for (const y of A) { const w = x + y; if ([...w].length <= n && !next.includes(w)) { next.push(w); if (!from.has(w)) from.set(w, x); } }
        const list = F.lang(next), fresh = list.filter((w) => !seen.has(w));
        if (!list.length && !fresh.length) { levels.push({ k, list, fresh, stop: 'empty' }); break; }
        fresh.forEach((w) => seen.add(w));
        levels.push({ k, list, fresh });
        if (!fresh.length) { levels[levels.length - 1].stop = 'nothing new'; break; }
        cur = list;
      }
      const sup = (k) => String(k).split('').map((d) => '⁰¹²³⁴⁵⁶⁷⁸⁹'[d]).join('');
      const rowsY = (k) => k * 62;
      const keyOf = (k, w) => 'L' + k + ':' + (w === '' ? 'ε' : w);
      const scene = (upto, o) => {
        o = o || {};
        const items = [];
        for (const L of levels.slice(0, upto + 1)) {
          const shown = L.list.slice(0, per);
          const fr = new Set(L.fresh);
          const c = chips('L' + L.k, shown, 0, rowsY(L.k), { cls: (w) => (fr.has(w) ? (o.hot === L.k ? 'hot' : 'good') : 'gone'), extra: (w) => (L.k ? { enter: 'from', src: keyOf(L.k - 1, from.get(w) === null ? '' : from.get(w)) } : {}) });
          items.push(...c.items, lbl('lv' + L.k, -14, rowsY(L.k), 'A' + sup(L.k)));
          if (L.list.length > per) items.push({ key: 'more' + L.k, kind: 'text', x: c.w + 6, y: rowsY(L.k) + 22, text: '+' + (L.list.length - per) + ' more', cls: 'strong', size: 14 });
        }
        return items;
      };
      // the chip a new string grows from must exist in the frame before: fix sources to strings shown
      for (const L of levels) if (L.k) for (const w of L.list) { const p = from.get(w); const prev = levels[L.k - 1]; if (!prev.list.slice(0, per).includes(p)) from.set(w, prev.list[0] === undefined ? '' : prev.list[0]); }
      F2.add({ items: scene(0), say: 'A = ' + setText(A) + '. A* is every string made by gluing together any number of strings from A. Zero pieces give ε, so A⁰ = {ε}, whatever A is.', hl: { def: ['0', '1'] }, meta: {} });
      F2.set('size', 1);
      for (let i = 1; i < levels.length; i++) {
        const L = levels[i];
        F2.set('level', L.k).set('size', seen.size >= 0 ? levels.slice(0, i + 1).reduce((a, x) => a + x.fresh.length, 0) : 0);
        F2.add({ items: scene(i, { hot: L.k }), say: L.stop === 'empty' ? 'A' + sup(L.k) + ' = A' + sup(L.k - 1) + ' · A ' + (A.length ? 'has nothing of length ≤ ' + n + ': every longer piece runs past the cut.' : 'is empty: with no strings in A there is nothing to glue on.') : 'A' + sup(L.k) + ' = A' + sup(L.k - 1) + ' · A: ' + L.list.length + ' string' + (L.list.length === 1 ? '' : 's') + ' of length ≤ ' + n + (L.fresh.length < L.list.length ? ', of which ' + (L.list.length - L.fresh.length) + ' (faded) appeared at an earlier level' : '') + '.' + (L.stop === 'nothing new' ? ' Nothing new, and nothing new can ever come.' : ''), hl: { def: ['1'] }, meta: i === 1 ? { ask: true } : {} });
      }
      const star = F.lang([...seen]);
      const missing = F.sigmaStar([...new Set(A.join(''))], Math.min(n, 3)).filter((w) => !seen.has(w));
      const yy = rowsY(levels.length) + 10;
      const res = chips('S', star.slice(0, per + 2), 0, yy, { cls: () => 'good' });
      F2.add({ items: scene(levels.length - 1).concat(res.items, [lbl('ls', -14, yy, 'A*'), ...(star.length > per + 2 ? [{ key: 'moreS', kind: 'text', x: res.w + 6, y: yy + 22, text: '+' + (star.length - per - 2) + ' more', cls: 'strong', size: 14 }] : [])]), say: 'A* up to length ' + n + ' is the union of the levels: ' + setText(star.slice(0, 10)) + (star.length > 10 ? ' …' : '') + '.' + (!A.length || (A.length === 1 && A[0] === '') ? ' So ' + (A.length ? '{ε}' : '∅') + '* = {ε}: the star always contains ε, even of the empty language.' : missing.length ? ' Not every string is reachable: ' + show(missing[0]) + ' is not in A*.' : ''), hl: { def: ['2', '3'] }, mark: 'star' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The star', text: ['A = ' + setText(A), 'A⁰ = {ε},  Aᵏ⁺¹ = Aᵏ A', 'A* = A⁰ ∪ A¹ ∪ A² ∪ …', 'ε ∈ A* always;  ∅* = {ε}* = {ε}'].join('\n') }] } };
    },
    predict: [
      { at: (f, i) => i === 0, pick: 'option', options: ['Yes', 'No'], ask: 'Is ε in A*, even if ε is not in A?', answer: () => 'Yes', explain: (fr) => fr[0].say },
      { at: (f) => f.meta && f.meta.ask, pick: 'option', options: (fr, i) => { const m = /: (\d+) string/.exec(fr[i + 1].say), v = m ? +m[1] : 0; return [...new Set([Math.max(0, v - 1), v, v + 1, v + 2])].map(String); }, ask: 'How many strings will A² have (within the length cut)?', answer: (fr, i) => { const m = /: (\d+) string/.exec(fr[i + 1].say); return m ? m[1] : '0'; }, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What is ∅*?', options: ['∅', '{ε}', 'Σ*'], answer: 1, why: 'Zero pieces are always allowed, giving ε; with no strings in ∅ there is nothing else.' },
      { q: 'A = {aa, aaa}. Which length is missing from A*?', options: ['0', '1', '5', 'None'], answer: 1, why: 'Every length but 1 is a sum of 2s and 3s (0 being the empty sum).' },
      { q: 'How does A⁺ differ from A*?', options: ['It does not', 'A⁺ needs at least one piece: A⁺ = AA*', 'A⁺ is finite'], answer: 1, why: 'A⁺ contains ε only when ε ∈ A.' },
      { q: 'Is (A*)* = A*?', options: ['Yes', 'No, it is bigger'], answer: 0, why: 'Gluing pieces that are themselves glued pieces gives nothing new.' },
    ],
  });
})();
