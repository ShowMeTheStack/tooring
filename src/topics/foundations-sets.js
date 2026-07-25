// Sets: the operations as regions of a Venn diagram that the elements are sorted into, the power set built
// by counting in binary with each subset taking its place in the lattice of subsets, and the Cartesian
// product as a grid of ordered pairs (and a relation as a set of its cells).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found, Geo = T.geom;
  const H = K.rel;

  T.family({ id: 'found-sets', part: 'foundations', order: 10, title: 'Sets', blurb: 'Collections of things, with no order and no repeats. Union, intersection and difference pick regions of a Venn diagram; the power set and the Cartesian product build bigger sets from smaller ones.' });

  const setText = (xs) => (xs.length ? '{' + xs.join(', ') + '}' : '∅');
  const noRepeats = (label) => (v) => (new Set(v).size !== v.length ? label + ': a set lists each element once' : v.some((x) => [...x].length > 3) ? label + ': at most 3 characters per element' : v.some((x) => x === '') ? label + ': use names like 1, 2, a, b (ε is not an element here)' : null);

  // ---------------------------------------------------------------------------------------------------
  // Venn regions
  // ---------------------------------------------------------------------------------------------------
  const OPS = {
    union: { label: 'A ∪ B', n: 2, f: (a, b) => a || b, how: 'in A or in B (or both)' },
    inter: { label: 'A ∩ B', n: 2, f: (a, b) => a && b, how: 'in A and in B' },
    diff: { label: 'A − B', n: 2, f: (a, b) => a && !b, how: 'in A but not in B' },
    rdiff: { label: 'B − A', n: 2, f: (a, b) => b && !a, how: 'in B but not in A' },
    sym: { label: 'A △ B', n: 2, f: (a, b) => a !== b, how: 'in exactly one of A and B' },
    compA: { label: 'Aᶜ (complement in U)', n: 2, f: (a) => !a, how: 'in U but not in A' },
    notUnion: { label: '(A ∪ B)ᶜ', n: 2, f: (a, b) => !(a || b), how: 'in neither A nor B' },
    bothNot: { label: 'Aᶜ ∩ Bᶜ', n: 2, f: (a, b) => !a && !b, how: 'outside A and outside B' },
    dist1: { label: 'A ∩ (B ∪ C)', n: 3, f: (a, b, c) => a && (b || c), how: 'in A, and in B or C' },
    dist2: { label: '(A ∩ B) ∪ (A ∩ C)', n: 3, f: (a, b, c) => (a && b) || (a && c), how: 'in both A and B, or in both A and C' },
    all3: { label: 'A ∩ B ∩ C', n: 3, f: (a, b, c) => a && b && c, how: 'in all three' },
  };
  const regionName = (reg, n) => {
    const ins = ['A', 'B', 'C'].slice(0, n).filter((s) => reg.includes(s)), outs = ['A', 'B', 'C'].slice(0, n).filter((s) => !reg.includes(s));
    if (!ins.length) return 'outside ' + (n === 2 ? 'both sets' : 'all three sets');
    return 'in ' + ins.join(' and ') + (outs.length ? ', not in ' + outs.join(' or ') : '');
  };

  T.topic({
    id: 'set-ops', family: 'found-sets', order: 10, title: 'Set operations as Venn regions',
    blurb: 'Sort every element of the universe into the region of the Venn diagram it belongs to. An operation is just a choice of regions: watch each region be kept or dropped.',
    inputs: [
      { id: 'U', kind: 'list', label: 'Universe U', def: ['1', '2', '3', '4', '5', '6', '7', '8'], min: 1, max: 10, check: noRepeats('Universe U') },
      { id: 'A', kind: 'list', label: 'A', def: ['1', '2', '3', '4'], max: 8, check: noRepeats('A') },
      { id: 'B', kind: 'list', label: 'B', def: ['3', '4', '5', '6'], max: 8, check: noRepeats('B') },
      { id: 'C', kind: 'list', label: 'C (three-set operations)', def: ['2', '4', '6', '8'], max: 8, check: noRepeats('C') },
      { id: 'op', kind: 'choice', label: 'Operation', def: 'diff', options: Object.entries(OPS).map(([value, o]) => ({ value, label: o.label })) },
    ],
    check: (inp) => {
      const n = OPS[inp.op].n;
      for (const s of ['A', 'B', 'C'].slice(0, n)) { const bad = inp[s].find((x) => !inp.U.includes(x)); if (bad !== undefined) return s + ': ' + bad + ' is not in the universe U'; }
      const regs = {};
      for (const x of inp.U) { const r = ['A', 'B', 'C'].slice(0, n).filter((s) => inp[s].includes(x)).join(''); regs[r] = (regs[r] || 0) + 1; }
      if (Object.values(regs).some((c) => c > 4)) return 'Too many elements in one region of the picture (at most 4), so they stay readable';
      return null;
    },
    presets: [
      { label: 'A − B', values: { U: ['1', '2', '3', '4', '5', '6', '7', '8'], A: ['1', '2', '3', '4'], B: ['3', '4', '5', '6'], op: 'diff' } },
      { label: 'Disjoint sets: A ∩ B = ∅', values: { U: ['a', 'b', 'c', 'd', 'e', 'f'], A: ['a', 'b'], B: ['d', 'e', 'f'], op: 'inter' } },
      { label: 'A ⊆ B, so A − B = ∅', values: { U: ['1', '2', '3', '4', '5'], A: ['2', '3'], B: ['1', '2', '3', '4'], op: 'diff' } },
      { label: 'De Morgan: (A ∪ B)ᶜ', values: { U: ['1', '2', '3', '4', '5', '6', '7'], A: ['1', '2', '3'], B: ['3', '4', '5'], op: 'notUnion' } },
      { label: 'De Morgan: Aᶜ ∩ Bᶜ', values: { U: ['1', '2', '3', '4', '5', '6', '7'], A: ['1', '2', '3'], B: ['3', '4', '5'], op: 'bothNot' } },
      { label: 'Three sets: A ∩ (B ∪ C)', values: { U: ['1', '2', '3', '4', '5', '6', '7', '8'], A: ['1', '2', '3', '4'], B: ['3', '4', '5', '6'], C: ['2', '4', '6', '8'], op: 'dist1' } },
      { label: 'Empty A', values: { U: ['x', 'y', 'z'], A: [], B: ['y'], op: 'union' } },
    ],
    counters: [{ id: 'placed', label: 'elements placed' }, { id: 'kept', label: 'in the result' }],
    run(inp) {
      const op = OPS[inp.op], n = op.n;
      const names = ['A', 'B', 'C'].slice(0, n);
      const inS = (s, x) => inp[s].includes(x);
      const regOf = (x) => names.filter((s) => inS(s, x)).join('');
      const U = inp.U;
      const r = n === 3 ? 118 : 116;
      const sets = names.map((s) => ({ id: s, label: s }));
      // where each region's elements go: borrow the kit's anchors, then lay chips in a column
      const members = {};
      for (const x of U) (members[regOf(x)] = members[regOf(x)] || []).push(x);
      const probe = K.set.venn({ sets, members, universe: 'U', r, prefix: 'vn' }).items;
      const anchor = {};
      for (const it of probe) if (it.kind === 'text' && it.key.startsWith('vn:m:')) { const reg = it.key.split(':')[2]; const a = anchor[reg] || (anchor[reg] = { x: it.x, ys: [] }); a.ys.push(it.y); }
      const chipPos = {};
      for (const [reg, xs] of Object.entries(members)) {
        const a = anchor[reg], cy = a.ys.reduce((p, q) => p + q, 0) / a.ys.length - 5;
        xs.forEach((x, k) => { chipPos[x] = { x: a.x, y: cy + (k - (xs.length - 1) / 2) * 30 }; });
      }
      const chipW = (x) => Math.max(30, Geo.textWidth(x, 15, { mono: true }) + 14);
      const top = -r * 1.75 - 64;
      const rowW = U.length * 40;
      const listKey = (x) => 'u:' + x;
      const result = U.filter((x) => op.f(...names.map((s) => inS(s, x))));
      const F2 = new T.Frames(['placed', 'kept']);
      const placed = new Set();
      const decided = {};
      const scene = (o) => {
        o = o || {};
        const items = K.set.venn({ sets, members: {}, universe: 'U', r, prefix: 'vn', hot: o.hotSets || [] }).items;
        U.forEach((x, i) => items.push({ key: listKey(x), kind: 'cell', x: -rowW / 2 + i * 40, y: top, w: 36, h: 34, text: x, cls: 'mono' + (placed.has(x) ? ' read' : ''), size: 15 }));
        for (const x of U) if (placed.has(x)) {
          const p = chipPos[x], w = chipW(x);
          const st = decided[x] === true ? 'good' : decided[x] === false ? 'gone' : o.lit && o.lit.includes(x) ? 'hot' : '';
          items.push({ key: 'el:' + x, kind: 'cell', x: p.x - w / 2, y: p.y - 13, w, h: 26, text: x, cls: 'mono ' + st, size: 15, rx: 13, enter: 'from', src: listKey(x), pick: true });
        }
        if (o.result) {
          const ry = r * (n === 3 ? 1.95 : 1.72) + 20;
          const res = o.result;
          items.push({ key: 'res:label', kind: 'text', x: 0, y: ry, text: op.label.replace(/ \(.*\)$/, '') + ' = ' + (res.length ? '' : '∅'), anchor: 'middle', cls: 'strong', size: 16 });
          const w = res.length * 40;
          res.forEach((x, i) => items.push({ key: 'res:' + x, kind: 'cell', x: -w / 2 + i * 40, y: ry + 14, w: 36, h: 34, text: x, cls: 'mono good', size: 15, enter: 'from', src: 'el:' + x }));
        }
        return items;
      };
      const def = ['U = ' + setText(U)].concat(names.map((s) => s + ' = ' + setText(inp[s])), [op.label.replace(/ \(.*\)$/, '') + ' = {x : x is ' + op.how + '}']);
      F2.add({ items: scene(), say: 'The universe U has ' + U.length + ' elements. ' + names.map((s) => s + ' = ' + setText(inp[s])).join(', ') + '. Each circle is a set; the box around them is U.', hl: { def: ['0'] } });
      // place the elements region by region, the busiest regions of the picture first
      const regs = Object.keys(members).sort((a, b) => b.length - a.length || (a < b ? -1 : 1));
      for (const reg of regs) {
        members[reg].forEach((x) => placed.add(x));
        F2.count('placed', members[reg].length);
        F2.add({ items: scene({ lit: members[reg] }), say: members[reg].join(', ') + (members[reg].length === 1 ? ' is ' : ' are ') + regionName(reg, n) + (reg === '' ? ': outside every circle, but still in U.' : '.'), hl: { def: names.map((s, i) => (reg.includes(s) ? String(i + 1) : null)).filter(Boolean) } });
      }
      const emptySets = names.filter((s) => !inp[s].length);
      F2.add({ items: scene({ hotSets: names }), say: 'Now ' + op.label.replace(/ \(.*\)$/, '') + ': keep exactly the elements that are ' + op.how + '. Each region is kept or dropped as a whole.' + (emptySets.length ? ' ' + emptySets.join(' and ') + (emptySets.length === 1 ? ' is' : ' are') + ' empty, so ' + (emptySets.length === 1 ? 'its circle holds' : 'their circles hold') + ' nothing of its own.' : ''), hl: { def: [String(n + 1)] }, meta: { pick: result.map((x) => 'el:' + x), count: result.length } });
      for (const reg of regs) {
        const keep = op.f(...names.map((s) => reg.includes(s)));
        members[reg].forEach((x) => { decided[x] = keep; });
        if (keep) F2.count('kept', members[reg].length);
        F2.add({ items: scene(), say: (reg === '' ? 'Outside the circles' : 'The region ' + regionName(reg, n)) + ' (' + members[reg].join(', ') + '): ' + (keep ? 'kept, since these are ' + op.how + '.' : 'dropped, since these are not ' + op.how + '.'), hl: { def: [String(n + 1)] } });
      }
      F2.add({ items: scene({ result }), say: op.label.replace(/ \(.*\)$/, '') + ' = ' + setText(result) + (result.length ? ', ' + result.length + ' element' + (result.length === 1 ? '' : 's') + '.' : ': no element qualifies, so the result is the empty set.') + (inp.op === 'notUnion' || inp.op === 'bothNot' ? ' Try the other De Morgan preset: (A ∪ B)ᶜ and Aᶜ ∩ Bᶜ keep the very same region.' : inp.op === 'dist1' ? ' (A ∩ B) ∪ (A ∩ C) keeps the very same regions: intersection distributes over union.' : ''), hl: { def: [String(n + 1)] }, mark: 'result' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The sets', text: def.join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.pick && f.meta.pick.length, pick: 'item', ask: 'Click an element that will be in the result.', answer: (fr, i) => fr[i].meta.pick, explain: (fr) => fr[fr.length - 1].say },
      { at: (f) => f.meta && f.meta.pick && !f.meta.pick.length, pick: 'option', options: ['0', '1', '2', '3', '4'], ask: 'How many elements will the result have?', answer: () => '0', explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A ⊆ B. What is A − B?', options: ['A', 'B', '∅', 'B − A'], answer: 2, why: 'Every element of A is also in B, so none is left when B is taken away.' },
      { q: 'Which set always equals (A ∪ B)ᶜ?', options: ['Aᶜ ∪ Bᶜ', 'Aᶜ ∩ Bᶜ', 'A ∩ B', 'A − B'], answer: 1, why: 'Outside the union means outside A and outside B: De Morgan\'s law.' },
      { q: 'If A ∩ B = ∅, what is |A ∪ B|?', options: ['|A| + |B|', '|A| · |B|', 'max(|A|, |B|)', 'It depends on U'], answer: 0, why: 'With no overlap nothing is counted twice. In general |A ∪ B| = |A| + |B| − |A ∩ B|.' },
      { q: 'How many regions does a Venn diagram of three sets have, counting the outside?', options: ['3', '6', '7', '8'], answer: 3, why: 'Each element is in or out of each set: 2 × 2 × 2 = 8 combinations.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // The power set by counting in binary
  // ---------------------------------------------------------------------------------------------------
  const binom = (n, k) => { let r = 1; for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i; return Math.round(r); };
  T.topic({
    id: 'set-powerset', family: 'found-sets', order: 20, title: 'The power set, counted in binary',
    blurb: 'A subset says yes or no to each element: a string of bits. Count from 0 to 2ⁿ − 1 and every subset appears exactly once, each taking its place in the lattice of subsets.',
    inputs: [{ id: 'S', kind: 'list', label: 'Set S', def: ['a', 'b', 'c'], max: 4, check: noRepeats('Set S') }],
    presets: [
      { label: '{a, b, c}: 8 subsets', values: { S: ['a', 'b', 'c'] } },
      { label: '{1, 2, 3, 4}: 16 subsets', values: { S: ['1', '2', '3', '4'] } },
      { label: 'One element', values: { S: ['x'] } },
      { label: 'The empty set: P(∅) = {∅}', values: { S: [] } },
    ],
    counters: [{ id: 'count', label: 'count' }, { id: 'subsets', label: 'subsets found' }],
    run(inp) {
      const S = inp.S, n = S.length, N = 1 << n;
      const F2 = new T.Frames(['count', 'subsets']);
      const subOf = (c) => S.filter((_, i) => (c >> (n - 1 - i)) & 1);
      const label = (sub) => (sub.length ? '{' + sub.join(',') + '}' : '∅');
      const bits = (c) => (n ? c.toString(2).padStart(n, '0') : '');
      // the lattice: level k holds the subsets of size k, ∅ at the bottom
      const all = F.powerset(S);
      const levels = [];
      for (const s of all) (levels[s.length] = levels[s.length] || []).push(s);
      const nodeW = (s) => Math.max(40, Geo.textWidth(label(s), 15, { mono: true }) + 18);
      const GX = Math.max(n === 4 ? 78 : 92, ...all.map(nodeW).map((w) => w + 14)), GY = 78;
      const pos = {};
      levels.forEach((lv, k) => lv.forEach((s, j) => { pos[label(s)] = { x: (j - (lv.length - 1) / 2) * GX, y: (n - k) * GY }; }));
      const cy = -110;
      const CW = 46;
      const scene = (upto, opts) => {
        opts = opts || {};
        const items = [];
        // the counter: one cell per element, its name above
        S.forEach((x, i) => {
          items.push({ key: 'h:' + x, kind: 'text', x: (i - (n - 1) / 2) * CW, y: cy - 10, text: x, anchor: 'middle', cls: 'strong', size: 15 });
          const on = upto >= 0 && (upto >> (n - 1 - i)) & 1;
          items.push({ key: 'bit:' + i, kind: 'cell', x: (i - (n - 1) / 2) * CW - CW / 2 + 3, y: cy, w: CW - 6, h: 40, text: upto >= 0 ? (on ? '1' : '0') : '·', cls: 'mono ' + (on ? 'good' : 'empty') + (opts.flip && opts.flip.includes(i) ? ' hot' : ''), size: 17 });
        });
        if (!n) items.push({ key: 'bit:none', kind: 'cell', x: -40, y: cy, w: 80, h: 40, text: 'no bits', cls: 'empty', size: 14 });
        items.push({ key: 'cnt', kind: 'text', x: n ? (n / 2) * CW + 18 : 58, y: cy + 26, text: upto >= 0 ? '= ' + upto : '', cls: 'strong', size: 16 });
        const shown = [];
        for (let c = 0; c <= upto; c++) shown.push(subOf(c));
        const has = new Set(shown.map(label));
        for (const s of shown) {
          const p = pos[label(s)], w = nodeW(s);
          const now = opts.now !== undefined && label(subOf(opts.now)) === label(s);
          items.push({ key: 'n:' + label(s), kind: 'state', x: p.x, y: p.y, w, h: 34, rx: 17, text: label(s), size: 15, cls: 'state set' + (now ? ' hot' : ''), enter: now ? 'from' : undefined, src: now ? (n ? 'bit:0' : 'bit:none') : undefined });
          // an edge up to each superset with one more element that is already there
          for (const x of S) if (!s.includes(x)) {
            const t = S.filter((y) => s.includes(y) || y === x);
            if (has.has(label(t))) items.push({ key: 'e:' + label(s) + '>' + label(t), kind: 'edge', from: 'n:' + label(s), to: 'n:' + label(t), head: false, gapB: 0, cls: 'tree soft', audit: 'edge-x' });
          }
        }
        if (opts.counts) levels.forEach((lv, k) => { const right = Math.max(...lv.map((s) => pos[label(s)].x + nodeW(s) / 2)); items.push({ key: 'lv:' + k, kind: 'text', x: right + 22, y: (n - k) * GY + 5, text: 'size ' + k + ': ' + lv.length, cls: 'hot', size: 14 }); });
        return items;
      };
      F2.add({ items: scene(-1), say: n ? 'S = {' + S.join(', ') + '}. A subset is a yes or no for each of the ' + n + ' elements: a string of ' + n + ' bits. So there are 2 × … × 2 = 2^' + n + ' = ' + N + ' subsets.' : 'S = ∅ has no elements, so a subset is a string of zero bits. There is exactly one such string, the empty one.', hl: { def: ['0', '1'] }, meta: { total: N } });
      for (let c = 0; c < N; c++) {
        const s = subOf(c);
        const flip = c ? [...Array(n).keys()].filter((i) => (((c - 1) ^ c) >> (n - 1 - i)) & 1) : [];
        F2.set('count', c).set('subsets', c + 1);
        F2.add({ items: scene(c, { now: c, flip }), say: (n ? 'Count ' + c + ' = ' + bits(c) + ' in binary: ' : '') + (s.length ? 'take ' + s.join(' and ') + ', giving ' + label(s) + '.' : n ? 'take nothing, giving the empty set ∅.' : 'the only subset of ∅ is ∅ itself, so P(∅) = {∅}, which has one element (it is not empty).') + (c === 0 && n ? ' It sits at the bottom of the lattice; lines join each subset to those with one more element.' : ''), hl: { def: ['1'] }, meta: { c, next: c + 1 < N ? label(subOf(c + 1)) : null, nextBits: c + 1 < N ? bits(c + 1) : null } });
      }
      if (n) F2.add({ items: scene(N - 1, { counts: true }), say: 'All ' + N + ' subsets, each found once. Level k holds the subsets of size k: ' + levels.map((lv) => lv.length).join(' + ') + ' = ' + N + '. Every element doubles the count, which is why |P(S)| = 2^|S|.', hl: { def: ['2'] }, mark: 'complete' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The power set', text: ['P(S) = { T : T ⊆ S }', 'subset ↔ bit string: bit i says whether element i is in', '|P(S)| = 2^|S| = Σₖ C(n, k)'].join('\n') }] } };
    },
    predict: [
      { at: (f, i) => i === 0, pick: 'option', options: (fr, i, inp) => [...new Set([inp.S.length, 2 * inp.S.length, inp.S.length * inp.S.length, 1 << inp.S.length].map(String))].sort((a, b) => a - b), ask: 'How many subsets does S have?', answer: (fr) => String(fr[0].meta.total), explain: (fr) => fr[0].say },
      { at: (f, i, fr, inp) => f.meta && f.meta.c === (inp.S.length >= 3 ? 4 : -1), pick: 'option', options: (fr, i, inp) => { const S = inp.S, n = S.length; return [5, 6, 3, 10].filter((c) => c < (1 << n)).map((c) => { const s = S.filter((_, k) => (c >> (n - 1 - k)) & 1); return '{' + s.join(',') + '}'; }); }, ask: (fr, i) => 'The next count is ' + fr[i].meta.next.length + '… in binary ' + fr[i].meta.nextBits + '. Which subset is that?', answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'How many subsets does a set of 5 elements have?', options: ['5', '10', '25', '32'], answer: 3, why: '2⁵ = 32: two choices for each element.' },
      { q: 'What is P(∅)?', options: ['∅', '{∅}', '{ε}', 'It is undefined'], answer: 1, why: 'The empty set has exactly one subset, itself, so P(∅) is a set with one element.' },
      { q: 'With S = {a, b, c} and a as the leftmost bit, which subset does 011 stand for?', options: ['{a}', '{b, c}', '{a, b}', '{c}'], answer: 1, why: 'Bits for a, b, c: 0, 1, 1, so b and c are in.' },
      { q: 'How many subsets of a 4-element set have exactly 2 elements?', options: ['4', '6', '8', '16'], answer: 1, why: 'C(4, 2) = 6: the middle level of the lattice.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // The Cartesian product as a grid
  // ---------------------------------------------------------------------------------------------------
  const REL = {
    none: { label: 'nothing', f: null },
    eq: { label: 'first = second', f: (a, b) => a === b, say: 'the pairs with equal coordinates, the diagonal: the equality relation' },
    lt: { label: 'first < second', f: (a, b) => (/^-?\d+$/.test(a) && /^-?\d+$/.test(b) ? +a < +b : a < b), say: 'the pairs whose first coordinate is smaller: the relation <' },
  };
  T.topic({
    id: 'set-product', family: 'found-sets', order: 30, title: 'The Cartesian product as a grid',
    blurb: 'A × B holds every ordered pair (a, b): one cell for each row a and column b, so |A × B| = |A| · |B|. A relation is just a set of these cells.',
    inputs: [
      { id: 'A', kind: 'list', label: 'A (rows)', def: ['1', '2', '3'], max: 5, check: noRepeats('A') },
      { id: 'B', kind: 'list', label: 'B (columns)', def: ['x', 'y'], max: 5, check: noRepeats('B') },
      { id: 'rel', kind: 'choice', label: 'Then light up', def: 'none', options: Object.entries(REL).map(([value, r]) => ({ value, label: r.label })) },
    ],
    presets: [
      { label: '{1, 2, 3} × {x, y}', values: { A: ['1', '2', '3'], B: ['x', 'y'], rel: 'none' } },
      { label: '{x, y} × {1, 2, 3}: the other order', values: { A: ['x', 'y'], B: ['1', '2', '3'], rel: 'none' } },
      { label: 'A × A and the relation <', values: { A: ['1', '2', '3', '4'], B: ['1', '2', '3', '4'], rel: 'lt' } },
      { label: 'A × A and equality', values: { A: ['a', 'b', 'c'], B: ['a', 'b', 'c'], rel: 'eq' } },
      { label: 'A × ∅ = ∅', values: { A: ['1', '2', '3'], B: [], rel: 'none' } },
    ],
    counters: [{ id: 'pairs', label: 'pairs' }],
    run(inp) {
      const A = inp.A, B = inp.B, rel = REL[inp.rel];
      const F2 = new T.Frames(['pairs']);
      const made = new Set();
      const cw = Math.max(64, ...A.flatMap((a) => B.map((b) => Geo.textWidth('(' + a + ', ' + b + ')', 15, { mono: true }) + 18)));
      const lit = new Set();
      const draw = (hot) => {
        const rows = A.map((a) => B.map((b) => '(' + a + ', ' + b + ')'));
        const t = K.table.draw({ rows: A.length && B.length ? rows : [[]], rowHead: A.length ? A : [' '], colHead: B.length ? B : [' '], corner: 'A × B', cw, ch: 42, mono: true, size: 15, prefix: 'pr', skip: (r, c) => !A.length || !B.length || !made.has(r + ',' + c), cls: (r, c) => (lit.has(r + ',' + c) ? 'good' : hot && hot[0] === r && hot[1] === c ? 'hot' : '') });
        for (const it of t.items) if (it.kind === 'cell' && /^pr:\d+,\d+$/.test(it.key)) { const [r, c] = it.key.slice(3).split(',').map(Number); it.enter = 'from'; it.src = ['pr:rh:' + r, 'pr:ch:' + c]; }
        return t.items;
      };
      const total = A.length * B.length;
      F2.add({ items: draw(), say: 'A = ' + setText(A) + ' labels the rows and B = ' + setText(B) + ' the columns. Each cell will hold one ordered pair (row, column).', hl: { def: ['0'] }, meta: { total } });
      if (!total) F2.add({ items: draw(), say: (A.length ? 'B' : 'A') + ' is empty, so there is no ' + (A.length ? 'column' : 'row') + ' and not a single cell: ' + (A.length ? 'A × ∅' : '∅ × B') + ' = ∅. A pair needs one coordinate from each set.', hl: { def: ['1'] }, mark: 'empty' });
      else if (total <= 12) {
        A.forEach((a, r) => B.forEach((b, c) => { made.add(r + ',' + c); F2.count('pairs'); F2.add({ items: draw([r, c]), say: 'Row ' + a + ', column ' + b + ': the pair (' + a + ', ' + b + ').', hl: { def: ['0'] } }); }));
      } else A.forEach((a, r) => { B.forEach((b, c) => made.add(r + ',' + c)); F2.count('pairs', B.length); F2.add({ items: draw(), say: 'Row ' + a + ': (' + a + ', ' + B[0] + ') to (' + a + ', ' + B[B.length - 1] + '), ' + B.length + ' pairs.', hl: { def: ['0'] } }); });
      if (total) F2.add({ items: draw(), say: 'The grid has ' + A.length + ' rows of ' + B.length + ' cells, so |A × B| = ' + A.length + ' · ' + B.length + ' = ' + total + '. ' + (A.join() === B.join() ? 'Here A = B, and (x, y) and (y, x) are different cells unless x = y.' : 'B × A would be a different set: (' + A[0] + ', ' + B[0] + ') is not (' + B[0] + ', ' + A[0] + ').'), hl: { def: ['1'] }, mark: 'product' });
      if (total && rel.f) {
        A.forEach((a, r) => B.forEach((b, c) => { if (rel.f(a, b)) lit.add(r + ',' + c); }));
        F2.add({ items: draw(), say: 'A relation from A to B is any subset of A × B. Lit: ' + rel.say + ', ' + lit.size + ' of the ' + total + ' cells.', hl: { def: ['2'] }, mark: 'relation' });
        F2.add({ items: draw(), say: 'Every one of the 2^' + total + ' sets of cells is a relation, from ∅ (no cell) to all of A × B (every cell).', hl: { def: ['2'] } });
      }
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The product', text: ['A × B = { (a, b) : a ∈ A, b ∈ B }', '|A × B| = |A| · |B|', 'a relation from A to B: any R ⊆ A × B'].join('\n') }] } };
    },
    predict: [
      { at: (f, i) => i === 0, pick: 'option', options: (fr, i, inp) => [...new Set([inp.A.length + inp.B.length, inp.A.length * inp.B.length, Math.pow(2, inp.A.length * inp.B.length), Math.max(inp.A.length, inp.B.length)])].sort((a, b) => a - b).map(String), ask: 'How many ordered pairs will A × B have?', answer: (fr) => String(fr[0].meta.total), explain: (fr) => (fr.find((f) => f.mark === 'product' || f.mark === 'empty') || fr[1]).say },
    ],
    quiz: [
      { q: '|A| = 3 and |B| = 4. How many relations from A to B are there?', options: ['7', '12', '2¹²', '3⁴'], answer: 2, why: 'A relation is any subset of the 12 cells of A × B, and 12 cells have 2¹² subsets.' },
      { q: 'When is A × B = B × A?', options: ['Always', 'When A = B, or when one of them is empty', 'When |A| = |B|', 'Never'], answer: 1, why: 'Pairs are ordered: (1, x) ≠ (x, 1). The two products agree only if A = B or both are ∅.' },
      { q: 'What is A × ∅?', options: ['A', '∅', '{∅}', 'A × {ε}'], answer: 1, why: 'A pair needs a second coordinate from ∅, and there is none.' },
    ],
  });
})();
