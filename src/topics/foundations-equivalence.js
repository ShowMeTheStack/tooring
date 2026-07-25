// Equivalence relations and partitions: elements related by a rule ("same remainder", "same length") are
// sorted into classes one class at a time; the classes are disjoint, cover everything, and turn the
// relation's matrix into squares along the diagonal once the elements are listed class by class.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found;
  const H = K.rel;

  T.family({ id: 'found-equivalence', part: 'foundations', order: 40, title: 'Equivalence relations and partitions', blurb: 'Reflexive, symmetric and transitive: an equivalence cuts a set into classes that do not overlap and leave nothing out. Every partition comes from exactly one equivalence.' });

  const RULES = {
    mod3: { label: 'same remainder mod 3', num: true, key: (x) => ((+x % 3) + 3) % 3, name: (k) => 'remainder ' + k, say: 'x and y leave the same remainder when divided by 3', def: 'x ~ y  ⇔  x mod 3 = y mod 3' },
    mod2: { label: 'same parity (mod 2)', num: true, key: (x) => ((+x % 2) + 2) % 2, name: (k) => (k ? 'odd' : 'even'), say: 'x and y are both even or both odd', def: 'x ~ y  ⇔  x mod 2 = y mod 2' },
    len: { label: 'same length', key: (x) => [...x].length, name: (k) => 'length ' + k, say: 'x and y have the same length', def: 'x ~ y  ⇔  |x| = |y|' },
    first: { label: 'same first symbol', key: (x) => (x === '' ? 'ε' : [...x][0]), name: (k) => (k === 'ε' ? 'no first symbol' : 'starts with ' + k), say: 'x and y begin with the same symbol', def: 'x ~ y  ⇔  x and y start with the same symbol' },
    na: { label: 'same number of a\'s', key: (x) => [...x].filter((c) => c === 'a').length, name: (k) => k + ' a' + (k === 1 ? '' : '\'s'), say: 'x and y have equally many a\'s', def: 'x ~ y  ⇔  #a(x) = #a(y)' },
    all: { label: 'everything related', key: () => 0, name: () => 'everything', say: 'always: everything is related to everything', def: 'x ~ y for all x, y' },
    eq: { label: 'equality only', key: (x) => x, name: (k) => 'only ' + (k === '' ? 'ε' : k), say: 'x and y are the same element', def: 'x ~ y  ⇔  x = y' },
  };
  const show = (x) => (x === '' ? 'ε' : x);

  T.topic({
    id: 'equiv-classes', family: 'found-equivalence', order: 10, title: 'Classes of an equivalence',
    blurb: 'Pick an element, light up everything equivalent to it, and move that class into its own block. Repeat until nothing is left: the blocks form a partition.',
    inputs: [
      { id: 'items', kind: 'list', label: 'Elements', def: ['0', '1', '2', '3', '4', '5', '6', '7', '8'], min: 1, max: 10, check: (v) => (new Set(v).size !== v.length ? 'Elements: an element is listed twice' : v.some((x) => [...x].length > 4) ? 'Elements: at most 4 symbols each, so they fit' : null) },
      { id: 'rule', kind: 'choice', label: 'Related when', def: 'mod3', options: Object.entries(RULES).map(([value, r]) => ({ value, label: r.label })) },
    ],
    check: (inp) => (RULES[inp.rule].num && inp.items.some((x) => !/^-?\d+$/.test(x)) ? 'Elements: this rule needs whole numbers, but ' + show(inp.items.find((x) => !/^-?\d+$/.test(x))) + ' is not one' : null),
    presets: [
      { label: 'Remainders mod 3', values: { items: ['0', '1', '2', '3', '4', '5', '6', '7', '8'], rule: 'mod3' } },
      { label: 'Strings by length (with ε)', values: { items: ['', 'a', 'b', 'ab', 'ba', 'aa', 'bab'], rule: 'len' } },
      { label: 'Strings by number of a\'s', values: { items: ['b', 'ab', 'ba', 'aab', 'bb', 'aba', 'a'], rule: 'na' } },
      { label: 'Everything related: one class', values: { items: ['p', 'q', 'r', 's'], rule: 'all' } },
      { label: 'Equality: all singletons', values: { items: ['1', '2', '3', '4'], rule: 'eq' } },
    ],
    counters: [{ id: 'classes', label: 'classes' }, { id: 'placed', label: 'elements placed' }],
    run(inp) {
      const D = inp.items, rule = RULES[inp.rule];
      const narrow = H.narrow();
      const key = (x) => JSON.stringify(rule.key(x));
      const classes = F.classesBy(D, (x) => rule.key(x));
      const cls = {};
      classes.forEach((c, i) => c.forEach((x) => { cls[x] = 'kc' + (i % 6); }));
      // the pool: every element in a row (two rows on a phone)
      const CW = Math.max(46, ...D.map((x) => T.geom.textWidth(show(x), 16, { mono: true }) + 18)), CH = 40, GAP = 10;
      const perRow = narrow ? Math.min(D.length, 5) : D.length;
      const poolW = perRow * (CW + GAP) - GAP;
      const poolPos = (i) => ({ x: -poolW / 2 + (i % perRow) * (CW + GAP), y: Math.floor(i / perRow) * (CH + GAP) });
      const poolH = Math.ceil(D.length / perRow) * (CH + GAP) - GAP;
      // the blocks below: side by side, each a column of its members (wrapping on a phone)
      const by = poolH + 90;
      const bw = (c) => CW + 24;
      const perLine = narrow ? 3 : classes.length;
      const blockH = Math.max(...classes.map((c) => c.length)) * (CH + 8) + 40;
      const lineW = (from) => classes.slice(from, from + perLine).reduce((a, c) => a + bw(c) + 16, -16);
      const blockBox = classes.map((c, i) => {
        const line = Math.floor(i / perLine), start = line * perLine;
        let x = -lineW(start) / 2;
        for (let j = start; j < i; j++) x += bw(classes[j]) + 16;
        return { x, y: by + line * (blockH + 20), w: bw(c), h: blockH };
      });
      const F2 = new T.Frames(['classes', 'placed']);
      const placed = new Set();
      const scene = (opts) => {
        opts = opts || {};
        const items = opts.noPool ? [] : [{ key: 'pool', kind: 'region', x: -poolW / 2 - 16, y: -36, w: poolW + 32, h: poolH + 52, cls: 'frame', text: 'D' }];
        classes.forEach((c, i) => {
          if (i >= (opts.blocks || 0)) return;
          const b = blockBox[i];
          items.push({ key: 'blk:' + i, kind: 'region', x: b.x, y: b.y, w: b.w, h: b.h, cls: 'r' + (i % 6), text: '[' + show(c[0]) + ']', enter: 'fade' });
        });
        D.forEach((x, i) => {
          let p = poolPos(i);
          let c = 'mono';
          if (placed.has(x)) {
            const ci = classes.findIndex((cc) => cc.includes(x)), j = classes[ci].indexOf(x), b = blockBox[ci];
            p = { x: b.x + 12, y: b.y + 32 + j * (CH + 8) };
            c += ' ' + cls[x];
          } else if (opts.hot === x) c += ' hot';
          else if (opts.lit && opts.lit.includes(x)) c += ' act';
          else if (opts.dim) c += '';
          items.push({ key: 'el:' + x, kind: 'cell', x: p.x, y: p.y, w: CW, h: CH, text: show(x), cls: c, pick: true });
        });
        if (opts.labels) classes.forEach((c, i) => { if (i < (opts.blocks || 0)) { const b = blockBox[i]; items.push({ key: 'bl:' + i, kind: 'text', x: b.x + b.w / 2, y: b.y + b.h + 18, text: rule.name(rule.key(c[0])), anchor: 'middle', cls: 'strong', size: 13 }); } });
        return items;
      };
      F2.add({ items: scene(), say: 'D has ' + D.length + ' elements, and x ~ y when ' + rule.say + '. That is an equivalence: everything is related to itself, the rule is symmetric, and it chains.', hl: { def: ['0'] }, meta: { count: classes.length } });
      classes.forEach((c, i) => {
        const x = c[0];
        F2.add({ items: scene({ blocks: i, hot: x, lit: c.filter((y) => y !== x) }), say: 'Take ' + show(x) + ', the first element not yet in a class. Everything equivalent to it (' + rule.name(rule.key(x)) + ') lights up: ' + (c.length > 1 ? c.filter((y) => y !== x).map(show).join(', ') + '.' : 'nothing else, so ' + show(x) + ' is alone.'), hl: { def: ['1'] }, meta: { mates: c.filter((y) => y !== x).map((y) => 'el:' + y), first: x } });
        c.forEach((y) => placed.add(y));
        F2.count('classes').count('placed', c.length);
        F2.add({ items: scene({ blocks: i + 1, labels: true }), say: '[' + show(x) + '] = {' + c.map(show).join(', ') + '} becomes a block. ' + (i === 0 ? 'Every element of the block is related to every other, and to nothing outside it.' : 'It shares no element with the earlier block' + (i > 1 ? 's' : '') + ': two classes are either equal or disjoint.'), hl: { def: ['1', '2'] } });
      });
      F2.add({ items: scene({ blocks: classes.length, labels: true }), say: 'Nothing is left in D: ' + classes.length + ' class' + (classes.length === 1 ? '' : 'es') + ', disjoint, none empty, covering all of D. That is a partition, and the equivalence can be read back from it: x ~ y exactly when they share a block.', hl: { def: ['2'] }, mark: 'partition' });
      // the matrix with the elements listed class by class: squares along the diagonal
      const order = classes.flat();
      const R = F.partitionToRelation(classes);
      const m = H.matrix({ D: order.map(show), R: R.map(([a, b]) => [show(a), show(b)]), x: 0, y: 0, cw: 34, ch: 32, prefix: 'mx', corner: '~', blank: true });
      const mb = m.box;
      const blocksRight = Math.max(...blockBox.map((b) => b.x + b.w));
      const mx = narrow ? -mb.w / 2 : blocksRight + 50, my = narrow ? by - 40 - mb.h : by;
      const m2 = H.matrix({ D: order.map(show), R: R.map(([a, b]) => [show(a), show(b)]), x: mx, y: my, cw: 34, ch: 32, prefix: 'mx', corner: '~', blank: true, good: R.map(([a, b]) => [show(a), show(b)]) });
      F2.add({ items: scene({ blocks: classes.length, labels: true, noPool: narrow }).concat(m2.items), say: 'The relation as a matrix, with D listed class by class: the 1s form ' + classes.length + ' solid square' + (classes.length === 1 ? '' : 's') + ' along the diagonal, one per block, and 0s everywhere else (left blank).', hl: { def: ['3'] } });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Equivalence and partition', text: [rule.def, '[x] = { y ∈ D : x ~ y }', 'classes: equal or disjoint, never empty, cover D', 'x ~ y  ⇔  x and y lie in the same block'].join('\n') }] } };
    },
    predict: [
      { at: (f, i) => i === 0, pick: 'option', options: (fr, i, inp) => [...Array(Math.max(7, inp.items.length)).keys()].map((k) => String(k + 1)), ask: 'How many classes will D fall into?', answer: (fr) => String(fr[0].meta.count), explain: (fr) => fr[fr.length - 2].say },
      { at: (f) => f.meta && f.meta.mates && f.meta.mates.length, once: true, pick: 'item', ask: (fr, i) => 'Click another element in the same class as ' + show(fr[i].meta.first) + '.', answer: (fr, i) => fr[i].meta.mates, explain: (fr, i) => fr[i].say },
    ],
    quiz: [
      { q: 'Can two different classes of an equivalence share an element?', options: ['Yes, sometimes', 'No: if they share one, they are the same class'], answer: 1, why: 'If z ~ x and z ~ y then x ~ y by symmetry and transitivity, so [x] = [y].' },
      { q: 'How many classes does "same remainder mod 4" have on the whole numbers 0, 1, 2, …?', options: ['2', '4', 'Infinitely many', 'One per number'], answer: 1, why: 'The remainders 0, 1, 2 and 3: four classes, each infinite.' },
      { q: 'Which equivalence has the most classes on a set of n elements?', options: ['Everything related', 'Equality', 'Same parity', 'They all have n'], answer: 1, why: 'Equality relates each element only to itself, so every class is a single element: n classes.' },
      { q: 'You list the elements class by class. What does the matrix of the relation look like?', options: ['All 1s', 'Only the diagonal', 'Solid squares of 1s along the diagonal', 'A triangle'], answer: 2, why: 'Inside a block everything is related (a square of 1s); between blocks nothing is.' },
    ],
  });
})();
