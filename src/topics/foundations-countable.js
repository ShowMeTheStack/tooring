// Countable sets: a set is countable when its elements can be listed, first, second, third, …, so that each
// one gets a number. The grid N × N is walked diagonal by diagonal, the positive fractions are walked the
// same way skipping repeats, and a hotel with infinitely many rooms takes in new guests when it is full.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const H = K.rel;

  T.family({ id: 'found-countable', part: 'foundations', order: 50, title: 'Countable sets', blurb: 'A set is countable when its elements can be numbered 0, 1, 2, … with none left out. Pairs of numbers, fractions and strings all can, though there seem to be far more of them.' });

  /** The zig-zag walk over the grid: step n visits (i, j), diagonal d = i + j going up and down in turn */
  const zig = (n) => {
    let d = 0;
    while (((d + 1) * (d + 2)) / 2 <= n) d++;
    const k = n - (d * (d + 1)) / 2;
    return d % 2 ? { i: k, j: d - k, d } : { i: d - k, j: k, d };
  };
  const zigIndex = (i, j) => { const d = i + j; return (d * (d + 1)) / 2 + (d % 2 ? i : j); };
  const gcd = (a, b) => (b ? gcd(b, a % b) : a);

  /** A grid of cells with row and column numbers, ⋯ past the last column and ⋮ past the last row */
  function grid(G, opts) {
    const C = opts.cell || 56, GAP = opts.gap || 12, P = opts.prefix || 'gr';
    const items = [];
    const at = (i, j) => ({ x: j * (C + GAP), y: i * (C + GAP) });
    for (let j = 0; j < G; j++) items.push({ key: P + ':ch:' + j, kind: 'text', x: at(0, j).x + C / 2, y: -14, text: opts.colName(j), anchor: 'middle', cls: 'strong', size: 14 });
    for (let i = 0; i < G; i++) items.push({ key: P + ':rh:' + i, kind: 'text', x: -12, y: at(i, 0).y + C / 2 + 5, text: opts.rowName(i), anchor: 'end', cls: 'strong', size: 14 });
    if (opts.axes) {
      items.push({ key: P + ':ax:j', kind: 'text', x: at(0, G - 1).x + C + GAP + 6, y: -14, text: opts.axes[1], cls: 'title' });
      items.push({ key: P + ':ax:i', kind: 'text', x: -12, y: at(G - 1, 0).y + C + GAP + 30, text: opts.axes[0], anchor: 'end', cls: 'title' });
    }
    for (let i = 0; i < G; i++) for (let j = 0; j < G; j++) {
      const p = at(i, j), c = opts.cellOf(i, j);
      const it = { key: P + ':' + i + ',' + j, kind: 'cell', x: p.x, y: p.y, w: C, h: C, cls: 'mono ' + (c.cls || ''), pick: true };
      if (c.lines) { it.lines = c.lines; it.size = 13; } else { it.text = c.text; it.size = c.size || 15; }
      items.push(it);
    }
    for (let i = 0; i < G; i++) items.push({ key: P + ':mr:' + i, kind: 'text', x: at(i, G - 1).x + C + GAP + 6, y: at(i, 0).y + C / 2 + 5, text: '⋯', cls: 'strong', size: 16 });
    for (let j = 0; j < G; j++) items.push({ key: P + ':mb:' + j, kind: 'text', x: at(0, j).x + C / 2, y: at(G - 1, 0).y + C + GAP + 12, text: '⋮', anchor: 'middle', cls: 'strong', size: 16 });
    return { items, key: (i, j) => P + ':' + i + ',' + j, at, C, GAP, w: G * (C + GAP), h: G * (C + GAP) };
  }
  /** The trail from cell to cell, the last step lit */
  const trail = (visits, key) => visits.slice(1).map((v, k) => ({ key: 'tr:' + k, kind: 'edge', from: key(visits[k].i, visits[k].j), to: key(v.i, v.j), cls: k === visits.length - 2 ? 'hot' : 'soft', audit: 'edge-x', gapA: 1, gapB: 1.5 }));

  // ---------------------------------------------------------------------------------------------------
  // N × N
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'count-pairs', family: 'found-countable', order: 10, title: 'Numbering every pair of numbers',
    blurb: 'Row by row never gets past the first row. Diagonal by diagonal, each diagonal finite, reaches every pair (i, j) after finitely many steps: N × N is countable.',
    inputs: [
      { id: 'steps', kind: 'number', label: 'Steps', def: 15, min: 1, max: 28 },
      { id: 'walk', kind: 'choice', label: 'Walk', def: 'zig', options: [{ value: 'zig', label: 'diagonal by diagonal' }, { value: 'rows', label: 'row by row' }] },
    ],
    presets: [
      { label: 'Diagonals: 15 steps', values: { steps: 15, walk: 'zig' } },
      { label: 'Diagonals: 28 steps', values: { steps: 28, walk: 'zig' } },
      { label: 'Row by row gets stuck', values: { steps: 8, walk: 'rows' } },
    ],
    counters: [{ id: 'n', label: 'numbers given out' }, { id: 'rows', label: 'rows reached' }],
    run(inp) {
      const rows = inp.walk === 'rows';
      const steps = inp.steps;
      const visits = [];
      for (let n = 0; n < steps; n++) visits.push(rows ? { i: 0, j: n, d: n } : zig(n));
      const G = rows ? 6 : Math.max(4, Math.min(7, visits[visits.length - 1].d + 1));
      const num = new Map();
      const F2 = new T.Frames(['n', 'rows']);
      const scene = (upto) => {
        const seen = visits.slice(0, upto).filter((v) => v.i < G && v.j < G);
        const cur = upto ? visits[upto - 1] : null;
        const g = grid(G, { prefix: 'np', rowName: (i) => String(i), colName: (j) => String(j), axes: ['i', 'j'], cellOf: (i, j) => {
          const n = num.get(i + ',' + j);
          if (n !== undefined && n < upto) return { lines: ['(' + i + ',' + j + ')', '#' + n], cls: cur && cur.i === i && cur.j === j ? 'hot' : 'good' };
          return { text: '(' + i + ',' + j + ')', size: 13, cls: 'empty' };
        } });
        return g.items.concat(trail(seen, g.key));
      };
      visits.forEach((v, n) => num.set(v.i + ',' + v.j, n));
      F2.add({ items: scene(0), say: 'Every pair (i, j) of natural numbers is a cell of this grid, which goes on for ever to the right and downwards. To show N × N is countable, give each cell a number 0, 1, 2, … so that no cell is missed.', hl: { def: ['0'] }, meta: { q22: zigIndex(2, 2) } });
      let maxRow = 0;
      visits.forEach((v, n) => {
        maxRow = Math.max(maxRow, v.i);
        F2.count('n').set('rows', maxRow + 1);
        const nx = visits[n + 1];
        const off = v.j >= G;
        F2.add({ items: scene(n + 1), say: rows ? (off ? '(0, ' + v.j + ') gets #' + n + ', off the picture to the right. The walk is still in row 0, and it always will be.' : '(0, ' + v.j + ') gets #' + n + '. Still in row 0.') : '(' + v.i + ', ' + v.j + ') gets #' + n + (n === 0 ? '. Diagonal 0 has just this one cell.' : v.d !== visits[n - 1].d ? ': a new diagonal, i + j = ' + v.d + ', with ' + (v.d + 1) + ' cells.' : ', on diagonal i + j = ' + v.d + '.'), hl: { def: rows ? ['3'] : ['1', '2'] }, meta: nx && !rows ? { next: 'np:' + nx.i + ',' + nx.j, turn: nx.d !== v.d } : {} });
      });
      F2.add({ items: scene(steps), say: rows ? 'Row by row is a failure: row 0 alone is infinite, so (1, 0) would never get a number. A listing must reach every element after finitely many steps.' : 'Each diagonal is finite, so the walk finishes diagonal d and moves on. The cell (i, j) lies on diagonal i + j and is reached at step ' + 'd(d + 1)/2 + i or + j: every pair gets a number. N × N is countable, as big as N itself.', hl: { def: rows ? ['3'] : ['1', '2', '3'] }, mark: rows ? 'stuck' : 'countable' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Listing N × N', text: ['countable: a list e₀, e₁, e₂, … that reaches every element', 'diagonal d: the d + 1 cells with i + j = d', '#(i, j) = d(d + 1)/2 + (i if d is odd, j if d is even)', 'row by row: row 0 never ends, so row 1 is never reached'].join('\n') }] } };
    },
    predict: [
      { at: (f, i, fr, inp) => i === 0 && inp.walk === 'zig' && inp.steps > 12, pick: 'option', options: ['8', '10', '12', '24'], ask: 'Which number will the cell (2, 2) get?', answer: (fr) => String(fr[0].meta.q22), explain: () => '(2, 2) is on diagonal 4, which starts at #10 (after 1 + 2 + 3 + 4 cells), and it is the third cell along: #12.' },
      { at: (f) => f.meta && f.meta.turn, once: true, pick: 'item', ask: 'The diagonal is finished. Which cell comes next? Click it.', answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr, inp) => inp.walk === 'rows' && i === 2, pick: 'option', options: ['Yes, eventually', 'No, never'], ask: 'Will this walk ever give (1, 0) a number?', answer: () => 'No, never', explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why does the diagonal walk reach every pair while row by row does not?', options: ['Diagonals are shorter than rows', 'Each diagonal is finite, so every diagonal is finished after finitely many steps', 'It visits some cells twice', 'It skips cells'], answer: 1, why: 'The pair (i, j) lies on diagonal i + j, and only finitely many cells come before it.' },
      { q: 'Which number does the diagonal walk give to (0, 3)?', options: ['3', '6', '9', '10'], answer: 1, why: 'Diagonal 3 starts at #6 (after 1 + 2 + 3 cells) and, going this way, (0, 3) is its first cell.' },
      { q: 'N × N is countable. What follows for N × N × N?', options: ['It is uncountable', 'It is countable too: pair a pair with a number', 'Nothing'], answer: 1, why: 'N × N × N is (N × N) × N, and a numbering of N × N turns it into N × N again.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // The positive rationals
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'count-rationals', family: 'found-countable', order: 20, title: 'Every fraction gets a number',
    blurb: 'Put p/q in row p, column q, and walk the diagonals. A fraction that is not in lowest terms (like 2/4) is a repeat and is skipped; every positive rational is reached.',
    inputs: [{ id: 'steps', kind: 'number', label: 'Cells to visit', def: 15, min: 1, max: 28 }],
    presets: [
      { label: '15 cells', values: { steps: 15 } },
      { label: '28 cells', values: { steps: 28 } },
      { label: 'Just the start: the first repeat', values: { steps: 5 } },
    ],
    counters: [{ id: 'visited', label: 'cells visited' }, { id: 'listed', label: 'fractions listed' }, { id: 'skipped', label: 'repeats skipped' }],
    run(inp) {
      const steps = inp.steps;
      const visits = [];
      for (let n = 0; n < steps; n++) visits.push(zig(n));
      const G = Math.max(4, Math.min(7, visits[visits.length - 1].d + 1));
      const F2 = new T.Frames(['visited', 'listed', 'skipped']);
      const narrow = H.narrow();
      const info = visits.map((v) => { const p = v.i + 1, q = v.j + 1, g = gcd(p, q); return { p, q, g, fresh: g === 1 }; });
      let idx = 0;
      info.forEach((x) => { if (x.fresh) x.n = idx++; });
      const per = narrow ? 6 : 9;
      const scene = (upto) => {
        const cur = upto ? visits[upto - 1] : null;
        const state = new Map();
        visits.slice(0, upto).forEach((v, k) => state.set(v.i + ',' + v.j, info[k]));
        const g = grid(G, { prefix: 'qg', rowName: (i) => String(i + 1), colName: (j) => String(j + 1), axes: ['p', 'q'], cellOf: (i, j) => {
          const s = state.get(i + ',' + j), t = (i + 1) + '/' + (j + 1), here = cur && cur.i === i && cur.j === j;
          if (!s) return { text: t, cls: 'empty' };
          if (!s.fresh) return { lines: [t, '= ' + (s.p / s.g) + '/' + (s.q / s.g)], cls: 'gone' + (here ? ' bad' : '') };
          return { lines: [t, '#' + s.n], cls: here ? 'hot' : 'good' };
        } });
        const items = g.items.concat(trail(visits.slice(0, upto), g.key));
        // the list so far, under the grid
        const listed = info.slice(0, upto).filter((x) => x.fresh);
        const ly = g.h + 50;
        items.push({ key: 'ql:t', kind: 'text', x: -12, y: ly + 24, text: 'list', anchor: 'end', cls: 'title' });
        listed.forEach((x, k) => items.push({ key: 'ql:' + x.n, kind: 'cell', x: (k % per) * 50, y: ly + Math.floor(k / per) * 48, w: 46, h: 38, text: x.p + '/' + x.q, cls: 'mono good', size: 14, sub: undefined, enter: 'from', src: 'qg:' + (x.p - 1) + ',' + (x.q - 1) }));
        return items;
      };
      F2.add({ items: scene(0), say: 'Row p, column q holds the fraction p/q, so every positive rational appears somewhere, most of them many times (1/2 = 2/4 = 3/6 …). Walk the diagonals and give a number to each fraction the first time it shows up.', hl: { def: ['0'] } });
      visits.forEach((v, n) => {
        const x = info[n];
        F2.count('visited');
        if (x.fresh) F2.count('listed'); else F2.count('skipped');
        const nx = info[n + 1];
        F2.add({ items: scene(n + 1), say: x.fresh ? x.p + '/' + x.q + ' is in lowest terms and new: it gets #' + x.n + '.' : x.p + '/' + x.q + ' = ' + (x.p / x.g) + '/' + (x.q / x.g) + ', which already has a number, so it is skipped. Skipping keeps the list free of repeats.', hl: { def: [x.fresh ? '1' : '2'] }, meta: nx ? { nextSkip: !nx.fresh, nextFrac: nx.p + '/' + nx.q } : {} });
      });
      const last = info.filter((x) => x.fresh).length;
      F2.add({ items: scene(steps), say: last + ' different fractions listed so far. Any p/q in lowest terms sits at row p, column q, which the walk reaches after finitely many steps, so the positive rationals are countable. For all of Q, list 0 first and then each fraction followed by its negative.', hl: { def: ['3'] }, mark: 'countable' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Listing the fractions', text: ['p/q sits in row p, column q', 'gcd(p, q) = 1: new, give it the next number', 'gcd(p, q) > 1: a repeat of a smaller fraction, skip it', 'Q: 0, r₀, −r₀, r₁, −r₁, …'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.nextSkip, once: true, pick: 'option', options: ['Yes', 'No'], ask: (fr, i) => 'The next cell is ' + fr[i].meta.nextFrac + '. Will it get a new number?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i) => i === 0, pick: 'option', options: ['Yes', 'No'], ask: 'There are infinitely many fractions between 0 and 1 alone. Can all positive fractions still be numbered 0, 1, 2, …?', answer: () => 'Yes', explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why skip 2/4 instead of giving it a number?', options: ['It is not a rational number', 'It equals 1/2, which already has one, and a list should not repeat', 'It is too big', 'Skipping is optional and changes nothing about countability'], answer: 1, why: 'A numbering pairs each rational with one number. Even with repeats the list would show countability, but without them it is a one-to-one listing.' },
      { q: 'Between any two fractions lies another. Does that make the rationals uncountable?', options: ['Yes', 'No: being dense says nothing about whether they can be listed'], answer: 1, why: 'The diagonal walk lists them all, though no listing can be in increasing order.' },
      { q: 'Which number does 3/1 get in this walk?', options: ['#2', '#3', '#4', '#5'], answer: 1, why: 'The walk lists 1/1 (#0), 1/2 (#1), 2/1 (#2), then starts diagonal 2 with 3/1 (#3); 2/2 and 1/3 come after it.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // A full hotel with infinitely many rooms
  // ---------------------------------------------------------------------------------------------------
  const SCEN = {
    one: { label: 'one new guest', rule: 'room n → room n + 1', move: (n) => n + 1, newRoom: (k) => 1, count: 1 },
    three: { label: 'three new guests', rule: 'room n → room n + 3', move: (n) => n + 3, newRoom: (k) => k, count: 3 },
    bus: { label: 'a bus with infinitely many guests', rule: 'room n → room 2n', move: (n) => 2 * n, newRoom: (k) => 2 * k - 1, count: Infinity },
    finite: { label: 'a full hotel with 6 rooms', rule: 'room n → room n + 1', move: (n) => n + 1, newRoom: () => 1, count: 1, finite: 6 },
  };
  T.topic({
    id: 'hilbert-hotel', family: 'found-countable', order: 30, title: 'The hotel with infinitely many rooms',
    blurb: 'Every room is taken, yet a new guest gets a room: everyone moves up one. Even a bus with infinitely many guests fits, if everyone moves to the room with twice their number.',
    inputs: [{ id: 'scen', kind: 'choice', label: 'Who arrives', def: 'one', options: Object.entries(SCEN).map(([value, s]) => ({ value, label: s.label })) }],
    presets: [
      { label: 'One new guest', values: { scen: 'one' } },
      { label: 'Three new guests', values: { scen: 'three' } },
      { label: 'An infinite bus', values: { scen: 'bus' } },
      { label: 'A finite hotel cannot', values: { scen: 'finite' } },
    ],
    counters: [{ id: 'moved', label: 'guests moved' }, { id: 'arrived', label: 'new guests in' }],
    run(inp) {
      const S = SCEN[inp.scen];
      const narrow = H.narrow();
      const R = S.finite || (narrow ? 6 : 8);
      const W = 48, GAP = 6;
      const rx = (n) => (n - 1) * (W + GAP);
      const F2 = new T.Frames(['moved', 'arrived']);
      const newN = S.count === Infinity ? Math.ceil(R / 2) : S.count;
      const qx = (k) => -60 - (newN - k) * (W + GAP) - (narrow ? 0 : 20);
      // guests: g1 … gR in their rooms; where[g] is a room number (or null: moved off the picture)
      const where = {};
      for (let n = 1; n <= R; n++) where['g' + n] = n;
      const nw = {};
      for (let k = 1; k <= newN; k++) nw['n' + k] = null;
      const scene = (o) => {
        o = o || {};
        const items = [];
        for (let n = 1; n <= R; n++) items.push({ key: 'room:' + n, kind: 'cell', x: rx(n), y: 60, w: W, h: 40, text: String(n), cls: 'room' + ((o.free || []).includes(n) ? ' free' : ''), size: 15, pick: true });
        if (!S.finite) items.push({ key: 'room:more', kind: 'text', x: rx(R + 1) + 4, y: 86, text: '⋯ for ever', cls: 'strong', size: 15 });
        else items.push({ key: 'room:wall', kind: 'line', x1: rx(R + 1) - GAP / 2, y1: -10, x2: rx(R + 1) - GAP / 2, y2: 110, cls: 'hot' });
        items.push({ key: 'lbl:rooms', kind: 'text', x: -14, y: 86, text: 'rooms', anchor: 'end', cls: 'title' });
        for (const [g, n] of Object.entries(where)) if (n !== null && n <= R) items.push({ key: 'gu:' + g, kind: 'cell', x: rx(n), y: 0, w: W, h: 40, text: g, cls: 'mono guest' + ((o.bad || []).includes(g) ? ' bad' : ''), size: 14 });
        for (const [g, n] of Object.entries(nw)) {
          const k = +g.slice(1);
          if (n === null) items.push({ key: 'gu:' + g, kind: 'cell', x: narrow ? rx(k) : qx(k), y: narrow ? 124 : 0, w: W, h: 40, text: S.count === Infinity ? 'b' + k : g, cls: 'mono guest new', size: 14 });
          else if (n <= R) items.push({ key: 'gu:' + g, kind: 'cell', x: rx(n), y: 0, w: W, h: 40, text: S.count === Infinity ? 'b' + k : g, cls: 'mono guest new', size: 14 });
        }
        if (o.rule) {
          // an arc from each guest to the place it is going (only those whose target is on the picture)
          let top = o.arcs ? 0 : 60;
          for (let n = 1; n <= R && o.arcs; n++) {
            const m = S.move(n);
            if (m > R) continue;
            const bend = Math.max(22, (m - n) * (W + GAP) * 0.32);
            top = Math.max(top, bend);
            items.push({ key: 'arc:' + n, kind: 'edge', from: 'gu:g' + n, to: 'gu:g' + m, bend, cls: 'hot', audit: 'edge-x' });
          }
          if (S.finite && o.arcs) items.push({ key: 'arc:out', kind: 'edge', from: 'gu:g' + R, to: { x: rx(R + 1) + W / 2, y: -6 }, bend: 22, cls: 'bad' });
          items.push({ key: 'rule', kind: 'text', x: rx(1), y: -top - 24, text: 'everyone: ' + S.rule, cls: 'hot', size: 16 });
        }
        if (S.count === Infinity && Object.values(nw).every((n) => n === null)) items.push(narrow ? { key: 'bus:more', kind: 'text', x: rx(newN + 1) + 4, y: 149, text: '⋯', cls: 'strong', size: 16 } : { key: 'bus:more', kind: 'text', x: qx(1) - 12, y: 25, text: '⋯', anchor: 'end', cls: 'strong', size: 16 });
        return items;
      };
      F2.add({ items: scene(), say: S.finite ? 'A hotel with ' + R + ' rooms, every one taken: guest gn is in room n.' : 'Rooms 1, 2, 3, … go on for ever, and every one is taken: guest gn is in room n. The hotel is full.', hl: { def: ['0'] } });
      F2.add({ items: scene(), say: S.count === Infinity ? 'A bus arrives with infinitely many passengers b1, b2, b3, …, each wanting a room.' : (S.count === 1 ? 'A new guest arrives.' : 'Three new guests arrive.') + ' Nobody may share a room and nobody may be sent away.', hl: { def: ['0'] } });
      if (S.finite) {
        F2.add({ items: scene({ rule: true, arcs: true, bad: ['g' + R] }), say: 'Try the same trick: everyone moves from room n to room n + 1. But g' + R + ' in room ' + R + ' needs room ' + (R + 1) + ', and there is none.', hl: { def: ['1'] }, meta: { ask: 'finite' } });
        F2.add({ items: scene({ bad: ['g' + R] }), say: 'However the guests are shuffled, ' + (R + 1) + ' guests cannot fit in ' + R + ' rooms one to a room: that is the pigeonhole principle. Only an infinite hotel can be full and still take more.', hl: { def: ['3'] }, mark: 'no room' });
        return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The hotel', text: ['guest gn is in room n, every room taken', 'move: ' + S.rule, 'a finite hotel has a last room', 'n + 1 guests never fit in n rooms'].join('\n') }] } };
      }
      const free = [];
      for (let k = 1; k <= newN; k++) if (S.newRoom(k) <= R) free.push(S.newRoom(k));
      F2.add({ items: scene({ rule: true, arcs: true }), say: 'The trick: every guest moves at the same moment, from room n to ' + S.rule.replace('room n → ', '') + '. That room always exists, because there is no last room.', hl: { def: ['1'] }, meta: { free: free.map((n) => 'room:' + n) } });
      for (let n = 1; n <= R; n++) where['g' + n] = S.move(n);
      F2.count('moved', R);
      F2.add({ items: scene({ rule: true, free }), say: 'Everyone has moved. No two guests share a room, since different n give different ' + S.rule.replace('room n → room ', '') + ', and nobody left. Free now: ' + (S.count === Infinity ? 'every odd room 1, 3, 5, …' : 'room' + (free.length === 1 ? ' ' : 's ') + free.join(', ')) + '.' + (S.count === Infinity ? ' (Guests from rooms past ' + Math.floor(R / 2) + ' moved beyond the picture.)' : ''), hl: { def: ['1'] } });
      for (let k = 1; k <= newN; k++) nw['n' + k] = S.newRoom(k);
      F2.count('arrived', newN);
      F2.add({ items: scene({}), say: S.count === Infinity ? 'Passenger bk takes room 2k − 1: b1 → 1, b2 → 3, b3 → 5, and so on for every passenger. Even infinitely many more guests fit.' : (newN === 1 ? 'The new guest takes room 1.' : 'The new guests take rooms 1, 2 and 3.') + ' Everyone has a room again.', hl: { def: ['2'] } });
      F2.add({ items: scene({}), say: S.count === Infinity ? 'In counting terms: the evens and the odds are each as big as N, and N together with another copy of N is still countable. "Full" does not mean "no room" when the set is infinite.' : 'In counting terms: N with ' + newN + ' extra element' + (newN === 1 ? '' : 's') + ' can be put in one-to-one correspondence with N itself, by the map n ↦ n + ' + newN + '.', hl: { def: ['3'] }, mark: 'all in' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The hotel', text: ['guest gn is in room n, every room taken', 'move: ' + S.rule, 'newcomers: ' + (S.count === Infinity ? 'bk → room 2k − 1 (the odd rooms)' : S.count === 1 ? 'room 1' : 'rooms 1, 2, 3'), S.count === Infinity ? 'N ∪ N′ is as big as N' : '|N| + ' + newN + ' = |N|'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.free, pick: 'item', ask: 'After everyone moves, which room will be free? Click one.', answer: (fr, i) => fr[i].meta.free, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.ask === 'finite', pick: 'option', options: ['Yes, with some other shuffle', 'No'], ask: 'Could some other way of moving the guests make room?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why can guest g5 always move to room 6?', options: ['Room 6 is empty', 'There is no last room, and g6 is moving out at the same moment', 'g5 shares with g6', 'The hotel builds a new room'], answer: 1, why: 'All guests move at once, so room n + 1 is vacated as it is filled, and every room has a next one.' },
      { q: 'An infinite bus arrives. Which move frees infinitely many rooms?', options: ['n → n + 1', 'n → 2n', 'n → n − 1', 'Nothing works'], answer: 1, why: 'Doubling sends everyone to the even rooms and leaves every odd room free.' },
      { q: 'What does the hotel show about countable sets?', options: ['Infinite sets are all the same size', 'Adding a countable set to a countable set gives a countable set', 'N is finite', 'The rationals are uncountable'], answer: 1, why: 'Room numbers number the guests: the old ones and the new ones together still get one number each.' },
    ],
  });
})();
