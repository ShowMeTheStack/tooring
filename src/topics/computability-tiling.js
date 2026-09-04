// Wang tiles: square tiles with a colour on each edge, placed without turning so that touching edges agree.
// A puzzle with a backtracking solver that places, gets stuck and steps back; and a tile set that computes,
// each row of a tiling being the next number of a binary counter, which is why tiling the plane is as
// hard as deciding whether a machine runs for ever.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'tiling', part: 'computability', order: 80, title: 'Tiling', blurb: 'Square tiles with coloured edges, laid so neighbours agree: a jigsaw that can carry out any computation, so no algorithm can tell whether a set of tiles covers the whole plane.' });

  const COLOURS = ['amber', 'blue', 'green', 'red', 'purple', 'teal', 'pink', 'lime'];
  const SIDES = ['north', 'east', 'south', 'west'];
  const parseTile = (s) => [...String(s)].map(Number);
  const desc = (t) => t.map((c, i) => SIDES[i] + ' ' + COLOURS[c]).join(', ');

  // ---------------------------------------------------------------- tile-puzzle
  const SET_A = ['0120', '1112', '1211', '1022'];
  const SET_B = ['1202', '2101', '2020', '1210'];
  const SET_X = ['2001', '1022', '0222', '0011'];
  const MAXF = 70;
  T.topic({
    id: 'tile-puzzle', family: 'tiling', order: 10, title: 'A tiling puzzle',
    blurb: 'Fill the board with copies of the tiles, never turning them, so that every pair of touching edges has the same colour. A solver goes cell by cell, backing up when nothing fits.',
    inputs: [
      { id: 'tiles', kind: 'list', label: 'Tiles (north east south west, colours 0–7)', def: SET_A, check: (v) => {
        if (!v.length) return 'Tiles: give at least one tile, as four digits like 0120';
        if (v.length > 6) return 'Tiles: at most 6 tiles';
        const bad = v.find((x) => !/^[0-7]{4}$/.test(x));
        return bad !== undefined ? 'Tiles: "' + bad + '" should be four colour digits 0–7 (north, east, south, west), like 0120' : null;
      } },
      { id: 'w', kind: 'number', label: 'Width', def: 3, min: 1, max: 4 },
      { id: 'h', kind: 'number', label: 'Height', def: 3, min: 1, max: 4 },
      { id: 'wrap', kind: 'choice', label: 'Edges', def: 'plain', options: [{ value: 'plain', label: 'a plain board' }, { value: 'torus', label: 'wrap round (a torus)' }] },
    ],
    presets: [
      { label: 'Four tiles on a 3 × 3 board', values: { tiles: SET_A, w: 3, h: 3, wrap: 'plain' } },
      { label: 'The same tiles wrapped round: impossible', values: { tiles: SET_A, w: 3, h: 3, wrap: 'torus' } },
      { label: 'Lots of backtracking', values: { tiles: SET_B, w: 3, h: 3, wrap: 'plain' } },
      { label: 'No tiling at all', values: { tiles: SET_X, w: 3, h: 3, wrap: 'plain' } },
    ],
    counters: [{ id: 'placed', label: 'tiles placed' }, { id: 'back', label: 'backtracks' }, { id: 'filled', label: 'cells filled' }],
    run(inp) {
      const tiles = inp.tiles.map(parseTile), W = inp.w, H = inp.h, torus = inp.wrap === 'torus';
      const res = T.wang.tile(tiles.map((t) => ({ n: t[0], e: t[1], s: t[2], w: t[3] })), W, H, { torus, traceLimit: 4000 });
      const steps = res.trace.filter((s) => s.kind === 'place' || s.kind === 'backtrack');
      const board = Array.from({ length: H }, () => new Array(W).fill(null));
      const F = new T.Frames(['placed', 'back', 'filled']);
      const PS = 52, BS = 62;
      const palW = tiles.length * (PS + 3);
      const boardW = W * (BS + 3);
      const BX = Math.max(0, (palW - boardW) / 2), BY = 120;
      const fits = (x, y, t) => {
        const c = tiles[t];
        if (x > 0 && board[y][x - 1] !== null && tiles[board[y][x - 1]][1] !== c[3]) return false;
        if (y > 0 && board[y - 1][x] !== null && tiles[board[y - 1][x]][2] !== c[0]) return false;
        if (torus && x === W - 1 && board[y][0] !== null && tiles[x === 0 ? t : board[y][0]][3] !== c[1]) return false;
        if (torus && y === H - 1 && board[0][x] !== null && tiles[y === 0 ? t : board[0][x]][0] !== c[2]) return false;
        return true;
      };
      const scene = (hot, mark, palHot) => {
        const pal = K.dominoes.wang({ tiles, grid: [tiles.map((_, i) => i)], size: PS, prefix: 'pal', check: false }).items;
        for (const it of pal) { it.pick = true; it.enter = 'fade'; const i = +it.key.split(',')[1]; if (i === palHot) it.cls = 'hot'; }
        const nums = tiles.map((_, i) => ({ key: 'pn' + i, kind: 'text', x: i * (PS + 3) + PS / 2, y: PS + 18, text: String(i + 1), anchor: 'middle', cls: 'strong' }));
        const b = K.dominoes.wang({ tiles, grid: board, size: BS, prefix: 'bd', x: BX, y: BY }).items;
        for (const it of b) {
          const [r, c] = it.key.split(':').pop().split(',').map(Number);
          if (hot && r === hot[1] && c === hot[0]) it.cls = (it.cls ? it.cls + ' ' : '') + (mark === 'bad' ? 'bad' : 'hot');
        }
        const items = [{ key: 'palT', kind: 'text', x: 0, y: -14, text: 'tiles: any number of copies, no turning', cls: 'strong' }].concat(pal, nums, b);
        if (torus) items.push({ key: 'torusT', kind: 'text', x: BX, y: BY + H * (BS + 3) + 26, text: 'wraps round: the right edge meets the left, the bottom meets the top', cls: 'strong' });
        return items;
      };
      F.add({ items: scene(null), say: 'Fill the ' + W + ' × ' + H + ' board with copies of these ' + tiles.length + ' tiles so that touching edges match' + (torus ? ', and, since the board wraps round, the right edge must match the left and the bottom the top' : '') + '. The solver goes row by row, left to right, trying tile 1 first.' });
      let asked = 0;
      const show = steps.length > MAXF ? steps.slice(0, MAXF - 4) : steps;
      show.forEach((s, k) => {
        const idx = s.y * W + s.x;
        // everything after this cell is empty again: the solver has come back here
        for (let j = idx + (s.kind === 'place' ? 1 : 0); j < W * H; j++) board[Math.floor(j / W)][j % W] = null;
        if (s.kind === 'place') {
          const options = tiles.map((_, t) => t).filter((t) => fits(s.x, s.y, t));
          // a question before a forced move: the one tile that fits
          const ask = options.length === 1 && asked < 3 && k > 0 && (s.x > 0 || s.y > 0);
          if (ask) { asked++; F.add({ items: scene([s.x, s.y]), say: 'The lit cell is next. Its neighbours already placed fix the colours it needs.', meta: { ask: 'pal:0,' + s.tile, why: 'Tile ' + (s.tile + 1) + ' (' + desc(tiles[s.tile]) + ') is the only one whose edges agree with its placed neighbours.' } }); }
          board[s.y][s.x] = s.tile;
          F.count('placed');
          F.set('filled', board.flat().filter((x) => x !== null).length);
          const need = [];
          if (s.x > 0) need.push('west ' + COLOURS[tiles[s.tile][3]] + ' to meet its left neighbour');
          if (s.y > 0) need.push('north ' + COLOURS[tiles[s.tile][0]] + ' to meet the tile above');
          F.add({ items: scene([s.x, s.y], 'hot', s.tile), say: 'Cell (' + (s.x + 1) + ', ' + (s.y + 1) + '): tile ' + (s.tile + 1) + ' fits' + (need.length ? ', with ' + need.join(' and ') : ' as the first tile') + (options.length > 1 ? '; ' + options.length + ' tiles fit here, so this is a guess the solver may have to take back.' : '; it is the only tile that fits.'), hl: { tiles: [String(s.tile)] } });
        } else {
          F.count('back');
          F.add({ items: scene([s.x, s.y], 'bad'), say: 'Cell (' + (s.x + 1) + ', ' + (s.y + 1) + '): no tile fits its neighbours' + (torus && (s.x === W - 1 || s.y === H - 1) ? ' (including the ones it wraps round to)' : '') + '. Step back and try the next tile in the cell before.', mark: 'stuck', hl: { tiles: [] } });
        }
      });
      if (show.length < steps.length) F.add({ items: scene(null), say: '… and ' + (steps.length - show.length) + ' more placements and backtracks, skipped here.' });
      if (res.verdict === 'tiled') {
        for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) board[y][x] = res.board[y][x];
        F.set('filled', W * H);
        F.add({ items: scene(null), say: 'The board is full and every pair of touching edges agrees' + (torus ? ', across the wrap-round too' : '') + ': a tiling.', mark: 'tiled' });
      } else {
        for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) board[y][x] = null;
        F.set('filled', 0);
        F.add({ items: scene(null), say: res.verdict === 'impossible' ? 'Every choice in every cell has been tried and each one got stuck: no tiling of this board exists' + (torus ? '. The plain board has one, but its colours never wrap round to meet.' : '.') : 'The solver gave up after too many tries.', mark: res.verdict });
      }
      return { frames: F.list, def: { sections: [
        { id: 'tiles', kind: 'table', title: 'The tiles', colHead: SIDES, rowHead: tiles.map((_, i) => String(i + 1)), rows: tiles.map((t) => t.map((c) => c + ' ' + COLOURS[c])) },
        { id: 'rule', kind: 'math', title: 'The rule', text: 'east of a tile = west of its right neighbour\nsouth of a tile = north of the tile below' + (torus ? '\nthe last column meets the first, the last row the first' : '') },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, pick: 'item', ask: 'Only one tile fits the lit cell. Click it among the tiles at the top.', answer: (fr, i) => fr[i].meta.ask, explain: (fr, i) => fr[i].meta.why },
    ],
    quiz: [
      { q: 'Why does the solver sometimes step back to an earlier cell?', options: ['An earlier guess left a cell where no tile fits, so that guess must change', 'It forgot which tile it placed', 'The board is too small', 'To check its work'], answer: 0, why: 'When several tiles fit a cell the solver guesses; if that guess makes a later cell impossible, it undoes it and tries the next one.' },
      { q: 'A tile set tiles a 3 × 3 board but not the same board wrapped round. Why can that happen?', options: ['Wrapping adds constraints: the right edge must also match the left and the bottom the top', 'A torus has fewer cells', 'Tiles may be turned on a torus', 'It cannot happen'], answer: 0, why: 'The wrap-round edges must agree too, which can rule out every tiling the plain board allows.' },
      { q: 'If the tiles cannot even fill some n × n square, can they tile the whole plane?', options: ['No: any tiling of the plane contains a tiling of every square', 'Yes, the plane has more room', 'Only if n is odd', 'It depends on the colours'], answer: 0, why: 'Cut an n × n square out of a tiling of the plane and you have a tiling of the square. So a stuck square proves the plane cannot be tiled.' },
      { q: 'Can a solver decide whether a tile set covers the whole infinite plane by trying bigger and bigger squares?', options: ['It finds out when some square fails, but if every square works it never finishes', 'Yes, squares of size 10 are enough', 'Yes, by trying every tile in every cell', 'No tile set can tile the plane'], answer: 0, why: 'Failing squares give a "no", but there are tile sets that tile the plane only in patterns that never repeat, so success can never be confirmed by a finite search. In general the question is undecidable.' },
    ],
  });

  // ---------------------------------------------------------------- tile-compute: rows are steps of a computation
  // Each tile is a cell of a binary counter: north = the old bit, east = the carry coming in, south = the
  // new bit, west = the carry going out. Bits are blue (0) and amber (1); carries purple (none) and red (one).
  const BIT = [1, 0], CAR = [4, 3];
  const CTILES = [[0, 0], [0, 1], [1, 0], [1, 1]].map(([b, c]) => [BIT[b], CAR[c], BIT[b ^ c], CAR[b & c]]);
  const CNAME = ['0, no carry', '0, carry in', '1, no carry', '1, carry in'];
  T.topic({
    id: 'tile-compute', family: 'tiling', order: 20, title: 'Tiles that compute',
    blurb: 'Four tiles that add one: the north edges of each row spell a binary number, a carry enters on the right, and the south edges spell the next number. Every row is forced by the one above, so a tiling is a computation, and it stops exactly when the computation would.',
    inputs: [
      { id: 'bits', kind: 'number', label: 'Bits per row', def: 3, min: 2, max: 4 },
      { id: 'start', kind: 'number', label: 'Starting number', def: 0, min: 0, max: 15 },
      { id: 'rows', kind: 'number', label: 'Rows', def: 5, min: 2, max: 8 },
      { id: 'over', kind: 'choice', label: 'Left edge', def: 'free', options: [{ value: 'free', label: 'a carry may fall off (it wraps to 0)' }, { value: 'none', label: 'no carry may leave (it halts)' }] },
    ],
    check: (inp) => (inp.start >= 2 ** inp.bits ? 'Starting number: at most ' + (2 ** inp.bits - 1) + ' with ' + inp.bits + ' bits' : null),
    presets: [
      { label: 'Count from 0 with 3 bits', values: { bits: 3, start: 0, rows: 5, over: 'free' } },
      { label: 'A long carry: 0111', values: { bits: 4, start: 7, rows: 3, over: 'free' } },
      { label: 'Overflow wraps round to 0', values: { bits: 2, start: 1, rows: 5, over: 'free' } },
      { label: 'Overflow forbidden: the tiling gets stuck', values: { bits: 2, start: 1, rows: 5, over: 'none' } },
    ],
    counters: [{ id: 'rows', label: 'rows tiled' }, { id: 'tiles', label: 'tiles placed' }],
    run(inp) {
      const N = inp.bits, R = inp.rows;
      const S = 58, G = 3;
      const F = new T.Frames(['rows', 'tiles']);
      const grid = [];
      const value = (bits) => bits.reduce((a, b) => a * 2 + b, 0);
      const bitsOf = (v) => Array.from({ length: N }, (_, i) => (v >> (N - 1 - i)) & 1);
      const PX = N * (S + G) + 150;
      const scene = (hot, stuck) => {
        const items = [];
        // the seed: the starting number written above the board
        bitsOf(inp.start).forEach((b, i) => items.push({ key: 'seed' + i, kind: 'cell', x: i * (S + G), y: -50, w: S, h: 34, text: String(b), cls: 'mono ' + (b ? 'hot' : 'act') }));
        items.push({ key: 'seedT', kind: 'text', x: N * (S + G) + 14, y: -27, text: 'start ' + inp.start, cls: 'strong' });
        items.push(...K.dominoes.wang({ tiles: CTILES, grid, size: S, prefix: 'bd' }).items);
        for (const it of items) if (it.kind === 'tile' && hot) { const [r, c] = it.key.split(':').pop().split(',').map(Number); if (r === hot[0] && c === hot[1]) it.cls = 'hot'; }
        grid.forEach((row, r) => {
          const done = row.every((x) => x !== null);
          if (!done) return;
          const v = value(row.map((t) => [0, 0, 1, 1][t] ^ [0, 1, 0, 1][t]));
          items.push({ key: 'rv' + r, kind: 'text', x: N * (S + G) + 14, y: r * (S + G) + S / 2 + 5, text: '→ ' + v, cls: 'strong' });
        });
        if (stuck) { const k = items.findIndex((it) => it.key === 'bd:e:' + stuck[0] + ',' + stuck[1]); if (k >= 0) items.splice(k, 1); }
        if (stuck) items.push({ key: 'stuck', kind: 'cell', x: stuck[1] * (S + G), y: stuck[0] * (S + G), w: S, h: S, text: '?', cls: 'bad', rx: 3 });
        // the four tiles, labelled, on the right
        CTILES.forEach((t, i) => {
          items.push({ key: 'pal' + i, kind: 'tile', x: PX, y: i * (S + 22), size: S, edges: t, pick: true });
          items.push({ key: 'palL' + i, kind: 'text', x: PX + S + 12, y: i * (S + 22) + S / 2 + 5, text: 'bit ' + CNAME[i], cls: 'strong' });
        });
        items.push({ key: 'palT', kind: 'text', x: PX, y: -27, text: 'the four tiles', cls: 'title' });
        items.push({ key: 'key1', kind: 'text', x: PX, y: 4 * (S + 22) + 8, text: 'north/south: blue 0, amber 1', cls: 'strong' });
        items.push({ key: 'key2', kind: 'text', x: PX, y: 4 * (S + 22) + 32, text: 'east/west: purple no carry, red carry', cls: 'strong' });
        return items;
      };
      F.add({ items: scene(null), say: 'Each tile is one cell of a counter: its north edge is the old bit, its east edge the carry coming in from the right, its south edge the new bit and its west edge the carry going out. The seed row says the count starts at ' + inp.start + '.' });
      let cur = bitsOf(inp.start), asked = 0, halted = false;
      for (let r = 0; r < R && !halted; r++) {
        grid.push(new Array(N).fill(null));
        let carry = 1;
        for (let c = N - 1; c >= 0; c--) {
          const b = cur[c], t = b * 2 + carry;
          const outCarry = b & carry;
          if (c === 0 && outCarry && inp.over === 'none') {
            F.add({ items: scene(null, [r, 0]), say: 'Row ' + (r + 1) + ', leftmost cell: the only tile with north ' + (b ? 'amber' : 'blue') + ' and east red sends a carry out of the left edge, which this board forbids. No tile fits, so the tiling cannot go on: the counter has overflowed and the computation has halted.', mark: 'halted' });
            halted = true;
            break;
          }
          const first = r === 0 || (r === 1 && asked < 2);
          if (first && asked < 2 && (r > 0 || c < N - 1)) {
            asked++;
            F.add({ items: scene([r, c]), say: 'The lit cell needs north ' + (b ? 'amber (bit 1)' : 'blue (bit 0)') + ' to match the bit above, and east ' + (carry ? 'red (a carry)' : 'purple (no carry)') + ' to match its right neighbour.', meta: { ask: 'pal' + t, why: 'Only the tile for bit ' + CNAME[t] + ' has those two edges; its south edge is the new bit ' + (b ^ carry) + '.' } });
          }
          grid[r][c] = t;
          F.count('tiles');
          if (r === 0) F.add({ items: scene([r, c]), say: 'Cell ' + (N - c) + ' from the right: old bit ' + b + ', carry in ' + carry + '. Exactly one tile fits: new bit ' + (b ^ carry) + ', carry out ' + outCarry + '.' + (c === N - 1 ? ' The right edge always brings in a carry: that is the "+1".' : '') });
          carry = outCarry;
        }
        if (halted) break;
        const next = cur.map((b, i) => [0, 0, 1, 1][grid[r][i]] ^ [0, 1, 0, 1][grid[r][i]]);
        F.count('rows');
        F.add({ items: scene(null), say: 'Row ' + (r + 1) + ' is forced: ' + cur.join('') + ' (' + value(cur) + ') on top becomes ' + next.join('') + ' (' + value(next) + ') below' + (value(next) === 0 && value(cur) !== 0 ? ', the carry falling off the left edge and the count wrapping to 0' : '') + '. The next row must start from these bits.' });
        cur = next;
      }
      if (!halted) F.add({ items: scene(null), say: 'No choice was ever made: every row follows from the one above, as every step of a machine follows from its configuration. With carries allowed to fall off, the rows go on for ever, so these tiles fill an infinite strip below the seed. Swap the counter for any Turing machine and the same idea gives tiles that cover the plane exactly when the machine never halts; that is why no algorithm can decide whether a tile set tiles the plane.', mark: 'tiled' });
      return { frames: F.list, def: { sections: [
        { id: 'tiles', kind: 'table', title: 'The counter tiles', colHead: ['north (old bit)', 'east (carry in)', 'south (new bit)', 'west (carry out)'], rowHead: CNAME.map((x) => 'bit ' + x), rows: [[0, 0], [0, 1], [1, 0], [1, 1]].map(([b, c]) => [String(b), String(c), String(b ^ c), String(b & c)]) },
        { id: 'rule', kind: 'math', title: 'One row is one step', text: 'new bit = old bit XOR carry in\ncarry out = old bit AND carry in\nthe right edge brings in carry 1: each row adds one' + (inp.over === 'none' ? '\nthe left edge allows no carry out: overflow means no tile fits' : '') },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, pick: 'item', ask: 'Which of the four tiles fits the lit cell? Click it on the right.', answer: (fr, i) => fr[i].meta.ask, explain: (fr, i) => fr[i].meta.why },
    ],
    quiz: [
      { q: 'Why is there never a choice when a row of the counter is tiled from right to left?', options: ['The north edge (the old bit) and the east edge (the carry) together pick out exactly one of the four tiles', 'There is only one tile', 'The solver always picks the first', 'There is a choice'], answer: 0, why: 'The four tiles are one for each pair of old bit and carry in, so the cell above and the cell to the right decide the tile.' },
      { q: 'With the left edge forbidding a carry, why does the tiling get stuck?', options: ['When every bit is 1, the leftmost cell would have to send a carry out, and no tile may', 'The tiles run out', 'The board is too wide', 'Because 0 has no tile'], answer: 0, why: 'At overflow the forced tile has a red west edge, which the border rules out, so no tile fits: the tiling stops exactly when the counter "halts".' },
      { q: 'What is the link between tilings and machines?', options: ['Rows can be the configurations of any Turing machine, so tiles can be made that cover the plane exactly when it runs for ever', 'Machines are made of tiles', 'Tiles can only count', 'There is none'], answer: 0, why: 'Edges carry the tape symbols and the state down from row to row, as here they carry bits; a halting machine leaves a row where nothing fits.' },
      { q: 'What does this show about the question "does this tile set cover the whole plane?"', options: ['It is undecidable, since a decider would tell whether machines run for ever', 'It is decidable by trying squares', 'Every tile set covers the plane', 'It only matters for counters'], answer: 0, why: 'Turning machines into tile sets reduces the (non-)halting question to tiling, so tiling the plane has no general algorithm.' },
    ],
  });
})();
