// The Post correspondence problem as a domino puzzle: a bounded solver (breadth-first or iterative
// deepening), the modified problem and its conversion, the construction from a Turing machine, and a
// backtracking solver for Wang tilings.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  // A domino is {top, bottom}. A partial match is summarised by which row is ahead and by how much:
  // that overhang is all that matters for how the match can continue.
  function extend(state, d) {
    const x = state.side === 'top' ? state.over + d.top : d.top;
    const y = state.side === 'top' ? d.bottom : state.over + d.bottom;
    if (x.startsWith(y)) return { side: 'top', over: x.slice(y.length) };
    if (y.startsWith(x)) return { side: 'bottom', over: y.slice(x.length) };
    return null;
  }
  const skey = (s) => s.side[0] + s.over;
  const EMPTY = { side: 'top', over: '' };

  function verify(dominoes, seq, mpcp = false) {
    if (!seq.length) return { ok: false, reason: 'a match needs at least one domino' };
    if (mpcp && seq[0] !== 0) return { ok: false, reason: 'the modified problem must start with the first domino' };
    const top = seq.map((i) => dominoes[i].top).join(''), bottom = seq.map((i) => dominoes[i].bottom).join('');
    return { ok: top === bottom, top, bottom, reason: top === bottom ? '' : 'the rows differ' };
  }
  // the dominoes laid one by one, for drawing
  function layout(dominoes, seq) {
    let top = '', bottom = '';
    return seq.map((i, k) => { top += dominoes[i].top; bottom += dominoes[i].bottom; return { k, domino: i, top, bottom }; });
  }

  // Breadth-first search over overhang states (each state kept once): finds a shortest match within bounds.
  // verdict: match | none (the whole reachable state space was explored: no match exists) | limit.
  function solve(dominoes, opts = {}) {
    const mpcp = !!opts.mpcp, maxNodes = opts.maxNodes || 200000, maxOver = opts.maxOver || 60, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 500;
    if (opts.method === 'iddfs') return solveIDDFS(dominoes, opts);
    const trace = [], parent = new Map();
    let frontier = [], cut = false, nodes = 0;
    const firsts = mpcp ? [0] : dominoes.map((_, i) => i);
    for (const i of firsts) {
      const s = extend(EMPTY, dominoes[i]);
      if (!s) { if (wantTrace) trace.push({ kind: 'dead', say: `Domino ${i + 1} alone already disagrees: ${dominoes[i].top} over ${dominoes[i].bottom}.`, seq: [i] }); continue; }
      const k = skey(s);
      if (s.over === '') return found([i]);
      if (!parent.has(k)) { parent.set(k, { prev: null, d: i }); frontier.push(s); }
    }
    function seqOf(k) { const seq = []; for (let x = k; x != null; x = parent.get(x).prev) seq.unshift(parent.get(x).d); return seq; }
    function found(seq) {
      const v = verify(dominoes, seq, mpcp);
      trace.push({ kind: 'match', say: `A match with ${seq.length} domino${seq.length > 1 ? 'es' : ''}: ${seq.map((i) => i + 1).join(', ')}; both rows read ${v.top}.`, seq, rows: layout(dominoes, seq) });
      return { verdict: 'match', seq, top: v.top, nodes, trace };
    }
    while (frontier.length) {
      const next = [];
      for (const s of frontier) {
        const k0 = skey(s), seq0 = wantTrace && trace.length < traceLimit ? seqOf(k0) : null;
        for (let i = 0; i < dominoes.length; i++) {
          if (++nodes > maxNodes) { cut = true; break; }
          const t = extend(s, dominoes[i]);
          if (!t) continue;
          if (t.over === '') { parent.set('done', { prev: k0, d: i }); return found(seqOf('done')); }
          if (t.over.length > maxOver) { cut = true; continue; }
          const k = skey(t);
          if (parent.has(k)) continue;
          parent.set(k, { prev: k0, d: i });
          next.push(t);
          if (seq0 && trace.length < traceLimit) trace.push({ kind: 'try', say: `After ${seq0.concat(i).map((j) => j + 1).join(', ')} the ${t.side} row is ahead by ${t.over}.`, seq: seq0.concat(i), side: t.side, over: t.over });
        }
        if (cut && nodes > maxNodes) break;
      }
      if (nodes > maxNodes) break;
      frontier = next;
    }
    const none = !cut;
    trace.push({ kind: none ? 'none' : 'limit', say: none ? 'Every reachable overhang has been explored and none closes up: there is no match.' : `No match found within the bounds (${maxNodes} tries, overhang up to ${maxOver}).` });
    return { verdict: none ? 'none' : 'limit', seq: null, nodes, trace };
  }

  // Iterative deepening: depth-first with a growing length limit (memory stays small).
  function solveIDDFS(dominoes, opts = {}) {
    const mpcp = !!opts.mpcp, maxDepth = opts.maxDepth || 12, maxNodes = opts.maxNodes || 500000, trace = [];
    let nodes = 0;
    for (let depth = 1; depth <= maxDepth; depth++) {
      trace.push({ kind: 'depth', say: `Try every sequence of at most ${depth} dominoes.`, depth });
      const seq = [];
      const go = (s) => {
        if (seq.length && s.over === '') return true;
        if (seq.length === depth || nodes > maxNodes) return false;
        for (let i = 0; i < dominoes.length; i++) {
          if (mpcp && !seq.length && i !== 0) continue;
          nodes++;
          const t = extend(s, dominoes[i]);
          if (!t) continue;
          seq.push(i);
          if (go(t)) return true;
          seq.pop();
        }
        return false;
      };
      if (go(EMPTY)) {
        const v = verify(dominoes, seq, mpcp);
        trace.push({ kind: 'match', say: `A match: ${seq.map((i) => i + 1).join(', ')}; both rows read ${v.top}.`, seq: seq.slice(), rows: layout(dominoes, seq) });
        return { verdict: 'match', seq: seq.slice(), top: v.top, nodes, trace };
      }
      if (nodes > maxNodes) break;
    }
    trace.push({ kind: 'limit', say: `No match of length up to ${maxDepth}.` });
    return { verdict: 'limit', seq: null, nodes, trace };
  }

  // MPCP -> PCP: star every symbol (before it on top, after it on the bottom); the first domino gets an
  // extra leading star below so only it can start; a closing domino absorbs the last star.
  function mpcpToPcp(dominoes, star = '*', end = '$') {
    const pre = (u) => [...u].map((c) => star + c).join(''), post = (u) => [...u].map((c) => c + star).join('');
    const out = [{ top: pre(dominoes[0].top), bottom: star + post(dominoes[0].bottom), role: 'start' }];
    dominoes.forEach((d, i) => out.push({ top: pre(d.top), bottom: post(d.bottom), role: 'copy of ' + (i + 1) }));
    out.push({ top: star + end, bottom: end, role: 'end' });
    const trace = [
      { kind: 'star', say: `Put ${star} before every symbol on top and after every symbol below; now no domino can start a match, since tops begin with ${star} and bottoms do not.`, dominoes: out.slice(1, -1) },
      { kind: 'first', say: `Domino 1 gets a copy with an extra ${star} at the start of its bottom: the only domino that can begin.`, domino: out[0] },
      { kind: 'end', say: `Add ${star}${end} over ${end} to absorb the one ${star} left hanging at the end.`, domino: out[out.length - 1] },
    ];
    // MPCP match 1, i2, …, ik becomes 0, i2+1, …, ik+1, last
    const mapSeq = (seq) => [0, ...seq.slice(1).map((i) => i + 1), out.length - 1];
    return { dominoes: out, mapSeq, trace };
  }

  // TM -> MPCP: the match spells the accepting computation history #C0#C1#…#, one configuration per
  // round, the bottom always one configuration ahead. States become single letters so strings stay plain.
  // The machine must not move left from the first cell (true of the tiny machines this is meant for).
  function tmToMpcp(M, w) {
    if (M.k !== 1) throw new Error('single-tape machines only');
    const pool = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.split('').filter((c) => !M.gamma.includes(c));
    const sym = new Map();
    M.states.forEach((q, i) => sym.set(q, pool[i]));
    const S = (q) => sym.get(q), B = M.blank;
    const acc = M.accept.concat(M.halt);
    const input = T.tm.symbols(M, w);
    const dom = [], trace = [];
    const add = (top, bottom, role) => dom.push({ top, bottom, role });
    add('#', '#' + S(M.start) + (input.join('') || B) + '#', 'start');
    trace.push({ kind: 'start', say: `First domino: # over #${S(M.start)}${input.join('') || B}#, the start configuration (states are renamed ${[...sym].map(([q, c]) => `${q} = ${c}`).join(', ')}).`, domino: dom[0] });
    for (const r of M.rules) {
      if (acc.includes(r.from) || M.reject.includes(r.from)) continue;
      const q = S(r.from), a = r.read[0], p = S(r.to), b = r.write[0];
      if (r.move[0] === 'R') add(q + a, b + p, `${r.from}, ${a} → R`);
      else if (r.move[0] === 'S') add(q + a, p + b, `${r.from}, ${a} → S`);
      else for (const c of M.gamma) add(c + q + a, p + c + b, `${r.from}, ${a} → L (left of it: ${c})`);
    }
    trace.push({ kind: 'moves', say: 'One domino per move: the top shows the head\'s neighbourhood now, the bottom shows it one step later.', dominoes: dom.slice(1) });
    const n0 = dom.length;
    for (const c of M.gamma) add(c, c, 'copy ' + c);
    add('#', '#', 'next configuration');
    add('#', B + '#', 'blank at the right end');
    trace.push({ kind: 'copy', say: 'Copy dominoes carry the unchanged cells, # ends a configuration, and # over _# adds a blank on the right when needed.', dominoes: dom.slice(n0) });
    const n1 = dom.length;
    for (const qa of acc) for (const c of M.gamma) { add(c + S(qa), S(qa), 'accept eats left'); add(S(qa) + c, S(qa), 'accept eats right'); }
    for (const qa of acc) add(S(qa) + '##', '#', 'finish');
    trace.push({ kind: 'finish', say: 'Once the accepting state appears it eats the symbols beside it, one per configuration, and a final domino closes the match.', dominoes: dom.slice(n1) });
    return { dominoes: dom, symbols: Object.fromEntries(sym), trace };
  }

  // ---------- Wang tiles ----------
  // A tile is {n, e, s, w} (edge colours). Fill a width × height board so touching edges agree; options:
  // border (a colour every outer edge must have), first (tile index forced at the top-left), torus (wrap).
  function tile(tiles, width, height, opts = {}) {
    const board = Array.from({ length: height }, () => new Array(width).fill(-1));
    const trace = [], wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 2000, maxNodes = opts.maxNodes || 500000;
    let nodes = 0, cut = false;
    const fits = (x, y, t) => {
      const c = tiles[t];
      if (opts.first != null && x === 0 && y === 0 && t !== opts.first) return false;
      if (opts.border != null) {
        if (y === 0 && c.n !== opts.border) return false;
        if (x === 0 && c.w !== opts.border) return false;
        if (y === height - 1 && c.s !== opts.border) return false;
        if (x === width - 1 && c.e !== opts.border) return false;
      }
      if (x > 0 && tiles[board[y][x - 1]].e !== c.w) return false;
      if (y > 0 && tiles[board[y - 1][x]].s !== c.n) return false;
      if (opts.torus) {
        // on a board one cell wide (or high) the wrap-around neighbour is the tile itself
        if (x === width - 1 && tiles[x === 0 ? t : board[y][0]].w !== c.e) return false;
        if (y === height - 1 && tiles[y === 0 ? t : board[0][x]].n !== c.s) return false;
      }
      return true;
    };
    const go = (i) => {
      if (i === width * height) return true;
      if (++nodes > maxNodes) { cut = true; return false; }
      const x = i % width, y = Math.floor(i / width);
      for (let t = 0; t < tiles.length; t++) {
        if (!fits(x, y, t)) continue;
        board[y][x] = t;
        if (wantTrace && trace.length < traceLimit) trace.push({ kind: 'place', say: `Tile ${t + 1} fits at (${x + 1}, ${y + 1}).`, x, y, tile: t });
        if (go(i + 1)) return true;
        board[y][x] = -1;
        if (cut) return false;
      }
      if (wantTrace && trace.length < traceLimit) trace.push({ kind: 'backtrack', say: `Nothing fits at (${x + 1}, ${y + 1}): step back.`, x, y });
      return false;
    };
    const ok = go(0);
    trace.push({ kind: ok ? 'tiled' : cut ? 'limit' : 'impossible', say: ok ? `The ${width} × ${height} board is tiled.` : cut ? 'Gave up: too many tries.' : `No tiling of the ${width} × ${height} board exists.` });
    return { verdict: ok ? 'tiled' : cut ? 'limit' : 'impossible', board: ok ? board.map((r) => r.slice()) : null, nodes, trace };
  }
  function checkTiling(tiles, board, opts = {}) {
    const h = board.length, w = board[0].length;
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const c = tiles[board[y][x]];
      if (!c) return false;
      if (x > 0 && tiles[board[y][x - 1]].e !== c.w) return false;
      if (y > 0 && tiles[board[y - 1][x]].s !== c.n) return false;
      if (opts.border != null && ((y === 0 && c.n !== opts.border) || (x === 0 && c.w !== opts.border) || (y === h - 1 && c.s !== opts.border) || (x === w - 1 && c.e !== opts.border))) return false;
      if (opts.torus && ((x === w - 1 && tiles[board[y][0]].w !== c.e) || (y === h - 1 && tiles[board[0][x]].n !== c.s))) return false;
      if (opts.first != null && x === 0 && y === 0 && board[0][0] !== opts.first) return false;
    }
    return true;
  }

  T.pcp = { extend, verify, layout, solve, solveIDDFS, mpcpToPcp, tmToMpcp };
  T.wang = { tile, check: checkTiling };
})();
