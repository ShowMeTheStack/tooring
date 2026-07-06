// Cook–Levin: from a small nondeterministic machine N, an input w and a time bound t, build the tableau and
// the CNF formula that is satisfiable exactly when N accepts w within t steps.
//
// The tableau has t + 1 rows, one configuration each, written # u q v # with the state just left of the
// head's cell; a row has width W = C + 3 where C = max(|w|, t + 1) tape cells (the head cannot get further).
// The tape ends on the left: a left move from the first cell stays put. Halting rows repeat unchanged.
//
// Variables x(i, j, s): cell (i, j) holds s. Clauses: cell (exactly one symbol per cell), start (row 0 is
// the start configuration), accept (an accepting state appears somewhere), move (every 2 × 3 window is
// legal). A window position's legal windows are read off every pair (row, next row) of this width, and
// "the window is one of these" becomes CNF with one selector variable per legal window.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const SEP = '\u0001';

  function setup(N, w, t) {
    if (N.k !== 1) throw new Error('single-tape machines only');
    const input = T.tm.symbols(N, w), C = Math.max(input.length, t + 1), W = C + 3;
    const Q = N.states.map((q) => 'q:' + q);
    const symbols = ['#', ...N.gamma, ...Q];
    const sIndex = new Map(symbols.map((s, i) => [s, i]));
    const halting = (q) => T.tm.isHalting(N, q);
    const start = ['#', 'q:' + N.start, ...input, ...new Array(C - input.length).fill(N.blank), '#'];
    return { input, C, W, Q, symbols, sIndex, halting, start };
  }

  // All successor rows of a row (empty when the machine is stuck or would leave the tableau).
  function successors(N, S, row) {
    const p = row.findIndex((x) => x.startsWith('q:'));
    const q = row[p].slice(2);
    if (S.halting(q)) return [{ row, rule: null }];
    const a = row[p + 1], out = [];
    for (const r of N.delta.get(q + T.tm.SEP + a) || []) {
      const nr = row.slice(), b = r.write[0], to = 'q:' + r.to;
      if (r.move[0] === 'R') { if (p + 1 > S.C) continue; nr[p] = b; nr[p + 1] = to; }
      else if (r.move[0] === 'L' && p > 1) { nr[p - 1] = to; nr[p] = row[p - 1]; nr[p + 1] = b; }
      else { nr[p] = to; nr[p + 1] = b; }
      out.push({ row: nr, rule: r });
    }
    return out;
  }

  // Breadth-first search over rows for an accepting run within t steps (the run used to fill the tableau).
  function acceptingRun(N, w, t) {
    const S = setup(N, w, t);
    const key = (r) => r.join(SEP);
    let frontier = [{ row: S.start, prev: null }];
    const isAcc = (row) => row.some((x) => x.startsWith('q:') && T.tm.isAccept(N, x.slice(2)));
    for (let i = 0; i <= t; i++) {
      const hit = frontier.find((n) => isAcc(n.row));
      if (hit) { const rows = []; for (let n = hit; n; n = n.prev) rows.unshift(n.row); while (rows.length < t + 1) rows.push(rows[rows.length - 1]); return { accepts: true, rows, steps: i }; }
      if (i === t) break;
      const seen = new Set(), next = [];
      for (const n of frontier) for (const s of successors(N, S, n.row)) { const k = key(s.row); if (!seen.has(k)) { seen.add(k); next.push({ row: s.row, prev: n }); } }
      frontier = next;
    }
    return { accepts: false, rows: null };
  }

  // The legal windows at each column offset j (window over columns j, j+1, j+2), from every row of width W.
  function legalWindows(N, S) {
    const per = Array.from({ length: S.W - 2 }, () => new Set());
    const G = N.gamma, C = S.C, digits = new Array(C).fill(0);
    let rows = 0;
    for (let more = true; more;) {
      for (let p = 1; p <= C; p++) for (const q of S.Q) {
        const row = ['#'];
        for (let c = 0, d = 0; c <= C; c++) { if (c === p - 1) row.push(q); else row.push(G[digits[d++]]); }
        row.push('#');
        rows++;
        for (const s of successors(N, S, row)) for (let j = 0; j + 2 < S.W; j++) per[j].add([row[j], row[j + 1], row[j + 2], s.row[j], s.row[j + 1], s.row[j + 2]].join(SEP));
      }
      let i = 0;
      while (i < C && ++digits[i] === G.length) { digits[i] = 0; i++; }
      more = i < C;
    }
    return { per: per.map((s) => [...s].map((x) => x.split(SEP))), rows };
  }

  function build(N, w, t, opts = {}) {
    const S = setup(N, w, t), W = S.W, K = S.symbols.length, R = t + 1;
    const x = (i, j, s) => 1 + (i * W + j) * K + S.sIndex.get(s);
    let nVars = R * W * K;
    const clauses = [], counts = { cell: 0, start: 0, accept: 0, move: 0 };
    const add = (c, kind) => { clauses.push(c); counts[kind]++; };
    const trace = [{ kind: 'tableau', say: `The tableau has ${R} rows (time 0 to ${t}) and ${W} columns; each cell holds one of ${K} symbols (#, the ${N.gamma.length} tape symbols, the ${N.states.length} states).`, rows: R, cols: W, symbols: S.symbols }];
    // cell: exactly one symbol in every cell
    for (let i = 0; i < R; i++) for (let j = 0; j < W; j++) {
      add(S.symbols.map((s) => x(i, j, s)), 'cell');
      for (let a = 0; a < K; a++) for (let b = a + 1; b < K; b++) add([-x(i, j, S.symbols[a]), -x(i, j, S.symbols[b])], 'cell');
    }
    trace.push({ kind: 'cell', say: `Cell clauses: every cell holds at least one symbol and no two: ${counts.cell} clauses.`, count: counts.cell });
    // start: row 0 is the start configuration
    S.start.forEach((s, j) => add([x(0, j, s)], 'start'));
    trace.push({ kind: 'start', say: `Start clauses: row 0 reads ${S.start.map((s) => s.replace('q:', '')).join(' ')}: ${counts.start} one-literal clauses.`, row: S.start, count: counts.start });
    // accept: some cell holds an accepting state
    const accLits = [];
    for (const q of N.accept.concat(N.halt)) for (let i = 0; i < R; i++) for (let j = 0; j < W; j++) accLits.push(x(i, j, 'q:' + q));
    add(accLits, 'accept');
    trace.push({ kind: 'accept', say: `Accept clause: one big clause saying an accepting state appears in some cell (${accLits.length} literals).`, count: 1 });
    // move: every window is legal
    const L = legalWindows(N, S);
    const selectors = [];
    for (let i = 0; i + 1 < R; i++) for (let j = 0; j + 2 < W; j++) {
      const list = L.per[j], ys = list.map(() => ++nVars);
      selectors.push({ i, j, first: ys[0], windows: list });
      add(ys, 'move');
      list.forEach((win, l) => {
        for (let c = 0; c < 6; c++) add([-ys[l], x(i + (c < 3 ? 0 : 1), j + (c % 3), win[c])], 'move');
      });
    }
    trace.push({ kind: 'move', say: `Move clauses: for each of the ${t * (W - 2)} window positions, one selector per legal window (${L.per.map((l) => l.length).join(', ')} legal windows by column, found from ${L.rows} rows); a selector forces its six cells, and one selector must be on. ${counts.move} clauses.`, count: counts.move, legal: L.per.map((l) => l.length) });
    const formula = { n: nVars, clauses, names: null };
    trace.push({ kind: 'total', say: `The formula has ${nVars} variables and ${clauses.length} clauses: polynomial in |w| for a fixed machine and a polynomial time bound.`, vars: nVars, clauses: clauses.length, counts });
    // turn an accepting run into an assignment
    const fromRun = (rows) => {
      const a = new Array(nVars + 1).fill(false);
      rows.forEach((row, i) => row.forEach((s, j) => { a[x(i, j, s)] = true; }));
      for (const sel of selectors) {
        const want = [0, 1, 2].map((c) => rows[sel.i][sel.j + c]).concat([0, 1, 2].map((c) => rows[sel.i + 1][sel.j + c]));
        const l = sel.windows.findIndex((win) => win.every((s, c) => s === want[c]));
        if (l < 0) return null;
        a[sel.first + l] = true;
      }
      return a;
    };
    // read the tableau back from any satisfying assignment
    const decode = (a) => Array.from({ length: R }, (_, i) => Array.from({ length: W }, (_, j) => S.symbols.find((s) => a[x(i, j, s)]) || '?'));
    return { formula, counts, rows: R, cols: W, symbols: S.symbols, start: S.start, legal: L.per.map((l) => l.length), fromRun, decode, varOf: x, trace };
  }

  // Build, find a run, check the run satisfies the formula, and (optionally) solve the formula.
  function demonstrate(N, w, t, opts = {}) {
    const B = build(N, w, t, opts), run = acceptingRun(N, w, t);
    const res = { build: B, accepts: run.accepts, rows: run.rows };
    if (run.accepts) { const a = B.fromRun(run.rows); res.runSatisfies = !!a && T.sat.evaluate(B.formula, a); res.assignment = a; }
    if (opts.solve) { const s = T.sat.solve(B.formula); res.sat = s.sat; if (s.sat) res.solvedRows = B.decode(s.assignment); }
    return res;
  }

  T.cook = { setup, successors, acceptingRun, legalWindows, build, demonstrate };
})();
