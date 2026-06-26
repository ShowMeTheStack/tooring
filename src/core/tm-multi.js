// Variants of the Turing machine: the k-tape machine simulated on one tape, 2-D tapes, nondeterministic
// machines (computation tree, address-tape simulation, exhaustive search), enumerators and dovetailing.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const TM = T.tm;

  // ---------- k tapes on one tape ----------
  // One tape with 2k tracks: track i holds tape i, and a mark on track i shows where head i is.
  // A single head sweeps right to gather the symbols under the marks, decides the rule, then sweeps left
  // applying writes and moving marks. Every head move of the single head counts as one step.
  function simulateKTape(M, input, opts = {}) {
    const k = M.tapes, maxSim = opts.maxSteps == null ? 2000 : opts.maxSteps, traceLimit = opts.traceLimit || 3000;
    const wantTrace = opts.trace !== false, B = M.blank;
    const cells = new Map(); // pos -> {sym:[k], mark:[k]}
    const cell = (p) => { let c = cells.get(p); if (!c) { c = { sym: new Array(k).fill(B), mark: new Array(k).fill(false) }; cells.set(p, c); } return c; };
    const w = TM.symbols(M, input);
    w.forEach((s, i) => { cell(i).sym[0] = s; });
    for (let i = 0; i < k; i++) cell(0).mark[i] = true;
    let L = 0, R = Math.max(0, w.length - 1), H = 0, steps = 0, state = M.start, sim = 0;
    const trace = [];
    const note = (s) => { if (wantTrace && trace.length < traceLimit) trace.push(s); };
    const tracks = () => {
      const out = [];
      for (let i = 0; i < k; i++) { const sy = [], mk = []; for (let p = L; p <= R; p++) { const c = cells.get(p); sy.push(c ? c.sym[i] : B); mk.push(!!(c && c.mark[i])); } out.push({ symbols: sy, marks: mk }); }
      return { from: L, tracks: out, head: H };
    };
    note(Object.assign({ kind: 'sim-start', say: `Put the ${k} tapes on ${k} tracks of one tape and mark every head on the first cell.`, state, steps }, tracks()));
    let verdict = null;
    while (true) {
      if (TM.isAccept(M, state)) { verdict = 'accept'; break; }
      if (TM.isReject(M, state)) { verdict = 'reject'; break; }
      // gather: sweep right from L to R
      const seen = new Array(k).fill(B);
      for (H = L; ; H++) {
        const c = cells.get(H);
        if (c) c.mark.forEach((m, i) => { if (m) seen[i] = c.sym[i]; });
        if (c && c.mark.some(Boolean)) note({ kind: 'gather', say: `At cell ${H} the marks show ${c.mark.map((m, i) => (m ? `head ${i + 1} on ${c.sym[i]}` : null)).filter(Boolean).join(', ')}.`, pos: H, seen: seen.slice(), state });
        if (H === R) break;
        steps++;
      }
      const rs = M.delta.get(state + TM.SEP + seen.join(TM.SEP)) || [];
      if (!rs.length) { verdict = 'reject'; note({ kind: 'stuck', say: `No rule for ${state} on (${seen.join(', ')}): the simulated machine rejects.`, state, seen }); break; }
      if (sim >= maxSim) { verdict = 'limit'; break; }
      const r = rs[0];
      steps++; // the single head acts at least once per simulated step
      note({ kind: 'decide', say: `The symbols under the heads are (${seen.join(', ')}), so use: ${TM.describeRule(M, r)}`, rule: r, state, seen, steps });
      // update: sweep left from R to L; marks that move right cost a step out and a step back
      const done = new Array(k).fill(false);
      for (H = R; ; H--) {
        const c = cells.get(H);
        if (c) for (let i = 0; i < k; i++) if (c.mark[i] && !done[i]) {
          done[i] = true; c.sym[i] = r.write[i];
          const d = TM.MOVES[r.move[i]];
          if (d) { c.mark[i] = false; cell(H + d).mark[i] = true; if (H + d < L) L = H + d; if (H + d > R) R = H + d; if (d > 0) steps += 2; }
          note({ kind: 'update', say: `Head ${i + 1}: write ${r.write[i]} at cell ${H}` + (d ? ` and move its mark ${d < 0 ? 'left' : 'right'}.` : ', mark stays.'), pos: H, head: i, write: r.write[i], move: r.move[i] });
        }
        if (H <= L) break;
        steps++;
      }
      state = r.to; sim++;
      note(Object.assign({ kind: 'sim-step', say: `Simulated step ${sim} done: now in ${state}, ${steps} single-tape steps so far.`, state, sim, steps }, tracks()));
    }
    // decode the tracks back into k tapes
    const tapes = [], heads = [];
    for (let i = 0; i < k; i++) {
      const t = new TM.Tape(B);
      for (const [p, c] of cells) { if (c.sym[i] !== B) t.set(p, c.sym[i]); if (c.mark[i]) heads[i] = p; }
      tapes.push(t);
    }
    note({ kind: verdict, say: `The one-tape simulation ends with ${verdict} after ${sim} simulated steps and ${steps} single-tape steps.`, state, sim, steps });
    return { verdict, state, simulated: sim, steps, tapes: tapes.map((t) => t.trimmed().join('')), heads, trace };
  }

  // ---------- 2-D tape ----------
  // Moves are L, R, U (up: y-1), D (down: y+1) and S; the input is written on row 0 from (0,0).
  function run2d(M, input, opts = {}) {
    const maxSteps = opts.maxSteps == null ? 10000 : opts.maxSteps, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 2000;
    const grid = new Map(), B = M.blank;
    const get = (x, y) => grid.get(x + ',' + y) || B;
    const set = (x, y, s) => { if (s === B) grid.delete(x + ',' + y); else grid.set(x + ',' + y, s); };
    TM.symbols(M, input).forEach((s, i) => set(i, 0, s));
    let x = 0, y = 0, state = M.start, steps = 0, verdict = null;
    const D = { L: [-1, 0], R: [1, 0], U: [0, -1], D: [0, 1], S: [0, 0] };
    const box = () => {
      let x0 = x, x1 = x, y0 = y, y1 = y;
      for (const k of grid.keys()) { const [a, b] = k.split(',').map(Number); x0 = Math.min(x0, a); x1 = Math.max(x1, a); y0 = Math.min(y0, b); y1 = Math.max(y1, b); }
      const rows = [];
      for (let j = y0; j <= y1; j++) { const row = []; for (let i = x0; i <= x1; i++) row.push(get(i, j)); rows.push(row); }
      return { x0, y0, rows, head: [x, y] };
    };
    const trace = [], seen = opts.loops === false ? null : new Set();
    const note = (s) => { if (wantTrace && trace.length < traceLimit) trace.push(s); };
    note(Object.assign({ kind: 'start', say: `Start in ${state} at (0, 0) with the input on row 0.`, state }, box()));
    while (true) {
      if (TM.isAccept(M, state)) { verdict = 'accept'; break; }
      if (TM.isReject(M, state)) { verdict = 'reject'; break; }
      if (seen) { const key = state + '@' + x + ',' + y + '|' + [...grid.entries()].sort().join(';'); if (seen.has(key)) { verdict = 'loop'; break; } seen.add(key); }
      const rs = M.delta.get(state + TM.SEP + get(x, y)) || [];
      if (!rs.length) { verdict = 'reject'; break; }
      if (steps >= maxSteps) { verdict = 'limit'; break; }
      const r = rs[0];
      set(x, y, r.write[0]); x += D[r.move[0]][0]; y += D[r.move[0]][1]; state = r.to; steps++;
      if (wantTrace) note(Object.assign({ kind: 'move', say: `In ${r.from} reading ${r.read[0]}: write ${r.write[0]}, move ${r.move[0]}, go to ${r.to}.`, rule: r, state }, box()));
    }
    const final = box();
    note(Object.assign({ kind: verdict, say: `Stopped with ${verdict} after ${steps} steps.`, state }, final));
    return { verdict, steps, state, grid: final, get, trace };
  }

  // ---------- nondeterminism ----------
  const successors = (M, c) => TM.rulesFor(M, c).map((r) => ({ rule: r, cfg: TM.apply(TM.cloneCfg(c), r) }));

  // Breadth-first exploration of the computation tree: nodes are configurations, children follow rules.
  // verdict accept (some branch accepts), reject (every branch halts without accepting), limit (cut off).
  function ntmTree(M, input, opts = {}) {
    const maxDepth = opts.maxDepth == null ? 12 : opts.maxDepth, maxNodes = opts.maxNodes || 4000, dedupe = !!opts.dedupe;
    const wantTrace = opts.trace !== false;
    const root = TM.initial(M, input);
    const nodes = [{ id: 0, parent: -1, depth: 0, state: root.state, config: TM.configString(M, root), rule: null, status: 'open' }];
    const trace = [], cfgs = [root], seen = new Set([TM.key(root)]);
    const note = (s) => { if (wantTrace) trace.push(s); };
    note({ kind: 'root', say: `The root is the start configuration ${nodes[0].config}.`, node: 0, nodes: [nodes[0]] });
    let frontier = [0], verdict = null, acceptNode = -1, cut = false;
    for (let depth = 0; frontier.length && verdict == null; depth++) {
      const next = [];
      for (const id of frontier) {
        const n = nodes[id], c = cfgs[id];
        if (TM.isAccept(M, c.state)) { n.status = 'accept'; verdict = 'accept'; acceptNode = id; break; }
        if (TM.isReject(M, c.state)) { n.status = 'reject'; continue; }
        if (depth >= maxDepth || nodes.length >= maxNodes) { n.status = 'cut'; cut = true; continue; }
        const kids = successors(M, c);
        if (!kids.length) { n.status = 'reject'; continue; }
        n.status = 'expanded';
        const made = [];
        for (const { rule, cfg } of kids) {
          if (dedupe) { const k = TM.key(cfg); if (seen.has(k)) continue; seen.add(k); }
          const child = { id: nodes.length, parent: id, depth: depth + 1, state: cfg.state, config: TM.configString(M, cfg), rule, status: 'open' };
          nodes.push(child); cfgs.push(cfg); next.push(child.id); made.push(child.id);
        }
        note({ kind: 'expand', say: `${n.config} has ${kids.length} move${kids.length === 1 ? '' : 's'}: ` + made.map((i) => nodes[i].config).join('; ') + '.', node: id, children: made, depth });
      }
      if (verdict == null && next.length) note({ kind: 'level', say: `Level ${depth + 1} holds ${next.length} configuration${next.length === 1 ? '' : 's'}.`, depth: depth + 1, nodes: next.slice() });
      frontier = verdict == null ? next : [];
    }
    if (verdict == null) verdict = cut ? 'limit' : 'reject';
    const path = [];
    for (let i = acceptNode; i >= 0; i = nodes[i].parent) path.unshift(i);
    note({ kind: verdict, say: verdict === 'accept' ? `An accepting configuration at depth ${nodes[acceptNode].depth}: the machine accepts.` : verdict === 'reject' ? 'Every branch halted without accepting: the machine rejects.' : `Stopped at depth ${maxDepth} or ${maxNodes} nodes with branches still running.`, path });
    return { verdict, nodes, path, trace };
  }

  // Deterministic simulation with an address tape: try every choice sequence in shortlex order,
  // re-running from the start each time. The tree is finite and fully rejecting when no address of
  // some length leads to a configuration that is still running.
  function ntmAddress(M, input, opts = {}) {
    const maxLen = opts.maxLen == null ? 10 : opts.maxLen, wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 3000;
    let b = 1;
    for (const a of M.delta.values()) b = Math.max(b, a.length);
    const trace = [];
    const note = (s) => { if (wantTrace && trace.length < traceLimit) trace.push(s); };
    let tried = 0, simSteps = 0;
    note({ kind: 'address-start', say: `At most ${b} choices at any step, so addresses are strings over 1..${b}.`, branching: b });
    for (let len = 0; len <= maxLen; len++) {
      let alive = false;
      const addr = new Array(len).fill(1);
      while (true) {
        tried++;
        let c = TM.initial(M, input), outcome = 'running';
        const path = [TM.configString(M, c)];
        for (let i = 0; ; i++) {
          if (TM.isAccept(M, c.state)) { outcome = 'accept'; break; }
          if (TM.isReject(M, c.state)) { outcome = 'reject'; break; }
          const rs = TM.rulesFor(M, c);
          if (!rs.length) { outcome = 'reject'; break; }
          if (i === len) { outcome = 'running'; break; }
          if (addr[i] > rs.length) { outcome = 'invalid'; break; }
          c = TM.apply(c, rs[addr[i] - 1]); simSteps++; path.push(TM.configString(M, c));
        }
        note({ kind: 'address', say: `Address ${addr.join('') || 'ε'}: ${{ accept: 'reaches an accepting configuration', reject: 'halts without accepting', invalid: 'names a choice that does not exist', running: 'is still running when the address ends' }[outcome]}.`, address: addr.slice(), outcome, path });
        if (outcome === 'accept') { note({ kind: 'accept', say: `Accepted along address ${addr.join('') || 'ε'}.`, address: addr.slice() }); return { verdict: 'accept', address: addr.slice(), tried, simSteps, branching: b, trace }; }
        if (outcome === 'running') alive = true;
        let i = len - 1;
        while (i >= 0 && addr[i] === b) { addr[i] = 1; i--; }
        if (i < 0) break;
        addr[i]++;
      }
      if (!alive) { note({ kind: 'reject', say: `No address of length ${len} is still running: every branch has halted, so the machine rejects.` }); return { verdict: 'reject', tried, simSteps, branching: b, trace }; }
    }
    note({ kind: 'limit', say: `Addresses up to length ${maxLen} found no acceptance and some branches still run.` });
    return { verdict: 'limit', tried, simSteps, branching: b, trace };
  }

  // Plain depth-first search of all branches to a depth: the oracle for the two searches above.
  function ntmExhaustive(M, input, maxDepth = 12) {
    let cut = false;
    const go = (c, d) => {
      if (TM.isAccept(M, c.state)) return true;
      if (TM.isReject(M, c.state)) return false;
      const rs = TM.rulesFor(M, c);
      if (d >= maxDepth) { if (rs.length) cut = true; return false; }
      return rs.some((r) => go(TM.apply(TM.cloneCfg(c), r), d + 1));
    };
    const acc = go(TM.initial(M, input), 0);
    return acc ? 'accept' : cut ? 'limit' : 'reject';
  }

  // ---------- enumerators ----------
  // Each time the machine enters its print state from another state (or starts in it), the output tape
  // is printed; staying in the print state (say, to walk along the tape) prints nothing more.
  function enumerate(M, opts = {}) {
    const maxPrints = opts.maxPrints || 20, maxSteps = opts.maxSteps || 100000;
    const c = TM.initial(M, '');
    const prints = [], trace = [];
    const doPrint = () => {
      const s = c.tapes[M.outTape || 0].trimmed().join('');
      prints.push(s);
      trace.push({ kind: 'print', say: `Print ${s || 'ε'} (string number ${prints.length}).`, printed: s, step: c.step, tapes: TM.windows(c) });
    };
    if (c.state === M.print) doPrint();
    while (prints.length < maxPrints && c.step < maxSteps) {
      const rs = TM.rulesFor(M, c);
      if (!rs.length || TM.isHalting(M, c.state)) { trace.push({ kind: 'halt', say: `The enumerator halts after printing ${prints.length} strings.` }); break; }
      const was = c.state;
      TM.apply(c, rs[0]);
      if (c.state === M.print && was !== M.print) doPrint();
    }
    return { prints, steps: c.step, trace };
  }

  // Dovetailing: in round i, run the recogniser for i steps on each of the first i strings, and print
  // every string that has been accepted (once). No single looping input can stall the listing.
  function dovetail(M, alphabet, opts = {}) {
    const rounds = opts.rounds || 8, words = TM.strings(alphabet, 12).slice(0, rounds);
    const printed = [], trace = [], done = new Set();
    for (let i = 1; i <= rounds; i++) {
      trace.push({ kind: 'round', say: `Round ${i}: run ${i} step${i === 1 ? '' : 's'} on each of ${words.slice(0, i).map((w) => w || 'ε').join(', ')}.`, round: i });
      for (let j = 0; j < i; j++) {
        const w = words[j];
        const r = TM.run(M, w, { maxSteps: i, trace: false, loops: false });
        trace.push({ kind: 'try', say: `${w || 'ε'} for ${i} steps: ${r.verdict === 'limit' ? 'still running' : r.verdict}.`, round: i, input: w, result: r.verdict });
        if (r.verdict === 'accept' && !done.has(w)) { done.add(w); printed.push(w); trace.push({ kind: 'print', say: `Print ${w || 'ε'}.`, printed: w, round: i }); }
      }
    }
    return { printed, trace };
  }

  // A recogniser built from an enumerator: accept w if it is ever printed (bounded here by maxPrints).
  function recogniseByEnumerator(E, w, maxPrints = 200) {
    const { prints } = enumerate(E, { maxPrints });
    const i = prints.indexOf(w);
    return { verdict: i >= 0 ? 'accept' : 'limit', at: i, prints: prints.slice(0, i >= 0 ? i + 1 : prints.length) };
  }

  Object.assign(TM, { simulateKTape, run2d, successors, ntmTree, ntmAddress, ntmExhaustive, enumerate, dovetail, recogniseByEnumerator });
})();
