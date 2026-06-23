// Turing machines: the text format, the compiled machine, and a deterministic runner with a trace.
// One engine serves single-tape, k-tape and multi-head machines: a machine has a list of heads,
// and each head sits on a tape (k-tape: head i on tape i; multi-head: every head on tape 0).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const SEP = '\u0001';
  const MOVES = { L: -1, R: 1, S: 0, N: 0, '-': 0 };
  const ACCEPT_NAMES = ['qa', 'qacc', 'qaccept', 'accept', 'acc', 'halt', 'qh', 'H'];
  const REJECT_NAMES = ['qr', 'qrej', 'qreject', 'reject', 'rej'];

  // ---------- tapes ----------
  // A two-way infinite tape stored as an array with an offset; unwritten cells read as blank.
  class Tape {
    constructor(blank, cells, off) { this.b = blank; this.a = cells || []; this.o = off || 0; }
    get(p) { const v = this.a[p + this.o]; return v === undefined ? this.b : v; }
    set(p, s) {
      let i = p + this.o;
      if (i < 0) { const n = -i; this.a = new Array(n).fill(this.b).concat(this.a); this.o += n; i = 0; }
      this.a[i] = s;
    }
    clone() { return new Tape(this.b, this.a.slice(), this.o); }
    // positions of the leftmost and rightmost non-blank cells (lo > hi when the tape is blank)
    bounds() {
      let lo = 0, hi = -1;
      for (let i = 0; i < this.a.length; i++) if (this.a[i] !== undefined && this.a[i] !== this.b) { lo = i; break; }
      for (let i = this.a.length - 1; i >= 0; i--) if (this.a[i] !== undefined && this.a[i] !== this.b) { hi = i; break; }
      if (hi < lo) return { lo: 0, hi: -1 };
      return { lo: lo - this.o, hi: hi - this.o };
    }
    // the cells from position a to b inclusive
    slice(a, b) { const r = []; for (let p = a; p <= b; p++) r.push(this.get(p)); return r; }
    // non-blank contents with the blanks trimmed at both ends
    trimmed() { const { lo, hi } = this.bounds(); return this.slice(lo, hi); }
  }

  // ---------- parsing ----------
  const splitList = (s) => s.split(/[\s,]+/).filter(Boolean);

  // Parse the text format. Rules look like `q0, a -> q1, b, R` (k tapes: k reads, then k writes and k moves).
  // A read may be `a|b` (any of these) or `*` (any symbol not given its own rule); a write of `*` keeps the symbol.
  // Directives: name, start, accept, reject, halt, blank, input, tape (extra symbols), tapes, heads,
  // mode (standard | oneway | lba | 2d), output (tape [k] | head), print (enumerator state), kind, nondet.
  function parse(text, opts = {}) {
    const errors = [], raw = [], dir = {};
    String(text).split('\n').forEach((line0, ln) => {
      const line = line0.replace(/\/\/.*$/, '').trim();
      if (!line) return;
      const arrow = line.includes('->') ? '->' : line.includes('→') ? '→' : null;
      if (!arrow) {
        const m = /^([A-Za-z]+)\s*:\s*(.*)$/.exec(line);
        if (m) dir[m[1].toLowerCase()] = m[2].trim();
        else errors.push({ line: ln + 1, msg: `cannot read "${line}": expected a rule with -> or a directive like start: q0` });
        return;
      }
      const [lhs, rhs] = line.split(arrow).map((s) => s.split(',').map((x) => x.trim()));
      raw.push({ lhs, rhs, line: ln + 1, text: line });
    });
    const heads = +(dir.heads || 0), tapes = +(dir.tapes || 1);
    const k = heads || tapes;
    const rules = [];
    for (const r of raw) {
      const from = r.lhs[0], reads = r.lhs.slice(1);
      if (reads.length !== k) { errors.push({ line: r.line, msg: `expected ${k} read symbol${k > 1 ? 's' : ''} after the state, found ${reads.length}` }); continue; }
      let to = r.rhs[0], writes, moves;
      if (r.rhs.length === 1 + 2 * k) { writes = r.rhs.slice(1, 1 + k); moves = r.rhs.slice(1 + k); }
      else if (r.rhs.length === 1 + k) { writes = reads.map(() => '*'); moves = r.rhs.slice(1); }
      else { errors.push({ line: r.line, msg: `expected the next state, ${k} write${k > 1 ? 's' : ''} and ${k} move${k > 1 ? 's' : ''}` }); continue; }
      moves = moves.map((m) => m.toUpperCase());
      const okMoves = dir.mode === '2d' ? ['L', 'R', 'U', 'D', 'S', 'N', '-'] : Object.keys(MOVES);
      const bad = moves.find((m) => !okMoves.includes(m));
      if (bad) { errors.push({ line: r.line, msg: `unknown move "${bad}" (use ${okMoves.slice(0, dir.mode === '2d' ? 5 : 3).join(', ')})` }); continue; }
      if (!from || !to) { errors.push({ line: r.line, msg: 'a rule needs a state on both sides' }); continue; }
      rules.push({ from, read: reads.map((x) => x.split('|').map((s) => s.trim()).filter(Boolean)), to, write: writes, move: moves.map((m) => (m === 'N' || m === '-' ? 'S' : m)), line: r.line });
    }
    const spec = {
      name: dir.name || opts.name || 'M', blank: dir.blank || '_', start: dir.start || (rules[0] && rules[0].from) || 'q0',
      accept: dir.accept ? splitList(dir.accept) : null, reject: dir.reject ? splitList(dir.reject) : null,
      halt: dir.halt ? splitList(dir.halt) : null, input: dir.input ? splitList(dir.input) : null,
      extra: dir.tape ? splitList(dir.tape) : [], tapes: heads ? 1 : tapes, heads: heads || 0, mode: dir.mode || 'standard',
      output: dir.output || null, print: dir.print || null, kind: dir.kind || null, nondet: dir.nondet === 'yes' || dir.nondet === 'true' || dir.mode === 'nondet',
      leftEnd: dir.leftend || (dir.mode === 'lba' ? '<' : '>'), rightEnd: dir.rightend || '>',
    };
    let machine = null;
    try { machine = build(spec, rules, errors); } catch (e) { errors.push({ line: 0, msg: e.message }); }
    return { machine, errors };
  }

  // Parse or throw: for library machines and tests.
  function compile(text, opts) {
    const { machine, errors } = parse(text, opts);
    if (errors.length) throw new Error('TM ' + ((machine && machine.name) || '') + ': ' + errors.map((e) => `line ${e.line}: ${e.msg}`).join('; '));
    return machine;
  }

  // Build a machine from a spec and pattern rules: expand | and * into plain rules over the tape alphabet.
  function build(spec, rules, errors = []) {
    const k = spec.heads || spec.tapes || 1;
    const blank = spec.blank;
    const markers = spec.mode === 'oneway' ? [spec.leftEnd] : spec.mode === 'lba' ? [spec.leftEnd, spec.rightEnd] : [];
    const syms = new Set([blank, ...markers, ...(spec.input || []), ...(spec.extra || [])]);
    for (const r of rules) {
      r.read.forEach((alts) => alts.forEach((s) => s !== '*' && syms.add(s)));
      r.write.forEach((s) => s !== '*' && syms.add(s));
    }
    const gamma = [...syms];
    const input = spec.input || gamma.filter((s) => s !== blank && !markers.includes(s));
    const states = [];
    const addState = (q) => { if (!states.includes(q)) states.push(q); };
    addState(spec.start);
    rules.forEach((r) => { addState(r.from); addState(r.to); });
    const accept = spec.accept || states.filter((q) => ACCEPT_NAMES.includes(q));
    const reject = spec.reject || states.filter((q) => REJECT_NAMES.includes(q));
    const halt = spec.halt || [];
    accept.forEach(addState); reject.forEach(addState); halt.forEach(addState);
    // explicit rules first (no * in the read), then wildcard rules fill the keys nobody claimed
    const delta = new Map(), explicit = new Set(), list = [];
    const add = (from, read, rule, wild) => {
      const key = from + SEP + read.join(SEP);
      if (wild && explicit.has(key)) return;
      const write = rule.write.map((w, i) => (w === '*' ? read[i] : w));
      if (!delta.has(key)) delta.set(key, []);
      const arr = delta.get(key);
      if (wild && arr.length && !spec.nondet) return; // the first wildcard rule wins in a deterministic machine
      const plain = { from, read, to: rule.to, write, move: rule.move.slice(), line: rule.line };
      arr.push(plain); list.push(plain);
    };
    const tuples = (alts) => alts.reduce((acc, a) => {
      const opts = a.includes('*') ? gamma : a;
      const out = [];
      for (const t of acc) for (const s of opts) out.push(t.concat([s]));
      return out;
    }, [[]]);
    for (const r of rules) if (!r.read.some((a) => a.includes('*'))) for (const t of tuples(r.read)) { add(r.from, t, r, false); explicit.add(r.from + SEP + t.join(SEP)); }
    for (const r of rules) if (r.read.some((a) => a.includes('*'))) for (const t of tuples(r.read)) add(r.from, t, r, true);
    // endmarkers may be read but never overwritten or crossed
    for (const r of list) r.read.forEach((s, i) => {
      if (spec.mode === 'oneway' || spec.mode === 'lba') {
        if (s === spec.leftEnd && (r.write[i] !== s || r.move[i] === 'L')) errors.push({ line: r.line, msg: `on the left-end marker ${s} a rule must write ${s} back and must not move left` });
        if (spec.mode === 'lba' && s === spec.rightEnd && (r.write[i] !== s || r.move[i] === 'R')) errors.push({ line: r.line, msg: `on the right-end marker ${s} a rule must write ${s} back and must not move right` });
      }
    });
    const M = {
      name: spec.name, kind: spec.kind || (spec.print ? 'enumerator' : spec.output ? 'transducer' : 'decider'),
      tapes: spec.heads ? 1 : k, heads: spec.heads || 0, k, mode: spec.mode, blank, leftEnd: spec.leftEnd, rightEnd: spec.rightEnd,
      input, gamma, states, start: spec.start, accept, reject, halt, print: spec.print, rules: list, delta,
      output: spec.output, outTape: 0,
    };
    if (spec.output) { const m = /tape\s*(\d+)/.exec(spec.output); if (m) M.outTape = +m[1] - 1; M.outMode = /head/.test(spec.output) ? 'head' : 'tape'; }
    M.deterministic = [...delta.values()].every((a) => a.length <= 1);
    return M;
  }

  // Build directly from plain rule objects {from, read:[..], to, write:[..], move:[..]} (macro compiler, encodings).
  function fromRules(spec, plain) {
    return build(Object.assign({ blank: '_', start: 'q0', mode: 'standard', extra: [], tapes: 1, heads: 0 }, spec),
      plain.map((r) => ({ from: r.from, read: r.read.map((s) => [s]), to: r.to, write: r.write.slice(), move: r.move.slice(), line: r.line || 0 })));
  }

  // Print a machine back in the text format, one plain rule per line.
  function toText(M) {
    const out = [`name: ${M.name}`, `start: ${M.start}`];
    if (M.accept.length) out.push(`accept: ${M.accept.join(' ')}`);
    if (M.reject.length) out.push(`reject: ${M.reject.join(' ')}`);
    if (M.halt.length) out.push(`halt: ${M.halt.join(' ')}`);
    if (M.blank !== '_') out.push(`blank: ${M.blank}`);
    out.push(`input: ${M.input.join(' ')}`);
    if (M.heads) out.push(`heads: ${M.heads}`); else if (M.tapes > 1) out.push(`tapes: ${M.tapes}`);
    if (M.mode !== 'standard') out.push(`mode: ${M.mode}`);
    if (M.output) out.push(`output: ${M.output}`);
    if (M.print) out.push(`print: ${M.print}`);
    for (const r of M.rules) out.push(`${r.from}, ${r.read.join(', ')} -> ${r.to}, ${r.write.join(', ')}, ${r.move.join(', ')}`);
    return out.join('\n');
  }

  // Split an input string into symbols: by characters when every input symbol is one character, else by spaces.
  function symbols(M, w) {
    if (Array.isArray(w)) return w.slice();
    if (M.input.every((s) => s.length === 1) && !/\s/.test(w)) return [...w];
    return w.split(/\s+/).filter(Boolean);
  }

  // ---------- configurations ----------
  const isAccept = (M, q) => M.accept.includes(q) || M.halt.includes(q);
  const isReject = (M, q) => M.reject.includes(q);
  const isHalting = (M, q) => isAccept(M, q) || isReject(M, q);

  // The start configuration: input on tape 0 from cell 0 (cell 1 behind a left-end marker), all heads at the input start.
  function initial(M, input) {
    const w = symbols(M, input);
    const tapes = [];
    for (let t = 0; t < M.tapes; t++) tapes.push(new Tape(M.blank));
    let start = 0;
    if (M.mode === 'oneway' || M.mode === 'lba') {
      for (const tp of tapes) tp.set(0, M.leftEnd);
      start = 1;
    }
    w.forEach((s, i) => tapes[0].set(start + i, s));
    if (M.mode === 'lba') tapes[0].set(start + w.length, M.rightEnd);
    const heads = [];
    for (let h = 0; h < M.k; h++) heads.push({ t: M.heads ? 0 : h, p: start });
    return { state: M.start, tapes, heads, step: 0 };
  }

  const cloneCfg = (c) => ({ state: c.state, tapes: c.tapes.map((t) => t.clone()), heads: c.heads.map((h) => ({ t: h.t, p: h.p })), step: c.step });
  const readsOf = (c) => c.heads.map((h) => c.tapes[h.t].get(h.p));
  const rulesFor = (M, c) => M.delta.get(c.state + SEP + readsOf(c).join(SEP)) || [];

  // Apply one rule in place: writes in head order (a later head wins a shared cell), then all moves.
  function apply(c, r) {
    c.heads.forEach((h, i) => c.tapes[h.t].set(h.p, r.write[i]));
    c.heads.forEach((h, i) => { h.p += MOVES[r.move[i]]; });
    c.state = r.to; c.step++;
    return c;
  }

  // A canonical key for loop detection: state, heads and trimmed tapes (heads relative to nothing, so exact).
  function key(c) {
    let s = c.state + SEP + c.heads.map((h) => h.p).join(',');
    for (const t of c.tapes) { const { lo, hi } = t.bounds(); s += SEP + lo + ':' + t.slice(lo, hi).join('\u0002'); }
    return s;
  }

  // The visible window of every tape: one blank beyond the written cells and the heads on both sides.
  function windows(c) {
    return c.tapes.map((t, ti) => {
      const { lo, hi } = t.bounds();
      const hp = c.heads.filter((h) => h.t === ti).map((h) => h.p);
      const a = Math.min(hi < lo ? hp[0] : lo, ...hp) - 1, b = Math.max(hi, ...hp) + 1;
      return { from: a, cells: t.slice(a, b), heads: c.heads.map((h, i) => (h.t === ti ? { head: i, at: h.p } : null)).filter(Boolean) };
    });
  }

  // Configuration in the usual notation u q v (single tape; for several tapes, one per tape joined by " | ").
  function configString(M, c) {
    return c.tapes.map((t, ti) => {
      const hp = c.heads.filter((h) => h.t === ti).map((h) => h.p);
      const { lo, hi } = t.bounds();
      const a = Math.min(hi < lo ? hp[0] : lo, ...hp), b = Math.max(hi, ...hp);
      const head = hp[0];
      const left = t.slice(a, head - 1).join(''), right = t.slice(head, b).join('');
      return (left ? left + ' ' : '') + c.state + ' ' + (right || M.blank);
    }).join(' | ');
  }

  // Output of a transducer: tape `outTape` trimmed, or from the head to the first blank; endmarkers left out.
  function outputOf(M, c) {
    const t = c.tapes[M.outTape || 0];
    let cells;
    if (M.outMode === 'head') { cells = []; const h = c.heads.find((x) => x.t === (M.outTape || 0)); for (let p = h.p; t.get(p) !== M.blank; p++) cells.push(t.get(p)); }
    else cells = t.trimmed();
    cells = cells.filter((s) => !((M.mode === 'oneway' || M.mode === 'lba') && (s === M.leftEnd || s === M.rightEnd)));
    return cells.join(M.input.every((s) => s.length === 1) ? '' : ' ');
  }

  const describeRule = (M, r) => {
    const rd = r.read.join(', '), wr = r.write.join(', '), mv = r.move.join(', ');
    return M.k === 1
      ? `In ${r.from} reading ${r.read[0]}: write ${r.write[0]}, move ${r.move[0]}, go to ${r.to}.`
      : `In ${r.from} reading (${rd}): write (${wr}), move (${mv}), go to ${r.to}.`;
  };

  // ---------- running ----------
  // Run a deterministic machine. opts: maxSteps (10000), trace (true), traceLimit (4000), loops (true),
  // history (true, up to historyLimit configurations in u q v notation).
  // verdict: accept | reject | loop (a configuration repeated: provably never halts) | limit (ran out of steps).
  function run(M, input, opts = {}) {
    const maxSteps = opts.maxSteps == null ? 10000 : opts.maxSteps;
    const wantTrace = opts.trace !== false, traceLimit = opts.traceLimit || 4000;
    const loops = opts.loops !== false, wantHist = opts.history !== false && wantTrace, histLimit = opts.historyLimit || 2000;
    const c = initial(M, input);
    const trace = [], history = [], seen = loops ? new Map() : null;
    const snap = (extra) => Object.assign({ state: c.state, step: c.step, heads: c.heads.map((h) => h.p), tapes: windows(c) }, extra);
    const note = (s) => { if (!wantTrace) return; if (trace.length < traceLimit) trace.push(s); else if (trace.length === traceLimit) trace.push({ kind: 'cut', say: `The trace stops here; the machine keeps running (up to ${maxSteps} steps).` }); };
    if (wantTrace) note(snap({ kind: 'start', say: `Start in ${M.start} with ${symbols(M, input).join('') || 'the empty string ε'} on the tape, head on the first cell.` }));
    if (wantHist) history.push(configString(M, c));
    let verdict = null, reason = '', loopAt = null, nondet = false;
    while (true) {
      if (isAccept(M, c.state)) { verdict = 'accept'; reason = 'reached ' + c.state; break; }
      if (isReject(M, c.state)) { verdict = 'reject'; reason = 'reached ' + c.state; break; }
      if (loops) {
        const k = key(c);
        if (seen.has(k)) { verdict = 'loop'; loopAt = { first: seen.get(k), again: c.step }; reason = `configuration at step ${c.step} repeats step ${seen.get(k)}`; break; }
        seen.set(k, c.step);
      }
      const rs = rulesFor(M, c);
      if (!rs.length) { verdict = 'reject'; reason = `no rule for ${c.state} on ${readsOf(c).join(', ')}`; break; }
      if (c.step >= maxSteps) { verdict = 'limit'; reason = `no verdict after ${maxSteps} steps`; break; }
      if (rs.length > 1) nondet = true;
      const r = rs[0];
      apply(c, r);
      if (wantTrace) note(snap({ kind: 'move', say: describeRule(M, r), rule: r, from: r.from, read: r.read, to: r.to, write: r.write, move: r.move, line: r.line }));
      if (wantHist && history.length < histLimit) history.push(configString(M, c));
    }
    const out = (verdict === 'accept' && (M.output || M.kind === 'transducer' || M.kind === 'beaver')) ? outputOf(M, c) : null;
    const say = {
      accept: M.output ? `Halted in ${c.state} after ${c.step} steps; the output is ${out || 'ε'}.` : `Accepted in ${c.state} after ${c.step} steps.`,
      reject: `Rejected after ${c.step} steps: ${reason}.`,
      loop: `Never halts: the configuration at step ${loopAt && loopAt.again} is the same as at step ${loopAt && loopAt.first}, so the machine cycles forever.`,
      limit: `No answer after ${maxSteps} steps: the machine may still halt later, or may run forever.`,
    }[verdict];
    note(snap({ kind: verdict, say, reason }));
    return { verdict, accepted: verdict === 'accept', halted: verdict === 'accept' || verdict === 'reject', steps: c.step, state: c.state, output: out, reason, loopAt, nondet, trace, history, config: c, ones: countOnes(M, c) };
  }

  // For busy beavers: the number of non-blank cells left on tape 0.
  function countOnes(M, c) { return c.tapes[0].trimmed().filter((s) => s !== M.blank).length; }

  // Is the machine a decider on these inputs (halts on every one within the limit)?
  function decides(M, inputs, maxSteps = 10000) {
    const bad = [];
    for (const w of inputs) { const r = run(M, w, { maxSteps, trace: false }); if (!r.halted) bad.push({ input: w, verdict: r.verdict }); }
    return { ok: !bad.length, bad };
  }

  // All strings over an alphabet up to length n in shortlex order.
  function strings(alpha, n) {
    const out = [''];
    let layer = [''];
    for (let l = 1; l <= n; l++) { const next = []; for (const w of layer) for (const a of alpha) next.push(w + a); for (const x of next) out.push(x); layer = next; }
    return out;
  }

  T.tm = Object.assign(T.tm || {}, {
    SEP, MOVES, Tape, parse, compile, build, fromRules, toText, symbols, run, decides, strings,
    initial, cloneCfg, readsOf, rulesFor, apply, key, windows, configString, outputOf, describeRule,
    isAccept, isReject, isHalting, countOnes,
  });
})();
