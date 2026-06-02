// Finite automata: DFA, NFA and ε-NFA as plain data, with every classical construction and decision
// procedure. A machine is { states, alphabet, start, accept, trans: [{ from, sym, to }] } where sym is a
// single character, or '' for an ε-move. A DFA may be partial: a missing move goes to an implicit dead
// state, which complete() makes explicit. Machines are values: constructions never change their input.
// Each construction returns { fa, trace } (or a result object with a trace); trace steps are
// { kind, say, ...data } with the actual state names and symbols.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const FA = T.FA = {};
  const EPS = FA.EPS = '';
  const chars = (w) => Array.from(w);
  const showW = (w) => (w === '' ? 'ε' : w);
  const showSym = (a) => (a === EPS ? 'ε' : a);
  const uniq = (xs) => [...new Set(xs)];
  const plural = (n, w) => `${n} ${w}${n === 1 ? '' : 's'}`;
  FA.showString = showW;

  // A name for a set of states; the empty set is ∅ (the dead state of a subset construction).
  const setName = FA.setName = (names) => (names.length ? '{' + names.join(',') + '}' : '∅');
  const listStates = (xs) => (xs.length ? '{' + xs.join(', ') + '}' : '∅');
  // Fresh names that avoid the ones already taken: base, base′, base″, base‴, base4, ...
  function freshName(taken, base) {
    if (!taken.has(base)) { taken.add(base); return base; }
    const marks = ['′', '″', '‴'];
    for (let i = 0; ; i++) {
      const n = i < 3 ? base + marks[i] : base + (i + 1);
      if (!taken.has(n)) { taken.add(n); return n; }
    }
  }
  FA.freshName = freshName;

  // ---------------------------------------------------------------- building and checking

  // Normalise a machine description: states mentioned anywhere are added (in order of appearance),
  // duplicates go, and the alphabet defaults to the symbols used, sorted.
  FA.make = function (s) {
    const trans = [], seen = new Set();
    for (const e of s.trans || []) {
      const sym = e.sym === undefined || e.sym === null || e.sym === 'ε' || e.sym === 'eps' ? EPS : String(e.sym);
      const k = e.from + '\u0000' + sym + '\u0000' + e.to;
      if (!seen.has(k)) { seen.add(k); trans.push({ from: String(e.from), sym, to: String(e.to) }); }
    }
    const states = uniq([...(s.states || []), ...(s.start !== undefined && s.start !== null ? [s.start] : []),
      ...trans.flatMap((e) => [e.from, e.to]), ...(s.accept || [])].map(String));
    const alphabet = s.alphabet ? uniq(s.alphabet.map(String)) : uniq(trans.map((e) => e.sym).filter((a) => a !== EPS)).sort();
    const m = { states, alphabet, start: s.start === undefined || s.start === null ? null : String(s.start), accept: uniq((s.accept || []).map(String)), trans };
    if (s.name) m.name = s.name;
    if (s.pos) m.pos = s.pos; // editor layout { state: {x, y} }, carried along untouched
    return m;
  };
  FA.clone = (m) => FA.make(JSON.parse(JSON.stringify(m)));

  // What kind of machine this is: 'enfa' if any ε-move, 'nfa' if some state has two moves on one
  // symbol, else 'dfa' (possibly partial).
  FA.kind = function (m) {
    if (m.trans.some((e) => e.sym === EPS)) return 'enfa';
    const seen = new Set();
    for (const e of m.trans) { const k = e.from + '\u0000' + e.sym; if (seen.has(k)) return 'nfa'; seen.add(k); }
    return 'dfa';
  };
  FA.isDFA = (m) => FA.kind(m) === 'dfa';
  FA.missing = function (m) {
    const has = new Set(m.trans.map((e) => e.from + '\u0000' + e.sym)), out = [];
    for (const q of m.states) for (const a of m.alphabet) if (!has.has(q + '\u0000' + a)) out.push({ state: q, sym: a });
    return out;
  };
  FA.isComplete = (m) => FA.isDFA(m) && FA.missing(m).length === 0;

  // Errors make the machine unusable; warnings are things a student may want to know.
  // opts.expect = 'dfa' turns nondeterminism into errors (for "build a DFA" exercises), and
  // opts.complete = true also reports missing moves as errors.
  FA.validate = function (m, opts = {}) {
    const errors = [], warnings = [];
    const st = new Set();
    for (const q of m.states || []) {
      if (typeof q !== 'string' || !q.length) errors.push('A state has an empty name.');
      else if (/\s/.test(q)) errors.push(`State name "${q}" contains a space.`);
      else if (st.has(q)) errors.push(`State ${q} is listed twice.`);
      st.add(q);
    }
    const sig = new Set();
    for (const a of m.alphabet || []) {
      if (chars(a).length !== 1) errors.push(`Alphabet symbol "${a}" must be a single character.`);
      else if (a === 'ε') errors.push('ε cannot be an alphabet symbol: it stands for the empty string.');
      if (sig.has(a)) errors.push(`Symbol ${a} is listed twice in the alphabet.`);
      sig.add(a);
    }
    if (!(m.states || []).length) errors.push('The machine has no states.');
    if (m.start === null || m.start === undefined) errors.push('No start state is given.');
    else if (!st.has(m.start)) errors.push(`The start state ${m.start} is not one of the states.`);
    for (const q of m.accept || []) if (!st.has(q)) errors.push(`Accepting state ${q} is not one of the states.`);
    for (const e of m.trans || []) {
      if (!st.has(e.from)) errors.push(`The move ${e.from} -${showSym(e.sym)}-> ${e.to} starts at an unknown state ${e.from}.`);
      if (!st.has(e.to)) errors.push(`The move ${e.from} -${showSym(e.sym)}-> ${e.to} ends at an unknown state ${e.to}.`);
      if (e.sym !== EPS && !sig.has(e.sym)) errors.push(`The move ${e.from} -${e.sym}-> ${e.to} reads ${e.sym}, which is not in the alphabet.`);
    }
    if (errors.length) return { ok: false, errors, warnings, kind: null };
    const kind = FA.kind(m);
    const dfaIssue = (msg) => (opts.expect === 'dfa' ? errors : warnings).push(msg);
    if (kind === 'enfa') dfaIssue('The machine has ε-moves, so it is an ε-NFA, not a DFA.');
    const by = new Map();
    for (const e of m.trans) if (e.sym !== EPS) { const k = e.from + '\u0000' + e.sym; by.set(k, (by.get(k) || []).concat([e.to])); }
    for (const [k, tos] of by) if (tos.length > 1) { const [q, a] = k.split('\u0000'); dfaIssue(`State ${q} has ${tos.length} moves on ${a} (to ${tos.join(', ')}): that is nondeterministic.`); }
    const miss = FA.missing(m);
    if (miss.length) (opts.complete ? errors : warnings).push(`${plural(miss.length, 'move')} missing (e.g. from ${miss[0].state} on ${miss[0].sym}); missing moves go to an implicit dead state.`);
    const reach = reachableSet(m);
    const unreach = m.states.filter((q) => !reach.has(q));
    if (unreach.length) warnings.push(`Unreachable from ${m.start}: ${unreach.join(', ')}.`);
    if (!m.accept.length) warnings.push('No accepting states, so the language is ∅.');
    return { ok: errors.length === 0, errors, warnings, kind };
  };
  function check(m, what) {
    const v = FA.validate(m);
    if (!v.ok) throw new Error((what ? what + ': ' : '') + v.errors[0]);
    return v;
  }

  // ---------------------------------------------------------------- text format

  // Whitespace symbols (a lexer needs them) are written \s, \t and \n in the text format.
  const unesc = (s) => ({ '\\s': ' ', '\\t': '\t', '\\n': '\n' }[s] || s);
  const esc = (a) => ({ ' ': '\\s', '\t': '\\t', '\n': '\\n' }[a] || a);
  // Lines:  start q0 | accept q1 q2 | states q0 q1 | alphabet a b | q0 -a-> q1 | q0 -a,b-> q2 |
  // q1 -eps-> q2 (or -ε->). Blank lines and lines starting with # or // are ignored. "final" and
  // "accepting" mean accept; a ":" after a keyword is allowed. "at q0 120 80" records an editor position.
  FA.parse = function (text) {
    const errors = [], spec = { states: [], trans: [], accept: [] };
    let alphabet = null;
    String(text).split(/\r?\n/).forEach((raw, i) => {
      const line = raw.trim(), ln = i + 1;
      if (!line || line.startsWith('#') || line.startsWith('//')) return;
      const e = line.match(/^(\S+)\s+-(.+?)->\s*(\S+)$/) || line.match(/^(\S+)\s*-(.+?)->\s+(\S+)$/);
      if (e && !/^(start|accept|final|accepting|states|alphabet|sigma):?$/i.test(e[1])) {
        const lab = e[2].trim();
        const syms = lab === ',' ? [','] : lab.split(/[\s,]+/).filter(Boolean);
        if (!syms.length) { errors.push({ line: ln, msg: `No symbol on the arrow: write ${e[1]} -a-> ${e[3]}.` }); return; }
        for (let s of syms) {
          s = unesc(s);
          if (s === 'eps' || s === 'ε' || s === 'ϵ') spec.trans.push({ from: e[1], sym: EPS, to: e[3] });
          else if (chars(s).length !== 1) errors.push({ line: ln, msg: `"${s}" is not a single symbol (separate symbols with commas, write ε as eps).` });
          else spec.trans.push({ from: e[1], sym: s, to: e[3] });
        }
        return;
      }
      const k = line.match(/^(\w+):?\s*(.*)$/);
      const word = k ? k[1].toLowerCase() : '';
      const rest = k ? k[2].split(/[\s,]+/).filter(Boolean) : [];
      if (word === 'start' || word === 'initial') {
        if (rest.length !== 1) errors.push({ line: ln, msg: 'start takes exactly one state.' });
        else if (spec.start !== undefined && spec.start !== rest[0]) errors.push({ line: ln, msg: `A second start state ${rest[0]}; there is one start state (${spec.start}).` });
        else spec.start = rest[0];
      } else if (word === 'accept' || word === 'final' || word === 'accepting') spec.accept.push(...rest);
      else if (word === 'at' && rest.length === 3 && isFinite(+rest[1]) && isFinite(+rest[2])) (spec.pos = spec.pos || {})[rest[0]] = { x: +rest[1], y: +rest[2] };
      else if (word === 'states') spec.states.push(...rest);
      else if (word === 'alphabet' || word === 'sigma') {
        alphabet = (alphabet || []).concat(rest.map(unesc));
        for (const a of rest.map(unesc)) if (chars(a).length !== 1) errors.push({ line: ln, msg: `Alphabet symbol "${a}" must be a single character.` });
      } else errors.push({ line: ln, msg: `Cannot read "${line}". Expected e.g. "q0 -a-> q1", "start q0" or "accept q2".` });
    });
    if (alphabet) spec.alphabet = alphabet;
    if (spec.start === undefined && !errors.length) errors.push({ line: 0, msg: 'No start line (write e.g. "start q0").' });
    const fa = FA.make(spec);
    if (!errors.length) for (const msg of FA.validate(fa).errors) errors.push({ line: 0, msg });
    return { ok: errors.length === 0, fa, errors };
  };

  FA.format = function (m, opts = {}) {
    const eps = opts.ascii ? 'eps' : 'ε';
    const out = [];
    if (m.name) out.push('# ' + m.name);
    out.push('alphabet ' + m.alphabet.map(esc).join(' '));
    out.push('states ' + m.states.join(' '));
    if (m.start !== null) out.push('start ' + m.start);
    if (m.accept.length) out.push('accept ' + m.accept.join(' '));
    // one line per (from, to) pair with the symbols together, in state order then alphabet order
    const groups = new Map(), symOrder = (a) => (a === EPS ? -1 : m.alphabet.indexOf(a));
    for (const e of m.trans) { const k = e.from + '\u0000' + e.to; if (!groups.has(k)) groups.set(k, { from: e.from, to: e.to, syms: [] }); groups.get(k).syms.push(e.sym); }
    const si = new Map(m.states.map((q, i) => [q, i]));
    [...groups.values()].sort((x, y) => si.get(x.from) - si.get(y.from) || symOrder(x.syms[0]) - symOrder(y.syms[0]) || si.get(x.to) - si.get(y.to))
      .forEach((g) => out.push(`${g.from} -${g.syms.sort((a, b) => symOrder(a) - symOrder(b)).map((a) => (a === EPS ? eps : esc(a))).join(',')}-> ${g.to}`));
    if (m.pos) for (const q of m.states) if (m.pos[q]) out.push(`at ${q} ${Math.round(m.pos[q].x)} ${Math.round(m.pos[q].y)}`);
    return out.join('\n') + '\n';
  };

  // ---------------------------------------------------------------- internal indexes

  // Integer-indexed view of a machine for the fast paths: out[i] maps symbol -> target indexes,
  // eps[i] lists ε-targets.
  function index(m) {
    const ix = new Map(m.states.map((q, i) => [q, i])), n = m.states.length;
    const out = m.states.map(() => new Map()), eps = m.states.map(() => []);
    for (const e of m.trans) {
      const f = ix.get(e.from), t = ix.get(e.to);
      if (e.sym === EPS) eps[f].push(t);
      else { let l = out[f].get(e.sym); if (!l) out[f].set(e.sym, (l = [])); l.push(t); }
    }
    const acc = new Uint8Array(n);
    for (const q of m.accept) acc[ix.get(q)] = 1;
    return { ix, n, out, eps, acc, start: ix.get(m.start) };
  }
  function closeIdx(I, list) {
    const seen = new Uint8Array(I.n), st = [];
    for (const i of list) if (!seen[i]) { seen[i] = 1; st.push(i); }
    while (st.length) { const i = st.pop(); for (const j of I.eps[i]) if (!seen[j]) { seen[j] = 1; st.push(j); } }
    const r = [];
    for (let i = 0; i < I.n; i++) if (seen[i]) r.push(i);
    return r;
  }
  // A lazily built DFA over sets of states: the engine under acceptance, equivalence, counting and
  // enumeration. Nodes are { set (indexes), key, acc, next: Map }.
  function lazyDet(m) {
    const I = index(m), nodes = new Map();
    const node = (set) => {
      const key = set.join(',');
      let nd = nodes.get(key);
      if (!nd) nodes.set(key, (nd = { set, key, acc: set.some((i) => I.acc[i]), next: new Map(), names: null }));
      return nd;
    };
    const start = node(closeIdx(I, [I.start]));
    const step = (nd, a) => {
      let r = nd.next.get(a);
      if (!r) {
        const t = [];
        for (const i of nd.set) { const l = I.out[i].get(a); if (l) t.push(...l); }
        r = node(closeIdx(I, t));
        nd.next.set(a, r);
      }
      return r;
    };
    const names = (nd) => nd.names || (nd.names = nd.set.map((i) => m.states[i]));
    // how to show a node: a DFA's state by its own name, an NFA's subset as a set (∅ for dead)
    const dfa = FA.kind(m) === 'dfa';
    const label = (nd) => (dfa && nd.set.length === 1 ? m.states[nd.set[0]] : setName(names(nd)));
    return { start, step, names, label, I };
  }
  FA._lazyDet = lazyDet;

  // ---------------------------------------------------------------- running

  // ε-closure of a set of states, tracing each ε-move followed.
  FA.closure = function (m, set) {
    const trace = [], seen = new Set(set), order = [...set], stack = [...set];
    trace.push({ kind: 'closure-start', states: [...set], say: `The ε-closure starts with ${listStates([...set])}.` });
    const epsFrom = new Map();
    for (const e of m.trans) if (e.sym === EPS) epsFrom.set(e.from, (epsFrom.get(e.from) || []).concat([e.to]));
    while (stack.length) {
      const q = stack.pop();
      for (const r of epsFrom.get(q) || []) {
        if (seen.has(r)) continue;
        seen.add(r); order.push(r); stack.push(r);
        trace.push({ kind: 'closure-add', from: q, to: r, say: `ε-move ${q} → ${r}: add ${r}.` });
      }
    }
    const si = new Map(m.states.map((q, i) => [q, i]));
    const result = order.slice().sort((a, b) => si.get(a) - si.get(b));
    if (trace.length > 1) trace.push({ kind: 'closure-done', states: result, say: `ε-closure = ${listStates(result)}.` });
    return { result, trace };
  };

  // Run a machine on w and trace it: the set of live states after each symbol (a single state for a
  // DFA), the moves used, and the ε-closure steps. Works for DFA, NFA and ε-NFA alike.
  FA.run = function (m, w) {
    check(m, 'run');
    const sym = chars(w), dfa = FA.isDFA(m), trace = [];
    const acc = new Set(m.accept);
    const c0 = FA.closure(m, [m.start]);
    let cur = c0.result;
    trace.push({ kind: 'start', pos: 0, states: cur, closure: c0.trace.slice(1), say: dfa ? `Start in ${m.start}.` : `Start in ${m.start}; with its ε-closure the live states are ${listStates(cur)}.` });
    const bySym = new Map();
    for (const e of m.trans) if (e.sym !== EPS) { const k = e.from + '\u0000' + e.sym; bySym.set(k, (bySym.get(k) || []).concat([e])); }
    for (let i = 0; i < sym.length; i++) {
      const a = sym[i];
      if (!m.alphabet.includes(a)) {
        trace.push({ kind: 'stuck', pos: i, sym: a, states: [], say: `${a} is not in the alphabet {${m.alphabet.join(', ')}}: the string is rejected.` });
        trace.push({ kind: 'end', pos: i, accepted: false, states: [], say: `Rejected: ${showW(w)} uses a symbol outside the alphabet.` });
        return { accepted: false, states: [], trace };
      }
      const edges = cur.flatMap((q) => bySym.get(q + '\u0000' + a) || []);
      const moved = uniq(edges.map((e) => e.to));
      const cl = FA.closure(m, moved);
      const from = cur;
      cur = cl.result;
      if (!cur.length) {
        trace.push({ kind: 'stuck', pos: i + 1, sym: a, from, edges, states: [], say: dfa ? `${from[0]} has no move on ${a}: the machine falls into the dead state.` : `No live state has a move on ${a}: the set of live states is empty.` });
        trace.push({ kind: 'end', pos: sym.length, accepted: false, states: [], say: `Rejected: nothing is alive after reading ${showW(sym.slice(0, i + 1).join(''))}.` });
        return { accepted: false, states: [], trace };
      }
      const via = edges.map((e) => `${e.from}→${e.to}`).join(', ');
      trace.push({ kind: 'read', pos: i + 1, sym: a, from, edges, moved, closure: cl.trace.slice(1), states: cur,
        say: dfa ? `Read ${a}: ${from[0]} → ${cur[0]}.` : `Read ${a}: ${via}${cur.length > moved.length ? `, then ε-moves add ${cur.filter((q) => !moved.includes(q)).join(', ')}` : ''}; live states ${listStates(cur)}.` });
    }
    const hit = cur.filter((q) => acc.has(q));
    const accepted = hit.length > 0;
    trace.push({ kind: 'end', pos: sym.length, accepted, states: cur, hit,
      say: accepted ? (dfa ? `End in ${cur[0]}, an accepting state: accept ${showW(w)}.` : `Accept: ${hit.join(', ')} ${hit.length === 1 ? 'is' : 'are'} accepting.`)
        : (dfa ? `End in ${cur[0]}, not accepting: reject ${showW(w)}.` : `Reject: none of ${listStates(cur)} is accepting.`) });
    return { accepted, states: cur, trace };
  };

  // A fast membership test: returns a function w -> boolean (memoising the subsets it meets).
  FA.acceptor = function (m) {
    const D = lazyDet(m);
    const alpha = new Set(m.alphabet);
    return (w) => {
      let nd = D.start;
      for (const a of chars(w)) { if (!alpha.has(a)) return false; nd = D.step(nd, a); if (!nd.set.length) return false; }
      return nd.acc;
    };
  };
  FA.accepts = (m, w) => FA.acceptor(m)(w);

  // Accepting computations on w: each is a list of moves { from, sym, to } (ε-moves included). An
  // ε-cycle cannot repeat a configuration within one computation, so the search ends. limit caps the
  // number returned; total counts all accepting computations found (up to cap).
  FA.paths = function (m, w, limit = 20, cap = 10000) {
    check(m, 'paths');
    const sym = chars(w), acc = new Set(m.accept), found = [];
    const from = new Map();
    for (const e of m.trans) from.set(e.from, (from.get(e.from) || []).concat([e]));
    let total = 0;
    const path = [];
    const dfs = (q, i, epsSeen) => {
      if (total >= cap) return;
      if (i === sym.length && acc.has(q)) { total++; if (found.length < limit) found.push(path.slice()); }
      for (const e of from.get(q) || []) {
        if (e.sym === EPS) {
          if (epsSeen.has(e.to)) continue;
          epsSeen.add(e.to); path.push(e); dfs(e.to, i, epsSeen); path.pop(); epsSeen.delete(e.to);
        } else if (i < sym.length && e.sym === sym[i]) {
          path.push(e); dfs(e.to, i + 1, new Set([e.to])); path.pop();
        }
      }
    };
    dfs(m.start, 0, new Set([m.start]));
    return { paths: found, total, capped: total >= cap };
  };

  // ---------------------------------------------------------------- reachability

  function reachableSet(m) {
    const seen = new Set(m.start === null ? [] : [m.start]), q = [...seen];
    const from = new Map();
    for (const e of m.trans) from.set(e.from, (from.get(e.from) || []).concat([e.to]));
    while (q.length) { const s = q.shift(); for (const t of from.get(s) || []) if (!seen.has(t)) { seen.add(t); q.push(t); } }
    return seen;
  }
  function coReachableSet(m) {
    const seen = new Set(m.accept), q = [...seen];
    const to = new Map();
    for (const e of m.trans) to.set(e.to, (to.get(e.to) || []).concat([e.from]));
    while (q.length) { const s = q.shift(); for (const t of to.get(s) || []) if (!seen.has(t)) { seen.add(t); q.push(t); } }
    return seen;
  }
  FA.reachable = (m) => m.states.filter((q) => reachableSet(m).has(q));

  // Restrict a machine to a set of states it keeps (start is always kept so the result stays a machine).
  function restrict(m, keep) {
    return FA.make({ states: m.states.filter((q) => keep.has(q) || q === m.start), alphabet: m.alphabet, start: m.start,
      accept: m.accept.filter((q) => keep.has(q)), trans: m.trans.filter((e) => keep.has(e.from) && keep.has(e.to)) });
  }

  FA.removeUnreachable = function (m) {
    check(m, 'remove unreachable');
    const trace = [], seen = new Set([m.start]), queue = [m.start];
    trace.push({ kind: 'reach', state: m.start, say: `${m.start} is reachable: it is the start.` });
    while (queue.length) {
      const s = queue.shift();
      for (const e of m.trans) if (e.from === s && !seen.has(e.to)) {
        seen.add(e.to); queue.push(e.to);
        trace.push({ kind: 'reach', state: e.to, edge: e, say: `${e.to} is reachable from ${s} on ${showSym(e.sym)}.` });
      }
    }
    for (const q of m.states) if (!seen.has(q)) trace.push({ kind: 'remove', state: q, say: `${q} cannot be reached from ${m.start}: remove it.` });
    if (seen.size === m.states.length) trace.push({ kind: 'done', say: 'Every state is reachable; nothing to remove.' });
    return { fa: restrict(m, seen), removed: m.states.filter((q) => !seen.has(q)), trace };
  };

  // Keep only useful states: reachable from the start and able to reach acceptance. (The result may be
  // a partial DFA; the dropped states only ever led to rejection.)
  FA.trim = function (m) {
    check(m, 'trim');
    const r = reachableSet(m), c = coReachableSet(m), trace = [];
    const keep = new Set(m.states.filter((q) => r.has(q) && c.has(q)));
    for (const q of m.states) {
      if (!r.has(q)) trace.push({ kind: 'remove', state: q, why: 'unreachable', say: `${q} is unreachable: remove it.` });
      else if (!c.has(q)) trace.push({ kind: 'remove', state: q, why: 'dead', say: `No accepting state can be reached from ${q}: it is dead, remove it.` });
    }
    return { fa: restrict(m, keep), trace };
  };

  // ---------------------------------------------------------------- completion and complement

  FA.complete = function (m, deadName = 'dead') {
    check(m, 'complete');
    const trace = [], miss = FA.missing(m);
    if (!miss.length) return { fa: FA.clone(m), dead: null, trace: [{ kind: 'done', say: 'Every state already has a move on every symbol: the machine is complete.' }] };
    const dead = freshName(new Set(m.states), deadName);
    trace.push({ kind: 'dead', state: dead, say: `Add a dead state ${dead}: it rejects everything and never leaves.` });
    const trans = m.trans.slice();
    for (const { state, sym } of miss) {
      trans.push({ from: state, sym, to: dead });
      trace.push({ kind: 'edge', edge: { from: state, sym, to: dead }, say: `${state} had no move on ${sym}: send it to ${dead}.` });
    }
    for (const a of m.alphabet) trans.push({ from: dead, sym: a, to: dead });
    trace.push({ kind: 'loop', state: dead, say: `${dead} loops to itself on ${m.alphabet.join(', ')}.` });
    return { fa: FA.make({ states: [...m.states, dead], alphabet: m.alphabet, start: m.start, accept: m.accept, trans }), dead, trace };
  };

  // A complete DFA for any machine: determinise if needed, then complete.
  function toCompleteDFA(m, trace) {
    let d = m;
    if (!FA.isDFA(d)) { const r = FA.subset(d); d = r.fa; trace.push({ kind: 'determinize', fa: d, steps: r.trace, say: `First determinise: the subset construction gives a DFA with ${plural(d.states.length, 'state')}.` }); }
    if (!FA.isComplete(d)) { const r = FA.complete(d); d = r.fa; trace.push({ kind: 'complete', fa: d, steps: r.trace, say: `Complete it with the dead state ${r.dead}, so every string has a run.` }); }
    return d;
  }
  FA.toCompleteDFA = (m) => { const trace = []; const fa = toCompleteDFA(m, trace); return { fa, trace }; };

  FA.complement = function (m) {
    check(m, 'complement');
    const trace = [];
    const d = toCompleteDFA(m, trace);
    const acc = d.states.filter((q) => !d.accept.includes(q));
    trace.push({ kind: 'flip', accept: acc, was: d.accept, say: `Swap accepting and non-accepting states: accept ${listStates(acc)} instead of ${listStates(d.accept)}.` });
    return { fa: FA.make({ ...d, accept: acc }), trace };
  };

  // ---------------------------------------------------------------- ε-removal and subset construction

  FA.removeEps = function (m) {
    check(m, 'remove ε');
    const trace = [], trans = [], acc = new Set(m.accept), newAcc = [];
    const seen = new Set();
    for (const q of m.states) {
      const C = FA.closure(m, [q]).result;
      trace.push({ kind: 'closure', state: q, closure: C, say: `ε-closure(${q}) = ${listStates(C)}.` });
      for (const p of C) for (const e of m.trans) if (e.from === p && e.sym !== EPS) {
        const k = q + '\u0000' + e.sym + '\u0000' + e.to;
        if (seen.has(k)) continue;
        seen.add(k);
        trans.push({ from: q, sym: e.sym, to: e.to });
        if (p !== q) trace.push({ kind: 'edge', edge: { from: q, sym: e.sym, to: e.to }, via: p, say: `${q} reaches ${p} by ε and ${p} reads ${e.sym} to ${e.to}: add ${q} -${e.sym}-> ${e.to}.` });
      }
      if (C.some((p) => acc.has(p))) {
        newAcc.push(q);
        if (!acc.has(q)) trace.push({ kind: 'accept', state: q, say: `${q} reaches an accepting state by ε-moves alone: make ${q} accepting.` });
      }
    }
    trace.push({ kind: 'done', say: 'Drop every ε-move; the new moves and accepting states make up for them.' });
    return { fa: FA.make({ states: m.states, alphabet: m.alphabet, start: m.start, accept: newAcc, trans }), trace };
  };

  // Subset construction, lazily: only subsets reachable from the start's ε-closure are built. The empty
  // subset (∅) is kept as the dead state unless opts.dropEmpty, so the DFA is complete by default.
  // opts.startSet starts from a set of states instead of the start state (several initial states).
  FA.subset = function (m, opts = {}) {
    check(m, 'subset construction');
    const trace = [], I = index(m);
    const nameOf = (set) => setName(set.map((i) => m.states[i]));
    const start = closeIdx(I, opts.startSet ? opts.startSet.map((q) => I.ix.get(q)) : [I.start]);
    const sets = new Map(), order = [];
    const add = (set, from) => {
      const k = set.join(',');
      if (sets.has(k)) return false;
      sets.set(k, set); order.push(set);
      trace.push({ kind: 'subset-new', set: set.map((i) => m.states[i]), name: nameOf(set), from: from || null, accepting: set.some((i) => I.acc[i]),
        say: from ? `New subset ${nameOf(set)}${set.some((i) => I.acc[i]) ? ' (accepting: it contains an accepting state)' : ''}.` : opts.startSet ? `The start subset holds every initial state: ${nameOf(set)}.` : set.length > 1 ? `The start subset is the ε-closure of ${m.start}: ${nameOf(set)}.` : `The start subset is ${nameOf(set)}.` });
      return true;
    };
    add(start, null);
    const trans = [];
    for (let qi = 0; qi < order.length; qi++) {
      const S = order[qi];
      for (const a of m.alphabet) {
        const moved = [];
        for (const i of S) for (const j of I.out[i].get(a) || []) if (!moved.includes(j)) moved.push(j);
        moved.sort((x, y) => x - y);
        const Tset = closeIdx(I, moved);
        if (!Tset.length && opts.dropEmpty) continue;
        const fresh = add(Tset, nameOf(S));
        trans.push({ from: nameOf(S), sym: a, to: nameOf(Tset) });
        trace.push({ kind: 'subset-edge', from: nameOf(S), sym: a, moved: moved.map((i) => m.states[i]), to: nameOf(Tset), fresh,
          say: `From ${nameOf(S)} on ${a}: the moves reach ${listStates(moved.map((i) => m.states[i]))}${Tset.length > moved.length ? `, with ε-closure ${nameOf(Tset)}` : ''}${fresh ? ' (new)' : ''}.` });
      }
    }
    const states = order.map(nameOf);
    const fa = FA.make({ states, alphabet: m.alphabet, start: nameOf(start), accept: order.filter((S) => S.some((i) => I.acc[i])).map(nameOf), trans });
    trace.push({ kind: 'done', say: `The DFA has ${plural(states.length, 'state')} out of ${2 ** m.states.length > 1e9 ? '2^' + m.states.length : 2 ** m.states.length} possible subsets.` });
    const map = {};
    order.forEach((S) => (map[nameOf(S)] = S.map((i) => m.states[i])));
    return { fa, sets: map, trace };
  };
  FA.determinize = FA.subset;

  // ---------------------------------------------------------------- product constructions

  const OPS = {
    union: { f: (x, y) => x || y, sym: '∪', say: 'either is accepting' },
    intersection: { f: (x, y) => x && y, sym: '∩', say: 'both are accepting' },
    difference: { f: (x, y) => x && !y, sym: '−', say: 'the first accepts and the second does not' },
    xor: { f: (x, y) => x !== y, sym: '⊕', say: 'exactly one is accepting' },
  };
  OPS.symdiff = OPS.xor; OPS.and = OPS.intersection; OPS.or = OPS.union; OPS.minus = OPS.difference;
  // Bring two machines to complete DFAs over the union of their alphabets.
  function align(a, b, trace) {
    const sigma = uniq([...a.alphabet, ...b.alphabet]).sort();
    const widen = (m, tag) => {
      let x = m.alphabet.length === sigma.length ? m : FA.make({ ...m, alphabet: sigma });
      if (x !== m) trace.push({ kind: 'alphabet', which: tag, say: `Machine ${tag} now reads the joint alphabet {${sigma.join(', ')}}; new symbols lead to its dead state.` });
      const sub = [];
      x = toCompleteDFA(x, sub);
      sub.forEach((s) => trace.push({ ...s, which: tag, say: `Machine ${tag}: ${s.say[0].toLowerCase()}${s.say.slice(1)}` }));
      return x;
    };
    return [widen(a, 'A'), widen(b, 'B')];
  }
  FA.product = function (a, b, op = 'intersection') {
    check(a, 'product (A)'); check(b, 'product (B)');
    const O = OPS[op];
    if (!O) throw new Error(`Unknown product operation ${op}: use union, intersection, difference or xor.`);
    const trace = [];
    const [A, B] = align(a, b, trace);
    const dA = deltaMap(A), dB = deltaMap(B), accA = new Set(A.accept), accB = new Set(B.accept);
    const nm = (p, q) => `(${p},${q})`;
    const start = [A.start, B.start], seen = new Map([[nm(...start), start]]), queue = [start], trans = [], accept = [];
    trace.push({ kind: 'pair-new', pair: start, name: nm(...start), say: `Start in the pair ${nm(...start)}: both machines start together.` });
    while (queue.length) {
      const [p, q] = queue.shift(), n = nm(p, q);
      if (O.f(accA.has(p), accB.has(q))) { accept.push(n); trace.push({ kind: 'pair-accept', pair: [p, q], name: n, say: `${n} is accepting for ${op}: ${O.say}.` }); }
      for (const s of A.alphabet) {
        const p2 = dA.get(p).get(s), q2 = dB.get(q).get(s), n2 = nm(p2, q2);
        const fresh = !seen.has(n2);
        if (fresh) { seen.set(n2, [p2, q2]); queue.push([p2, q2]); }
        trans.push({ from: n, sym: s, to: n2 });
        trace.push({ kind: 'pair-edge', from: n, sym: s, to: n2, pair: [p2, q2], fresh, say: `On ${s}: A goes ${p} → ${p2} and B goes ${q} → ${q2}, so ${n} → ${n2}${fresh ? ' (new pair)' : ''}.` });
      }
    }
    const fa = FA.make({ states: [...seen.keys()], alphabet: A.alphabet, start: nm(...start), accept, trans });
    trace.push({ kind: 'done', say: `The product has ${plural(fa.states.length, 'reachable pair')} out of ${A.states.length} × ${B.states.length}.` });
    return { fa, pairs: Object.fromEntries(seen), trace };
  };
  FA.union = (a, b) => FA.product(a, b, 'union');
  FA.intersection = (a, b) => FA.product(a, b, 'intersection');
  FA.difference = (a, b) => FA.product(a, b, 'difference');
  FA.symmetricDifference = (a, b) => FA.product(a, b, 'xor');
  function deltaMap(d) {
    const m = new Map(d.states.map((q) => [q, new Map()]));
    for (const e of d.trans) m.get(e.from).set(e.sym, e.to);
    return m;
  }
  FA._deltaMap = deltaMap;

  // ---------------------------------------------------------------- NFA constructions

  // Rename b's states so they do not clash with a's (adding ′ marks).
  function disjoint(a, b) {
    const taken = new Set(a.states), ren = new Map();
    for (const q of b.states) ren.set(q, freshName(taken, q));
    const r = (q) => ren.get(q);
    return FA.make({ states: b.states.map(r), alphabet: b.alphabet, start: r(b.start), accept: b.accept.map(r), trans: b.trans.map((e) => ({ from: r(e.from), sym: e.sym, to: r(e.to) })) });
  }
  FA.disjoint = disjoint;

  FA.unionNFA = function (a, b) {
    check(a, 'union'); check(b, 'union');
    const B = disjoint(a, b), taken = new Set([...a.states, ...B.states]), s = freshName(taken, 's');
    const trace = [];
    if (B.states.some((q, i) => q !== b.states[i])) trace.push({ kind: 'rename', say: `Rename B's states (${b.states.join(', ')} → ${B.states.join(', ')}) so the two machines share none.` });
    trace.push({ kind: 'start', state: s, say: `A new start ${s} with ε-moves to ${a.start} and ${B.start}: guess which machine to run.` });
    const fa = FA.make({ states: [s, ...a.states, ...B.states], alphabet: uniq([...a.alphabet, ...B.alphabet]).sort(), start: s, accept: [...a.accept, ...B.accept],
      trans: [{ from: s, sym: EPS, to: a.start }, { from: s, sym: EPS, to: B.start }, ...a.trans, ...B.trans] });
    return { fa, trace };
  };
  FA.concatNFA = function (a, b) {
    check(a, 'concatenation'); check(b, 'concatenation');
    const B = disjoint(a, b), trace = [];
    if (B.states.some((q, i) => q !== b.states[i])) trace.push({ kind: 'rename', say: `Rename B's states (${b.states.join(', ')} → ${B.states.join(', ')}) so the two machines share none.` });
    const link = a.accept.map((f) => ({ from: f, sym: EPS, to: B.start }));
    link.forEach((e) => trace.push({ kind: 'edge', edge: e, say: `ε-move from A's accepting ${e.from} to B's start ${B.start}: after a word of A, start B.` }));
    trace.push({ kind: 'accept', accept: B.accept, say: `Only B's accepting states ${listStates(B.accept)} accept now.` });
    const fa = FA.make({ states: [...a.states, ...B.states], alphabet: uniq([...a.alphabet, ...B.alphabet]).sort(), start: a.start, accept: B.accept, trans: [...a.trans, ...link, ...B.trans] });
    return { fa, trace };
  };
  // Star with a new accepting start state. (Making the old start accepting instead would be wrong when
  // the start has incoming moves: it would accept strings that end part-way through a loop.)
  FA.starNFA = function (a) {
    check(a, 'star');
    const s = freshName(new Set(a.states), 's'), trace = [];
    trace.push({ kind: 'start', state: s, say: `A new start ${s}, accepting so that ε is in the star, with an ε-move to ${a.start}.` });
    const back = a.accept.map((f) => ({ from: f, sym: EPS, to: a.start }));
    back.forEach((e) => trace.push({ kind: 'edge', edge: e, say: `ε-move from accepting ${e.from} back to ${a.start}: start another piece.` }));
    const fa = FA.make({ states: [s, ...a.states], alphabet: a.alphabet, start: s, accept: [s, ...a.accept], trans: [{ from: s, sym: EPS, to: a.start }, ...a.trans, ...back] });
    return { fa, trace };
  };

  FA.reverse = function (m) {
    check(m, 'reverse');
    const trace = [], trans = m.trans.map((e) => ({ from: e.to, sym: e.sym, to: e.from }));
    trace.push({ kind: 'flip-edges', say: `Turn every arrow around (${plural(m.trans.length, 'move')}).` });
    let start = m.accept[0], states = m.states;
    if (m.accept.length !== 1) {
      start = freshName(new Set(m.states), 's');
      states = [start, ...m.states];
      m.accept.forEach((f) => trans.push({ from: start, sym: EPS, to: f }));
      trace.push({ kind: 'start', state: start, targets: m.accept, say: m.accept.length ? `A new start ${start} with ε-moves to the old accepting states ${listStates(m.accept)}.` : `There were no accepting states, so the new start ${start} leads nowhere: the reversal of ∅ is ∅.` });
    } else trace.push({ kind: 'start', state: start, say: `The single old accepting state ${start} becomes the start.` });
    trace.push({ kind: 'accept', accept: [m.start], say: `The old start ${m.start} becomes the only accepting state.` });
    return { fa: FA.make({ states, alphabet: m.alphabet, start, accept: [m.start], trans }), trace };
  };

  // Homomorphism h: each symbol a is replaced by the string h[a] (possibly ε). Each move q -a-> r becomes a
  // chain of new states spelling h[a] (an ε-move when h[a] is empty).
  FA.homomorphism = function (m, h) {
    check(m, 'homomorphism');
    for (const a of m.alphabet) if (typeof h[a] !== 'string') throw new Error(`h(${a}) is not given.`);
    const taken = new Set(m.states), states = m.states.slice(), trans = [], trace = [];
    for (const e of m.trans) {
      if (e.sym === EPS) { trans.push(e); continue; }
      const w = chars(h[e.sym]);
      if (!w.length) { trans.push({ from: e.from, sym: EPS, to: e.to }); trace.push({ kind: 'edge', edge: e, chain: [], say: `h(${e.sym}) = ε: ${e.from} -${e.sym}-> ${e.to} becomes an ε-move.` }); continue; }
      let cur = e.from;
      const chain = [];
      w.forEach((c, i) => {
        const nxt = i === w.length - 1 ? e.to : freshName(taken, `${e.from}${e.sym}${i + 1}`);
        if (nxt !== e.to) { states.push(nxt); chain.push(nxt); }
        trans.push({ from: cur, sym: c, to: nxt });
        cur = nxt;
      });
      trace.push({ kind: 'edge', edge: e, chain, say: `${e.from} -${e.sym}-> ${e.to} becomes a path spelling h(${e.sym}) = ${h[e.sym]}${chain.length ? ` through ${chain.join(', ')}` : ''}.` });
    }
    const alphabet = uniq(m.alphabet.flatMap((a) => chars(h[a]))).sort();
    return { fa: FA.make({ states, alphabet, start: m.start, accept: m.accept, trans }), trace };
  };

  // Inverse homomorphism h⁻¹(L) over the source alphabet: q -a-> r when the machine can go from q to r
  // reading h[a]. Same states, start and accepting states (ε-moves are removed first).
  FA.inverseHomomorphism = function (m, h, source) {
    check(m, 'inverse homomorphism');
    source = source || Object.keys(h).sort();
    const trace = [];
    let M = m;
    if (FA.kind(m) === 'enfa') { M = FA.removeEps(m).fa; trace.push({ kind: 'remove-eps', say: 'First remove the ε-moves, so each move reads one symbol.' }); }
    const by = new Map();
    for (const e of M.trans) { const k = e.from + '\u0000' + e.sym; by.set(k, (by.get(k) || []).concat([e.to])); }
    const trans = [];
    for (const q of M.states) for (const a of source) {
      if (typeof h[a] !== 'string') throw new Error(`h(${a}) is not given.`);
      let cur = [q];
      for (const c of chars(h[a])) cur = uniq(cur.flatMap((p) => by.get(p + '\u0000' + c) || []));
      for (const r of cur) trans.push({ from: q, sym: a, to: r });
      trace.push({ kind: 'edge', from: q, sym: a, word: h[a], to: cur, say: cur.length ? `From ${q}, reading h(${a}) = ${showW(h[a])} reaches ${cur.join(', ')}: add ${q} -${a}-> ${cur.join(', ')}.` : `From ${q}, h(${a}) = ${showW(h[a])} cannot be read: no move on ${a}.` });
    }
    return { fa: FA.make({ states: M.states, alphabet: source, start: M.start, accept: M.accept, trans }), trace };
  };

  // Right quotient L(a)/L(b) = { x : xy ∈ L(a) for some y ∈ L(b) }: same machine, and q accepts when
  // some y ∈ L(b) leads from q to acceptance (checked by an emptiness test on a product).
  FA.quotient = function (a, b) {
    check(a, 'quotient'); check(b, 'quotient');
    const trace = [], accept = [];
    for (const q of a.states) {
      const fromQ = FA.make({ ...a, start: q });
      const r = FA.isEmpty(FA.product(fromQ, b, 'intersection').fa);
      if (!r.empty) { accept.push(q); trace.push({ kind: 'test', state: q, accepting: true, witness: r.witness, say: `From ${q}, the string ${showW(r.witness)} is in L(B) and leads to acceptance: ${q} accepts.` }); }
      else trace.push({ kind: 'test', state: q, accepting: false, say: `No string of L(B) leads from ${q} to acceptance: ${q} does not accept.` });
    }
    return { fa: FA.make({ ...a, accept }), trace };
  };
  // Left quotient L(b)\L(a) = { y : xy ∈ L(a) for some x ∈ L(b) }: start in every state of a that some
  // x ∈ L(b) reaches (found by running both machines together).
  FA.leftQuotient = function (a, b) {
    check(a, 'left quotient'); check(b, 'left quotient');
    const A = FA.kind(a) === 'enfa' ? FA.removeEps(a).fa : a;
    const B = FA.kind(b) === 'enfa' ? FA.removeEps(b).fa : b;
    const accB = new Set(B.accept), trace = [];
    const k = (p, q) => p + '\u0000' + q, seen = new Set([k(A.start, B.start)]), queue = [[A.start, B.start, '']], starts = new Map();
    const byA = new Map(), byB = new Map();
    for (const e of A.trans) byA.set(e.from + '\u0000' + e.sym, (byA.get(e.from + '\u0000' + e.sym) || []).concat([e.to]));
    for (const e of B.trans) byB.set(e.from + '\u0000' + e.sym, (byB.get(e.from + '\u0000' + e.sym) || []).concat([e.to]));
    while (queue.length) {
      const [p, q, x] = queue.shift();
      if (accB.has(q) && !starts.has(p)) { starts.set(p, x); trace.push({ kind: 'start', state: p, witness: x, say: `${showW(x)} is in L(B) and takes A to ${p}: ${p} becomes a start.` }); }
      for (const s of A.alphabet) for (const p2 of byA.get(p + '\u0000' + s) || []) for (const q2 of byB.get(q + '\u0000' + s) || []) {
        if (!seen.has(k(p2, q2))) { seen.add(k(p2, q2)); queue.push([p2, q2, x + s]); }
      }
    }
    const s0 = freshName(new Set(A.states), 's');
    const fa = FA.make({ states: [s0, ...A.states], alphabet: A.alphabet, start: s0, accept: A.accept, trans: [...[...starts.keys()].map((p) => ({ from: s0, sym: EPS, to: p })), ...A.trans] });
    return { fa, trace };
  };

  // ---------------------------------------------------------------- minimisation

  // Prepare for minimisation: a complete DFA with no unreachable states.
  function prepMin(m, trace) {
    const d = toCompleteDFA(m, trace);
    const r = FA.removeUnreachable(d);
    if (r.removed.length) trace.push({ kind: 'unreachable', removed: r.removed, say: `Remove unreachable ${r.removed.join(', ')}: they never affect the language.` });
    return r.fa;
  }
  // The DFA whose states are the blocks of a partition; a block of one state keeps its name.
  function quotientByBlocks(d, blocks) {
    const si = new Map(d.states.map((q, i) => [q, i]));
    blocks = blocks.map((b) => b.slice().sort((x, y) => si.get(x) - si.get(y))).sort((x, y) => si.get(x[0]) - si.get(y[0]));
    // the block holding the start comes first, the rest in order of their first state
    const sb = blocks.findIndex((b) => b.includes(d.start));
    blocks = [blocks[sb], ...blocks.filter((_, i) => i !== sb)];
    const name = (b) => (b.length === 1 ? b[0] : setName(b));
    const of = new Map();
    blocks.forEach((b) => b.forEach((q) => of.set(q, name(b))));
    const del = deltaMap(d), acc = new Set(d.accept);
    const trans = [];
    for (const b of blocks) for (const a of d.alphabet) trans.push({ from: name(b), sym: a, to: of.get(del.get(b[0]).get(a)) });
    return { fa: FA.make({ states: blocks.map(name), alphabet: d.alphabet, start: of.get(d.start), accept: blocks.filter((b) => acc.has(b[0])).map(name), trans }), blocks: blocks.map((b) => b.slice()), of };
  }

  // Table filling: mark pairs that are distinguishable. Pass 0 marks accepting/non-accepting pairs; each
  // later pass marks {p, q} when some symbol leads to an already-marked pair. Unmarked pairs merge.
  FA.minimizeTable = function (m) {
    check(m, 'minimise');
    const trace = [];
    const d = prepMin(m, trace);
    const Q = d.states, n = Q.length, del = deltaMap(d), acc = new Set(d.accept);
    const marked = new Map(), key = (i, j) => (i < j ? i + ',' + j : j + ',' + i);
    const idx = new Map(Q.map((q, i) => [q, i]));
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (acc.has(Q[i]) !== acc.has(Q[j])) {
      marked.set(key(i, j), { round: 0, reason: 'accept' });
      trace.push({ kind: 'mark', pair: [Q[i], Q[j]], round: 0, reason: 'accept', say: `Mark {${Q[i]}, ${Q[j]}}: ε separates them (${acc.has(Q[i]) ? Q[i] : Q[j]} accepts, the other does not).` });
    }
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      const newly = [];
      for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) {
        if (marked.has(key(i, j))) continue;
        for (const a of d.alphabet) {
          const p = idx.get(del.get(Q[i]).get(a)), q = idx.get(del.get(Q[j]).get(a));
          if (p !== q && marked.has(key(p, q)) && marked.get(key(p, q)).round < round) {
            newly.push([i, j, a, p, q]);
            break;
          }
        }
      }
      // marks of this round only use marks from earlier rounds, so the rounds match the length of the
      // shortest distinguishing string
      for (const [i, j, a, p, q] of newly) {
        const was = marked.get(key(p, q));
        marked.set(key(i, j), { round, reason: 'symbol', sym: a, via: [Q[p], Q[q]] });
        changed = true;
        trace.push({ kind: 'mark', pair: [Q[i], Q[j]], round, reason: 'symbol', sym: a, via: [Q[p], Q[q]], viaRound: was.round,
          say: `Mark {${Q[i]}, ${Q[j]}}: on ${a} they go to {${Q[p]}, ${Q[q]}}, which is already marked.` });
      }
      if (!changed) trace.push({ kind: 'round', round, say: `Pass ${round} marks nothing new: the table is finished.` });
    }
    // unmarked pairs are equivalent; gather the classes
    const cls = Q.map((_, i) => i);
    const find = (x) => (cls[x] === x ? x : (cls[x] = find(cls[x])));
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (!marked.has(key(i, j))) {
      trace.push({ kind: 'equal', pair: [Q[i], Q[j]], say: `{${Q[i]}, ${Q[j]}} is never marked: ${Q[i]} and ${Q[j]} are equivalent.` });
      cls[find(j)] = find(i);
    }
    const groups = new Map();
    Q.forEach((q, i) => { const r = find(i); if (!groups.has(r)) groups.set(r, []); groups.get(r).push(q); });
    const res = quotientByBlocks(d, [...groups.values()]);
    for (const b of res.blocks) if (b.length > 1) trace.push({ kind: 'merge', states: b, name: setName(b), say: `Merge ${b.join(', ')} into ${setName(b)}.` });
    trace.push({ kind: 'done', say: `The minimal DFA has ${plural(res.fa.states.length, 'state')} (from ${d.states.length}).` });
    const table = {};
    for (const [k, v] of marked) { const [i, j] = k.split(',').map(Number); table[Q[i] + '|' + Q[j]] = v; }
    return { fa: res.fa, blocks: res.blocks, table, states: Q, trace };
  };

  // Moore's refinement: start from {accepting, non-accepting} and split blocks whose states disagree on
  // which block some symbol leads to, round by round, until stable.
  FA.minimizeMoore = function (m) {
    check(m, 'minimise');
    const trace = [];
    const d = prepMin(m, trace), del = deltaMap(d), acc = new Set(d.accept);
    let P = [d.states.filter((q) => acc.has(q)), d.states.filter((q) => !acc.has(q))].filter((b) => b.length);
    trace.push({ kind: 'partition', round: 0, blocks: P.map((b) => b.slice()), say: `Round 0: accepting ${listStates(P.find((b) => acc.has(b[0])) || [])} and non-accepting ${listStates(P.find((b) => !acc.has(b[0])) || [])}.` });
    for (let round = 1; ; round++) {
      const blockOf = new Map();
      P.forEach((b, i) => b.forEach((q) => blockOf.set(q, i)));
      const next = [];
      for (const b of P) {
        const groups = new Map();
        for (const q of b) {
          const sig = d.alphabet.map((a) => blockOf.get(del.get(q).get(a))).join(',');
          if (!groups.has(sig)) groups.set(sig, []);
          groups.get(sig).push(q);
        }
        const parts = [...groups.values()];
        if (parts.length > 1) {
          // name the symbol that first tells two of the parts apart
          const a = d.alphabet.find((s) => blockOf.get(del.get(parts[0][0]).get(s)) !== blockOf.get(del.get(parts[1][0]).get(s)));
          trace.push({ kind: 'split', round, block: b, into: parts, sym: a, say: `Split ${listStates(b)} into ${parts.map(listStates).join(' and ')}: on ${a} they lead to different blocks.` });
        }
        next.push(...parts);
      }
      if (next.length === P.length) { trace.push({ kind: 'partition', round, blocks: P.map((x) => x.slice()), stable: true, say: `Round ${round} splits nothing: the partition is stable with ${plural(P.length, 'block')}.` }); break; }
      P = next;
      trace.push({ kind: 'partition', round, blocks: P.map((x) => x.slice()), say: `After round ${round}: ${plural(P.length, 'block')}.` });
    }
    const res = quotientByBlocks(d, P);
    trace.push({ kind: 'done', say: `The minimal DFA has ${plural(res.fa.states.length, 'state')} (from ${d.states.length}).` });
    return { fa: res.fa, blocks: res.blocks, trace };
  };

  // Hopcroft: a worklist of splitters (set, symbol). For each, the states that move into the set on the
  // symbol are separated from the rest in every block they cut. When a cut block is still waiting as a
  // splitter, both halves replace it; otherwise only the smaller half is queued (the other half's effect
  // follows from it), which is what gives the O(n k log n) bound.
  FA.minimizeHopcroft = function (m) {
    check(m, 'minimise');
    const trace = [];
    const d = prepMin(m, trace), acc = new Set(d.accept);
    const inv = new Map(d.states.map((q) => [q, new Map()]));
    for (const e of d.trans) { const mm = inv.get(e.to); mm.set(e.sym, (mm.get(e.sym) || []).concat([e.from])); }
    const F = d.states.filter((q) => acc.has(q)), N = d.states.filter((q) => !acc.has(q));
    let P = [F, N].filter((b) => b.length);
    trace.push({ kind: 'partition', blocks: P.map((b) => b.slice()), say: `Start with accepting ${listStates(F)} and non-accepting ${listStates(N)}.` });
    const W = [];
    const smaller = F.length && N.length ? (F.length <= N.length ? F : N) : null;
    if (smaller) for (const a of d.alphabet) W.push([smaller.slice(), a]);
    if (smaller) trace.push({ kind: 'queue', splitters: W.map(([b, a]) => ({ block: b, sym: a })), say: `Queue the smaller block ${listStates(smaller)} with each symbol as a splitter.` });
    const sameSet = (x, y) => x.length === y.length && x.every((q) => y.includes(q));
    while (W.length) {
      const [A, a] = W.shift();
      const X = new Set(A.flatMap((q) => inv.get(q).get(a) || []));
      trace.push({ kind: 'splitter', block: A, sym: a, pre: [...X], say: `Splitter (${listStates(A)}, ${a}): the states that reach it on ${a} are ${listStates([...X])}.` });
      const next = [];
      for (const Y of P) {
        const y1 = Y.filter((q) => X.has(q)), y2 = Y.filter((q) => !X.has(q));
        if (!y1.length || !y2.length) { next.push(Y); continue; }
        next.push(y1, y2);
        trace.push({ kind: 'split', block: Y, into: [y1, y2], sym: a, splitter: A, say: `Split ${listStates(Y)} into ${listStates(y1)} (reach ${listStates(A)} on ${a}) and ${listStates(y2)}.` });
        for (const b of d.alphabet) {
          const wi = W.findIndex(([B, s]) => s === b && sameSet(B, Y));
          if (wi >= 0) W.splice(wi, 1, [y1, b], [y2, b]);
          else W.push([y1.length <= y2.length ? y1 : y2, b]);
        }
      }
      P = next;
    }
    trace.push({ kind: 'partition', blocks: P.map((b) => b.slice()), stable: true, say: `No splitters left: ${plural(P.length, 'block')}.` });
    const res = quotientByBlocks(d, P);
    trace.push({ kind: 'done', say: `The minimal DFA has ${plural(res.fa.states.length, 'state')} (from ${d.states.length}).` });
    return { fa: res.fa, blocks: res.blocks, trace };
  };

  // Rename states q0, q1, ... in breadth-first order from the start (symbols in alphabet order), so
  // equal minimal DFAs come out identical.
  FA.canonical = function (m, prefix = 'q') {
    const del = new Map(m.states.map((q) => [q, new Map()]));
    for (const e of m.trans) del.get(e.from).set(e.sym, (del.get(e.from).get(e.sym) || []).concat([e.to]));
    const ren = new Map([[m.start, prefix + 0]]), queue = [m.start];
    while (queue.length) {
      const q = queue.shift();
      for (const a of [EPS, ...m.alphabet]) for (const r of del.get(q).get(a) || []) if (!ren.has(r)) { ren.set(r, prefix + ren.size); queue.push(r); }
    }
    for (const q of m.states) if (!ren.has(q)) ren.set(q, prefix + ren.size);
    const r = (q) => ren.get(q);
    const states = m.states.map(r).sort((x, y) => +x.slice(prefix.length) - +y.slice(prefix.length));
    return FA.make({ states, alphabet: m.alphabet, start: r(m.start), accept: m.accept.map(r), trans: m.trans.map((e) => ({ from: r(e.from), sym: e.sym, to: r(e.to) })) });
  };

  // Brzozowski: determinise the reversal, then determinise the reversal of that. The result is minimal
  // (reachable subsets of a co-deterministic machine are pairwise distinguishable).
  FA.minimizeBrzozowski = function (m) {
    check(m, 'minimise');
    const trace = [];
    // Reversal here keeps several initial states (the old accepting states) instead of adding an
    // ε-start: a separate start state would sit in the first subset only and spoil minimality.
    const rev = (d) => FA.make({ states: d.states, alphabet: d.alphabet, start: d.start, accept: [d.start], trans: d.trans.map((e) => ({ from: e.to, sym: e.sym, to: e.from })) });
    const r1 = rev(m);
    trace.push({ kind: 'reverse', fa: r1, starts: m.accept, say: `Reverse the machine: arrows turn around, ${m.start} becomes the accepting state, and ${listStates(m.accept)} become the initial states.` });
    const d1 = FA.subset(r1, { dropEmpty: true, startSet: m.accept }).fa;
    trace.push({ kind: 'determinize', fa: d1, say: `Determinise it (reachable subsets only): ${plural(d1.states.length, 'state')} for the reversed language.` });
    const r2 = rev(d1);
    trace.push({ kind: 'reverse', fa: r2, starts: d1.accept, say: 'Reverse again: back to the original language, and now no state has two ways in on one symbol.' });
    const d2 = FA.canonical(FA.subset(r2, { startSet: d1.accept }).fa);
    trace.push({ kind: 'determinize', fa: d2, say: `Determinise once more: ${plural(d2.states.length, 'state')}, and this DFA is minimal.` });
    return { fa: d2, trace };
  };
  FA.minimize = (m, method = 'hopcroft') => ({ table: FA.minimizeTable, moore: FA.minimizeMoore, hopcroft: FA.minimizeHopcroft, brzozowski: FA.minimizeBrzozowski }[method])(m);

  // ---------------------------------------------------------------- isomorphism and equivalence

  // Two DFAs are isomorphic when a renaming of states turns one into the other. Only the reachable parts
  // are compared; a partial and a complete DFA for one language are not isomorphic (one has a dead state).
  FA.isomorphic = function (a, b) {
    if (!FA.isDFA(a) || !FA.isDFA(b)) return { iso: false, reason: 'Isomorphism is checked between DFAs.' };
    const A = FA.removeUnreachable(a).fa, B = FA.removeUnreachable(b).fa;
    if (A.states.length !== B.states.length) return { iso: false, reason: `They have ${A.states.length} and ${B.states.length} reachable states.` };
    const sa = [...A.alphabet].sort().join(), sb = [...B.alphabet].sort().join();
    if (sa !== sb) return { iso: false, reason: 'They read different alphabets.' };
    const dA = deltaMap(A), dB = deltaMap(B), accA = new Set(A.accept), accB = new Set(B.accept);
    const map = new Map([[A.start, B.start]]), used = new Set([B.start]), queue = [A.start];
    while (queue.length) {
      const p = queue.shift(), q = map.get(p);
      if (accA.has(p) !== accB.has(q)) return { iso: false, reason: `${p} and ${q} would match, but only one of them accepts.` };
      for (const s of A.alphabet) {
        const p2 = dA.get(p).get(s), q2 = dB.get(q).get(s);
        if ((p2 === undefined) !== (q2 === undefined)) return { iso: false, reason: `On ${s}, ${p2 === undefined ? p : q} has no move but ${p2 === undefined ? q : p} does.` };
        if (p2 === undefined) continue;
        if (map.has(p2)) { if (map.get(p2) !== q2) return { iso: false, reason: `On ${s}, ${p} goes to ${p2} (matched to ${map.get(p2)}) but ${q} goes to ${q2}.` }; }
        else { if (used.has(q2)) return { iso: false, reason: `${q2} would match two states.` }; map.set(p2, q2); used.add(q2); queue.push(p2); }
      }
    }
    return { iso: true, map: Object.fromEntries(map) };
  };

  // Breadth-first search over pairs of subsets, both machines running in step, symbols in alphabet order.
  // The first pair where exactly one accepts gives the shortest counterexample, and the shortlex-least
  // one of that length. mode 'equal' stops when acceptance differs, 'include' when A accepts and B not.
  function pairSearch(a, b, mode) {
    const sigma = uniq([...a.alphabet, ...b.alphabet]).sort();
    const A = lazyDet(FA.make({ ...a, alphabet: sigma })), B = lazyDet(FA.make({ ...b, alphabet: sigma }));
    const trace = [], seen = new Map();
    const k = (x, y) => x.key + '|' + y.key;
    const queue = [[A.start, B.start]];
    seen.set(k(A.start, B.start), null);
    const bad = (x, y) => (mode === 'include' ? x.acc && !y.acc : x.acc !== y.acc);
    while (queue.length) {
      const [x, y] = queue.shift();
      const kk = k(x, y);
      trace.push({ kind: 'visit', pair: [A.label(x), B.label(y)], say: `Visit (${A.label(x)}, ${B.label(y)}).` });
      if (bad(x, y)) {
        // walk back the parent links to spell the string
        const w = [];
        for (let c = kk; seen.get(c); c = seen.get(c).parent) w.push(seen.get(c).sym);
        const str = w.reverse().join('');
        trace.push({ kind: 'found', string: str, say: `${showW(str)} is accepted by ${x.acc ? 'A' : 'B'} but not by ${x.acc ? 'B' : 'A'}.` });
        return { found: true, string: str, inA: x.acc, inB: y.acc, trace, visited: seen.size };
      }
      for (const s of sigma) {
        const x2 = A.step(x, s), y2 = B.step(y, s), k2 = k(x2, y2);
        if (!seen.has(k2)) { seen.set(k2, { parent: kk, sym: s }); queue.push([x2, y2]); }
      }
    }
    trace.push({ kind: 'done', say: `All ${plural(seen.size, 'reachable pair')} agree.` });
    return { found: false, trace, visited: seen.size };
  }
  FA.equivalent = function (a, b) {
    check(a, 'equivalence (A)'); check(b, 'equivalence (B)');
    const r = pairSearch(a, b, 'equal');
    return r.found ? { equal: false, counterexample: r.string, acceptedBy: r.inA ? 'A' : 'B', trace: r.trace } : { equal: true, counterexample: null, trace: r.trace };
  };
  // L(a) ⊆ L(b)?
  FA.includes = function (a, b) {
    check(a, 'inclusion (A)'); check(b, 'inclusion (B)');
    const r = pairSearch(a, b, 'include');
    return r.found ? { included: false, counterexample: r.string, trace: r.trace } : { included: true, counterexample: null, trace: r.trace };
  };

  // ---------------------------------------------------------------- emptiness, finiteness, counting

  // Empty unless an accepting state is reachable; the witness is the shortlex-least accepted string.
  FA.isEmpty = function (m) {
    check(m, 'emptiness');
    const D = lazyDet(m), trace = [], seen = new Map([[D.start.key, null]]), queue = [D.start];
    trace.push({ kind: 'visit', states: D.names(D.start), say: `Start from ${D.label(D.start)}.` });
    while (queue.length) {
      const x = queue.shift();
      if (x.acc) {
        const w = [];
        for (let c = x.key; seen.get(c); c = seen.get(c).parent) w.push(seen.get(c).sym);
        const str = w.reverse().join('');
        trace.push({ kind: 'found', string: str, say: `An accepting state is reachable by ${showW(str)}: the language is not empty.` });
        return { empty: false, witness: str, trace };
      }
      for (const s of m.alphabet) {
        const y = D.step(x, s);
        if (!y.set.length || seen.has(y.key)) continue;
        seen.set(y.key, { parent: x.key, sym: s });
        queue.push(y);
        trace.push({ kind: 'visit', states: D.names(y), say: `Reach ${D.label(y)} on ${s}.` });
      }
    }
    trace.push({ kind: 'done', say: 'No accepting state can be reached: the language is empty.' });
    return { empty: true, witness: null, trace };
  };
  FA.isUniversal = (m) => { const r = FA.isEmpty(FA.complement(m).fa); return { universal: r.empty, counterexample: r.witness }; };

  // Infinite exactly when a cycle lies on some path from the start to acceptance. Restrict to useful
  // states (after removing ε-moves), then look for a cycle; the witness is x y z with y the loop.
  FA.isFinite = function (m) {
    check(m, 'finiteness');
    const trace = [];
    let M = m;
    if (FA.kind(m) === 'enfa') { M = FA.removeEps(m).fa; trace.push({ kind: 'remove-eps', say: 'Remove ε-moves first, so every cycle reads at least one symbol.' }); }
    const useful = FA.trim(M).fa;
    const live = useful.accept.length ? useful.states : [];
    trace.push({ kind: 'useful', states: live, say: live.length ? `Useful states (reachable and can still accept): ${listStates(live)}.` : 'No useful states: the language is empty, hence finite.' });
    if (!live.length) return { finite: true, count: 0, words: [], trace };
    const out = new Map(live.map((q) => [q, []]));
    for (const e of useful.trans) out.get(e.from).push(e);
    // depth-first search for a back edge
    const color = new Map(), stack = [];
    let cyc = null;
    const dfs = (q) => {
      color.set(q, 1);
      for (const e of out.get(q)) {
        if (cyc) return;
        if (color.get(e.to) === 1) { const i = stack.findIndex((x) => x.from === e.to); cyc = (i < 0 ? [] : stack.slice(i)).concat([e]); return; }
        if (!color.get(e.to)) { stack.push(e); dfs(e.to); stack.pop(); }
      }
      color.set(q, 2);
    };
    dfs(useful.start);
    if (!cyc) {
      // finite: count by enumerating (the longest word is shorter than the number of useful states)
      const words = FA.enumerate(m, { max: Infinity, maxLen: live.length });
      trace.push({ kind: 'done', say: `No cycle among the useful states: the language is finite, with ${plural(words.length, 'string')}.` });
      return { finite: true, count: words.length, words, trace };
    }
    const loopAt = cyc[0].from;
    const x = shortestPath(useful, useful.start, loopAt), y = cyc.map((e) => e.sym).join('');
    const z = shortestToAccept(useful, loopAt);
    trace.push({ kind: 'cycle', cycle: cyc, states: cyc.map((e) => e.from), say: `A cycle ${cyc.map((e) => e.from).join(' → ')} → ${loopAt} reading ${y} lies between the start and acceptance: the language is infinite.` });
    trace.push({ kind: 'pump', x, y, z, say: `${showW(x)}·(${y})ⁱ·${showW(z)} is accepted for every i.` });
    return { finite: false, cycle: cyc, x, y, z, trace };
  };
  function shortestPath(m, from, to) {
    const prev = new Map([[from, null]]), q = [from];
    const out = new Map(m.states.map((s) => [s, []]));
    for (const e of m.trans) out.get(e.from).push(e);
    while (q.length) {
      const s = q.shift();
      if (s === to) break;
      for (const a of m.alphabet) for (const e of out.get(s)) if (e.sym === a && !prev.has(e.to)) { prev.set(e.to, e); q.push(e.to); }
    }
    const w = [];
    for (let s = to; prev.get(s); s = prev.get(s).from) w.push(prev.get(s).sym);
    return w.reverse().join('');
  }
  function shortestToAccept(m, from) {
    const acc = new Set(m.accept), prev = new Map([[from, null]]), q = [from];
    const out = new Map(m.states.map((s) => [s, []]));
    for (const e of m.trans) out.get(e.from).push(e);
    let hit = null;
    while (q.length) {
      const s = q.shift();
      if (acc.has(s)) { hit = s; break; }
      for (const a of m.alphabet) for (const e of out.get(s)) if (e.sym === a && !prev.has(e.to)) { prev.set(e.to, e); q.push(e.to); }
    }
    const w = [];
    for (let s = hit; prev.get(s); s = prev.get(s).from) w.push(prev.get(s).sym);
    return w.reverse().join('');
  }

  // Number of accepted strings of each length 0..n (BigInt counts, also as Numbers for display):
  // a dynamic programme over the determinised machine.
  FA.countByLength = function (m, n) {
    check(m, 'count');
    const D = lazyDet(m);
    let cur = new Map([[D.start, 1n]]);
    const counts = [];
    for (let len = 0; len <= n; len++) {
      let c = 0n;
      for (const [nd, k] of cur) if (nd.acc) c += k;
      counts.push(c);
      if (len === n) break;
      const next = new Map();
      for (const [nd, k] of cur) for (const a of m.alphabet) { const y = D.step(nd, a); if (y.set.length) next.set(y, (next.get(y) || 0n) + k); }
      cur = next;
    }
    return { counts, numbers: counts.map(Number), count: counts[n], trace: counts.map((c, i) => ({ kind: 'count', length: i, count: Number(c), say: `${c} accepted string${c === 1n ? '' : 's'} of length ${i}.` })) };
  };
  FA.count = (m, n) => FA.countByLength(m, n).count;

  // Accepted strings in shortlex order: at most max strings, of length at most maxLen. Prefixes that can
  // no longer reach acceptance are dropped, so sparse languages are found quickly.
  FA.enumerate = function (m, opts = {}) {
    const max = opts.max === undefined ? 50 : opts.max, maxLen = opts.maxLen === undefined ? 12 : opts.maxLen;
    const D = lazyDet(m), sigma = m.alphabet.slice().sort();
    // live subsets: build the reachable determinised graph, then propagate "can accept" backwards
    const nodes = [D.start], seen = new Set([D.start.key]);
    for (let i = 0; i < nodes.length && nodes.length < 20000; i++) for (const a of sigma) { const y = D.step(nodes[i], a); if (!seen.has(y.key)) { seen.add(y.key); nodes.push(y); } }
    const live = new Set(nodes.filter((x) => x.acc).map((x) => x.key));
    if (nodes.length < 20000) {
      for (let changed = true; changed;) { changed = false; for (const x of nodes) if (!live.has(x.key) && sigma.some((a) => live.has(D.step(x, a).key))) { live.add(x.key); changed = true; } }
    } else nodes.forEach((x) => live.add(x.key)); // too big to analyse: do not prune
    const out = [];
    let level = live.has(D.start.key) ? [['', D.start]] : [];
    for (let len = 0; len <= maxLen && level.length && out.length < max; len++) {
      for (const [w, x] of level) { if (x.acc) { out.push(w); if (out.length >= max) break; } }
      if (len === maxLen) break;
      const next = [];
      for (const [w, x] of level) for (const a of sigma) { const y = D.step(x, a); if (live.has(y.key)) next.push([w + a, y]); }
      level = next;
      if (level.length > 2e6) break;
    }
    return out;
  };

  // ---------------------------------------------------------------- Myhill–Nerode

  // The Myhill–Nerode classes of L(m): one per state of the minimal complete DFA, each with its
  // shortlex-least representative and the original states it gathers, plus a shortest suffix telling
  // each pair of classes apart.
  FA.nerode = function (m) {
    const mn = FA.minimizeHopcroft(m);
    const d = mn.fa, del = deltaMap(d), acc = new Set(d.accept);
    // representatives: breadth-first from the start in alphabet order gives shortlex-least strings
    const rep = new Map([[d.start, '']]), q = [d.start], sigma = d.alphabet.slice().sort();
    while (q.length) { const s = q.shift(); for (const a of sigma) { const t = del.get(s).get(a); if (!rep.has(t)) { rep.set(t, rep.get(s) + a); q.push(t); } } }
    const blockOf = new Map();
    mn.blocks.forEach((b) => blockOf.set(b.length === 1 ? b[0] : setName(b), b));
    const classes = d.states.map((s) => ({ state: s, rep: rep.get(s), states: blockOf.get(s) || [s], accepting: acc.has(s) }));
    const trace = classes.map((c) => ({ kind: 'class', ...c, say: `[${showW(c.rep)}]: every string that leads to ${c.states.join(' or ')}${c.accepting ? ' (accepting)' : ''}.` }));
    // a shortest distinguishing suffix for each pair of classes
    const dist = {};
    for (let i = 0; i < d.states.length; i++) for (let j = i + 1; j < d.states.length; j++) {
      const z = suffixBetween(d, del, acc, sigma, d.states[i], d.states[j]);
      dist[d.states[i] + '|' + d.states[j]] = z;
      trace.push({ kind: 'distinguish', pair: [classes[i].rep, classes[j].rep], suffix: z, say: `${showW(classes[i].rep)} and ${showW(classes[j].rep)} differ: append ${showW(z)} and exactly one is accepted.` });
    }
    return { classes, distinguish: dist, fa: d, trace };
  };
  function suffixBetween(d, del, acc, sigma, p, q) {
    const k = (x, y) => x + '\u0000' + y, prev = new Map([[k(p, q), null]]), queue = [[p, q]];
    while (queue.length) {
      const [x, y] = queue.shift();
      if (acc.has(x) !== acc.has(y)) {
        const w = [];
        for (let c = k(x, y); prev.get(c); c = prev.get(c).parent) w.push(prev.get(c).sym);
        return w.reverse().join('');
      }
      for (const a of sigma) { const x2 = del.get(x).get(a), y2 = del.get(y).get(a); if (!prev.has(k(x2, y2))) { prev.set(k(x2, y2), { parent: k(x, y), sym: a }); queue.push([x2, y2]); } }
    }
    return null;
  }

  // For the distinguisher game with any language given as a membership test: the shortest suffix z
  // (shortlex, length ≤ maxLen) with member(x z) ≠ member(y z), or null if none is found that short.
  FA.distinguishing = function (member, alphabet, x, y, maxLen = 8) {
    let found = null;
    T.Found.eachString(alphabet, maxLen, (z) => { if (!!member(x + z) !== !!member(y + z)) { found = z; return false; } return true; });
    return found;
  };
  // Group prefixes into apparent classes: two prefixes stay together while no suffix up to suffixLen
  // separates them. For a non-regular language the number of groups keeps growing with the bound.
  FA.nerodeExplore = function (member, alphabet, prefixes, suffixLen = 6) {
    const suffixes = T.Found.sigmaStar(alphabet, suffixLen);
    const groups = new Map(), trace = [];
    for (const x of prefixes) {
      const sig = suffixes.map((z) => (member(x + z) ? '1' : '0')).join('');
      if (!groups.has(sig)) { groups.set(sig, []); trace.push({ kind: 'class', rep: x, say: `${showW(x)} starts a new class: no earlier prefix behaves like it.` }); }
      else trace.push({ kind: 'join', prefix: x, rep: groups.get(sig)[0], say: `${showW(x)} behaves like ${showW(groups.get(sig)[0])} on every suffix up to length ${suffixLen}.` });
      groups.get(sig).push(x);
    }
    return { classes: [...groups.values()], trace };
  };

  // ---------------------------------------------------------------- pumping decomposition

  // For a DFA and an accepted string s with |s| ≥ number of states: s = x y z where y is read on the
  // first loop of the run (the first repeated state), so x yⁱ z is accepted for all i ≥ 0.
  FA.pumpSplit = function (m, s) {
    if (!FA.isDFA(m)) throw new Error('pumpSplit needs a DFA.');
    const del = deltaMap(m), w = chars(s), seen = new Map([[m.start, 0]]), trace = [];
    let q = m.start;
    trace.push({ kind: 'visit', pos: 0, state: q, say: `Before reading anything the DFA is in ${q}.` });
    for (let i = 0; i < w.length; i++) {
      q = del.get(q).get(w[i]);
      if (q === undefined) return { ok: false, reason: `The run dies on ${w[i]} at position ${i + 1}: ${showW(s)} is not accepted.`, trace };
      if (seen.has(q)) {
        const a = seen.get(q), b = i + 1;
        const x = w.slice(0, a).join(''), y = w.slice(a, b).join(''), z = w.slice(b).join('');
        trace.push({ kind: 'repeat', pos: b, state: q, first: a, say: `After ${b} symbols the DFA is back in ${q}, first seen after ${a}: the pigeonhole principle at work.` });
        trace.push({ kind: 'split', x, y, z, say: `x = ${showW(x)}, y = ${y}, z = ${showW(z)}: reading y loops from ${q} back to ${q}, so it can be repeated or skipped.` });
        return { ok: true, x, y, z, state: q, positions: [a, b], trace };
      }
      seen.set(q, i + 1);
      trace.push({ kind: 'visit', pos: i + 1, state: q, say: `After ${w.slice(0, i + 1).join('')} the DFA is in ${q}.` });
    }
    return { ok: false, reason: `No state repeats: ${showW(s)} is shorter than the number of states.`, trace };
  };

  // ---------------------------------------------------------------- random machines (presets, tests)

  FA.randomDFA = function (rnd, { n = 4, alphabet = ['a', 'b'], accept = 0.4, partial = 0 } = {}) {
    const states = Array.from({ length: n }, (_, i) => 'q' + i), trans = [];
    for (const q of states) for (const a of alphabet) if (rnd() >= partial) trans.push({ from: q, sym: a, to: states[Math.floor(rnd() * n)] });
    return FA.make({ states, alphabet, start: 'q0', accept: states.filter(() => rnd() < accept), trans });
  };
  FA.randomNFA = function (rnd, { n = 4, alphabet = ['a', 'b'], accept = 0.3, density = 0.3, eps = 0 } = {}) {
    const states = Array.from({ length: n }, (_, i) => 'q' + i), trans = [];
    for (const q of states) for (const r of states) {
      for (const a of alphabet) if (rnd() < density) trans.push({ from: q, sym: a, to: r });
      if (q !== r && rnd() < eps) trans.push({ from: q, sym: EPS, to: r });
    }
    return FA.make({ states, alphabet, start: 'q0', accept: states.filter(() => rnd() < accept), trans });
  };
})();
