// Pushdown automata: the text format, simulation as a tree of configurations, acceptance by final state
// and by empty stack (and conversion between them), CFG → PDA (top-down and bottom-up), PDA → CFG (the
// triple construction), the determinism check and the product of a PDA with a DFA.
//
// THE OBJECT
//   { states, input, stack, start, startStack, accept, acceptBy: 'final' | 'empty',
//     transitions: [{ id, from, read, pop, to, push }], meta }
// read is one input symbol or '' for ε (the move reads nothing). pop is one stack symbol, which must be on
// top and is removed, or '' for convenience: the move ignores the stack and removes nothing (it works even
// on an empty stack). push is an array written top first, so push ['A', 'Z'] leaves A on top; [] pushes
// nothing. A configuration is (state, remaining input, stack) with the stack written top first.
// meta (optional, set by the CFG constructions) lets the simulator prune hopeless configurations:
//   { minLen: { symbol: shortest yield }, prune: 'remaining' | 'consumed' }. 'remaining' (top-down) drops a
// configuration whose stack must still produce more terminals than the input has left; 'consumed'
// (bottom-up) drops one whose stack stands for more terminals than have been read.
//
// THE TEXT FORMAT
//   # comment line (or // to the end of a line)
//   start q0                    the start state (default: the first transition's state)
//   stack-start Z               the symbol on the stack at the beginning (also: bottom Z)
//   accept q2 q3                accepting states (also: final ...)
//   accept-by empty             or final (the default)
//   states q0 q1 q2             optional; input a b; stack A Z   (optional declarations)
//   q0, a, Z -> q0, A Z         from, read, pop -> to, push    (ε, eps or nothing for the empty string)
//   q1, b, A -> q1, ε
// A push is cut into symbols like a grammar's right side: spaces separate symbols, and inside a word the
// known stack symbols (declared, popped somewhere, or the start symbol) are read whole, longest first;
// any other character is a symbol on its own, so "AZ" is A, Z.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const EPS = 'ε';
  const isEps = (s) => s === '' || s === EPS || s === 'eps' || s === 'epsilon';
  const showS = (s) => (s === '' ? EPS : s);
  const showStack = (st) => (st.length ? (st.every((x) => [...x].length === 1) ? st.join('') : st.join(' ')) : EPS);
  const showW = (w) => (w.length ? (w.every((x) => [...x].length === 1) ? w.join('') : w.join(' ')) : EPS);
  const showT = (t) => '(' + t.from + ', ' + showS(t.read) + ', ' + showS(t.pop) + ') → (' + t.to + ', ' + showStack(t.push) + ')';
  const uniq = (a) => [...new Set(a)];

  // ---------- building ----------
  // make(spec) fills in alphabets and state lists from the transitions and numbers the transitions.
  function make(spec) {
    const tr = (spec.transitions || []).map((t, id) => ({ id, from: t.from, read: t.read || '', pop: t.pop || '', to: t.to, push: (t.push || []).slice() }));
    const start = spec.start != null ? spec.start : tr.length ? tr[0].from : 'q0';
    const states = uniq([start, ...(spec.states || []), ...tr.flatMap((t) => [t.from, t.to]), ...(spec.accept || [])]);
    const input = uniq([...(spec.input || []), ...tr.map((t) => t.read).filter((x) => x !== '')]);
    const startStack = spec.startStack != null ? spec.startStack : 'Z';
    const stack = uniq([...(startStack !== '' ? [startStack] : []), ...(spec.stack || []), ...tr.flatMap((t) => [t.pop, ...t.push]).filter((x) => x !== '')]);
    return { states, input, stack, start, startStack, accept: uniq(spec.accept || []), acceptBy: spec.acceptBy === 'empty' ? 'empty' : 'final',
      transitions: tr, meta: spec.meta || null };
  }
  function fresh(base, used) {
    used = used instanceof Set ? used : new Set(used);
    if (!used.has(base)) return base;
    for (let i = 0; ; i++) { const c = base + (i ? i : "'"); if (!used.has(c)) return c; }
  }

  // ---------- text ----------
  function stripComment(line) { if (/^\s*#/.test(line)) return ''; const i = line.indexOf('//'); return i >= 0 ? line.slice(0, i) : line; }
  function cutPush(text, known) {
    const out = [];
    for (const w of text.trim().split(/\s+/)) {
      if (!w || isEps(w)) continue;
      let i = 0;
      while (i < w.length) {
        const hit = known.find((k) => w.startsWith(k, i));
        if (hit) { out.push(hit); i += hit.length; continue; }
        const cp = String.fromCodePoint(w.codePointAt(i));
        if (cp !== EPS) out.push(cp);
        i += cp.length;
      }
    }
    return out;
  }
  function parse(text) {
    const spec = { transitions: [], states: [], input: [], stack: [], accept: [] };
    const raw = [];
    String(text).split(/\r?\n/).forEach((l0, k) => {
      const ln = k + 1, line = stripComment(l0).trim();
      if (!line) return;
      const arrow = line.indexOf('->') >= 0 ? line.indexOf('->') : line.indexOf('→');
      if (arrow < 0) {
        const [d, ...args] = line.split(/\s+/);
        const key = d.toLowerCase().replace(/:$/, '');
        if (key === 'start') spec.start = args[0];
        else if (key === 'stack-start' || key === 'start-stack' || key === 'bottom') spec.startStack = args[0];
        else if (key === 'accept' || key === 'final') spec.accept.push(...args);
        else if (key === 'accept-by') { if (!/^(empty|final)$/.test(args[0] || '')) throw err('accept-by takes empty or final', ln); spec.acceptBy = args[0]; }
        else if (key === 'states') spec.states.push(...args);
        else if (key === 'input') spec.input.push(...args);
        else if (key === 'stack') spec.stack.push(...args);
        else throw err('expected a transition like  q0, a, Z -> q1, A Z', ln);
        return;
      }
      const L = line.slice(0, arrow).split(','), R = line.slice(arrow + (line[arrow] === '→' ? 1 : 2)).split(',');
      if (L.length !== 3 || R.length !== 2) throw err('a transition is  state, read, pop -> state, push', ln);
      const [from, read, pop] = L.map((s) => s.trim()), to = R[0].trim();
      if (!from || !to) throw err('missing state name', ln);
      raw.push({ from, read: isEps(read) ? '' : read, pop: isEps(pop) ? '' : pop, to, pushText: R[1], line: ln });
    });
    const known = uniq([...spec.stack, ...(spec.startStack ? [spec.startStack] : []), ...raw.map((r) => r.pop).filter(Boolean)]).sort((a, b) => b.length - a.length);
    for (const r of raw) spec.transitions.push({ from: r.from, read: r.read, pop: r.pop, to: r.to, push: cutPush(r.pushText, known) });
    if (!spec.transitions.length) throw err('the automaton has no transitions');
    return make(spec);
  }
  function err(msg, line) { const e = new Error(line ? 'Line ' + line + ': ' + msg : msg); e.line = line || 0; return e; }
  function tryParse(text) { try { return { pda: parse(text), error: null }; } catch (e) { return { pda: null, error: e.message, line: e.line || 0 }; } }
  function toString(P) {
    const out = ['start ' + P.start, 'stack-start ' + P.startStack];
    if (P.acceptBy === 'empty') out.push('accept-by empty');
    if (P.accept.length) out.push('accept ' + P.accept.join(' '));
    out.push('states ' + P.states.join(' '));
    if (P.input.length) out.push('input ' + P.input.join(' '));
    out.push('stack ' + P.stack.join(' '));
    for (const t of P.transitions) out.push(t.from + ', ' + showS(t.read) + ', ' + showS(t.pop) + ' -> ' + t.to + ', ' + (t.push.length ? t.push.join(' ') : EPS));
    return out.join('\n');
  }
  // Read a word as input symbols (longest symbol first, whitespace ignored).
  function word(P, w) {
    if (Array.isArray(w)) return w.slice();
    const syms = P.input.slice().sort((a, b) => b.length - a.length), out = [];
    let i = 0; w = String(w);
    while (i < w.length) {
      if (/\s/.test(w[i])) { i++; continue; }
      const hit = syms.find((s) => w.startsWith(s, i));
      if (hit) { out.push(hit); i += hit.length; continue; }
      const cp = String.fromCodePoint(w.codePointAt(i)); if (cp !== EPS) out.push(cp); i += cp.length;
    }
    return out;
  }

  // ---------- simulation ----------
  function moves(P, c, w) {
    const out = [];
    for (const t of P.transitions) {
      if (t.from !== c.state) continue;
      if (t.read !== '' && w[c.pos] !== t.read) continue;
      if (t.pop !== '' && c.stack[0] !== t.pop) continue;
      out.push(t);
    }
    return out;
  }
  const accepting = (P, c, n) => c.pos === n && (P.acceptBy === 'empty' ? c.stack.length === 0 : P.accept.includes(c.state));
  // Breadth-first exploration one layer at a time: every configuration in the frontier makes all its
  // moves at once. Repeated configurations are not explored again (the search would only loop), and
  // bounds on configurations and stack height stop ε-moves that grow the stack forever.
  function stepper(P, w0, opts) {
    opts = Object.assign({ maxConfigs: 20000, maxStack: null, traceLimit: 600, keep: true }, opts || {});
    const w = word(P, w0), n = w.length;
    const meta = P.meta, minLen = meta && meta.minLen;
    // a proven bound (meta.stackBound = [a, b]: height a·(n+1) + b) loses no accepting run, so cutting
    // there does not make the answer uncertain
    const proven = opts.maxStack == null && meta && meta.stackBound;
    const maxStack = opts.maxStack != null ? opts.maxStack : proven ? meta.stackBound[0] * (n + 1) + meta.stackBound[1] : Math.max(12, 3 * n + 8);
    const need = (st) => { let s = 0; for (const x of st) { const v = minLen[x]; s += v === undefined ? 0 : v; } return s; };
    const configs = [], seen = new Set(), trace = [];
    const note = (st) => { if (trace.length < opts.traceLimit) trace.push(st); };
    let complete = true, count = 0, acceptIds = [];
    const key = (c) => c.state + '\u0001' + c.pos + '\u0001' + c.stack.join('\u0002');
    const add = (c) => { c.id = count++; if (opts.keep) configs.push(c); return c; };
    const root = add({ state: P.start, pos: 0, stack: P.startStack !== '' ? [P.startStack] : [], parent: null, via: null, depth: 0 });
    seen.add(key(root));
    note({ kind: 'start', config: root, say: 'Start in ' + P.start + ' with input ' + showW(w) + ' and stack ' + showStack(root.stack) + '.' });
    let frontier = [root];
    if (accepting(P, root, n)) { acceptIds.push(root.id); root.accepting = true; }
    const self = {
      input: w, configs, trace, get frontier() { return frontier; }, get complete() { return complete; },
      get accepted() { return acceptIds.length > 0; }, get acceptIds() { return acceptIds; }, get done() { return frontier.length === 0; },
      step() {
        const next = [], created = [];
        for (const c of frontier) {
          const ms = moves(P, c, w);
          if (!ms.length && !c.accepting) { c.dead = true; note({ kind: 'dead', config: c, say: 'No move from (' + c.state + ', ' + showW(w.slice(c.pos)) + ', ' + showStack(c.stack) + '): this branch dies.' }); }
          for (const t of ms) {
            const stack = t.push.concat(t.pop !== '' ? c.stack.slice(1) : c.stack);
            const d = { state: t.to, pos: c.pos + (t.read !== '' ? 1 : 0), stack, parent: c.id, via: t.id, depth: c.depth + 1 };
            const k = key(d);
            if (seen.has(k)) { note({ kind: 'repeat', from: c.id, transition: t.id, say: 'Move ' + showT(t) + ' reaches a configuration already seen; it is not explored again.' }); continue; }
            if (stack.length > maxStack) { if (!proven) complete = false; note({ kind: 'bound', from: c.id, transition: t.id, say: 'The stack would grow past ' + maxStack + ' symbols; this branch is cut off.' }); continue; }
            if (minLen && (meta.prune === 'remaining' ? need(stack) > n - d.pos : need(stack) > d.pos)) {
              note({ kind: 'prune', from: c.id, transition: t.id, say: meta.prune === 'remaining' ? 'The stack ' + showStack(stack) + ' needs more input than is left; drop it.' : 'The stack ' + showStack(stack) + ' stands for more input than has been read; drop it.' });
              continue;
            }
            if (count >= opts.maxConfigs) { complete = false; note({ kind: 'bound', from: c.id, say: 'The search reached its limit of ' + opts.maxConfigs + ' configurations.' }); frontier = []; return { frontier, created }; }
            seen.add(k); add(d); created.push(d); next.push(d);
            note({ kind: 'move', config: d, from: c.id, transition: t.id, say: showT(t) + ': (' + c.state + ', ' + showW(w.slice(c.pos)) + ', ' + showStack(c.stack) + ') ⊢ (' + d.state + ', ' + showW(w.slice(d.pos)) + ', ' + showStack(d.stack) + ').' });
            if (accepting(P, d, n)) {
              d.accepting = true; acceptIds.push(d.id);
              note({ kind: 'accept', config: d, say: 'All input read and ' + (P.acceptBy === 'empty' ? 'the stack is empty' : d.state + ' is accepting') + ': accept.' });
            }
          }
        }
        frontier = next;
        return { frontier, created };
      },
    };
    return self;
  }
  // Path of configurations from the start to config id (needs keep: true).
  function pathTo(run, id) { const out = []; let c = run.configs[id]; while (c) { out.unshift(c); c = c.parent === null ? null : run.configs[c.parent]; } return out; }
  function simulate(P, w, opts) {
    opts = Object.assign({ stopAtAccept: false }, opts || {});
    const s = stepper(P, w, opts);
    while (!s.done && !(opts.stopAtAccept && s.accepted)) s.step();
    const paths = opts.keep === false ? [] : s.acceptIds.map((id) => pathTo(s, id));
    s.trace.push({ kind: 'verdict', accepted: s.accepted, complete: s.complete,
      say: s.accepted ? 'Some branch accepts, so the PDA accepts ' + showW(s.input) + '.' : s.complete ? 'Every branch died, so the PDA rejects ' + showW(s.input) + '.' : 'No branch accepted within the search bounds (the answer may need a larger bound).' });
    return { accepted: s.accepted, complete: s.complete || s.accepted, configs: s.configs, accepting: s.acceptIds, paths, input: s.input, trace: s.trace };
  }
  function accepts(P, w, opts) { return simulate(P, w, Object.assign({ stopAtAccept: true, keep: false, traceLimit: 0 }, opts || {})); }

  // ---------- final state ↔ empty stack ----------
  // Final state → empty stack: a new bottom marker stops the old moves from emptying the stack by
  // accident; from any accepting state a drain state pops everything.
  function carryMeta(P, marker) {
    if (!P.meta) return null;
    const m = Object.assign({}, P.meta);
    if (m.minLen) { m.minLen = Object.assign({}, m.minLen); m.minLen[marker] = 0; }
    if (m.stackBound) m.stackBound = [m.stackBound[0], m.stackBound[1] + 1];
    return m;
  }
  function toEmpty(P) {
    const trace = [];
    if (P.acceptBy === 'empty') return { pda: P, trace: [{ kind: 'same', say: 'It already accepts by empty stack.' }] };
    const used = new Set([...P.states]), syms = new Set([...P.stack, ...P.input]);
    const s0 = fresh('s0', used); used.add(s0);
    const drain = fresh('drain', used);
    const X0 = fresh('⊥', syms);
    const tr = [{ from: s0, read: '', pop: X0, to: P.start, push: P.startStack !== '' ? [P.startStack, X0] : [X0] }];
    trace.push({ kind: 'bottom', marker: X0, state: s0, say: 'New start state ' + s0 + ' puts ' + showStack(tr[0].push) + ' on the stack, so the bottom marker ' + X0 + ' sits under everything the old machine does.' });
    tr.push(...P.transitions.map((t) => ({ from: t.from, read: t.read, pop: t.pop, to: t.to, push: t.push })));
    trace.push({ kind: 'copy', count: P.transitions.length, say: 'Keep all ' + P.transitions.length + ' old moves.' });
    const all = [...P.stack, X0];
    for (const q of P.accept) for (const Y of all) tr.push({ from: q, read: '', pop: Y, to: drain, push: [Y] });
    for (const Y of all) tr.push({ from: drain, read: '', pop: Y, to: drain, push: [] });
    trace.push({ kind: 'drain', state: drain, say: 'From each accepting state (' + (P.accept.join(', ') || 'none') + ') an ε-move enters ' + drain + ', which pops every symbol including ' + X0 + '; the stack empties exactly when the old machine would accept.' });
    const Q = make({ states: [s0, ...P.states, drain], input: P.input, stack: all, start: s0, startStack: X0, accept: [], acceptBy: 'empty', transitions: tr, meta: carryMeta(P, X0) });
    return { pda: Q, trace };
  }
  // Empty stack → final state: a bottom marker shows when the old stack is empty; seeing it, move to a
  // new accepting state.
  function toFinal(P) {
    const trace = [];
    if (P.acceptBy === 'final') return { pda: P, trace: [{ kind: 'same', say: 'It already accepts by final state.' }] };
    const used = new Set(P.states), syms = new Set([...P.stack, ...P.input]);
    const s0 = fresh('s0', used); used.add(s0);
    const f = fresh('f', used);
    const X0 = fresh('⊥', syms);
    const tr = [{ from: s0, read: '', pop: X0, to: P.start, push: P.startStack !== '' ? [P.startStack, X0] : [X0] }];
    trace.push({ kind: 'bottom', marker: X0, state: s0, say: 'New start state ' + s0 + ' puts ' + showStack(tr[0].push) + ' on the stack; ' + X0 + ' is uncovered exactly when the old stack is empty.' });
    tr.push(...P.transitions.map((t) => ({ from: t.from, read: t.read, pop: t.pop, to: t.to, push: t.push })));
    trace.push({ kind: 'copy', count: P.transitions.length, say: 'Keep all ' + P.transitions.length + ' old moves.' });
    for (const q of P.states) tr.push({ from: q, read: '', pop: X0, to: f, push: [] });
    trace.push({ kind: 'finish', state: f, say: 'From every old state, seeing ' + X0 + ' on top means the old stack is empty: an ε-move goes to the new accepting state ' + f + '.' });
    const Q = make({ states: [s0, ...P.states, f], input: P.input, stack: [...P.stack, X0], start: s0, startStack: X0, accept: [f], acceptBy: 'final', transitions: tr, meta: carryMeta(P, X0) });
    return { pda: Q, trace };
  }

  // ---------- CFG → PDA ----------
  function minLenMeta(G) {
    const m = T.grammar.minLengths(G), o = {};
    for (const t of G.terminals) o[t] = 1;
    for (const A of G.nonterminals) o[A] = m.get(A);
    return o;
  }
  // Top-down: one state; the stack holds the part of a leftmost sentential form still to be matched.
  // Expand a nonterminal on top by one of its rules, or match a terminal on top against the input.
  function fromCFGTopDown(G) {
    const g = T.grammar, trace = [], tr = [];
    for (const p of G.productions) {
      tr.push({ from: 'q', read: '', pop: p.A, to: 'q', push: p.rhs.slice() });
      trace.push({ kind: 'expand', prod: p.id, transition: tr.length - 1, say: 'Rule ' + g.showProd(G, p) + ' becomes the expand move (q, ε, ' + p.A + ') → (q, ' + showStack(p.rhs) + ').' });
    }
    for (const a of G.terminals) {
      tr.push({ from: 'q', read: a, pop: a, to: 'q', push: [] });
      trace.push({ kind: 'match', terminal: a, transition: tr.length - 1, say: 'Terminal ' + a + ' gets the match move (q, ' + a + ', ' + a + ') → (q, ε): read it and pop it.' });
    }
    // Some word of length n, if accepted at all, is accepted with the stack never above
    // (n+1)·|N|·(longest right side − 1) + 1: in a smallest parse tree no path repeats a nonterminal over the
    // same stretch of input, so a path has at most (n+1)·|N| nonterminals, and the stack holds the
    // waiting right siblings along that path.
    const maxRhs = Math.max(1, ...G.productions.map((p) => p.rhs.length));
    trace.push({ kind: 'done', say: 'The stack starts as ' + G.start + ' and the PDA accepts by empty stack: an empty stack after all the input means a leftmost derivation matched it.' });
    const P = make({ states: ['q'], input: G.terminals, stack: [...G.nonterminals, ...G.terminals], start: 'q', startStack: G.start, accept: [], acceptBy: 'empty',
      transitions: tr, meta: { minLen: minLenMeta(G), prune: 'remaining', stackBound: [G.nonterminals.length * Math.max(1, maxRhs - 1), 1] } });
    return { pda: P, trace };
  }
  // Bottom-up: shift input symbols onto the stack, and reduce when the top of the stack spells a right
  // side backwards (one pop per symbol, through a chain of helper states). Reaching the start symbol
  // over the bottom marker accepts. This is a nondeterministic shift-reduce parser.
  function fromCFGBottomUp(G) {
    const g = T.grammar, trace = [], tr = [];
    const syms = new Set([...G.nonterminals, ...G.terminals]);
    const bot = fresh('⊥', syms);
    for (const a of G.terminals) {
      tr.push({ from: 'q', read: a, pop: '', to: 'q', push: [a] });
      trace.push({ kind: 'shift', terminal: a, transition: tr.length - 1, say: 'Shift: (q, ' + a + ', ε) → (q, ' + a + ') pushes the input symbol ' + a + '.' });
    }
    const states = ['q'];
    for (const p of G.productions) {
      const k = p.rhs.length;
      if (k === 0) { tr.push({ from: 'q', read: '', pop: '', to: 'q', push: [p.A] }); }
      else {
        let cur = 'q';
        for (let j = 0; j < k; j++) {
          const last = j === k - 1, nx = last ? 'q' : 'r' + p.id + '_' + (j + 1);
          if (!last) states.push(nx);
          tr.push({ from: cur, read: '', pop: p.rhs[k - 1 - j], to: nx, push: last ? [p.A] : [] });
          cur = nx;
        }
      }
      trace.push({ kind: 'reduce', prod: p.id, say: 'Reduce by ' + g.showProd(G, p) + ': ' + (k ? 'pop ' + showStack(p.rhs.slice().reverse()) + ' (top first, ' + k + ' move' + (k > 1 ? 's through helper states' : '') + ') then push ' + p.A : 'push ' + p.A + ' without popping (an ε-rule)') + '.' });
    }
    tr.push({ from: 'q', read: '', pop: G.start, to: 'acc', push: [] });
    tr.push({ from: 'acc', read: '', pop: bot, to: 'f', push: [] });
    trace.push({ kind: 'finish', say: 'When ' + G.start + ' sits alone on the bottom marker ' + bot + ', pop both and enter the accepting state f.' });
    const minLen = minLenMeta(G); minLen[bot] = 0;
    const P = make({ states: [...states, 'acc', 'f'], input: G.terminals, stack: [bot, ...G.nonterminals, ...G.terminals], start: 'q', startStack: bot, accept: ['f'],
      acceptBy: 'final', transitions: tr, meta: { minLen, prune: 'consumed' } });
    return { pda: P, trace };
  }

  // ---------- PDA → CFG ----------
  // Private cleanup used only if cfg-transform.js is not loaded: drop non-generating, then unreachable.
  function cleanup(G) {
    if (T.cfg && T.cfg.removeUseless) return T.cfg.removeUseless(G);
    const g = T.grammar, gen = g.generatingSet(G);
    let ps = G.productions.filter((p) => gen.has(p.A) && p.rhs.every((s) => !g.isN(G, s) || gen.has(s)));
    let H = g.make(G.start, ps, { nonterminals: G.nonterminals.filter((A) => gen.has(A) || A === G.start), terminals: G.terminals, tokens: G.terminals });
    const reach = g.reachableSet(H);
    ps = H.productions.filter((p) => reach.has(p.A));
    H = g.make(G.start, ps, { nonterminals: H.nonterminals.filter((A) => reach.has(A)), terminals: G.terminals, tokens: G.terminals });
    return { grammar: H, trace: [{ kind: 'cleanup', say: 'Removed nonterminals that generate nothing, then those the start cannot reach.' }] };
  }
  // A nonterminal [p,X,q] generates exactly the inputs that take the PDA from p to q while removing X
  // from the stack (and leaving what was under it untouched).
  function toCFG(P) {
    const trace = [];
    let Q = P;
    if (P.acceptBy !== 'empty') {
      const r = toEmpty(P); Q = r.pda;
      trace.push({ kind: 'convert', pda: Q, say: 'First make the PDA accept by empty stack, since the construction tracks how symbols are popped.' }, ...r.trace);
    }
    // moves that ignore the stack become one move per possible top symbol, so every move pops exactly one
    const norm = [];
    let widened = 0;
    for (const t of Q.transitions) {
      if (t.pop !== '') { norm.push(t); continue; }
      widened++;
      for (const Y of Q.stack) norm.push({ from: t.from, read: t.read, pop: Y, to: t.to, push: t.push.concat([Y]) });
    }
    if (widened) {
      // a move that ignores the stack can also fire on an empty stack, which the triples cannot express;
      // after the bottom marker of toEmpty this cannot happen before acceptance
      trace.push({ kind: 'normalize', count: widened, say: widened + ' move(s) that ignore the stack become one move per top symbol Y, popping Y and pushing it back.' });
    }
    const N = (p, X, q) => '[' + p + ',' + X + ',' + q + ']';
    const S = fresh('S', new Set([...Q.input]));
    const prods = [];
    for (const q of Q.states) prods.push([S, [N(Q.start, Q.startStack, q)]]);
    trace.push({ kind: 'start-rules', say: 'Start rules ' + S + ' → ' + N(Q.start, Q.startStack, 'q') + ' for every state q: the whole input must remove the start symbol ' + Q.startStack + '.' });
    for (const t of norm) {
      const k = t.push.length, a = t.read !== '' ? [t.read] : [];
      const before = prods.length;
      if (k === 0) prods.push([N(t.from, t.pop, t.to), a]);
      else {
        // choose the intermediate states q1..qk in every way
        const idx = new Array(k).fill(0), n = Q.states.length;
        for (;;) {
          const qs = idx.map((i) => Q.states[i]);
          const rhs = a.slice();
          let prev = t.to;
          for (let j = 0; j < k; j++) { rhs.push(N(prev, t.push[j], qs[j])); prev = qs[j]; }
          prods.push([N(t.from, t.pop, qs[k - 1]), rhs]);
          let j = k - 1; while (j >= 0 && ++idx[j] === n) idx[j--] = 0;
          if (j < 0) break;
        }
      }
      trace.push({ kind: 'transition', transition: t, rules: prods.slice(before).map((r) => r[0] + ' → ' + (r[1].length ? r[1].join(' ') : EPS)),
        say: showT(t) + (k === 0 ? ' pops ' + t.pop + ' outright: ' + N(t.from, t.pop, t.to) + ' → ' + showS(t.read) + '.'
          : ' replaces ' + t.pop + ' by ' + k + ' symbol(s), each popped later between states guessed in every way: ' + (prods.length - before) + ' rule(s).') });
    }
        // every triple is a nonterminal, including those that never got a rule (they generate nothing)
    const triples = uniq([S, ...prods.flatMap((r) => [r[0], ...r[1].filter((x) => !Q.input.includes(x))])]);
    const raw = T.grammar.make(S, prods, { nonterminals: triples, terminals: Q.input, tokens: Q.input });
    const c = cleanup(raw);
    trace.push({ kind: 'cleanup', before: raw.productions.length, after: c.grammar.productions.length,
      say: 'The construction made ' + raw.productions.length + ' rules; removing useless symbols leaves ' + c.grammar.productions.length + '.' }, ...(c.trace || []).map((s) => Object.assign({ sub: 'cleanup' }, s)));
    return { grammar: c.grammar, raw, pda: Q, trace };
  }

  // ---------- determinism ----------
  // Deterministic when no two moves can ever apply to the same configuration: from the same state, their
  // reads overlap (equal, or one reads ε) and their pops overlap (equal, or one ignores the stack).
  function deterministic(P) {
    const conflicts = [], trace = [];
    const tr = P.transitions;
    for (let i = 0; i < tr.length; i++) for (let j = i + 1; j < tr.length; j++) {
      const a = tr[i], b = tr[j];
      if (a.from !== b.from) continue;
      const readClash = a.read === b.read || a.read === '' || b.read === '';
      const popClash = a.pop === b.pop || a.pop === '' || b.pop === '';
      if (!readClash || !popClash) continue;
      const why = (a.read === b.read ? (a.read === '' ? 'both read ε' : 'both read ' + a.read) : 'one reads ε while the other reads ' + (a.read || b.read)) + ' and ' +
        (a.pop === b.pop ? (a.pop === '' ? 'both ignore the stack' : 'both pop ' + a.pop) : 'one ignores the stack while the other pops ' + (a.pop || b.pop));
      conflicts.push({ a: a.id, b: b.id, why });
      trace.push({ kind: 'conflict', a: a.id, b: b.id, say: 'In state ' + a.from + ', ' + showT(a) + ' and ' + showT(b) + ' can both apply: ' + why + '.' });
    }
    const ok = conflicts.length === 0;
    trace.push({ kind: 'verdict', deterministic: ok, say: ok ? 'No two moves ever compete, so the PDA is deterministic.' : conflicts.length + ' competing pair(s), so the PDA is nondeterministic.' });
    return { deterministic: ok, conflicts, trace };
  }

  // ---------- product with a DFA ----------
  // DFA as a plain object { states, alphabet, start, accept: [..], delta: { state: { sym: state } } };
  // a missing entry means the DFA rejects (an implicit dead state). The product runs both machines side
  // by side: the PDA's ε-moves leave the DFA where it is. It accepts by final state, so an empty-stack
  // PDA is converted first.
  // Also takes a transition-list machine { states, alphabet, start, accept, trans: [{ from, sym, to }] }
  // as long as it is deterministic (no ε, at most one move per state and symbol).
  function asDelta(D) {
    if (D.delta) return D;
    const delta = {};
    for (const q of D.states) delta[q] = {};
    for (const t of D.trans || []) {
      if (t.sym === '') throw new Error('the finite automaton has ε-moves; make it deterministic first');
      if (delta[t.from][t.sym] != null && delta[t.from][t.sym] !== t.to) throw new Error('the finite automaton is not deterministic on ' + t.from + ', ' + t.sym);
      delta[t.from][t.sym] = t.to;
    }
    return { states: D.states, alphabet: D.alphabet, start: D.start, accept: D.accept, delta };
  }
  function productDFA(P0, D0) {
    const trace = [], D = asDelta(D0);
    let P = P0;
    if (P.acceptBy !== 'final') { const r = toFinal(P); P = r.pda; trace.push({ kind: 'convert', say: 'Make the PDA accept by final state first, so acceptance can also ask the DFA.' }, ...r.trace); }
    const name = (q, d) => q + '|' + d;
    const tr = [];
    for (const t of P.transitions) for (const d of D.states) {
      if (t.read === '') tr.push({ from: name(t.from, d), read: '', pop: t.pop, to: name(t.to, d), push: t.push });
      else { const e = D.delta[d] && D.delta[d][t.read]; if (e != null) tr.push({ from: name(t.from, d), read: t.read, pop: t.pop, to: name(t.to, e), push: t.push }); }
    }
    trace.push({ kind: 'pair', say: 'States are pairs (PDA state | DFA state). A move reading a goes to the pair of the PDA target and the DFA step on a; an ε-move keeps the DFA still. ' + tr.length + ' moves.' });
    const accept = [];
    for (const q of P.accept) for (const d of D.accept) accept.push(name(q, d));
    trace.push({ kind: 'accept', states: accept, say: 'Accept in pairs where both are accepting: ' + (accept.join(', ') || 'none') + '.' });
    const Q = make({ states: P.states.flatMap((q) => D.states.map((d) => name(q, d))), input: P.input.filter((a) => D.alphabet.includes(a)), stack: P.stack,
      start: name(P.start, D.start), startStack: P.startStack, accept, acceptBy: 'final', transitions: tr, meta: P.meta });
    return { pda: Q, trace };
  }

  // ---------- random PDAs (tests and exercises) ----------
  function random(rand, opts) {
    opts = Object.assign({ states: 3, input: ['a', 'b'], stack: ['A', 'Z'], transitions: 7, acceptBy: 'final' }, opts || {});
    const qs = Array.from({ length: opts.states }, (_, i) => 'q' + i), int = (k) => Math.floor(rand() * k);
    const tr = [];
    for (let i = 0; i < opts.transitions; i++) {
      const push = []; const k = int(3);
      for (let j = 0; j < k; j++) push.push(opts.stack[int(opts.stack.length)]);
      tr.push({ from: qs[int(qs.length)], read: rand() < 0.25 ? '' : opts.input[int(opts.input.length)], pop: rand() < 0.1 ? '' : opts.stack[int(opts.stack.length)], to: qs[int(qs.length)], push });
    }
    return make({ states: qs, input: opts.input, stack: opts.stack, start: 'q0', startStack: opts.stack[opts.stack.length - 1],
      accept: qs.filter(() => rand() < 0.4), acceptBy: opts.acceptBy, transitions: tr });
  }

  T.pda = { EPS, make, parse, tryParse, toString, word, showT, showStack, moves, stepper, simulate, accepts, pathTo,
    toEmpty, toFinal, asDelta, fromCFGTopDown, fromCFGBottomUp, toCFG, deterministic, productDFA, random, fresh };
})();
