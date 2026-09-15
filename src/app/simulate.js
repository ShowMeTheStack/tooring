// Running what a student builds in the sandbox: membership tests and step-by-step frames for finite
// automata, PDAs, Turing machines, grammars and regular expressions, and the conversions between them.
// The core engines do the work when they are loaded (T.FA, T.RE, T.pda, T.tm, T.grammar, T.cfg); small
// fallbacks keep finite automata, PDAs and Turing machines runnable without them.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, M = T.Machine;
  const Sim = (T.Sim = {});
  const show = (w) => (w === '' ? 'ε' : w);
  const set = (xs) => (xs.length ? '{' + xs.join(', ') + '}' : '∅');
  Sim.LIMIT = 400;

  // ---- finite automata ------------------------------------------------------------------------------------
  /** ε-closure and steps without the core engine */
  function faSteps(m, w) {
    const mv = M.moves(m);
    const close = (S) => { const out = new Set(S), st = [...S]; while (st.length) { const q = st.pop(); for (const x of mv) if (x.from === q && x.sym === '' && !out.has(x.to)) { out.add(x.to); st.push(x.to); } } return m.states.filter((q) => out.has(q)); };
    let cur = close([m.start]);
    const steps = [{ states: cur, edges: [] }];
    for (const a of w) {
      const edges = mv.filter((x) => x.sym === a && cur.includes(x.from));
      const next = close([...new Set(edges.map((x) => x.to))]);
      steps.push({ sym: a, from: cur, edges, states: next });
      cur = next;
      if (!cur.length) break;
    }
    return steps;
  }
  function faRun(m, w) {
    if (T.FA) {
      const core = M.toCore(m);
      if (core && core.fa) {
        const r = T.FA.run(core.fa, w);
        const steps = r.trace.filter((s) => s.kind === 'start' || s.kind === 'read' || s.kind === 'stuck').map((s) => ({ sym: s.sym, edges: s.edges || [], states: s.states || [], from: s.from, say: s.say, kind: s.kind }));
        return { steps, accepted: r.accepted, say: r.trace[r.trace.length - 1].say };
      }
    }
    const steps = faSteps(m, [...w]);
    const last = steps[steps.length - 1];
    const accepted = steps.length === [...w].length + 1 && last.states.some((q) => m.accept.includes(q));
    return { steps, accepted };
  }

  // ---- PDAs ------------------------------------------------------------------------------------------------
  const pushSyms = (p) => (p === '' ? [] : /\s/.test(p) ? p.split(/\s+/).filter(Boolean) : [...p]);
  /** Breadth-first search over configurations (state, position, stack) without the core engine */
  function pdaSearch(m, w) {
    const rules = m.trans.map((t, id) => Object.assign({ id, from: t.from, to: t.to }, M.pdaLabel(t.label)));
    const start = { state: m.start, pos: 0, stack: [m.bottom || 'Z'], parent: null, via: null };
    const seen = new Set(), all = [start], q = [start];
    const accepting = (c) => c.pos === w.length && (m.acceptBy === 'empty' ? !c.stack.length : m.accept.includes(c.state));
    while (q.length && all.length < 5000) {
      const c = q.shift();
      if (accepting(c)) return { accepted: true, path: pathOf(c), explored: all.length };
      for (const r of rules) {
        if (r.from !== c.state) continue;
        if (r.read !== '' && w[c.pos] !== r.read) continue;
        if (r.pop !== '' && c.stack[0] !== r.pop) continue;
        const stack = pushSyms(r.push).concat(r.pop !== '' ? c.stack.slice(1) : c.stack);
        if (stack.length > 3 * w.length + 12) continue;
        const d = { state: r.to, pos: c.pos + (r.read !== '' ? 1 : 0), stack, parent: c, via: r };
        const k = d.state + '|' + d.pos + '|' + stack.join(' ');
        if (seen.has(k)) continue;
        seen.add(k); all.push(d); q.push(d);
      }
    }
    // no accepting run: show the one that got furthest
    const best = all.reduce((a, c) => (c.pos > a.pos || (c.pos === a.pos && depth(c) > depth(a)) ? c : a), start);
    return { accepted: false, path: pathOf(best), explored: all.length };
  }
  const depth = (c) => { let n = 0; for (; c.parent; c = c.parent) n++; return n; };
  const pathOf = (c) => { const out = []; for (; c; c = c.parent) out.unshift(c); return out; };

  // ---- Turing machines ---------------------------------------------------------------------------------------
  function tmRun(m, w) {
    const rules = new Map();
    for (const t of m.trans) { const l = M.tmLabel(t.label); rules.set(t.from + '\u0000' + l.read, { to: t.to, write: l.write, move: l.move }); }
    const tape = new Map([...w].map((c, i) => [i, c]));
    let q = m.start, head = 0;
    const steps = [{ q, head, tape: new Map(tape) }];
    for (let n = 0; n < Sim.LIMIT; n++) {
      if (m.accept.includes(q) && !m.trans.some((t) => t.from === q)) break;
      const sym = tape.has(head) ? tape.get(head) : '⊔';
      const r = rules.get(q + '\u0000' + sym);
      if (!r) break;
      if (r.write === '⊔') tape.delete(head); else tape.set(head, r.write);
      steps.push({ q: r.to, head: head + (r.move === 'L' ? -1 : r.move === 'R' ? 1 : 0), tape: new Map(tape), from: q, read: sym, rule: r });
      q = r.to; head = steps[steps.length - 1].head;
    }
    const last = steps[steps.length - 1];
    const sym = last.tape.has(last.head) ? last.tape.get(last.head) : '⊔';
    const halted = !rules.has(last.q + '\u0000' + sym) || (m.accept.includes(last.q) && !m.trans.some((t) => t.from === last.q));
    return { steps, halted, accepted: halted && m.accept.includes(last.q) };
  }
  const tapeArr = (tape) => { if (!tape.size) return { list: [], offset: 0 }; const lo = Math.min(...tape.keys()), hi = Math.max(...tape.keys()); const list = []; for (let i = lo; i <= hi; i++) list.push(tape.has(i) ? tape.get(i) : '⊔'); return { list, offset: lo }; };

  // ---- one answer per string -------------------------------------------------------------------------------
  /**
   * Does the thing accept w? src: {kind: 'dfa'|'nfa'|'pda'|'tm'|'grammar'|'regex', text}.
   * Returns {accepted: true | false | null (no answer), note}.
   */
  Sim.accepts = function (src, w) {
    try {
      if (src.kind === 'regex') {
        if (!T.RE) return { accepted: null, note: 'needs the regex engine' };
        return { accepted: !!T.RE.test(src.text, w) };
      }
      if (src.kind === 'grammar') {
        if (!(T.grammar && T.parse && T.parse.earley)) return { accepted: null, note: 'needs the grammar engine' };
        const G = T.grammar.parse(src.text);
        return { accepted: !!T.parse.earley(G, T.grammar.input ? T.grammar.input(G, w) : [...w]).accepted };
      }
      const m = M.parse(src.text);
      if (m.kind === 'pda') {
        const core = M.toCore(m);
        if (core && core.pda) { const r = T.pda.accepts(core.pda, [...w]); return { accepted: r.accepted, note: r.complete ? '' : 'search bound reached' }; }
        return { accepted: pdaSearch(m, [...w]).accepted };
      }
      if (m.kind === 'tm') { const r = tmRun(m, w); return r.halted ? { accepted: r.accepted } : { accepted: null, note: 'no halt in ' + Sim.LIMIT + ' steps' }; }
      return { accepted: faRun(m, w).accepted };
    } catch (e) { return { accepted: null, note: e.message }; }
  };

  // ---- frames for a run ------------------------------------------------------------------------------------
  /** Frames that show src running on w, for the sandbox's player. pos: fixed state positions (dragged) */
  Sim.frames = function (src, w, pos) {
    if (src.kind === 'regex') return regexFrames(src.text, w);
    if (src.kind === 'grammar') return grammarFrames(src.text, w);
    const m = M.parse(src.text);
    if (pos) m.pos = Object.assign({}, pos);
    const P = K.graph.layout(m).pos;
    const g0 = K.graph.draw(m, { pos: P });
    const below = g0.box.y + g0.box.h + 64, cx = g0.box.x + g0.box.w / 2;
    const ws = [...w];
    const F = [];
    if (m.kind === 'tm') {
      const r = tmRun(m, w);
      const N = 11, sc = K.tape.scroller({ cells: N, origin: -2 });
      r.steps.forEach((s, i) => {
        const a = tapeArr(s.tape);
        const last = i === r.steps.length - 1;
        const items = K.graph.draw(m, { pos: P, active: [s.q], taken: s.from ? [s.from + '>' + s.q] : [], good: last && r.accepted ? [s.q] : [], bad: last && r.halted && !r.accepted ? [s.q] : [] }).items
          .concat(K.tape.draw({ tape: a.list, offset: a.offset, head: s.head, state: s.q, cells: N, origin: sc.at(s.head), prevOrigin: sc.prev, x: cx - N * 23, y: below, label: 'tape' }).items);
        let say = i === 0 ? 'Start in ' + s.q + ' with ' + show(w) + ' on the tape.' : 'In ' + s.from + ' reading ' + s.read + ': write ' + s.rule.write + ', move ' + s.rule.move + ', go to ' + s.q + '.';
        if (last) say += r.halted ? (r.accepted ? ' The machine halts in an accepting state.' : ' No move applies: the machine halts and rejects.') : ' After ' + Sim.LIMIT + ' steps it is still running; the run stops here.';
        F.push({ items, say, counters: { steps: i } });
      });
      return F;
    }
    if (m.kind === 'pda') {
      let path, accepted, explored;
      const core = M.toCore(m);
      if (core && core.pda) {
        const r = T.pda.simulate(core.pda, ws, { keep: true, stopAtAccept: true });
        accepted = r.accepted; explored = r.configs.length;
        if (r.paths.length) path = r.paths[0].map((c) => ({ state: c.state, pos: c.pos, stack: c.stack, via: c.via !== null && c.via !== undefined ? core.pda.transitions.find((t) => t.id === c.via) : null }));
        else { const best = r.configs.reduce((a, c) => (c.pos >= a.pos ? c : a), r.configs[0]); path = T.pda.pathTo(r, best.id).map((c) => ({ state: c.state, pos: c.pos, stack: c.stack, via: c.via !== null && c.via !== undefined ? core.pda.transitions.find((t) => t.id === c.via) : null })); }
      } else { const r = pdaSearch(m, ws); accepted = r.accepted; explored = r.explored; path = r.path.map((c) => ({ state: c.state, pos: c.pos, stack: c.stack, via: c.via })); }
      const sx = cx - Math.max(1, ws.length) * 22;
      path.forEach((c, i) => {
        const last = i === path.length - 1;
        const items = K.graph.draw(m, { pos: P, active: [c.state], taken: c.via ? [c.via.from + '>' + c.via.to] : [], good: last && accepted ? [c.state] : [], bad: last && !accepted ? [c.state] : [] }).items
          .concat(K.string.draw({ text: ws, pos: c.pos, x: sx, y: below, label: 'input', cw: 44 }).items)
          .concat(K.stack.draw({ items: c.stack.slice().reverse(), x: g0.box.x + g0.box.w + 70, y: below + 44, label: 'stack' }).items);
        const v = c.via;
        let say = i === 0 ? 'Start in ' + c.state + ' with ' + show(c.stack.join('')) + ' on the stack.' : 'Move ' + v.from + ' → ' + v.to + ': read ' + (v.read || 'ε') + ', pop ' + (v.pop || 'ε') + ', push ' + ((Array.isArray(v.push) ? v.push.join('') : v.push) || 'ε') + '.';
        if (last) say += accepted ? ' This branch accepts, so the PDA accepts ' + show(w) + '.' : ' No branch accepts (' + explored + ' configurations explored); this is the one that read furthest. ' + show(w) + ' is rejected.';
        F.push({ items, say, counters: { moves: i } });
      });
      return F;
    }
    const r = faRun(m, w);
    const sx = cx - Math.max(1, ws.length) * 22;
    r.steps.forEach((s, i) => {
      const last = i === r.steps.length - 1;
      const done = last && (i === ws.length || !s.states.length);
      const ok = done && r.accepted;
      const taken = (s.edges || []).map((e) => e.from + '>' + e.to);
      const items = K.graph.draw(m, { pos: P, active: s.states, taken, good: ok ? s.states.filter((q) => m.accept.includes(q)) : [], dim: [] }).items
        .concat(K.string.draw({ text: ws, pos: i, x: sx, y: below, label: 'input', cw: 44, headText: i >= ws.length ? 'end' : 'next' }).items);
      let say = s.say || (i === 0 ? 'Start in ' + set(s.states) + '.' : 'Read ' + s.sym + ': the live states are ' + set(s.states) + '.');
      if (last) say += ' ' + (r.accepted ? show(w) + ' is accepted.' : show(w) + ' is rejected.');
      F.push({ items, say: say.replace(/\s+/g, ' ').trim(), counters: { read: Math.min(i, ws.length) } });
    });
    return F;
  };

  function regexFrames(rx, w) {
    if (!T.RE) return [{ items: [], say: 'Running a regular expression needs the regex engine, which is not loaded.' }];
    const nfa = T.RE.thompson(rx).fa;
    const text = M.format(M.normalize(Object.assign({ kind: 'nfa' }, nfa)));
    const fr = Sim.frames({ kind: 'nfa', text }, w);
    if (fr.length) fr[0].say = 'The expression ' + rx + ' becomes an NFA by Thompson\'s construction; it runs on ' + show(w) + '. ' + fr[0].say;
    return fr;
  }
  function grammarFrames(text, w) {
    if (!T.grammar) return [{ items: [], say: 'Parsing needs the grammar engine, which is not loaded.' }];
    const G = T.grammar.parse(text);
    const word = T.grammar.input ? T.grammar.input(G, w) : [...w];
    const trees = T.grammar.parseTrees(G, word, 1);
    if (!trees.length) return [{ items: K.string.draw({ text: word, x: 0, y: 0, label: 'string' }).items, say: show(w) + ' has no parse tree: it is not in the language of the grammar.' }];
    // grow the tree one rule at a time, leftmost nonterminal first
    let id = 0;
    const mk = (n) => ({ id: 'n' + (id++), label: n.sym, src: n, cls: n.children ? 'nt' : 't' });
    const root = mk(trees[0]);
    const frames = [];
    const frontier = [root];
    const snapshot = (say, hot) => frames.push({ items: K.tree.draw(JSON.parse(JSON.stringify(root, (k, v) => (k === 'src' ? undefined : v))), { yield: true, yieldLabel: 'yield', hot: hot ? [hot] : [] }).items, say });
    snapshot('Start from ' + G.start + '.', root.id);
    for (let guard = 0; guard < 200; guard++) {
      const k = frontier.findIndex((x) => x.src.children);
      if (k < 0) break;
      const n = frontier[k];
      const kids = n.src.children.length ? n.src.children.map(mk) : [{ id: 'n' + (id++), label: 'ε', cls: 't', src: { children: null } }];
      n.children = kids;
      frontier.splice(k, 1, ...kids);
      snapshot('Expand ' + n.label + ' → ' + (n.src.children.length ? n.src.children.map((c) => c.sym).join(' ') : 'ε') + '.', n.id);
    }
    frames[frames.length - 1].say += ' The yield is ' + show(w) + ', so it is in the language.';
    return frames;
  }


  // ---- other models: register machines, counter machines, recursive functions, λ-terms ----------------------
  /**
   * Run a program of another model of computation and give frames for the sandbox's player:
   * kind 'ram' (input: values for r1, r2, ...), 'counter' (A=3 B=0), 'rec' (definitions, input: f 2 3),
   * 'lambda' (a term; input ignored). Returns {frames, verdict, note}.
   */
  Sim.MODELS = ['ram', 'counter', 'rec', 'lambda'];
  Sim.model = function (kind, text, input) {
    const F = [];
    const mono = (key, x, y, t, cls) => ({ key, kind: 'text', x, y, text: t, cls: 'mono' + (cls ? ' ' + cls : '') });
    const cells = (vals, x, y, hot) => Object.keys(vals).map((k, i) => ({ key: 'c:' + k, kind: 'cell', x: x + i * 64, y, w: 56, h: 44, text: String(vals[k]), sub: k, cls: hot && hot.includes(k) ? 'hot' : '' }));
    const listing = (lines, at) => lines.map((l, i) => mono('ln' + i, 0, 22 + i * 24, l, i === at ? 'hot' : ''));
    if (kind === 'ram' || kind === 'counter') {
      const ram = kind === 'ram';
      const nums = String(input || '').trim();
      let init;
      if (ram) { init = {}; nums.split(/[\s,]+/).filter(Boolean).forEach((v, i) => { const m = /^r?(\d+)=(\d+)$/.exec(v); if (m) init[+m[1]] = +m[2]; else init[i + 1] = +v; }); }
      else { init = {}; for (const v of nums.split(/[\s,]+/).filter(Boolean)) { const m = /^(\w+)=(\d+)$/.exec(v); if (m) init[m[1]] = +m[2]; } }
      const r = ram ? T.ram.run(text, init, { maxSteps: 2000 }) : T.counter.run(text, init, { maxSteps: 2000 });
      const lines = String(text).split('\n').filter((l) => l.trim());
      const lineOf = (st) => (st.line ? lines.findIndex((l, i) => i >= 0 && l === String(text).split('\n')[st.line - 1]) : lines.findIndex((l) => new RegExp('^\\s*' + st.at + '\\s*:').test(l)));
      const regsOf = (st) => { const v = ram ? st.regs : st.counters; const o = {}; const keys = ram ? [...new Set([0, ...Object.keys(v).map(Number), ...Object.keys(init).map(Number)])].sort((a, b) => a - b) : Object.keys(v); for (const k of keys) o[ram ? 'r' + k : k] = v[k] || 0; return o; };
      const start = ram ? Object.assign({ 0: 0 }, init) : Object.assign({}, init);
      const first = {}; for (const k of Object.keys(start)) first[ram ? 'r' + k : k] = start[k];
      const X = Math.max(...lines.map((l) => l.length)) * 9 + 40;
      F.push({ items: listing(lines, -1).concat(cells(first, X, 30)), say: 'Start with ' + (Object.entries(first).map(([k, v]) => k + ' = ' + v).join(', ') || 'every register 0') + '.' });
      for (const st of r.trace.slice(0, 300)) {
        if (st.kind !== 'exec') continue;
        const vals = regsOf(st);
        const hot = Object.keys(st.changed || {}).map((k) => (ram ? 'r' + k : k));
        F.push({ items: listing(lines, lineOf(st)).concat(cells(vals, X, 30, hot)), say: st.say });
      }
      const last = F[F.length - 1];
      last.say += ' ' + (r.verdict === 'halt' ? 'The program halts after ' + r.steps + ' steps' + (ram ? ', with r0 = ' + (r.output !== undefined ? r.output : r.get ? r.get(0) : '?') : '') + '.' : 'It is stopped after ' + r.steps + ' steps without halting.');
      return { frames: F, verdict: r.verdict === 'halt' ? 'halts' : 'no halt', note: ram ? 'r0 = ' + (r.output !== undefined ? r.output : '?') : '' };
    }
    if (kind === 'rec') {
      const d = T.rec.parseDefs(text, T.rec.library ? T.rec.library() : {});
      if (d.errors.length) throw new Error('line ' + d.errors[0].line + ': ' + d.errors[0].msg);
      const parts = String(input || '').trim().split(/[\s,()]+/).filter(Boolean);
      const fn = parts[0] || Object.keys(d.env).pop();
      const args = parts.slice(1).map(Number);
      const r = T.rec.evaluate(fn, args, d.env, { maxCalls: 20000, traceLimit: 400 });
      const stack = [];
      const draw = (say, hotTop) => F.push({ items: stack.slice(-9).map((l, i, a) => mono('k' + (stack.length - a.length + i), 0, 22 + i * 26, l, i === a.length - 1 && hotTop ? 'hot' : '')), say });
      draw('Evaluate ' + fn + '(' + args.join(', ') + ').');
      for (const st of r.trace.slice(0, 300)) {
        if (st.kind === 'call') { stack.push('  '.repeat(Math.min(8, st.depth || 0)) + st.say); draw('Call: ' + st.say + '.', true); }
        else if (st.kind === 'return') { if (stack.length) stack[stack.length - 1] = '  '.repeat(Math.min(8, st.depth || 0)) + st.say; draw('Return: ' + st.say + '.', true); }
      }
      F[F.length - 1].say += ' The value is ' + r.value + ' (' + r.calls + ' calls).';
      return { frames: F, verdict: r.verdict === 'value' || r.value !== undefined ? '= ' + r.value : r.verdict, note: '' };
    }
    if (kind === 'lambda') {
      const r = T.lambda.normalize(text, { maxSteps: 200, traceLimit: 200 });
      for (const st of r.trace) F.push({ items: [mono('term', 0, 30, st.after || st.term || r.text, 'big'), st.redex ? mono('redex', 0, 70, 'redex: ' + st.redex, 'hot') : mono('redex', 0, 70, ' ')], say: st.say });
      return { frames: F, verdict: r.verdict === 'normal' ? 'normal form' : r.verdict, note: r.text };
    }
    throw new Error('unknown model ' + kind);
  };

  // ---- conversions --------------------------------------------------------------------------------------------
  const faOf = (text) => { const c = M.toCore(M.parse(text)); if (!c || !c.fa) throw new Error((c && c.error) || 'not a finite automaton'); return c.fa; };
  const faText = (fa, kind) => M.format(Object.assign(M.normalize(Object.assign({}, fa, { kind: kind || 'nfa' })), { pos: {} }));
  const gram = (text) => T.grammar.parse(text);
  /** The conversions a kind of thing has: [{id, label, to (the kind it gives), ready (engine loaded), run(text) -> text}] */
  Sim.conversions = function (kind) {
    const fa = kind === 'dfa' || kind === 'nfa';
    const list = [];
    if (fa) list.push(
      { id: 'subset', label: 'To a DFA (subset construction)', to: 'dfa', ready: () => !!(T.FA && T.FA.subset), run: (t) => faText(T.FA.subset(faOf(t)).fa, 'dfa') },
      { id: 'minimise', label: 'Minimise', to: 'dfa', ready: () => !!(T.FA && T.FA.minimizeHopcroft), run: (t) => { const f = faOf(t); return faText(T.FA.minimizeHopcroft(T.FA.kind(f) === 'dfa' ? f : T.FA.subset(f).fa).fa, 'dfa'); } },
      { id: 'complement', label: 'Complement', to: 'dfa', ready: () => !!(T.FA && T.FA.complement), run: (t) => faText(T.FA.complement(faOf(t)).fa, 'dfa') },
      { id: 'reverse', label: 'Reverse', to: 'nfa', ready: () => !!(T.FA && T.FA.reverse), run: (t) => faText(T.FA.reverse(faOf(t)).fa, 'nfa') },
      { id: 'toRegex', label: 'To a regular expression', to: 'regex', ready: () => !!(T.RE && T.RE.fromFA), run: (t) => T.RE.fromFA(faOf(t)).regex },
    );
    if (kind === 'regex') list.push(
      { id: 'thompson', label: 'To an NFA (Thompson)', to: 'nfa', ready: () => !!(T.RE && T.RE.thompson), run: (t) => faText(T.RE.thompson(t).fa, 'nfa') },
      { id: 'mindfa', label: 'To the minimal DFA', to: 'dfa', ready: () => !!(T.RE && T.RE.minimalDFA), run: (t) => faText(T.RE.minimalDFA(t).fa, 'dfa') },
      { id: 'simplify', label: 'Simplify', to: 'regex', ready: () => !!(T.RE && T.RE.simplify), run: (t) => { const r = T.RE.simplify(t); return typeof r === 'string' ? r : r.regex || T.RE.show(r.ast || r.result || r); } },
    );
    if (kind === 'grammar') list.push(
      { id: 'cnf', label: 'To Chomsky normal form', to: 'grammar', ready: () => !!(T.cfg && T.cfg.toCNF), run: (t) => T.grammar.toString(T.cfg.toCNF(gram(t)).grammar) },
      { id: 'useless', label: 'Remove useless symbols', to: 'grammar', ready: () => !!(T.cfg && T.cfg.removeUseless), run: (t) => T.grammar.toString(T.cfg.removeUseless(gram(t)).grammar) },
      { id: 'eps', label: 'Remove ε-rules', to: 'grammar', ready: () => !!(T.cfg && T.cfg.removeEpsilon), run: (t) => T.grammar.toString(T.cfg.removeEpsilon(gram(t)).grammar) },
      { id: 'topdown', label: 'To a PDA', to: 'pda', ready: () => !!(T.pda && T.pda.fromCFGTopDown), run: (t) => M.format(M.parse(T.pda.toString(T.pda.fromCFGTopDown(gram(t)).pda))) },
    );
    if (kind === 'pda') list.push(
      { id: 'tocfg', label: 'To a grammar', to: 'grammar', ready: () => !!(T.pda && T.pda.toCFG), run: (t) => T.grammar.toString(T.pda.toCFG(T.pda.parse(M.format(M.parse(t)))).grammar) },
    );
    return list;
  };
})();
