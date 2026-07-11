// Machines and grammars as text: the form the editors keep in sync with their pictures, topics take as
// input and share links carry. Rules are written the way the core engines read them:
//     start q0                 accept q2 q3            states q5 (a state with no rules)
//     q0 -a,b-> q1             a finite automaton (ε for an empty move)
//     q0, a, Z -> q1, A Z      a PDA: state, read, pop -> state, push (stack-start Z, accept-by empty)
//     q0, a -> q1, b, R        a TM: state, read -> state, write, move, with _ for the blank
// Inside, a machine is held in diagram form, one edge per rule with a label: "a, b" for a finite automaton,
// "a, Z → A Z" for a PDA and "a → b, R" for a TM (the blank drawn ⊔). A line starting with # is a comment, and // starts one anywhere, so # can be a symbol.
// A grammar is one line per nonterminal: S → a S b | ε (-> also works). With no spaces in an
// alternative, each character is a symbol; with spaces, each word is.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const M = T.Machine = {};
  const EPS = new Set(['ε', 'eps', 'epsilon', 'λ', 'e', '']);
  M.isEps = (s) => EPS.has(String(s).trim()) && String(s).trim() !== 'e';
  const eps = (s) => { const t = String(s === undefined ? '' : s).trim(); return t === 'ε' || t === 'eps' || t === 'epsilon' || t === 'λ' || t === '' ? '' : t; };

  /** A finite automaton's label: its symbols ('' is ε) */
  M.symbols = (label) => String(label).split(',').map((x) => eps(x)).filter((x, i, a) => a.indexOf(x) === i);
  /** A PDA label "a, X → YZ": {read, pop, push} */
  M.pdaLabel = function (label) {
    const m = /^\s*([^,→>/]*?)\s*,\s*([^,→>/]*?)\s*(?:→|->|\/)\s*(.*?)\s*$/.exec(label);
    if (!m) throw new Error('"' + label + '" is not a PDA label like a, X → YX');
    return { read: eps(m[1]), pop: eps(m[2]), push: eps(m[3]).replace(/\s+/g, ' ') };
  };
  /** A TM label "a → b, R": {read, write, move} */
  M.tmLabel = function (label) {
    const m = /^\s*(\S+?)\s*(?:→|->|\/)\s*(\S+?)\s*[, ]\s*([LRSN])\s*$/i.exec(label);
    if (!m) throw new Error('"' + label + '" is not a TM label like a → b, R');
    const bl = (x) => (x === '_' ? '⊔' : x);
    return { read: bl(m[1]), write: bl(m[2]), move: m[3].toUpperCase() === 'N' ? 'S' : m[3].toUpperCase() };
  };
  const guessKind = (labels) => {
    if (labels.some((l) => /(→|->|\/)\s*\S+\s*[, ]\s*[LRSN]\s*$/i.test(l))) return 'tm';
    if (labels.some((l) => /,.*(→|->|\/)/.test(l))) return 'pda';
    return 'nfa';
  };

  /**
   * Parse machine text into the diagram form {kind, states, start, accept, trans: [{from, to, label}], blank,
   * bottom, acceptBy, pos}. Rules may be written the way the engines read them:
   *   q0 -a,b-> q1               a finite automaton (ε for an empty move)
   *   q0, a, Z -> q1, A Z        a PDA: state, read, pop -> state, push
   *   q0, a -> q1, b, R          a TM: state, read -> state, write, move (_ is the blank)
   * or as diagram edges, q0 -> q1 : label. Directives: start, accept (or final), states, kind, blank,
   * stack-start (or bottom), accept-by, at q x y (a position); a colon after a directive is allowed.
   */
  M.parse = function (text) {
    const m = { kind: null, states: [], start: null, accept: [], halt: [], reject: [], trans: [], blank: '⊔', pos: {}, bottom: null, acceptBy: null };
    const addState = (q) => { if (!m.states.includes(q)) m.states.push(q); };
    const name = /^[^\s:]+$/;
    const shapes = new Set();
    const tmSym = (x) => (x === '_' || x === '⊔' || x === 'B' && false ? '⊔' : x);
    const edge = (a, b, label, where) => {
      if (!name.test(a) || !name.test(b)) throw new Error(where + 'a state name has no spaces or colons');
      addState(a); addState(b);
      m.trans.push({ from: a, to: b, label });
    };
    String(text || '').split('\n').forEach((raw, k) => {
      const line = (/^\s*#/.test(raw) ? '' : raw.replace(/(^|\s)\/\/.*$/, '')).trim();
      if (!line) return;
      const where = 'line ' + (k + 1) + ': ';
      let r;
      if ((r = /^(\S+)\s*(?:->|→)\s*(\S+)\s*:\s*(.*)$/.exec(line))) { shapes.add('diagram'); edge(r[1], r[2], r[3].trim() === '' ? 'ε' : r[3].trim(), where); return; }
      if ((r = /^(\S+)\s+-(.+?)->\s*(\S+)$/.exec(line) || /^(\S+)\s*-(.+?)->\s+(\S+)$/.exec(line))) {
        shapes.add('fa');
        const syms = r[2].split(/[\s,]+/).filter(Boolean).map((x) => (x === 'eps' || x === 'ϵ' ? 'ε' : x));
        if (!syms.length) throw new Error(where + 'no symbol on the arrow: write ' + r[1] + ' -a-> ' + r[3]);
        edge(r[1], r[3], syms.join(', '), where);
        return;
      }
      const arrow = line.includes('->') ? '->' : line.includes('→') ? '→' : null;
      if (arrow) {
        const [lhs, rhs] = [line.slice(0, line.indexOf(arrow)), line.slice(line.indexOf(arrow) + arrow.length)];
        const L = lhs.split(',').map((x) => x.trim()), R = rhs.split(',').map((x) => x.trim());
        const e = (x) => (eps(x) === '' ? 'ε' : eps(x));
        if (L.length === 3 && R.length === 2) { shapes.add('pda'); edge(L[0], R[0], e(L[1]) + ', ' + e(L[2]) + ' → ' + e(R[1]), where); return; }
        if (L.length === 2 && (R.length === 3 || R.length === 2)) {
          shapes.add('tm');
          const read = tmSym(L[1]), write = R.length === 3 ? tmSym(R[1]) : read, move = (R.length === 3 ? R[2] : R[1]).toUpperCase();
          if (!/^[LRSN-]$/.test(move)) throw new Error(where + 'a move is L, R or S');
          edge(L[0], R[0], read + ' → ' + write + ', ' + (move === 'N' || move === '-' ? 'S' : move), where);
          return;
        }
        throw new Error(where + 'expected "q0 -a-> q1", "q0, a, Z -> q1, A Z" or "q0, a -> q1, b, R"');
      }
      const d = /^([A-Za-z-]+):?\s*(.*)$/.exec(line);
      const key = d ? d[1].toLowerCase() : '';
      const args = d ? d[2].split(/\s+/).map((x) => x.replace(/,$/, '')).filter(Boolean) : [];
      if (key === 'kind') { shapes.add('kind'); const v = (args[0] || '').toLowerCase(); if (!['dfa', 'nfa', 'enfa', 'pda', 'tm'].includes(v)) throw new Error(where + 'the kind is dfa, nfa, pda or tm'); m.kind = v === 'enfa' ? 'nfa' : v; return; }
      if (key === 'start' || key === 'initial') { if (args.length !== 1) throw new Error(where + 'start takes one state'); m.start = args[0]; addState(args[0]); return; }
      if (key === 'accept' || key === 'final' || key === 'accepting') { for (const q of args) { if (!m.accept.includes(q)) m.accept.push(q); addState(q); } return; }
      // a TM's halting states: reject (halts and rejects) and halt (halts with success, for a machine that computes)
      if (key === 'reject' || key === 'halt') { for (const q of args) { addState(q); if (!m[key].includes(q)) m[key].push(q); } return; }
      if (key === 'states' || key === 'state') { for (const q of args) addState(q); return; }
      if (key === 'blank') { m.blank = '⊔'; m.blankText = args[0] || '_'; return; }
      if (key === 'stack-start' || key === 'start-stack' || key === 'bottom') { m.bottom = args[0]; return; }
      if (key === 'accept-by') { m.acceptBy = args[0]; return; }
      if (key === 'at' && args.length === 3) { m.pos[args[0]] = { x: +args[1], y: +args[2] }; return; }
      if (['alphabet', 'sigma', 'input', 'stack', 'tape', 'name', 'tapes', 'mode'].includes(key)) return;
      throw new Error(where + 'cannot read "' + line + '": expected a rule like q0 -a-> q1, or start q0, accept q2');
    });
    if (!m.states.length) throw new Error('there are no states');
    if (!m.start) m.start = m.states[0];
    const guessed = shapes.has('tm') ? 'tm' : shapes.has('pda') ? 'pda' : shapes.has('fa') ? 'nfa' : guessKind(m.trans.map((t) => t.label));
    if ((shapes.has('tm') && shapes.has('pda')) || ((shapes.has('tm') || shapes.has('pda')) && shapes.has('fa'))) throw new Error('the rules mix the forms of different kinds of machine');
    if (m.kind && (m.kind === 'dfa' || m.kind === 'nfa') !== (guessed === 'nfa') && m.trans.length) throw new Error('kind ' + m.kind + ' does not match the rules, which are those of ' + (guessed === 'nfa' ? 'a finite automaton' : guessed === 'pda' ? 'a PDA' : 'a TM'));
    m.kind = m.kind || guessed;
    if (m.kind === 'pda') for (const t of m.trans) M.pdaLabel(t.label);
    if (m.kind === 'tm') for (const t of m.trans) M.tmLabel(t.label);
    if (m.kind === 'nfa' && !shapes.has('kind') && M.isDeterministic(m)) m.kind = 'dfa';
    if (m.kind === 'dfa') {
      const seen = new Set();
      for (const t of m.trans) for (const x of M.symbols(t.label)) {
        if (x === '') throw new Error('a DFA has no ε moves (' + t.from + ' → ' + t.to + ')');
        if (seen.has(t.from + '\u0000' + x)) throw new Error('a DFA has one move per state and symbol: ' + t.from + ' has two on ' + x);
        seen.add(t.from + '\u0000' + x);
      }
    }
    return m;
  };
  /**
   * Machine back to text, in the form the engines read (positions only with keepPos). A finite automaton
   * says "kind dfa" only when asked (opts.kind), since the engine finds that out for itself.
   */
  M.format = function (m, keepPos, opts) {
    opts = opts || {};
    const out = [];
    const tm = m.kind === 'tm', pda = m.kind === 'pda';
    const sep = tm ? ': ' : ' ';
    if (opts.kind && m.kind) out.push('kind ' + m.kind);
    out.push('start' + sep + (m.start || m.states[0] || 'q0'));
    if (pda) out.push('stack-start ' + (m.bottom || 'Z'));
    if (pda && m.acceptBy === 'empty') out.push('accept-by empty');
    if (m.accept && m.accept.length) out.push('accept' + sep + m.accept.join(' '));
    if (tm && m.halt && m.halt.length) out.push('halt: ' + m.halt.join(' '));
    if (tm && m.reject && m.reject.length) out.push('reject: ' + m.reject.join(' '));
    const used = new Set();
    for (const t of m.trans) { used.add(t.from); used.add(t.to); }
    const lone = m.states.filter((q) => !used.has(q) && q !== m.start && !(m.accept || []).includes(q));
    if (lone.length && !tm) out.push('states ' + lone.join(' '));
    const b = (x) => (x === '⊔' ? (m.blankText || '_') : x);
    const ep = (x) => (x === '' ? 'ε' : x);
    for (const t of m.trans) {
      if (pda) { const l = M.pdaLabel(t.label); out.push(t.from + ', ' + ep(l.read) + ', ' + ep(l.pop) + ' -> ' + t.to + ', ' + (l.push || 'ε')); }
      else if (tm) { const l = M.tmLabel(t.label); out.push(t.from + ', ' + b(l.read) + ' -> ' + t.to + ', ' + b(l.write) + ', ' + l.move); }
      else out.push(t.from + ' -' + M.symbols(t.label).map((x) => (x === '' ? 'ε' : x)).join(',') + '-> ' + t.to);
    }
    if (keepPos) for (const q of m.states) if (m.pos && m.pos[q]) out.push('at ' + q + ' ' + Math.round(m.pos[q].x) + ' ' + Math.round(m.pos[q].y));
    return out.join('\n');
  };
  /** The machine as the engines hold it, when they are loaded: {kind, fa | pda | tm} or null */
  M.toCore = function (m) {
    try {
      if ((m.kind === 'dfa' || m.kind === 'nfa') && T.FA) return { kind: m.kind, fa: T.FA.make({ states: m.states, start: m.start, accept: m.accept, trans: M.moves(m) }) };
      if (m.kind === 'pda' && T.pda) return { kind: 'pda', pda: T.pda.parse(M.format(m)) };
      if (m.kind === 'tm' && T.tm) { const r = T.tm.parse(M.format(m)); if (r.errors.length) throw new Error(r.errors[0].msg); return { kind: 'tm', tm: r.machine }; }
    } catch (e) { return { kind: m.kind, error: e.message }; }
    return null;
  };
  /** The alphabet a machine reads (no ε) */
  M.alphabet = function (m) {
    const s = new Set();
    for (const t of m.trans) {
      if (m.kind === 'pda') { const l = M.pdaLabel(t.label); if (l.read) s.add(l.read); }
      else if (m.kind === 'tm') { const l = M.tmLabel(t.label); if (l.read !== m.blank && l.read !== '_' && l.read !== '⊔') s.add(l.read); }
      else for (const x of M.symbols(t.label)) if (x) s.add(x);
    }
    return [...s].sort();
  };
  /** A finite automaton as moves: [{from, sym, to}] with '' for ε */
  M.moves = (m) => [].concat(...m.trans.map((t) => M.symbols(t.label).map((sym) => ({ from: t.from, sym, to: t.to }))));
  /** Is this automaton a DFA as drawn (no ε, at most one move per state and symbol)? Missing moves go to a dead state */
  M.isDeterministic = function (m) {
    const seen = new Set();
    for (const mv of M.moves(m)) { if (mv.sym === '') return false; const k = mv.from + '\u0000' + mv.sym; if (seen.has(k)) return false; seen.add(k); }
    return true;
  };
  /**
   * Accept many shapes of automaton (from the core engines or written by hand) and give the diagram form:
   * {states, start, accept, trans: [{from, to, label}]}. Understands trans/transitions/edges as lists of
   * {from, to, label|sym|symbol|on|read} or [from, sym, to], and delta as {q: {a: r or [r, s]}}.
   */
  M.normalize = function (x) {
    if (typeof x === 'string') return M.parse(x);
    const name = (q) => (q && typeof q === 'object' ? (q.name || q.id) : String(q));
    const states = (x.states || x.Q || []).map(name);
    const accept = [...(x.accept || x.accepting || x.final || x.F || [])].map(name);
    const trans = [];
    const add = (from, sym, to) => { from = name(from); to = name(to); for (const q of [from, to]) if (!states.includes(q)) states.push(q); const s = sym === '' || sym === null || sym === undefined ? 'ε' : String(sym); trans.push({ from, to, label: s }); };
    for (const t of x.trans || x.transitions || x.edges || []) {
      if (Array.isArray(t)) add(t[0], t[1], t[2]);
      else add(t.from, t.label !== undefined ? t.label : t.sym !== undefined ? t.sym : t.symbol !== undefined ? t.symbol : t.on !== undefined ? t.on : t.read, t.to);
    }
    const delta = x.delta || x.d;
    if (delta && typeof delta === 'object' && !Array.isArray(delta)) {
      const entries = delta instanceof Map ? [...delta.entries()] : Object.entries(delta);
      for (const [q, row] of entries) {
        const re = row instanceof Map ? [...row.entries()] : Object.entries(row || {});
        for (const [a, r] of re) for (const to of [].concat(r instanceof Set ? [...r] : r)) add(q, a, to);
      }
    }
    // labels on the same edge merge: a, b
    const merged = [];
    for (const t of trans) { const e = merged.find((u) => u.from === t.from && u.to === t.to); if (e && !x.kind) e.label += ', ' + t.label; else if (e && (x.kind === 'dfa' || x.kind === 'nfa')) e.label += ', ' + t.label; else merged.push(Object.assign({}, t)); }
    return { kind: x.kind || 'nfa', states, start: name(x.start === undefined ? x.q0 === undefined ? states[0] : x.q0 : x.start), accept, trans: merged, blank: x.blank || '⊔', pos: x.pos || {} };
  };

  // ---- grammars ---------------------------------------------------------------------------------------------
  const Gr = T.GrammarText = {};
  /** Parse grammar text: {start, rules: [{lhs, rhs: [symbols]}], nonterminals, terminals} */
  Gr.parse = function (text) {
    const rules = [], nts = [];
    const lines = String(text || '').split('\n');
    let last = null;
    lines.forEach((raw, k) => {
      const line = (/^\s*#/.test(raw) ? '' : raw.replace(/(^|\s)\/\/.*$/, '')).trim();
      if (!line) return;
      let r = /^(\S+)\s*(?:→|->|::=)\s*(.*)$/.exec(line);
      let lhs, body;
      if (r) { lhs = r[1]; body = r[2]; last = lhs; }
      else if (/^\|/.test(line) && last) { lhs = last; body = line.slice(1); }
      else throw new Error('line ' + (k + 1) + ': expected a rule like S → a S b | ε');
      if (!nts.includes(lhs)) nts.push(lhs);
      for (const alt of body.split('|')) {
        const a = alt.trim();
        const rhs = a === '' || a === 'ε' || a === 'eps' || a === 'λ' ? [] : /\s/.test(a) ? a.split(/\s+/).filter((x) => x !== 'ε') : [...a].filter((x) => x !== 'ε');
        rules.push({ lhs, rhs });
      }
    });
    if (!rules.length) throw new Error('the grammar has no rules');
    const terminals = [];
    for (const r of rules) for (const s of r.rhs) if (!nts.includes(s) && !terminals.includes(s)) terminals.push(s);
    return { start: rules[0].lhs, rules, nonterminals: nts, terminals };
  };
  Gr.format = function (g) {
    const by = new Map();
    for (const r of g.rules) { if (!by.has(r.lhs)) by.set(r.lhs, []); by.get(r.lhs).push(r.rhs.length ? r.rhs.join(r.rhs.some((s) => s.length > 1) ? ' ' : '') : 'ε'); }
    return [...by.entries()].map(([l, alts]) => l + ' → ' + alts.join(' | ')).join('\n');
  };
})();
