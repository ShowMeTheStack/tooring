// Grammars: the text format, the Chomsky hierarchy, derivations, parse trees, bounded generation and
// the ambiguity search. Every other grammar and parser engine builds on the objects made here.
//
// THE TEXT FORMAT
//   S -> a S b | ε              one rule per line; alternatives separated by |
//     | c                       a line starting with | continues the previous left side
//   Expr -> Expr '+' Term       arrows: ->  →  ::=
//   %token id num               declares multi-character terminals
//   %start S                    otherwise the start symbol is the first rule's left side
//   %left '+' '-'               precedence for LR conflict resolution, lowest first;
//   %right '^'   %nonassoc '<'  later lines bind tighter (yacc-style)
//   E -> '-' E %prec UMINUS     a rule may borrow the precedence of a declared symbol
//   # comment line, or // comment to the end of a line
//
// How a right side is cut into symbols (one rule, no guessing):
//   - whitespace between symbols is optional;
//   - quoted text ('if' or "if") is always one terminal;
//   - names of nonterminals (anything written alone on the left of an arrow) and %token names are read
//     whole, longest name first;
//   - every other character is a symbol on its own, so "aSb" is a, S, b and "id" is i, d unless id is
//     declared with %token or written 'id';
//   - ε, eps, epsilon or an empty alternative is the empty string.
// A directive line "%words" switches to the other common convention: every whitespace-separated word is
// one symbol (E -> E + T | id).
// Nonterminals are the names written alone on a left side, plus any single capital letter A–Z (so a
// capital with no rules is a nonterminal that generates nothing, which the cleanup lessons need).
// A left side written alone becomes one name when it looks like a name: a letter followed by lower-case
// letters, digits or _ and then primes (S, S', Expr, term, E1, T_a), or <angle> or [bracket] text.
// Anything else on a left side is cut like a right side, which is how unrestricted rules are written:
// "a B -> B a", "C B -> B C" (write CB with a space, or it is read as C, B anyway since CB is not a name).
//
// THE OBJECT
//   { start, nonterminals: [..], terminals: [..], productions: [{ id, lhs: [..], A, rhs: [..], prec }],
//     precedence: { sym: { level, assoc } }, words }
// A is the single left symbol of a context-free rule (null otherwise); rhs [] is ε. Words (strings of
// terminals) are arrays of symbols. Grammars are treated as immutable; transformations make new ones.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const EPS = 'ε', END = '$';
  const NAME = /^(?:[A-Za-z][a-z0-9_]*'*|<[^<>\s]+>|\[[^[\]\s]+\])$/;
  const isCap = (s) => /^[A-Z]$/.test(s);

  class GrammarError extends Error {
    constructor(msg, line) { super(line ? 'Line ' + line + ': ' + msg : msg); this.line = line || 0; this.plain = msg; }
  }

  // ---------- building ----------
  // make(start, productions, opts): productions as {A, rhs}, {lhs:[..], rhs} or [A, rhs] pairs.
  // opts.nonterminals: symbols that must count as nonterminals even if they have no rules left;
  // opts.terminals: alphabet symbols to keep even if unused; opts.precedence, opts.words carry over.
  function make(start, productions, opts) {
    opts = opts || {};
    const prods = productions.map((p, id) => {
      let lhs, rhs, prec = null, line = 0;
      if (Array.isArray(p)) { lhs = Array.isArray(p[0]) ? p[0].slice() : [p[0]]; rhs = p[1].slice(); }
      else { lhs = p.lhs ? p.lhs.slice() : [p.A]; rhs = p.rhs.slice(); prec = p.prec || null; line = p.line || 0; }
      return { id, lhs, A: lhs.length === 1 ? lhs[0] : null, rhs, prec, line };
    });
    const hint = new Set(opts.nonterminals || []), tokens = new Set(opts.tokens || []);
    const Ns = new Set([start]);
    for (const p of prods) if (p.lhs.length === 1) Ns.add(p.lhs[0]);
    const order = [start];
    const see = (s) => { if (!order.includes(s)) order.push(s); };
    for (const p of prods) { p.lhs.forEach(see); p.rhs.forEach(see); }
    for (const s of order) if (hint.has(s) || (isCap(s) && !tokens.has(s) && !(opts.quoted && opts.quoted.has(s)))) Ns.add(s);
    const nonterminals = order.filter((s) => Ns.has(s));
    const terminals = order.filter((s) => !Ns.has(s));
    for (const t of opts.terminals || []) if (!Ns.has(t) && !terminals.includes(t)) terminals.push(t);
    // a context-free rule needs its single left symbol to be a nonterminal
    for (const p of prods) if (p.lhs.length === 1 && !Ns.has(p.lhs[0])) p.A = null;
    return {
      start, nonterminals, terminals, productions: prods,
      precedence: opts.precedence ? JSON.parse(JSON.stringify(opts.precedence)) : {},
      words: !!opts.words, tokens: [...tokens].filter((t) => terminals.includes(t)),
    };
  }
  // A copy with new productions but the same start, alphabet and declarations.
  function derive(G, productions, start, extraN) {
    return make(start || G.start, productions, {
      nonterminals: G.nonterminals.concat(extraN || []), terminals: G.terminals,
      precedence: G.precedence, words: G.words, tokens: G.tokens,
    });
  }

  // Cached facts about a grammar object.
  const cache = new WeakMap();
  function info(G) {
    let c = cache.get(G);
    if (c) return c;
    const N = new Set(G.nonterminals), Tm = new Set(G.terminals), byA = new Map();
    for (const A of G.nonterminals) byA.set(A, []);
    for (const p of G.productions) if (p.A !== null) byA.get(p.A).push(p);
    c = { N, T: Tm, byA, cf: G.productions.every((p) => p.A !== null) };
    cache.set(G, c);
    return c;
  }
  const isN = (G, s) => info(G).N.has(s);

  // ---------- parsing the text ----------
  // A ' straight after a letter, digit, _ or another prime is a prime (S', E''), not a quote.
  const isPrime = (s, i) => s[i] === "'" && i > 0 && /[A-Za-z0-9_'\]>]/.test(s[i - 1]);
  function splitOutside(s, sep) {   // split on sep where not inside quotes
    const out = []; let cur = '', q = null;
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (q) { cur += ch; if (ch === q) q = null; continue; }
      if ((ch === '"' || ch === "'") && !isPrime(s, i)) { q = ch; cur += ch; continue; }
      if (s.startsWith(sep, i)) { out.push(cur); cur = ''; i += sep.length - 1; continue; }
      cur += ch;
    }
    out.push(cur);
    return out;
  }
  function stripComment(line) {
    if (/^\s*#/.test(line)) return '';
    let q = null;
    for (let i = 0; i < line.length; i++) {
      const ch = line[i];
      if (q) { if (ch === q) q = null; continue; }
      if ((ch === '"' || ch === "'") && !isPrime(line, i)) q = ch;
      else if (ch === '/' && line[i + 1] === '/') return line.slice(0, i);
    }
    return line;
  }
  function findArrow(s) {
    let q = null;
    for (let i = 0; i < s.length; i++) {
      const ch = s[i];
      if (q) { if (ch === q) q = null; continue; }
      if ((ch === '"' || ch === "'") && !isPrime(s, i)) { q = ch; continue; }
      if (s.startsWith('->', i)) return [i, 2];
      if (s.startsWith('::=', i)) return [i, 3];
      if (ch === '→') return [i, 1];
    }
    return null;
  }
  // Cut text into symbols. known: names read whole (longest first). quoted: collects quoted symbols.
  function cut(text, known, words, quoted, line) {
    const out = [];
    const s = text.trim();
    if (s === '' || s === EPS || s === 'eps' || s === 'epsilon') return out;
    let i = 0;
    while (i < s.length) {
      const ch = s[i];
      if (/\s/.test(ch)) { i++; continue; }
      if (ch === '"' || ch === "'") {
        const j = s.indexOf(ch, i + 1);
        if (j < 0) throw new GrammarError('unclosed quote ' + ch, line);
        if (j === i + 1) throw new GrammarError('empty quotes; write ε for the empty string', line);
        const sym = s.slice(i + 1, j); out.push(sym); quoted.add(sym); i = j + 1; continue;
      }
      if (words) {
        let j = i; while (j < s.length && !/\s/.test(s[j])) j++;
        const w = s.slice(i, j); if (w !== EPS) out.push(w); i = j; continue;
      }
      let hit = null;
      for (const k of known) if (s.startsWith(k, i)) { hit = k; break; }
      if (hit) { out.push(hit); i += hit.length; continue; }
      let cp = String.fromCodePoint(s.codePointAt(i));
      // a letter with primes is one symbol (S' with no rules is still S')
      if (/[A-Za-z]/.test(cp)) while (s[i + cp.length] === "'") cp += "'";
      if (cp !== EPS) out.push(cp);
      i += cp.length;
    }
    return out;
  }
  function parse(text) {
    const lines = String(text).split(/\r?\n/);
    const raw = [], tokens = new Set(), prec = {};
    let start = null, words = false, level = 0, lastLhs = null;
    lines.forEach((line0, k) => {
      const ln = k + 1, line = stripComment(line0).trim();
      if (!line) return;
      if (line[0] === '%') {
        const m = /^%(\w+)\s*(.*)$/.exec(line);
        if (!m) throw new GrammarError('unknown directive', ln);
        const args = m[2].trim() ? m[2].trim().split(/\s+/).map((w) => w.replace(/^(['"])(.+)\1$/, '$2')) : [];
        const d = m[1];
        if (d === 'token' || d === 'tokens') args.forEach((a) => tokens.add(a));
        else if (d === 'start') { if (args.length !== 1) throw new GrammarError('%start takes one symbol', ln); start = args[0]; }
        else if (d === 'words') words = true;
        else if (d === 'left' || d === 'right' || d === 'nonassoc') {
          level++;
          for (const a of args) prec[a] = { level, assoc: d };
        } else throw new GrammarError('unknown directive %' + d, ln);
        return;
      }
      const arrow = findArrow(line);
      let lhsText, rhsText;
      if (arrow) { lhsText = line.slice(0, arrow[0]).trim(); rhsText = line.slice(arrow[0] + arrow[1]); }
      else if (line[0] === '|' && lastLhs !== null) { lhsText = lastLhs; rhsText = line.slice(1); }
      else throw new GrammarError('expected a rule like  S -> a S b | ε', ln);
      if (!lhsText) throw new GrammarError('missing left side', ln);
      lastLhs = lhsText;
      raw.push({ lhsText, alts: splitOutside(rhsText, '|'), line: ln });
    });
    // with only %start, the grammar has no rules: it generates the empty language ∅
    if (!raw.length) { if (start) return make(start, [], { tokens: [...tokens], precedence: prec, words }); throw new GrammarError('the grammar has no rules'); }
    // pass 1: names written alone on a left side
    const names = new Set();
    for (const r of raw) {
      const t = r.lhsText.trim();
      if (/^(['"]).*\1$/.test(t)) throw new GrammarError('a left side cannot be a quoted terminal', r.line);
      if (words ? !/\s/.test(t) : NAME.test(t)) names.add(t);
    }
    const known = [...new Set([...names, ...tokens])].sort((a, b) => b.length - a.length);
    const quoted = new Set(), prods = [];
    for (const r of raw) {
      const lhs = names.has(r.lhsText.trim()) ? [r.lhsText.trim()] : cut(r.lhsText, known, words, quoted, r.line);
      if (!lhs.length) throw new GrammarError('empty left side', r.line);
      for (const alt0 of r.alts) {
        let alt = alt0, p = null;
        const pm = /%prec\s+(\S+)\s*$/.exec(alt);
        if (pm) { p = pm[1].replace(/^(['"])(.+)\1$/, '$2'); alt = alt.slice(0, pm.index); }
        const rhs = cut(alt, known, words, quoted, r.line);
        prods.push({ lhs, rhs, prec: p, line: r.line });
      }
    }
    for (const q of quoted) if (names.has(q)) throw new GrammarError('"' + q + '" is quoted as a terminal but also has rules');
    const all = new Set(prods.flatMap((p) => p.lhs.concat(p.rhs)));
    if (all.has(END) && !quoted.has(END)) throw new GrammarError('$ is reserved for the end of input; quote it to use it as a terminal');
    if (all.has(END)) throw new GrammarError('$ is reserved for the end of input');
    if (!start) {
      const first = prods.find((p) => p.lhs.length === 1 && (names.has(p.lhs[0]) || isCap(p.lhs[0])));
      start = first ? first.lhs[0] : prods[0].lhs.find(isCap) || prods[0].lhs[0];
    }
    const G = make(start, prods, { nonterminals: [...names], tokens: [...tokens], quoted, precedence: prec, words });
    // a quoted capital stays a terminal; make() kept it out of the nonterminals through opts.quoted
    for (const p of G.productions) {
      if (!p.lhs.some((s) => isN(G, s))) throw new GrammarError('the left side ' + p.lhs.join(' ') + ' has no nonterminal', p.line);
    }
    return G;
  }
  function tryParse(text) {
    try { return { grammar: parse(text), error: null }; }
    catch (e) { if (e instanceof GrammarError) return { grammar: null, error: e.message, line: e.line }; throw e; }
  }

  // ---------- printing ----------
  const sym = (s) => s;
  function needsQuote(G, s) {
    if (isN(G, s)) return false;
    if (G.words) return /\s/.test(s);
    if ((G.tokens || []).includes(s) && /^[A-Za-z0-9_]+$/.test(s)) return false;   // declared with %token
    if ([...s].length > 1 || isCap(s) || /[\s|'"%#→]/.test(s) || s === EPS) return true;
    // a one-character terminal that starts a nonterminal's name would be swallowed by that name
    return false;
  }
  function q(s) { return s.includes("'") ? '"' + s + '"' : "'" + s + "'"; }
  function showSym(G, s) { return needsQuote(G, s) ? q(s) : s; }
  function showRhs(G, rhs) { return rhs.length ? rhs.map((s) => showSym(G, s)).join(' ') : EPS; }
  function showProd(G, p) { return p.lhs.map((s) => showSym(G, s)).join(' ') + ' → ' + showRhs(G, p.rhs); }
  // Plain display of a word or sentential form: no spaces if every symbol is one character.
  function show(form) {
    if (!form.length) return EPS;
    return form.every((s) => [...s].length === 1) ? form.join('') : form.join(' ');
  }
  function toString(G) {
    const out = [];
    // names that the default reader would cut apart force the %words convention
    const words = G.words || G.nonterminals.some((A) => [...A].length > 1 && !NAME.test(A)) ||
      G.terminals.some((t) => /\s/.test(t) && false);
    const H = words && !G.words ? Object.assign({}, G, { words: true }) : G;
    if (words) out.push('%words');
    const toks = (G.tokens || []).filter((t) => G.terminals.includes(t) && /^[A-Za-z0-9_]+$/.test(t));
    if (toks.length && !words) out.push('%token ' + toks.join(' '));
    const levels = {};
    for (const [s, v] of Object.entries(G.precedence || {})) (levels[v.level] = levels[v.level] || { assoc: v.assoc, syms: [] }).syms.push(s);
    for (const l of Object.keys(levels).sort((a, b) => a - b)) out.push('%' + levels[l].assoc + ' ' + levels[l].syms.map((s) => showSym(H, s)).join(' '));
    if (!G.productions.some((p) => p.A === G.start)) out.push('%start ' + G.start);
    const done = new Set();
    const rulesOf = (key) => G.productions.filter((p) => p.lhs.join('\u0001') === key);
    const keys = [];
    if (G.productions.some((p) => p.A === G.start)) keys.push(G.start);
    for (const p of G.productions) { const k = p.lhs.join('\u0001'); if (!keys.includes(k)) keys.push(k); }
    for (const k of keys) {
      if (done.has(k)) continue; done.add(k);
      const ps = rulesOf(k);
      const lhs = ps[0].lhs.map((s) => showSym(H, s)).join(' ');
      out.push(lhs + ' -> ' + ps.map((p) => showRhs(H, p.rhs) + (p.prec ? ' %prec ' + showSym(H, p.prec) : '')).join(' | '));
    }
    return out.join('\n');
  }

  // Read a user's input string as terminals of G: longest terminal first, whitespace ignored.
  function input(G, s) {
    if (Array.isArray(s)) return s.slice();
    const terms = G.terminals.slice().sort((a, b) => b.length - a.length);
    const out = []; let i = 0; s = String(s);
    if (s.trim() === EPS) return out;
    while (i < s.length) {
      if (/\s/.test(s[i])) { i++; continue; }
      const hit = terms.find((t) => s.startsWith(t, i));
      if (hit) { out.push(hit); i += hit.length; continue; }
      const cp = String.fromCodePoint(s.codePointAt(i)); out.push(cp); i += cp.length;
    }
    return out;
  }

  // ---------- quick analyses (untraced; the traced versions live in cfg-transform.js) ----------
  function nullableSet(G) {
    const nul = new Set(); let changed = true;
    while (changed) {
      changed = false;
      for (const p of G.productions) if (p.A !== null && !nul.has(p.A) && p.rhs.every((s) => nul.has(s))) { nul.add(p.A); changed = true; }
    }
    return nul;
  }
  // Shortest terminal yield of every nonterminal (Infinity when it generates nothing).
  function minLengths(G) {
    const m = new Map(G.nonterminals.map((A) => [A, Infinity]));
    const len = (s) => (isN(G, s) ? m.get(s) : 1);
    let changed = true;
    while (changed) {
      changed = false;
      for (const p of G.productions) {
        if (p.A === null) continue;
        const l = p.rhs.reduce((a, s) => a + len(s), 0);
        if (l < m.get(p.A)) { m.set(p.A, l); changed = true; }
      }
    }
    return m;
  }
  function generatingSet(G) { const m = minLengths(G); return new Set(G.nonterminals.filter((A) => m.get(A) < Infinity)); }
  function reachableSet(G) {
    const seen = new Set([G.start]), todo = [G.start], byA = info(G).byA;
    while (todo.length) for (const p of byA.get(todo.pop()) || []) for (const s of p.rhs) if (isN(G, s) && !seen.has(s)) { seen.add(s); todo.push(s); }
    return seen;
  }

  // ---------- the Chomsky hierarchy ----------
  // Returns the most restrictive class whose form every rule has, with a step per rule saying why.
  function classify(G) {
    const N = info(G).N, trace = [];
    const startOnRight = G.productions.some((p) => p.rhs.includes(G.start));
    let right = true, left = true, cf = true, mono = true, csForm = true, strict = true;
    for (const p of G.productions) {
      const isCF = p.A !== null;
      const nts = p.rhs.filter((s) => N.has(s));
      const r = isCF && nts.length <= 1 && (nts.length === 0 || p.rhs[p.rhs.length - 1] === nts[0]);
      const l = isCF && nts.length <= 1 && (nts.length === 0 || p.rhs[0] === nts[0]);
      const st = isCF && ((p.rhs.length === 1 && !N.has(p.rhs[0])) || (p.rhs.length === 2 && !N.has(p.rhs[0]) && N.has(p.rhs[1])) || (p.rhs.length === 0));
      const epsStart = p.lhs.length === 1 && p.lhs[0] === G.start && p.rhs.length === 0 && !startOnRight;
      const m = p.lhs.length <= p.rhs.length || epsStart;
      // context-sensitive form: αAβ → αγβ with γ non-empty
      let cs = epsStart;
      for (let a = 0; !cs && a < p.lhs.length; a++) {
        if (!N.has(p.lhs[a])) continue;
        const al = p.lhs.slice(0, a), be = p.lhs.slice(a + 1);
        const g = p.rhs.length - al.length - be.length;
        cs = g >= 1 && al.every((s, i) => p.rhs[i] === s) && be.every((s, i) => p.rhs[p.rhs.length - be.length + i] === s);
      }
      right = right && r; left = left && l; cf = cf && isCF; mono = mono && m; csForm = csForm && cs; strict = strict && st;
      const tags = [];
      if (r) tags.push('right-linear'); if (l) tags.push('left-linear');
      if (isCF) tags.push('context-free'); if (m) tags.push(epsStart ? 'allowed start → ε' : 'non-contracting');
      let why;
      if (!isCF) why = 'its left side ' + show(p.lhs) + ' has more than one symbol, so it is not context-free';
      else if (r || l) why = 'one nonterminal at most, at the ' + (r && l ? (nts.length ? 'only position' : 'end (none at all)') : r ? 'right end' : 'left end');
      else why = 'a single nonterminal on the left, but ' + (nts.length > 1 ? nts.length + ' nonterminals' : 'its nonterminal in the middle') + ' on the right';
      trace.push({ kind: 'rule', prod: p.id, tags, rightLinear: r, leftLinear: l, contextFree: isCF, monotone: m, contextSensitiveForm: cs,
        say: showProd(G, p) + ': ' + why + (m ? '' : '; it shrinks (' + p.lhs.length + ' symbols become ' + p.rhs.length + ')') + '.' });
    }
    let level, name;
    if (cf && (right || left)) { level = 3; name = right ? 'regular (right-linear)' : 'regular (left-linear)'; if (right && left) name = 'regular (both right- and left-linear)'; }
    else if (cf) { level = 2; name = 'context-free'; }
    else if (mono) { level = 1; name = 'context-sensitive (monotone)'; }
    else { level = 0; name = 'unrestricted'; }
    let say = 'Every rule fits the ' + name + ' form, so the grammar is type ' + level + '.';
    if (cf && !right && !left && G.productions.every((p) => { const k = p.rhs.filter((s) => N.has(s)).length; return k <= 1; }))
      say += ' (Each rule is linear, but right- and left-linear rules are mixed, which can describe non-regular languages.)';
    if (level === 2 && !mono) say += ' (It has ε-rules, so it is not monotone as written; every context-free language without ε still has a monotone grammar.)';
    trace.push({ kind: 'verdict', level, say });
    return { level, name, rightLinear: cf && right, leftLinear: cf && left, strictRegular: cf && strict, contextFree: cf,
      monotone: mono, contextSensitiveForm: csForm, trace };
  }

  // ---------- derivations ----------
  // All ways to rewrite a sentential form one step: [{prod, pos}] (pos is where the left side starts).
  function options(G, form) {
    const out = [];
    for (const p of G.productions) {
      for (let i = 0; i + p.lhs.length <= form.length; i++) if (p.lhs.every((s, k) => form[i + k] === s)) out.push({ prod: p.id, pos: i });
    }
    return out;
  }
  function rewrite(G, form, prodId, pos) {
    const p = G.productions[prodId];
    if (!p || !p.lhs.every((s, k) => form[pos + k] === s)) throw new Error('rule ' + prodId + ' does not apply at position ' + pos);
    return form.slice(0, pos).concat(p.rhs, form.slice(pos + p.lhs.length));
  }
  const firstN = (G, form) => form.findIndex((s) => isN(G, s));
  const lastN = (G, form) => { for (let i = form.length - 1; i >= 0; i--) if (isN(G, form[i])) return i; return -1; };
  // Replay a list of {prod, pos} steps from the start symbol; returns the forms and a trace.
  function replay(G, steps) {
    let form = [G.start];
    const forms = [form], trace = [{ kind: 'form', form, say: 'Start with ' + G.start + '.' }];
    for (const st of steps) {
      const p = G.productions[st.prod];
      const next = rewrite(G, form, st.prod, st.pos);
      const lm = p.A !== null && firstN(G, form) === st.pos, rm = p.A !== null && lastN(G, form) === st.pos;
      trace.push({ kind: 'step', from: form, form: next, prod: st.prod, pos: st.pos, leftmost: lm, rightmost: rm,
        say: 'Rewrite ' + show(p.lhs) + ' at position ' + (st.pos + 1) + ' by ' + showProd(G, p) + ': ' + show(form) + ' ⇒ ' + show(next) + '.' });
      forms.push(next); form = next;
    }
    return { forms, steps: steps.slice(), trace };
  }

  // ---------- parse trees ----------
  // A node is { sym, prod, children }: children null for a terminal leaf, [] for an ε-rule.
  const leaf = (s) => ({ sym: s, prod: null, children: null });
  function yieldOf(t) { return t.children === null ? [t.sym] : t.children.flatMap(yieldOf); }
  function treeKey(t) { return t.children === null ? JSON.stringify(t.sym) : '(' + JSON.stringify(t.sym) + '#' + t.prod + ' ' + t.children.map(treeKey).join(' ') + ')'; }
  function treeSize(t) { return 1 + (t.children || []).reduce((a, c) => a + treeSize(c), 0); }
  function treeDepth(t) { return 1 + Math.max(0, ...(t.children || []).map(treeDepth)); }
  // Check that a tree only uses rules of G (and, for a complete tree, has terminal leaves).
  function checkTree(G, t) {
    if (t.children === null) return !isN(G, t.sym) || t.partial;
    const p = G.productions[t.prod];
    return !!p && p.A === t.sym && p.rhs.length === t.children.length && p.rhs.every((s, i) => t.children[i].sym === s) && t.children.every((c) => checkTree(G, c));
  }
  // Derivation from a tree, expanding the leftmost or rightmost unexpanded nonterminal each time
  // (order 'leftmost' | 'rightmost' | 'breadth', or a function choosing among frontier indexes).
  function derivationOf(G, tree, order) {
    order = order || 'leftmost';
    let frontier = [tree];
    const steps = [];
    const pending = () => frontier.map((n, i) => (n.children !== null ? i : -1)).filter((i) => i >= 0);
    const depth = new Map([[tree, 0]]);
    for (;;) {
      const idx = pending();
      if (!idx.length) break;
      let i;
      if (order === 'leftmost') i = idx[0];
      else if (order === 'rightmost') i = idx[idx.length - 1];
      else if (order === 'breadth') i = idx.reduce((b, k) => (depth.get(frontier[k]) < depth.get(frontier[b]) ? k : b), idx[0]);
      else i = order(idx, frontier);
      const n = frontier[i];
      for (const c of n.children) depth.set(c, depth.get(n) + 1);
      steps.push({ prod: n.prod, pos: i });
      frontier = frontier.slice(0, i).concat(n.children.map((c) => (c.children === null ? leaf(c.sym) : c)), frontier.slice(i + 1));
    }
    const r = replay(G, steps);
    r.order = typeof order === 'string' ? order : 'custom';
    return r;
  }
  // Tree from a derivation of a context-free grammar (any order): steps [{prod, pos}].
  function treeOf(G, steps) {
    const root = { sym: G.start, prod: null, children: null };
    let nodes = [root];
    const trace = [{ kind: 'root', node: root, say: 'The root is the start symbol ' + G.start + '.' }];
    for (const st of steps) {
      const p = G.productions[st.prod], n = nodes[st.pos];
      if (!p || p.A === null || !n || n.sym !== p.A || n.children !== null) throw new Error('step does not match the derivation');
      n.prod = p.id; n.children = p.rhs.map((s) => ({ sym: s, prod: null, children: null }));
      trace.push({ kind: 'grow', node: n, prod: p.id, pos: st.pos, say: 'Give ' + p.A + ' the children ' + showRhs(G, p.rhs) + ' (rule ' + showProd(G, p) + ').' });
      nodes = nodes.slice(0, st.pos).concat(n.children, nodes.slice(st.pos + 1));
    }
    const done = nodes.every((x) => !isN(G, x.sym));
    // leaves for nonterminals that were never expanded stay as partial leaves
    (function mark(t) { if (t.children === null) { if (isN(G, t.sym)) t.partial = true; } else t.children.forEach(mark); })(root);
    return { tree: root, complete: done, trace };
  }

  // ---------- exact bounded language (the oracle) ----------
  // Every terminal string of length ≤ n derivable from each nonterminal, by least fixpoint. Terminals are
  // coded as single characters internally so strings compare fast. Context-free grammars only.
  function coder(G) {
    const enc = new Map(), dec = new Map();
    G.terminals.forEach((t, i) => { const c = String.fromCharCode(0xE000 + i); enc.set(t, c); dec.set(c, t); });
    return { enc: (w) => w.map((t) => enc.get(t) || '￿').join(''), dec: (s) => [...s].map((c) => dec.get(c)), char: (t) => enc.get(t) };
  }
  function languageSets(G, n) {
    if (!info(G).cf) throw new Error('language() needs a context-free grammar');
    const C = coder(G), N = info(G).N;
    const L = new Map(G.nonterminals.map((A) => [A, new Set()]));
    const prods = G.productions.map((p) => ({ A: p.A, rhs: p.rhs.map((s) => (N.has(s) ? { A: s } : { c: C.char(s) })) }));
    let changed = true;
    while (changed) {
      changed = false;
      for (const p of prods) {
        let cur = [''];
        for (const x of p.rhs) {
          const next = [];
          if (x.c !== undefined) { for (const s of cur) if (s.length < n) next.push(s + x.c); }
          else { const set = L.get(x.A); for (const s of cur) for (const t of set) if (s.length + t.length <= n) next.push(s + t); }
          cur = next;
          if (!cur.length) break;
        }
        const tgt = L.get(p.A);
        for (const s of cur) if (!tgt.has(s)) { tgt.add(s); changed = true; }
      }
    }
    return { L, C };
  }
  const byLenLex = (a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0);
  function language(G, n, from) {
    const { L, C } = languageSets(G, n);
    const k = (w) => w.join('\u0001');
    return [...L.get(from || G.start)].map(C.dec).sort((a, b) => a.length - b.length || (k(a) < k(b) ? -1 : k(a) > k(b) ? 1 : 0));
  }
  // All words over G's terminals up to length n (for complement checks in tests and exercises).
  function allWords(alphabet, n) {
    const out = [[]];
    let layer = [[]];
    for (let l = 1; l <= n; l++) { const nx = []; for (const w of layer) for (const a of alphabet) nx.push(w.concat([a])); out.push(...nx); layer = nx; }
    return out;
  }

  // ---------- generation by breadth-first search over sentential forms ----------
  // Exact for non-contracting grammars (forms never shrink, so forms longer than n are dropped). For
  // context-free grammars it follows leftmost derivations and prunes forms whose shortest possible yield
  // is already too long; ε- and unit-cycles can make the search endless, so a budget stops it and the
  // result says complete: false. Unrestricted grammars are searched under the same budget.
  function generate(G, n, opts) {
    opts = Object.assign({ budget: 20000, traceLimit: 300, maxForm: null }, opts || {});
    const cf = info(G).cf, mono = classify(G).monotone, N = info(G).N;
    const minL = cf ? minLengths(G) : null;
    const maxForm = opts.maxForm || (mono ? n : n + 6);
    const trace = [], found = new Map();
    const key = (f) => f.join('\u0001');
    const seen = new Set([key([G.start])]);
    let queue = [[G.start]], explored = 0, complete = true, pruned = 0;
    const note = (st) => { if (trace.length < opts.traceLimit) trace.push(st); };
    note({ kind: 'start', form: [G.start], say: 'Begin with the start symbol ' + G.start + '.' });
    const startEps = mono && !cf;
    while (queue.length) {
      const next = [];
      for (const form of queue) {
        if (++explored > opts.budget) { complete = false; break; }
        if (!form.some((s) => N.has(s))) {
          const k = key(form);
          if (!found.has(k)) { found.set(k, form); note({ kind: 'word', form, say: show(form) + ' has no nonterminals left, so it is in the language.' }); }
          continue;
        }
        const moves = cf ? (() => { const i = firstN(G, form); return info(G).byA.get(form[i]).map((p) => ({ prod: p.id, pos: i })); })() : options(G, form);
        for (const mv of moves) {
          const f = rewrite(G, form, mv.prod, mv.pos);
          const k = key(f);
          if (seen.has(k)) continue;
          seen.add(k);
          let why = null;
          const terms = f.filter((s) => !N.has(s)).length;
          if (cf) {
            const ml = f.reduce((a, s) => a + (N.has(s) ? minL.get(s) : 1), 0);
            if (ml === Infinity) why = 'it contains a nonterminal that generates no string';
            else if (ml > n) why = 'every string it can produce is longer than ' + n;
          } else if (f.length > maxForm && !(startEps && f.length === 0)) {
            why = mono ? 'rules never shrink a form, and it is already longer than ' + n : 'it is longer than the search allows';
            if (!mono) complete = false;
          } else if (!cf && terms > n + 6) { why = 'too many terminals'; complete = false; }
          if (why) { pruned++; note({ kind: 'prune', from: form, form: f, prod: mv.prod, pos: mv.pos, say: 'Drop ' + show(f) + ': ' + why + '.' }); continue; }
          note({ kind: 'expand', from: form, form: f, prod: mv.prod, pos: mv.pos, say: show(form) + ' ⇒ ' + show(f) + ' by ' + showProd(G, G.productions[mv.prod]) + '.' });
          next.push(f);
        }
      }
      if (!complete) break;
      queue = next;
    }
    const words = [...found.values()].filter((w) => w.length <= n).sort((a, b) => a.length - b.length || (key(a) < key(b) ? -1 : key(a) > key(b) ? 1 : 0));
    return { words, complete, explored, pruned, trace };
  }

  // ---------- parse trees of a word by exhaustive search ----------
  // Enumerates distinct parse trees of w (up to max). A node for the same nonterminal over the same span
  // may appear at most twice on one root-to-leaf path: that keeps the search finite and still finds the
  // second tree that any derivation cycle A ⇒+ A creates.
  function parseTrees(G, w, max) {
    max = max || 2;
    const N = info(G).N, byA = info(G).byA, n = w.length;
    // D[A][i][j]: A ⇒* w[i..j) (least fixpoint, handles ε and unit rules)
    const D = new Map(G.nonterminals.map((A) => [A, Array.from({ length: n + 1 }, () => new Array(n + 1).fill(false))]));
    const der = (X, i, j) => (N.has(X) ? D.get(X)[i][j] : j === i + 1 && w[i] === X);
    let changed = true;
    const seqOK = (rhs, k, i, j) => {   // rhs[k..] ⇒* w[i..j)
      if (k === rhs.length) return i === j;
      for (let m = i; m <= j; m++) if (der(rhs[k], i, m) && seqOK(rhs, k + 1, m, j)) return true;
      return false;
    };
    while (changed) {
      changed = false;
      for (const p of G.productions) {
        if (p.A === null) continue;
        const t = D.get(p.A);
        for (let i = 0; i <= n; i++) for (let j = i; j <= n; j++) if (!t[i][j] && seqOK(p.rhs, 0, i, j)) { t[i][j] = true; changed = true; }
      }
    }
    if (!N.has(G.start) || !D.get(G.start)[0][n]) return [];
    // eager search with a cap, so the path counts are always those of the current branch
    const onPath = new Map();
    function node(A, i, j) {
      const k = A + '\u0001' + i + '\u0001' + j, c = onPath.get(k) || 0, out = [];
      if (c >= 2) return out;
      onPath.set(k, c + 1);
      for (const p of byA.get(A)) {
        if (out.length >= max) break;
        if (!seqOK(p.rhs, 0, i, j)) continue;
        for (const kids of seq(p.rhs, 0, i, j)) { out.push({ sym: A, prod: p.id, children: kids }); if (out.length >= max) break; }
      }
      onPath.set(k, c);
      return out;
    }
    function seq(rhs, k, i, j) {
      if (k === rhs.length) return i === j ? [[]] : [];
      const out = [];
      for (let m = i; m <= j && out.length < max; m++) {
        if (!der(rhs[k], i, m) || !seqOK(rhs, k + 1, m, j)) continue;
        const firsts = N.has(rhs[k]) ? node(rhs[k], i, m) : [leaf(rhs[k])];
        if (!firsts.length) continue;
        const rests = seq(rhs, k + 1, m, j);
        for (const f of firsts) for (const r of rests) { if (out.length >= max) break; out.push([f].concat(r)); }
      }
      return out;
    }
    return node(G.start, 0, n).map((t) => JSON.parse(JSON.stringify(t)));
  }

  // ---------- ambiguity search ----------
  // Tries words of the language in order of length and returns the first with two different trees.
  function ambiguity(G, n, opts) {
    opts = Object.assign({ traceLimit: 200 }, opts || {});
    const trace = [];
    const words = language(G, n);
    for (const w of words) {
      const ts = parseTrees(G, w, 2);
      if (ts.length >= 2) {
        trace.push({ kind: 'found', word: w, say: show(w) + ' has two different parse trees, so the grammar is ambiguous.' });
        const d1 = derivationOf(G, ts[0], 'leftmost'), d2 = derivationOf(G, ts[1], 'leftmost');
        return { ambiguous: true, word: w, trees: ts, derivations: [d1, d2], trace };
      }
      if (trace.length < opts.traceLimit) trace.push({ kind: 'try', word: w, trees: ts.length, say: show(w) + ' has exactly one parse tree.' });
    }
    trace.push({ kind: 'none', say: 'No word of length ≤ ' + n + ' has two parse trees; the grammar may still be ambiguous on longer words.' });
    return { ambiguous: false, word: null, trees: [], words: words.length, trace };
  }

  // ---------- random grammars (tests and exercises) ----------
  // rand() → [0, 1). opts: nonterminals, terminals, maxRules per nonterminal, maxLen of a right side, eps.
  function random(rand, opts) {
    opts = Object.assign({ nonterminals: 3, terminals: ['a', 'b'], maxRules: 3, maxLen: 3, eps: 0.15 }, opts || {});
    const Ns = 'SABCDEFGH'.slice(0, opts.nonterminals).split('');
    const prods = [];
    const int = (k) => Math.floor(rand() * k);
    for (const A of Ns) {
      const k = 1 + int(opts.maxRules);
      for (let r = 0; r < k; r++) {
        if (rand() < opts.eps) { prods.push([A, []]); continue; }
        const len = 1 + int(opts.maxLen), rhs = [];
        for (let i = 0; i < len; i++) rhs.push(rand() < 0.45 ? Ns[int(Ns.length)] : opts.terminals[int(opts.terminals.length)]);
        prods.push([A, rhs]);
      }
    }
    // drop exact duplicate rules
    const seen = new Set(), uniq = prods.filter((p) => { const k = p[0] + '>' + p[1].join(' '); if (seen.has(k)) return false; seen.add(k); return true; });
    return make('S', uniq, { nonterminals: Ns, terminals: opts.terminals });
  }

  T.grammar = {
    EPS, END, GrammarError, NAME,
    make, derive, parse, tryParse, toString, info, isN, input,
    show, showSym, showRhs, showProd,
    nullableSet, minLengths, generatingSet, reachableSet,
    classify, options, rewrite, replay, derivationOf, treeOf,
    leaf, yieldOf, treeKey, treeSize, treeDepth, checkTree,
    coder, languageSets, language, allWords, generate, parseTrees, ambiguity, random,
  };
})();
