// Checking exercise answers. T.Check.answer(exercise, answer) -> {ok, message, counterexample?, details?, cells?}
// runs the checker of the exercise's kind. Each kind and the fields an exercise of that kind has:
//
//   machine   machine: 'dfa'|'nfa'|'pda'|'tm', ref (the language: see below), alphabet, maxStates, maxLen,
//             tests: [strings that are always tried], steps (a TM's step limit), output: w => string (a TM
//             that computes; then the answer must halt with that output), start (the editor's first text).
//             Answer: machine text. Finite automata are checked by equivalence with a counterexample; PDAs
//             and TMs by running every string up to maxLen (and the tests) against the reference.   check-machine.js
//             acceptBy: 'empty' | 'final' (a PDA must accept that way).
//   regex     ref, alphabet, maxLen, maxSize. Answer: an expression. Checked by equivalence.          check-lang.js
//   grammar   ref, alphabet, maxLen, form: 'cnf'|'gnf'|'noleftrec'|'noeps'|'right-linear'|'unambiguous'
//             (or a list; ambLen bounds the search for two trees), also(G) -> sentence | null. Answer:
//             grammar text. Checked by bounded enumeration, and exactly when both sides are regular (right-
//             or left-linear grammars, regexes, finite automata).                                    check-lang.js
//   table     table: 'first'|'follow'|'ll1'|'cyk'|'custom', grammar, word (cyk), rows, cols, cells
//             (custom: {key: expected}), show: {grammar | machine | regex} (what a custom table is about,
//             shown above it). Answer: {key: text}. Checked cell by cell.                           check-table.js
//   choice    options: [..], answer: index | [indexes] (several right). Answer: index or [indexes].
//   string    answer: 'text' | ['text', ...], or accept(text) -> true | false | 'why not' | {ok, why};
//             set: true compares as sets {a, b}; caseless: true; placeholder (the empty box's hint).
//             Answer: text.
//   number    answer, tolerance. Answer: a number (or its text).
//   set       answer: '{a, b}' | '(1, 2), (2, 3)' | '{{a, b}, {c}}' (or several), or accept(value, canonical)
//             -> true | false | 'why not' | {ok, why}; placeholder.
//             Sets, pairs (a-b too), tuples and partitions at any depth, compared as sets. Answer: text.
//   pumping   lang: an id of T.Pump.catalogue (regular lemma) or of T.cfpump.catalogue (cf: true), p.
//             Answer: {s, i}: the string chosen, and the i used against the computer's split.
//
// The language of ref may be given as text of the answer's own kind (ref: 'start q0 ...'), or as
// {regex}, {machine}, {grammar} or {member: w => bool} (then alphabet is needed); member may be added to
// a ref too, and tools/check-content.mjs then checks that the two agree.
// Every exercise also has solution (an answer that must pass), wrong: [answers that must fail] and hints.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = (T.Check = T.Check || {});
  K.kinds = K.kinds || {};

  const show = (w) => (w === '' ? 'ε' : w);
  K.show = show;
  K.plural = (n, w, ws) => n + ' ' + (n === 1 ? w : ws || w + 's');
  /** The alphabet of an exercise as a list of symbols ('ab' or ['a', 'b']) */
  K.alphabet = (a) => (!a ? null : Array.isArray(a) ? a.slice() : [...String(a)].filter((c) => !/[\s,]/.test(c)));

  K.answer = function (x, a) {
    const kind = K.kinds[x.kind];
    if (!kind) return { ok: false, message: 'This exercise has an unknown kind, ' + x.kind + '.' };
    try { return kind.check(x, a); } catch (e) { return { ok: false, message: 'Your answer could not be checked: ' + (e.message || e) + '.' }; }
  };
  /** Is the answer empty (nothing typed or chosen)? */
  K.blank = (a) => a === undefined || a === null || (typeof a === 'string' && !a.trim()) || (Array.isArray(a) && !a.length);

  // ---- multiple choice ---------------------------------------------------------------------------------
  K.kinds.choice = {
    check(x, a) {
      const want = [].concat(x.answer).map(Number).sort();
      const got = [].concat(a === undefined || a === null ? [] : a).map(Number).sort();
      if (!got.length) return { ok: false, message: 'Choose ' + (want.length > 1 ? 'the right options' : 'an option') + ' first.' };
      if (want.length === got.length && want.every((v, i) => v === got[i])) return { ok: true, message: 'Right.' + (x.why ? ' ' + x.why : '') };
      if (want.length > 1) {
        const right = got.filter((v) => want.includes(v)).length;
        return { ok: false, message: 'Not quite: ' + right + ' of your choices ' + (right === 1 ? 'is' : 'are') + ' right, and ' + K.plural(want.length, 'option is', 'options are') + ' right in all.' };
      }
      const why = x.whyNot && x.whyNot[got[0]];
      return { ok: false, message: 'Not quite.' + (why ? ' ' + why : '') };
    },
  };

  // ---- a string or a number ------------------------------------------------------------------------------
  const norm = (s, x) => {
    let t = String(s === undefined || s === null ? '' : s).trim().replace(/\s+/g, ' ');
    if (/^(eps|epsilon|ε|λ)$/i.test(t) || t === '""') t = 'ε';
    if (x.caseless) t = t.toLowerCase();
    return t;
  };
  const asSet = (s) => String(s).replace(/^\s*\{|\}\s*$/g, '').split(/[\s,]+/).filter(Boolean).map((v) => (/^(eps|epsilon|λ)$/i.test(v) ? 'ε' : v)).filter((v) => v !== '∅').sort();
  K.asSet = asSet;
  /** What an accept hook said, as a result: true, false, a sentence saying why not, or {ok, why} */
  K.accepted = function (x, r) {
    if (r && typeof r === 'object') return r.ok ? { ok: true, message: 'Right.' + (r.why ? ' ' + r.why : x.why ? ' ' + x.why : '') } : { ok: false, message: r.why || (x.whyNot ? x.whyNot : 'Not quite.') };
    if (typeof r === 'string') return { ok: false, message: r };
    return r ? { ok: true, message: 'Right.' + (x.why ? ' ' + x.why : '') } : { ok: false, message: x.whyNot ? x.whyNot : 'Not quite.' };
  };
  K.kinds.string = {
    check(x, a) {
      if (K.blank(a)) return { ok: false, message: 'Type an answer first (ε for the empty string).' };
      let ok;
      if (x.accept) return K.accepted(x, x.accept(norm(a, x) === 'ε' ? '' : norm(a, x)));
      else if (x.set) { const g = asSet(a).join(','); ok = [].concat(x.answer).some((w) => asSet(w).join(',') === g); }
      else { const g = norm(a, x).replace(/\s/g, x.spaces ? ' ' : ''); ok = [].concat(x.answer).some((w) => norm(w, x).replace(/\s/g, x.spaces ? ' ' : '') === g); }
      return ok ? { ok: true, message: 'Right.' + (x.why ? ' ' + x.why : '') } : { ok: false, message: 'Not quite.' + (x.whyNot ? ' ' + x.whyNot : '') };
    },
  };
  K.kinds.number = {
    check(x, a) {
      if (K.blank(a)) return { ok: false, message: 'Type a number first.' };
      const v = typeof a === 'number' ? a : Number(String(a).trim().replace(/,/g, ''));
      if (!Number.isFinite(v)) return { ok: false, message: String(a).trim() + ' is not a number.' };
      const ok = Math.abs(v - x.answer) <= (x.tolerance || 0);
      return ok ? { ok: true, message: 'Right.' + (x.why ? ' ' + x.why : '') } : { ok: false, message: 'Not quite' + (x.higherLower ? (v < x.answer ? ': it is more than ' + v : ': it is less than ' + v) : '') + '.' };
    },
  };


  // ---- sets, pairs, tuples and partitions -------------------------------------------------------------------
  /**
   * Read set notation: {a, b}, (1, 2) and ⟨1, 2⟩ for tuples, a-b (or a→b) for a pair, ∅ or {} for the empty
   * set, and sets of these at any depth, so a partition is {{a, b}, {c}}. Items are separated by commas (or
   * spaces). Several items with no braces round them are read as a set: (a,b), (b,c) is a relation.
   * Returns {v} with v = {t: 'set'|'tuple', items} or {t: 'atom', v}, or {error: 'a sentence'}.
   */
  K.parseValue = function (text, opts) {
    opts = opts || {};
    const src = String(text === undefined || text === null ? '' : text).trim();
    if (!src) return { error: 'The answer is empty.' };
    const OPEN = { '{': '}', '(': ')', '[': ']', '⟨': '⟩', '<': '>' };
    const CLOSE = new Set(Object.values(OPEN));
    let i = 0;
    const atom = (raw) => {
      let a = raw.trim().replace(/^["']|["']$/g, '');
      if (/^(eps|epsilon|λ|ε|"")$/i.test(a)) a = 'ε';
      if (a === '∅') return { t: 'set', items: [] };
      const pair = opts.dash !== false && /^([^\s\-→]+)\s*(?:-|→|->)\s*([^\s\-→>]+)$/.exec(a);
      if (pair) return { t: 'tuple', items: [{ t: 'atom', v: pair[1] }, { t: 'atom', v: pair[2] }] };
      return { t: 'atom', v: a };
    };
    function list(close) {
      const items = [];
      let cur = '';
      const flush = () => { if (cur.trim()) for (const w of cur.trim().split(/\s+(?![-→]|->)(?<![-→]\s*|->\s*)/)) if (w) items.push(atom(w)); cur = ''; };
      while (i < src.length) {
        const c = src[i];
        if (OPEN[c] && !(c === '<' && src[i + 1] === '-')) {
          if (cur.trim()) throw new Error('"' + cur.trim() + c + '" needs a comma before the ' + c);
          i++;
          const inner = list(OPEN[c]);
          items.push({ t: c === '{' ? 'set' : 'tuple', items: inner });
          continue;
        }
        if (CLOSE.has(c) && !(c === '>' && (src[i - 1] === '-'))) {
          if (c !== close) throw new Error(close ? 'a ' + c + ' closes what was opened with the bracket that needs ' + close : 'there is a ' + c + ' with nothing to close');
          flush(); i++; return items;
        }
        if (c === ',' || c === ';') { flush(); i++; continue; }
        cur += c; i++;
      }
      if (close) throw new Error('a bracket is opened but never closed: add ' + close);
      flush();
      return items;
    }
    try {
      const top = list(null);
      if (!top.length) return { error: 'There is nothing between the brackets to read; write ∅ or {} for the empty set.' };
      return { v: top.length === 1 && !opts.topSet ? top[0] : { t: 'set', items: top } };
    } catch (e) { return { error: 'This cannot be read: ' + e.message + '.' }; }
  };
  /** A value in one canonical text: sets sorted with repeats dropped, tuples in their order */
  K.canonValue = function canon(v, caseless) {
    if (v.t === 'atom') return caseless ? v.v.toLowerCase() : v.v;
    const parts = v.items.map((x) => canon(x, caseless));
    if (v.t === 'tuple') return '(' + parts.join(',') + ')';
    return '{' + [...new Set(parts)].sort().join(',') + '}';
  };
  const asTop = (v) => (v.t === 'set' ? v : { t: 'set', items: [v] });
  K.kinds.set = {
    check(x, a) {
      if (K.blank(a)) return { ok: false, message: 'Type an answer first, like {a, b}, (1, 2) or {{a, b}, {c}}.' };
      const got = K.parseValue(a, x);
      if (got.error) return { ok: false, message: got.error };
      if (x.accept) return K.accepted(x, x.accept(got.v, K.canonValue(got.v)));
      const g = K.canonValue(got.v, x.caseless);
      const wants = [].concat(x.answer).map((w) => K.parseValue(w, x)).filter((w) => !w.error).map((w) => w.v);
      if (wants.some((w) => K.canonValue(w, x.caseless) === g)) return { ok: true, message: 'Right.' + (x.why ? ' ' + x.why : '') };
      // say how far off, without giving the answer away
      const w = wants[0];
      if (!w) return { ok: false, message: 'The exercise has no readable answer.' };
      if (w.t === 'tuple') {
        const same = got.v.t === 'tuple' && K.canonValue({ t: 'set', items: got.v.items }) === K.canonValue({ t: 'set', items: w.items });
        return { ok: false, message: same ? 'Not quite: the parts are right, but in a tuple their order matters.' : 'Not quite.' + (x.whyNot ? ' ' + x.whyNot : '') };
      }
      const A = new Set(asTop(w).items.map((v) => K.canonValue(v, x.caseless))), B = new Set(asTop(got.v).items.map((v) => K.canonValue(v, x.caseless)));
      const missing = [...A].filter((v) => !B.has(v)).length, extra = [...B].filter((v) => !A.has(v)).length;
      const thing = w.t === 'set' && w.items.length && w.items.every((v) => v.t === 'set') ? ['block', 'blocks'] : w.t === 'set' && w.items.length && w.items.every((v) => v.t === 'tuple') ? ['pair', 'pairs'] : ['element', 'elements'];
      const bits = [];
      if (missing) bits.push(K.plural(missing, thing[0], thing[1]) + (missing === 1 ? ' is' : ' are') + ' missing');
      if (extra) bits.push(K.plural(extra, thing[0], thing[1]) + (extra === 1 ? ' does' : ' do') + ' not belong');
      return { ok: false, message: 'Not quite' + (bits.length ? ': ' + bits.join(', and ') : '') + '.', details: x.whyNot ? [x.whyNot] : [] };
    },
  };

  // ---- the pumping game -----------------------------------------------------------------------------------
  /**
   * Play the game for an answer {s, i}: the computer picks p, takes s, splits it the way hardest for the
   * student, then pumps with i. Returns {ok, message, p, split, steps: [say]}. With no i, s must beat every
   * split. The view plays the same game move by move with K.pumpGame.
   */
  K.pumpGame = function (x) {
    if (x.cf) {
      const g = T.cfpump.game(x.lang, { p: x.p });
      return {
        cf: true, p: g.p, lang: g.lang, game: g,
        word(s) { return g.chooseWord(s); },
        split() {
          g.adversaryMove();
          // cornered (no split survives every i): offer the split that survives the most i, so the student
          // still has to find the i that breaks it
          if (!g.search.survives) {
            const L = g.lang, top = L.iMax ? L.iMax(g.word) : 3, range = [];
            for (let i = 0; i <= Math.max(3, top); i++) if (i !== 1) range.push(i);
            // ties (often every split survives no i at all) go to the split that looks most like a real
            // answer: v and y both present, as long as possible, and in the middle of the word
            const mid = g.word.length / 2;
            const score = (d) => [range.filter((i) => L.member(T.cfpump.pump(d, i))).length, (d.v ? 1 : 0) + (d.y ? 1 : 0), d.v.length + d.y.length, -Math.abs(d.at[1] + (d.x.length / 2) - mid)];
            const better = (a, b) => { for (let k = 0; k < a.length; k++) if (a[k] !== b[k]) return a[k] > b[k]; return false; };
            let best = null, bs = null;
            for (const d of T.cfpump.splits(g.word, g.p)) { const sc = score(d); if (!bs || better(sc, bs)) { best = d; bs = sc; } }
            if (best) g.setSplit(best);
          }
          const d = g.split; return { parts: [['u', d.u], ['v', d.v], ['x', d.x], ['y', d.y], ['z', d.z]], survives: g.search.survives, say: g.trace[g.trace.length - 1].say }; },
        pump(i) { const r = g.chooseI(i); return { win: r.studentWins, pumped: r.pumped, say: g.trace[g.trace.length - 1].say }; },
        beatsAll(s) { return !T.cfpump.adversarySplit(x.lang, s, g.p).survives; },
      };
    }
    const g = T.Pump.game(x.lang);
    g.pickP(x.p);
    return {
      cf: false, p: g.p, lang: g.lang, game: g,
      word(s) { return g.pickString(s); },
      split() { const r = g.pickSplit(); return { parts: [['x', r.x], ['y', r.y], ['z', r.z]], survives: r.survives, say: r.say }; },
      pump(i) { const r = g.pickI(i); return { win: r.winner === 'student', pumped: r.pumped, say: r.say }; },
      beatsAll(s) { return T.Pump.wins(x.lang, g.p, s).wins; },
    };
  };
  K.kinds.pumping = {
    check(x, a) {
      a = a || {};
      const s = a.s === undefined || a.s === null ? '' : String(a.s).trim().replace(/^ε$/, '');
      if (!s && a.s !== '') return { ok: false, message: 'Choose a string s first.' };
      const G = K.pumpGame(x);
      const w = G.word(s);
      if (!w.ok) return { ok: false, message: w.say };
      if (a.i === undefined || a.i === null || a.i === '') {
        return G.beatsAll(s) ? { ok: true, message: show(s) + ' defeats every way of splitting it: whatever the split, some i pumps it out of the language.' }
          : { ok: false, message: 'Some split of ' + show(s) + ' survives every i that was tried, so this string cannot win. Try a string that pins the pumped part down.' };
      }
      const sp = G.split();
      const i = Number(a.i);
      if (!Number.isInteger(i) || i < 0) return { ok: false, message: 'i is a whole number, 0 or more.' };
      const r = G.pump(i);
      const split = sp.parts.map(([k, v]) => k + ' = ' + show(v)).join(', ');
      if (r.win) return { ok: true, message: 'The computer split s as ' + split + '. ' + r.say };
      return { ok: false, message: 'The computer split s as ' + split + '. ' + r.say + (sp.survives ? ' This split survives every i tried, so no i wins against it: a different s is needed.' : ' Another i would win against this split.') };
    },
  };
})();
