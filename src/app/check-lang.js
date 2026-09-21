// Languages for checking answers, and the regex and grammar checkers. A language here is what a checker
// can ask about: {alphabet, fa (a finite automaton, when the language is known to be regular), has(word)
// (true, false or null when a machine gives no answer in time), words(n) (a set of keys, for grammars)}.
// Two languages are compared exactly when both have an automaton (FA.equivalent gives the shortest
// counterexample), otherwise on every word up to a length chosen so that a few thousand words are tried.
// Words are arrays of symbols, so a grammar's terminals may be longer than one character.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = (T.Check = T.Check || {});
  K.kinds = K.kinds || {};
  const KEY = '\u0001';
  const key = (w) => w.join(KEY);
  /** A word for people: ε, ab, or id + id when symbols are longer than one character */
  const showWord = (w) => (!w.length ? 'ε' : w.every((s) => [...s].length === 1) ? w.join('') : w.join(' '));
  K.showWord = showWord;
  const toWord = (w) => (Array.isArray(w) ? w : [...String(w)]);
  const CAP = 3000;

  /** Every word over the alphabet up to length n (shortlex), where n is as long as the cap allows */
  K.words = function (sigma, maxLen, cap) {
    cap = cap || CAP;
    const out = [[]];
    let layer = [[]];
    for (let n = 1; n <= maxLen; n++) {
      if (out.length + layer.length * sigma.length > cap) break;
      const next = [];
      for (const w of layer) for (const a of sigma) next.push(w.concat([a]));
      out.push(...next);
      layer = next;
    }
    return out;
  };

  // ---- languages from what an exercise or an answer gives ------------------------------------------------
  K.lang = {
    regex(text, sigma) {
      const c = T.RE.check(text);
      if (!c.ok) throw new Error('the expression cannot be read: ' + c.error);
      const used = T.RE.alphabet(c.ast);
      const alphabet = [...new Set([...(sigma || []), ...used])].sort();
      const fa = T.RE.thompson(c.ast, { alphabet }).fa;
      return K.lang.fromFA(fa, alphabet, { used, size: T.RE.size(c.ast) });
    },
    fromFA(fa, alphabet, extra) {
      const acc = T.FA.acceptor(fa);
      return Object.assign({ alphabet: alphabet || fa.alphabet, fa, has: (w) => acc(toWord(w)) }, extra || {});
    },
    grammar(text) {
      const G = T.grammar.parse(text);
      if (G.productions.some((p) => p.A === null)) throw new Error('every rule needs one nonterminal on its left side');
      const L = { alphabet: G.terminals.slice(), grammar: G, fa: null };
      const cls = T.grammar.classify(G);
      try {
        if (cls.rightLinear) L.fa = T.FA.make(T.cfg.rightLinearToNFA(G).nfa);
        else if (cls.leftLinear) L.fa = T.FA.make(T.cfg.leftLinearToNFA(G).nfa);
      } catch (e) { L.fa = null; }
      // all the words up to n at once: far quicker than parsing each one
      const memo = new Map();
      L.words = (n) => { if (!memo.has(n)) memo.set(n, new Set(T.grammar.language(G, n).map(key))); return memo.get(n); };
      L.has = (w) => { w = toWord(w); return L.words(w.length).has(key(w)); };
      return L;
    },
    machine(text, opts) {
      opts = opts || {};
      const m = T.Machine.parse(text);
      const core = T.Machine.toCore(m);
      if (!core || core.error) throw new Error((core && core.error) || 'the machine cannot be run');
      const alphabet = T.Machine.alphabet(m);
      if (core.fa) return K.lang.fromFA(core.fa, alphabet, { machine: m });
      if (core.pda) {
        return { alphabet, machine: m, fa: null, has: (w) => { const r = T.pda.accepts(core.pda, toWord(w), opts.pda); return r.accepted ? true : r.complete ? false : null; } };
      }
      const steps = opts.steps || 5000;
      const L = { alphabet, machine: m, fa: null, tm: core.tm };
      L.run = (w) => T.tm.run(core.tm, toWord(w).join(''), { maxSteps: steps, trace: false });
      L.has = (w) => { const r = L.run(w); return r.halted ? r.accepted : null; };
      return L;
    },
    member(fn, alphabet) { return { alphabet, fa: null, has: (w) => !!fn(toWord(w).join('')) }; },
    /** The reference language of an exercise: ref in its own kind or as {regex | machine | grammar | member} */
    ref(x, ownKind) {
      const sigma = K.alphabet(x.alphabet);
      const r = x.ref;
      let L;
      if (r === undefined || r === null) { if (!x.member) throw new Error('the exercise gives no reference language'); L = K.lang.member(x.member, sigma); }
      else if (typeof r === 'string') L = ownKind === 'regex' ? K.lang.regex(r, sigma) : ownKind === 'grammar' ? K.lang.grammar(r) : K.lang.machine(r, x);
      else if (r.regex !== undefined) L = K.lang.regex(r.regex, sigma);
      else if (r.grammar !== undefined) L = K.lang.grammar(r.grammar);
      else if (r.machine !== undefined) L = K.lang.machine(r.machine, x);
      else if (r.member) L = K.lang.member(r.member, sigma);
      else throw new Error('the reference language is not understood');
      if (sigma) L.alphabet = [...new Set([...sigma, ...L.alphabet])];
      if (!L.alphabet || !L.alphabet.length) L.alphabet = sigma || ['a', 'b'];
      return L;
    },
  };

  /**
   * Compare the student's language A with the reference R: {equal, exact, counterexample (a word), inA,
   * tested, undecided}. inA says the counterexample is in A (and not in R).
   */
  K.compare = function (A, R, opts) {
    opts = opts || {};
    const sigma = [...new Set([...(R.alphabet || []), ...(A.alphabet || [])])].sort();
    if (A.fa && R.fa) {
      const a = T.FA.make(Object.assign({}, A.fa, { alphabet: sigma })), b = T.FA.make(Object.assign({}, R.fa, { alphabet: sigma }));
      const r = T.FA.equivalent(a, b);
      if (r.equal) return { equal: true, exact: true };
      const w = toWord(r.counterexample || '');
      return { equal: false, exact: true, counterexample: w, inA: r.acceptedBy === 'A' };
    }
    const maxLen = opts.maxLen ?? 10;
    const base = K.words(sigma, maxLen, opts.cap), upTo = base[base.length - 1].length;
    const list = base.concat((opts.tests || []).map(toWord));
    let undecided = 0, tested = 0;
    for (const w of list) {
      const a = A.has(w), r = R.has(w);
      if (a === null || r === null) { undecided++; continue; }
      tested++;
      if (a !== r) return { equal: false, exact: false, counterexample: w, inA: a, tested, undecided };
    }
    return { equal: true, exact: false, tested, undecided, upTo };
  };
  /** The verdict sentence for a comparison, in terms of what the student built ("Your expression") */
  K.verdict = function (c, what, extra, verbs) {
    verbs = verbs || ['accepts', 'does not accept'];
    if (c.equal) {
      if (c.exact) return { ok: true, message: what + ' describes exactly the right language.' + (extra || '') };
      return { ok: true, message: what + ' agrees with the language on all ' + c.tested + ' strings up to length ' + c.upTo + (c.undecided ? ' (' + c.undecided + ' gave no answer in time)' : '') + '.' + (extra || '') };
    }
    const w = showWord(c.counterexample);
    return { ok: false, counterexample: w, message: c.inA ? what + ' ' + verbs[0] + ' ' + w + ', which is not in the language.' : what + ' ' + verbs[1] + ' ' + w + ', which is in the language.' };
  };

  // ---- regular expressions ----------------------------------------------------------------------------------
  K.kinds.regex = {
    check(x, a) {
      if (!a || !String(a).trim()) return { ok: false, message: 'Write an expression first.' };
      let A;
      try { A = K.lang.regex(String(a).trim(), null); } catch (e) { return { ok: false, message: e.message.replace(/^./, (c) => c.toUpperCase()) + '.' }; }
      const R = K.lang.ref(x, 'regex');
      const sigma = K.alphabet(x.alphabet) || R.alphabet;
      const bad = A.used.filter((s) => !sigma.includes(s));
      if (bad.length) return { ok: false, message: 'Your expression uses ' + bad.join(', ') + ', which ' + (bad.length > 1 ? 'are' : 'is') + ' not in the alphabet {' + sigma.join(', ') + '}.' };
      if (x.maxSize && A.size > x.maxSize) return { ok: false, message: 'Your expression has ' + A.size + ' parts; this exercise asks for at most ' + x.maxSize + '.' };
      return K.verdict(K.compare(A, R, x), 'Your expression', '', ['matches', 'does not match']);
    },
  };

  // ---- grammars ---------------------------------------------------------------------------------------------
  /** The forms a grammar exercise may ask for (form: one of these, or a list): a sentence when the grammar is not in it */
  const FORMS = K.grammarForms = {
    cnf: (G) => (T.cfg.isCNF(G) ? null : 'Your grammar is not in Chomsky normal form: every rule must be A → B C or A → a; only the start symbol may have S → ε, and then it may not appear on any right side.'),
    gnf: (G) => (T.cfg.isGNF(G) ? null : 'Your grammar is not in Greibach normal form: every rule must start with one terminal followed only by nonterminals (A → a B C …), and only the start symbol may have an ε-rule, when it appears on no right side.'),
    noleftrec: (G) => { const r = T.cfg.leftRecursive(G); return r && r.length ? 'Your grammar is still left-recursive: ' + r.map((x) => x.A || x.nonterminal || x).filter((v) => typeof v === 'string').join(', ') + ' can derive a form that starts with itself.' : null; },
    noeps: (G) => (G.productions.some((p) => p.rhs.length === 0) ? 'Your grammar still has an ε-rule; this exercise asks for none at all.' : null),
    'right-linear': (G) => (T.grammar.classify(G).rightLinear ? null : 'Your grammar is not right-linear: every rule must be A → w B or A → w, with at most one nonterminal, at the right end.'),
    unambiguous: (G, x) => { const r = T.grammar.ambiguity(G, x.ambLen || 7); return r.ambiguous ? 'Your grammar is ambiguous: ' + K.showWord(r.word) + ' has two different parse trees.' : null; },
  };
  K.kinds.grammar = {
    // older content wrapped the checker to add forms and x.also; these flags tell it the checker does that now
    cfForms: true, withAlso: true,
    check(x, a) {
      if (!a || !String(a).trim()) return { ok: false, message: 'Write a grammar first.' };
      let A;
      try { A = K.lang.grammar(String(a)); } catch (e) { return { ok: false, message: 'The grammar cannot be read: ' + (e.line ? 'line ' + e.line + ': ' : '') + e.message + '.' }; }
      const R = K.lang.ref(x, 'grammar');
      const sigma = K.alphabet(x.alphabet) || R.alphabet;
      const bad = A.alphabet.filter((s) => !sigma.includes(s));
      if (bad.length) return { ok: false, message: 'Your grammar has the terminal' + (bad.length > 1 ? 's ' : ' ') + bad.join(', ') + ', not in the alphabet {' + sigma.join(', ') + '}. (Nonterminals start with a capital letter.)' };
      for (const f of [].concat(x.form || [])) {
        const rule = FORMS[f];
        if (!rule) return { ok: false, message: 'The exercise asks for an unknown form, ' + f + '.' };
        const why = rule(A.grammar, x);
        if (why) return { ok: false, message: why };
      }
      const c = K.compare(A, R, Object.assign({ maxLen: 8 }, x, { cap: x.cap || 1500 }));
      const v = K.verdict(c, 'Your grammar', c.equal && !c.exact ? ' (Grammars cannot be compared exactly in general, so this checks every string up to that length.)' : '', ['generates', 'does not generate']);
      // a requirement beyond the language (it must be LL(1), say): x.also(G) gives a sentence when it falls short
      if (v.ok && typeof x.also === 'function') { const why = x.also(A.grammar); if (why) return { ok: false, message: why }; }
      return v;
    },
  };
})();
