// Checking a machine the student built against an exercise: a DFA or NFA by equivalence with the
// reference (exact, with the shortest counterexample); a PDA by running every string up to a length on
// both (equivalence of PDAs is undecidable); a TM by running it on every string up to a length, with a
// step limit, and for a TM that computes, comparing what it leaves on the tape.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = (T.Check = T.Check || {});
  K.kinds = K.kinds || {};
  const NAME = { dfa: 'a DFA', nfa: 'a finite automaton', pda: 'a PDA', tm: 'a Turing machine' };

  K.kinds.machine = {
    cfAccept: true, // older content wrapped the checker to add acceptBy; this tells it the checker does it now
    check(x, a) {
      if (!a || !String(a).trim()) return { ok: false, message: 'Build a machine first.' };
      const M = T.Machine;
      // a TM in the engine's own text (several tapes, output: directives) or in the macro language
      if ((x.machine || 'nfa') === 'tm' && (x.format === 'text' || x.format === 'macro' || (x.tapes || 1) > 1)) return tmTextCheck(x, String(a));
      let m;
      try { m = M.parse(String(a)); } catch (e) { return { ok: false, message: 'The machine cannot be read: ' + e.message + '.' }; }
      const want = x.machine || 'nfa';
      const fa = m.kind === 'dfa' || m.kind === 'nfa';
      if ((want === 'dfa' || want === 'nfa') !== fa || ((want === 'pda' || want === 'tm') && m.kind !== want)) return { ok: false, message: 'This exercise asks for ' + NAME[want] + ', and this is ' + NAME[m.kind] + '.' };
      if (want === 'dfa' && !M.isDeterministic(m)) {
        const eps = M.moves(m).find((v) => v.sym === '');
        return { ok: false, message: eps ? 'A DFA has no ε-moves, and ' + eps.from + ' has one.' : 'A DFA has at most one move for each state and symbol; ' + dupOf(m) + '.' };
      }
      if (want === 'dfa' && x.complete && !isComplete(m, K.alphabet(x.alphabet) || M.alphabet(m))) return { ok: false, message: 'This exercise asks for a complete DFA: every state needs a move on every symbol (add a dead state for the missing ones).' };
      if (want === 'pda' && x.acceptBy && (m.acceptBy || 'final') !== x.acceptBy) return { ok: false, message: x.acceptBy === 'empty' ? 'This exercise asks for acceptance by empty stack: add the line accept-by empty, and let the machine empty its stack exactly when the word is in the language.' : 'This exercise asks for acceptance by final state: remove accept-by empty and mark the accepting states.' };
            if (x.maxStates && m.states.length > x.maxStates) return { ok: false, message: 'Your machine has ' + m.states.length + ' states; this exercise asks for at most ' + x.maxStates + '.' };
      // a TM that computes needs no reference language: its output is compared instead
      const R = want === 'tm' && x.output ? null : K.lang.ref(x, 'machine');
      const sigma = K.alphabet(x.alphabet) || (R ? R.alphabet : T.Machine.alphabet(m));
      const used = M.alphabet(m).filter((s) => !(want === 'tm' && x.tape && x.tape.includes(s)));
      if (want !== 'tm') { const bad = used.filter((s) => !sigma.includes(s)); if (bad.length) return { ok: false, message: 'Your machine reads ' + bad.join(', ') + ', which ' + (bad.length > 1 ? 'are' : 'is') + ' not in the alphabet {' + sigma.join(', ') + '}.' }; }
      let A;
      try { A = K.lang.machine(String(a), x); } catch (e) { return { ok: false, message: 'Your machine cannot run: ' + e.message + '.' }; }
      A.alphabet = sigma;
      if (want === 'tm') return tmCheck(x, A, R, sigma);
      const c = K.compare(A, R, Object.assign({ maxLen: want === 'pda' ? 7 : 10 }, x, { tests: x.tests }));
      const why = want === 'pda' ? ' (Two PDAs cannot be compared exactly in general, so this runs every string up to that length.)' : ' (The language is given by a test rather than a machine, so this runs every string up to that length.)';
      return K.verdict(c, 'Your machine', c.equal && !c.exact ? why : '');
    },
  };
  function dupOf(m) {
    const seen = new Map();
    for (const v of T.Machine.moves(m)) { const k = v.from + '\u0000' + v.sym; if (seen.has(k)) return v.from + ' has two moves on ' + v.sym; seen.set(k, 1); }
    return 'one state has two moves on the same symbol';
  }
  function isComplete(m, sigma) {
    const mv = T.Machine.moves(m);
    return m.states.every((q) => sigma.every((a) => mv.some((v) => v.from === q && v.sym === a)));
  }

  /** A TM written in the engine's text format (any number of tapes) or the macro language */
  function tmTextCheck(x, text) {
    let tm;
    if (x.format === 'macro') {
      const r = T.tmMacro.compile(text);
      if (r.errors.length || !r.machine) return { ok: false, message: 'The program cannot be compiled: ' + (r.errors[0] ? (r.errors[0].line ? 'line ' + r.errors[0].line + ': ' : '') + (r.errors[0].msg || r.errors[0]) : 'no machine') + '.' };
      tm = r.machine;
    } else {
      const r = T.tm.parse(text);
      if (r.errors.length) return { ok: false, message: 'The machine cannot be read: line ' + r.errors[0].line + ': ' + r.errors[0].msg + '.' };
      tm = r.machine;
    }
    if (x.tapes && tm.k !== x.tapes) return { ok: false, message: 'This exercise asks for a machine with ' + x.tapes + ' tapes; yours has ' + tm.k + '.' };
    const steps = x.steps || 5000;
    const A = { tm, run: (w) => T.tm.run(tm, w.join(''), { maxSteps: steps, trace: false }) };
    const R = x.output ? null : K.lang.ref(x, 'machine');
    const sigma = K.alphabet(x.alphabet) || (R ? R.alphabet : ['0', '1']);
    return tmCheck(x, A, R, sigma);
  }

  /** A TM: it must halt on every string tried (within the step limit) and accept exactly the language, or compute the output */
  function tmCheck(x, A, R, sigma) {
    // maxLen 0 means the blank tape only
    const words = K.words(sigma, x.maxLen ?? 6, x.cap || 600).concat((x.tests || []).map((w) => [...w]));
    const steps = x.steps || 5000;
    let n = 0;
    for (const w of words) {
      const r = A.run(w);
      const s = K.showWord(w);
      if (!r.halted) return { ok: false, counterexample: s, message: r.verdict === 'loop' ? 'On ' + s + ' your machine runs forever: it comes back to a configuration it was in before.' : 'On ' + s + ' your machine has not halted after ' + steps + ' steps.' };
      n++;
      if (x.output) {
        const want = String(x.output(w.join('')));
        if (!r.accepted) return { ok: false, counterexample: s, message: 'On ' + s + ' your machine halts in ' + r.state + ', which is not a halting state of success (list it under halt: or accept:), so it gives no output; it should leave ' + K.show(want) + '.' };
        const out = r.output !== null && r.output !== undefined ? r.output : T.tm.outputOf(A.tm, r.config);
        if (out !== want) return { ok: false, counterexample: s, message: 'On ' + s + ' your machine leaves ' + K.show(out) + ' on the tape; it should leave ' + K.show(want) + '.' };
        continue;
      }
      const ref = R.has(w);
      if (ref === null) continue;
      if (r.accepted !== ref) return { ok: false, counterexample: s, message: r.accepted ? 'Your machine accepts ' + s + ', which is not in the language.' : 'Your machine rejects ' + s + ', which is in the language.' };
    }
    const upTo = Math.max(0, ...words.map((w) => w.length));
    return { ok: true, message: 'Your machine halts with the right ' + (x.output ? 'output' : 'answer') + ' on all ' + n + ' inputs tried, up to length ' + upTo + '.' };
  }
})();

// Programs and Moore and Mealy machines.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = (T.Check = T.Check || {});
  K.kinds = K.kinds || {};

  // ---- a program (RAM or counter machine, a macro, a λ-term, recursive definitions ...) -------------------
  // x.test(text) -> true | false | 'why not' | {ok, why, counterexample}; the text keeps its lines and spaces.
  K.kinds.program = {
    check(x, a) {
      if (!a || !String(a).trim()) return { ok: false, message: 'Write the program first.' };
      if (typeof x.test !== 'function') return { ok: false, message: 'This exercise has no test for its answer.' };
      const r = x.test(String(a));
      if (r && typeof r === 'object') return r.ok ? { ok: true, message: r.why || 'Your program passes every test.' } : { ok: false, message: r.why || 'Not yet.', counterexample: r.counterexample };
      if (typeof r === 'string') return { ok: false, message: r };
      return r ? { ok: true, message: x.why || 'Your program passes every test.' } : { ok: false, message: x.whyNot || 'Not quite.' };
    },
  };

  // ---- Moore and Mealy machines ----------------------------------------------------------------------------------
  /**
   * Text of a transducer:      moore | mealy        (the first line)
   *                            start q0
   *                            q0 -a-> q1           (Mealy: q0 -a/1-> q1, or several: q0 -a/1, b/0-> q1)
   *                            out q0 = 1           (Moore: what a state outputs; ε for nothing)
   * Read into the form T.Transducer runs: {type, states, inputs, start, trans: [{from, sym, to, out}], out}.
   */
  K.parseTransducer = function (text) {
    const m = { type: null, states: [], inputs: [], start: null, trans: [], out: {} };
    const add = (q) => { if (!m.states.includes(q)) m.states.push(q); };
    const errs = [];
    String(text || '').split('\n').forEach((raw, k) => {
      const line = (/^\s*#/.test(raw) ? '' : raw.replace(/(^|\s)\/\/.*$/, '')).trim();
      if (!line) return;
      const at = 'line ' + (k + 1) + ': ';
      let r;
      if (/^(moore|mealy)$/i.test(line)) { m.type = line.toLowerCase(); return; }
      if ((r = /^start:?\s+(\S+)$/i.exec(line))) { m.start = r[1]; add(r[1]); return; }
      if ((r = /^out(?:put)?:?\s+(\S+)\s*(?:=|:|\s)\s*(\S*)$/i.exec(line))) { add(r[1]); m.out[r[1]] = /^(ε|eps)$/.test(r[2]) ? '' : r[2]; return; }
      if ((r = /^(\S+)\s+-(.+?)->\s*(\S+)$/.exec(line))) {
        add(r[1]); add(r[3]);
        for (const part of r[2].split(',').map((x) => x.trim()).filter(Boolean)) {
          const [sym, out] = part.split('/').map((x) => x.trim());
          if (!sym) { errs.push(at + 'a move needs a symbol'); continue; }
          if (!m.inputs.includes(sym)) m.inputs.push(sym);
          m.trans.push({ from: r[1], sym, to: r[3], out: out === undefined ? undefined : /^(ε|eps)$/.test(out) ? '' : out });
        }
        return;
      }
      errs.push(at + 'cannot read "' + line + '": expected q0 -a-> q1, q0 -a/1-> q1, out q0 = 1 or start q0');
    });
    if (!m.type) m.type = m.trans.some((t) => t.out !== undefined) ? 'mealy' : 'moore';
    if (!m.start) m.start = m.states[0];
    if (!m.states.length) errs.push('there are no states');
    const seen = new Set();
    for (const t of m.trans) { const key = t.from + '\u0000' + t.sym; if (seen.has(key)) errs.push(t.from + ' has two moves on ' + t.sym + ': a transducer is deterministic'); seen.add(key); if (m.type === 'mealy' && t.out === undefined) errs.push(t.from + ' -' + t.sym + '-> ' + t.to + ' has no output: write ' + t.sym + '/output'); if (t.out === undefined) t.out = ''; }
    return { m, errors: errs };
  };
  K.runTransducer = (m, w) => (m.type === 'mealy' ? T.Transducer.runMealy(m, w) : T.Transducer.runMoore(m, w));
  /** transducer: machine: 'moore' | 'mealy', ref (text) or output(w), alphabet, maxLen. Answer: text. */
  K.kinds.transducer = {
    check(x, a) {
      if (!a || !String(a).trim()) return { ok: false, message: 'Build the machine first.' };
      const r = K.parseTransducer(String(a));
      if (r.errors.length) return { ok: false, message: 'The machine cannot be read: ' + r.errors[0] + '.' };
      const m = r.m;
      if (x.machine && m.type !== x.machine) return { ok: false, message: 'This exercise asks for a ' + (x.machine === 'moore' ? 'Moore machine (outputs on states)' : 'Mealy machine (outputs on moves)') + '.' };
      let ref = null;
      if (x.ref) { const rr = K.parseTransducer(x.ref); if (rr.errors.length) throw new Error('the reference cannot be read: ' + rr.errors[0]); ref = rr.m; }
      const want = (w) => (x.output ? String(x.output(w)) : K.runTransducer(ref, w).output);
      const sigma = K.alphabet(x.alphabet) || (ref ? ref.inputs : m.inputs);
      const words = K.words(sigma, x.maxLen ?? 7, x.cap || 2000);
      for (const wa of words) {
        const w = wa.join('');
        const got = K.runTransducer(m, w);
        const s = K.show(w);
        if (!got.complete) return { ok: false, counterexample: s, message: 'On ' + s + ' your machine gets stuck: a state has no move on a symbol it reads.' };
        if (got.output !== want(w)) return { ok: false, counterexample: s, message: 'On ' + s + ' your machine outputs ' + K.show(got.output) + '; it should output ' + K.show(want(w)) + '.' };
      }
      return { ok: true, message: 'Your machine gives the right output on all ' + words.length + ' inputs up to length ' + words[words.length - 1].length + '.' };
    },
  };
})();
