// Grammar cleanup and normal forms, every step traced: useless symbols, ε-rules, unit rules, Chomsky and
// Greibach normal forms, left-recursion removal, left factoring, and the conversions between regular
// (right- or left-linear) grammars and NFAs.
//
// Every function takes a grammar from T.grammar and returns { grammar, trace, ... } without changing the
// input. New nonterminals get names that the grammar reader reads back whole (S0, A', A1, T_a, [+]).
//
// NFAs are plain objects in the same shape as T.FA machines (fa.js), so they pass straight between the two:
//   { states: [..], alphabet: [..], start, accept: [..], trans: [{ from, sym, to }] }  sym '' is ε.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Gr = T.grammar;
  const { showProd, showRhs, show } = Gr;
  const EPS = Gr.EPS;

  // A new nonterminal name: the first unused candidate, else base1, base2, ...
  function fresh(used, base, candidates) {
    let b = String(base).replace(/'+$/, '');
    if (!/^[A-Za-z][a-z0-9_]*$/.test(b)) b = /^[A-Z]/.test(b) ? b[0] : 'X';
    for (const c of candidates || [b + "'", b + "''"]) if (!used.has(c)) { used.add(c); return c; }
    for (let i = 1; ; i++) { const c = b + i; if (!used.has(c)) { used.add(c); return c; } }
  }
  const usedNames = (G) => new Set(G.nonterminals.concat(G.terminals));
  const rk = (A, rhs) => A + '\u0002' + rhs.join('\u0001');
  // Build a grammar from [A, rhs] pairs, dropping exact duplicates.
  function build(G, pairs, start, extraN) {
    const seen = new Set(), out = [];
    for (const [A, rhs, prec] of pairs) { const k = rk(A, rhs); if (!seen.has(k)) { seen.add(k); out.push(prec ? { A, rhs, prec } : [A, rhs]); } }
    return Gr.derive(G, out, start, extraN);
  }
  const pairsOf = (G) => G.productions.map((p) => [p.A, p.rhs.slice(), p.prec]);
  const isCF = (G) => G.productions.every((p) => p.A !== null);
  function needCF(G, what) { if (!isCF(G)) throw new Error(what + ' needs a context-free grammar'); }

  // ---------- the three fixpoints ----------
  // Nullable: A ⇒* ε. A round looks at every rule; a rule whose right side is all nullable makes its left side nullable.
  function nullable(G) {
    needCF(G, 'nullable');
    const set = new Set(), trace = [];
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      const added = [];
      for (const p of G.productions) {
        if (set.has(p.A) || !p.rhs.every((s) => set.has(s))) continue;
        set.add(p.A); added.push(p.A); changed = true;
        trace.push({ kind: 'nullable', A: p.A, prod: p.id, round,
          say: p.rhs.length ? p.A + ' is nullable: every symbol of ' + showProd(G, p) + ' (' + p.rhs.join(', ') + ') is already nullable.' : p.A + ' is nullable because of the rule ' + showProd(G, p) + '.' });
      }
      trace.push({ kind: 'round', round, added, set: [...set], say: added.length ? 'Round ' + round + ' adds ' + added.join(', ') + '.' : 'Round ' + round + ' adds nothing, so the nullable set is {' + [...set].join(', ') + '}.' });
    }
    return { set, trace };
  }
  // Generating: A ⇒* some terminal string.
  function generating(G) {
    needCF(G, 'generating');
    const N = Gr.info(G).N, set = new Set(), trace = [];
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      const added = [];
      for (const p of G.productions) {
        if (set.has(p.A) || !p.rhs.every((s) => !N.has(s) || set.has(s))) continue;
        set.add(p.A); added.push(p.A); changed = true;
        const nts = p.rhs.filter((s) => N.has(s));
        trace.push({ kind: 'generating', A: p.A, prod: p.id, round,
          say: p.A + ' generates a terminal string through ' + showProd(G, p) + (nts.length ? ', since ' + [...new Set(nts)].join(', ') + (nts.length > 1 ? ' already generate' : ' already generates') + ' one.' : ', whose right side is all terminals.') });
      }
      trace.push({ kind: 'round', round, added, set: [...set], say: added.length ? 'Round ' + round + ' adds ' + added.join(', ') + '.' : 'Round ' + round + ' adds nothing; generating: {' + [...set].join(', ') + '}.' });
    }
    return { set, trace };
  }
  // Reachable: S ⇒* α A β. Breadth-first from the start symbol along right sides.
  function reachable(G) {
    needCF(G, 'reachable');
    const N = Gr.info(G).N, byA = Gr.info(G).byA, set = new Set([G.start]), trace = [], todo = [G.start];
    trace.push({ kind: 'reach', A: G.start, prod: null, say: G.start + ' is reachable: it is the start symbol.' });
    while (todo.length) {
      const A = todo.shift();
      for (const p of byA.get(A) || []) for (const s of p.rhs) {
        if (!N.has(s) || set.has(s)) continue;
        set.add(s); todo.push(s);
        trace.push({ kind: 'reach', A: s, prod: p.id, say: s + ' is reachable through ' + showProd(G, p) + '.' });
      }
    }
    return { set, trace };
  }

  // ---------- useless symbols ----------
  function removeUseless(G) {
    needCF(G, 'removeUseless');
    const N = Gr.info(G).N, trace = [];
    const gen = generating(G);
    trace.push({ kind: 'phase', phase: 'generating', say: 'First find the nonterminals that generate some terminal string.' }, ...gen.trace);
    const ok = (s) => !N.has(s) || gen.set.has(s);
    const dead = G.nonterminals.filter((A) => !gen.set.has(A));
    const dropped1 = G.productions.filter((p) => !ok(p.A) || !p.rhs.every(ok));
    trace.push({ kind: 'drop', phase: 'generating', symbols: dead, prods: dropped1.map((p) => p.id),
      say: dead.length ? 'Remove ' + dead.join(', ') + ' and every rule that mentions ' + (dead.length > 1 ? 'them' : 'it') + (dropped1.length ? ': ' + dropped1.map((p) => showProd(G, p)).join('; ') : '') + '.' : 'Every nonterminal generates something; nothing to remove.' });
    if (!gen.set.has(G.start)) {
      const E = build(G, [], G.start);
      trace.push({ kind: 'empty', say: 'The start symbol ' + G.start + ' generates nothing, so the language is empty (∅).' });
      return { grammar: E, generating: [...gen.set], reachable: [G.start], removed: G.nonterminals.filter((A) => A !== G.start), empty: true, trace, otherOrder: null };
    }
    const G1 = build(G, G.productions.filter((p) => ok(p.A) && p.rhs.every(ok)).map((p) => [p.A, p.rhs, p.prec]), G.start);
    const re = reachable(G1);
    trace.push({ kind: 'phase', phase: 'reachable', say: 'Then, in what is left, find the nonterminals reachable from ' + G.start + '.' }, ...re.trace);
    const far = G1.nonterminals.filter((A) => !re.set.has(A));
    const dropped2 = G1.productions.filter((p) => !re.set.has(p.A));
    const G2 = build(G1, G1.productions.filter((p) => re.set.has(p.A)).map((p) => [p.A, p.rhs, p.prec]), G.start);
    trace.push({ kind: 'drop', phase: 'reachable', symbols: far, prods: dropped2.map((p) => p.id),
      say: far.length ? 'Remove the unreachable ' + far.join(', ') + ' with ' + (far.length > 1 ? 'their' : 'its') + ' rules.' : 'Everything left is reachable.' });
    // the other order, to show why it matters
    const reFirst = reachable(G), Gr1 = build(G, G.productions.filter((p) => reFirst.set.has(p.A)).map((p) => [p.A, p.rhs]), G.start);
    const gen2 = generating(Gr1), ok2 = (s) => !Gr.info(Gr1).N.has(s) || gen2.set.has(s);
    const Gr2 = build(Gr1, Gr1.productions.filter((p) => ok2(p.A) && p.rhs.every(ok2)).map((p) => [p.A, p.rhs]), G.start);
    const leftover = Gr2.nonterminals.filter((A) => !G2.nonterminals.includes(A));
    trace.push({ kind: 'order', leftover,
      say: leftover.length
        ? 'Order matters: removing unreachable symbols first and then non-generating ones would have left ' + leftover.join(', ') + ' behind, because ' + (leftover.length > 1 ? 'they were' : 'it was') + ' only reachable through rules that die in the second pass.'
        : 'Order matters in general: deleting non-generating symbols removes rules, which can make other symbols unreachable, so the reachability pass must come second (here both orders happen to agree).' });
    const removed = G.nonterminals.filter((A) => !G2.nonterminals.includes(A));
    return { grammar: G2, generating: [...gen.set], reachable: [...re.set], removed, empty: false, trace, otherOrder: { grammar: Gr2, leftover } };
  }

  // ---------- ε-rules ----------
  // opts.keepEmpty (default true): if ε is in the language keep it with S → ε, adding a new start S0 → S | ε
  // first when S appears on some right side (so S → ε cannot be used inside a derivation).
  function removeEpsilon(G, opts) {
    needCF(G, 'removeEpsilon');
    opts = Object.assign({ keepEmpty: true }, opts || {});
    const nul = nullable(G), trace = [{ kind: 'phase', phase: 'nullable', say: 'Find the nullable nonterminals (those that derive ε).' }, ...nul.trace];
    const pairs = [];
    for (const p of G.productions) {
      const pos = p.rhs.map((s, i) => (nul.set.has(s) ? i : -1)).filter((i) => i >= 0);
      if (pos.length > 16) throw new Error('too many nullable symbols in one rule');
      const variants = [], seen = new Set();
      for (let mask = 0; mask < 1 << pos.length; mask++) {
        const drop = new Set(pos.filter((_, k) => mask & (1 << k)));
        const rhs = p.rhs.filter((_, i) => !drop.has(i));
        if (!rhs.length) continue;                               // ε-rules go
        if (rhs.length === 1 && rhs[0] === p.A) continue;        // A → A says nothing
        const k = rhs.join('\u0001'); if (seen.has(k)) continue; seen.add(k);
        variants.push(rhs); pairs.push([p.A, rhs, p.prec]);
      }
      if (!p.rhs.length) trace.push({ kind: 'drop', prod: p.id, say: 'Drop the ε-rule ' + showProd(G, p) + '.' });
      else if (pos.length) trace.push({ kind: 'expand', prod: p.id, nullablePositions: pos, variants,
        say: showProd(G, p) + ' has nullable ' + pos.map((i) => p.rhs[i]).join(', ') + '; keep every way of leaving them out: ' + variants.map((r) => p.A + ' → ' + showRhs(G, r)).join(', ') + '.' });
    }
    const empty = nul.set.has(G.start);
    let start = G.start, extra = [];
    if (empty && opts.keepEmpty) {
      if (G.productions.some((p) => p.rhs.includes(G.start))) {
        start = fresh(usedNames(G), G.start, [G.start + '0', 'S0']); extra = [start];
        pairs.unshift([start, [G.start]], [start, []]);
        trace.push({ kind: 'start', A: start, say: 'ε is in the language and ' + G.start + ' appears on a right side, so add a new start ' + start + ' → ' + G.start + ' | ε.' });
      } else {
        pairs.unshift([G.start, []]);
        trace.push({ kind: 'start', A: G.start, say: 'ε is in the language, so keep ' + G.start + ' → ε (' + G.start + ' never appears on a right side).' });
      }
    } else if (empty) trace.push({ kind: 'lose', say: 'ε is in the language; the new grammar generates everything except ε.' });
    return { grammar: build(G, pairs, start, extra), nullable: [...nul.set], emptyInLanguage: empty, keptEmpty: empty && opts.keepEmpty, trace };
  }

  // ---------- unit rules ----------
  const isUnit = (G, p) => p.rhs.length === 1 && Gr.isN(G, p.rhs[0]);
  function removeUnit(G) {
    needCF(G, 'removeUnit');
    const trace = [], pairs = new Map(G.nonterminals.map((A) => [A, [A]]));
    trace.push({ kind: 'phase', phase: 'pairs', say: 'Every (A, A) is a unit pair; (A, C) is one when (A, B) is and B → C is a unit rule.' });
    const units = G.productions.filter((p) => isUnit(G, p));
    for (let changed = true; changed;) {
      changed = false;
      for (const A of G.nonterminals) for (const B of pairs.get(A)) for (const p of units) {
        if (p.A !== B || pairs.get(A).includes(p.rhs[0])) continue;
        pairs.get(A).push(p.rhs[0]); changed = true;
        trace.push({ kind: 'pair', A, B: p.rhs[0], via: p.id, say: '(' + A + ', ' + p.rhs[0] + ') is a unit pair: (' + A + ', ' + B + ') with ' + showProd(G, p) + '.' });
      }
    }
    const out = [];
    for (const A of G.nonterminals) for (const B of pairs.get(A)) {
      const copied = [];
      for (const p of Gr.info(G).byA.get(B) || []) if (!isUnit(G, p)) { out.push([A, p.rhs, p.prec]); if (A !== B) copied.push(p.rhs); }
      if (A !== B && copied.length) trace.push({ kind: 'copy', A, B, rules: copied, say: 'Since ' + A + ' ⇒* ' + B + ', give ' + A + ' the non-unit rules of ' + B + ': ' + copied.map((r) => A + ' → ' + showRhs(G, r)).join(', ') + '.' });
    }
    if (units.length) trace.push({ kind: 'drop', prods: units.map((p) => p.id), say: 'Drop the unit rules ' + units.map((p) => showProd(G, p)).join(', ') + '.' });
    else trace.push({ kind: 'drop', prods: [], say: 'There are no unit rules.' });
    const pairList = []; for (const [A, Bs] of pairs) for (const B of Bs) pairList.push([A, B]);
    return { grammar: build(G, out, G.start), pairs: pairList, trace };
  }

  // ---------- Chomsky normal form ----------
  // Stated order: START (new start symbol), TERM (terminals in long rules get their own nonterminal),
  // BIN (split long right sides), DEL (ε-rules), UNIT (unit rules), then remove useless symbols.
  // BIN before DEL keeps DEL from multiplying long rules; DEL before UNIT because DEL creates unit rules.
  function termName(used, t) {
    if (/^[a-z0-9]+$/.test(t)) return fresh(used, 'T_' + t, ['T_' + t]);
    if (!/[[\]\s]/.test(t)) return fresh(used, 'T', ['[' + t + ']']);
    return fresh(used, 'T');
  }
  function toCNF(G) {
    needCF(G, 'toCNF');
    const stages = [], used = usedNames(G);
    // START
    const S0 = fresh(used, G.start, [G.start + '0', 'S0']);
    let H = build(G, [[S0, [G.start]], ...pairsOf(G)], S0, [S0]);
    stages.push({ name: 'START', grammar: H, trace: [{ kind: 'start', A: S0, say: 'Add a new start ' + S0 + ' → ' + G.start + ', so the start symbol never appears on a right side.' }] });
    // TERM
    let tr = [];
    const tn = new Map(), out = [];
    for (const p of H.productions) {
      if (p.rhs.length < 2) { out.push([p.A, p.rhs]); continue; }
      const rhs = p.rhs.map((s) => {
        if (Gr.isN(H, s)) return s;
        if (!tn.has(s)) { const X = termName(used, s); tn.set(s, X); tr.push({ kind: 'term', A: X, terminal: s, say: 'The terminal ' + s + ' sits in a long rule; add ' + X + ' → ' + s + '.' }); }
        return tn.get(s);
      });
      if (rhs.some((s, i) => s !== p.rhs[i])) tr.push({ kind: 'replace', prod: p.id, rhs, say: showProd(H, p) + ' becomes ' + p.A + ' → ' + rhs.join(' ') + '.' });
      out.push([p.A, rhs]);
    }
    for (const [t, X] of tn) out.push([X, [t]]);
    if (!tr.length) tr.push({ kind: 'none', say: 'No terminal appears in a right side of length 2 or more.' });
    H = build(H, out, S0, [...tn.values()]);
    stages.push({ name: 'TERM', grammar: H, trace: tr });
    // BIN: A → X1 X2 ... Xk becomes a chain; identical tails share one nonterminal
    tr = [];
    const tails = new Map(), out2 = [];
    for (const p of H.productions) {
      if (p.rhs.length <= 2) { out2.push([p.A, p.rhs]); continue; }
      let A = p.A, rest = p.rhs.slice();
      const chain = [];
      while (rest.length > 2) {
        const key = rest.slice(1).join('\u0001');
        let X = tails.get(key), isNew = false;
        if (!X) { X = fresh(used, p.A, [p.A + '1']); tails.set(key, X); isNew = true; }
        out2.push([A, [rest[0], X]]); chain.push(A + ' → ' + rest[0] + ' ' + X);
        if (!isNew) { rest = null; break; }
        A = X; rest = rest.slice(1);
      }
      if (rest) { out2.push([A, rest]); chain.push(A + ' → ' + rest.join(' ')); }
      tr.push({ kind: 'bin', prod: p.id, chain, say: showProd(H, p) + ' is too long; split it into ' + chain.join(', ') + '.' });
    }
    if (!tr.length) tr.push({ kind: 'none', say: 'No right side is longer than two symbols.' });
    H = build(H, out2, S0, [...tails.values()]);
    stages.push({ name: 'BIN', grammar: H, trace: tr });
    // DEL
    const del = removeEpsilon(H, { keepEmpty: true });
    H = del.grammar; stages.push({ name: 'DEL', grammar: H, trace: del.trace });
    // UNIT
    const un = removeUnit(H);
    H = un.grammar; stages.push({ name: 'UNIT', grammar: H, trace: un.trace });
    // cleanup
    const cl = removeUseless(H);
    H = cl.grammar; stages.push({ name: 'USELESS', grammar: H, trace: cl.trace });
    const trace = [];
    for (const st of stages) trace.push({ kind: 'stage', stage: st.name, grammar: st.grammar, say: 'Stage ' + st.name + '.' }, ...st.trace);
    trace.push({ kind: 'done', say: isCNF(H) ? 'Every rule now has the form A → B C, A → a' + (del.emptyInLanguage ? ' or ' + H.start + ' → ε' : '') + ': Chomsky normal form.' : 'Done.' });
    return { grammar: H, stages, emptyInLanguage: del.emptyInLanguage, trace };
  }
  // A → B C, A → a, and S → ε only for the start symbol. The start symbol may sit on a right side unless S → ε
  // is a rule (then S → B S could smuggle ε into the middle of a word).
  function isCNF(G) {
    const N = Gr.info(G).N;
    const startEps = G.productions.some((p) => p.A === G.start && p.rhs.length === 0);
    return isCF(G) && G.productions.every((p) => (p.rhs.length === 2 && N.has(p.rhs[0]) && N.has(p.rhs[1]) && (!startEps || (p.rhs[0] !== G.start && p.rhs[1] !== G.start))) ||
      (p.rhs.length === 1 && !N.has(p.rhs[0])) || (p.rhs.length === 0 && p.A === G.start));
  }

  // ---------- left recursion ----------
  // Which nonterminals are left-recursive (A ⇒+ A α), allowing nullable symbols before the recursion.
  function leftRecursive(G) {
    needCF(G, 'leftRecursive');
    const N = Gr.info(G).N, nul = Gr.nullableSet(G), edges = new Map(G.nonterminals.map((A) => [A, []]));
    for (const p of G.productions) for (const s of p.rhs) { if (N.has(s)) edges.get(p.A).push({ to: s, prod: p.id }); if (!nul.has(s)) break; }
    const out = [];
    for (const A of G.nonterminals) {
      // breadth-first search for a path A → ... → A along left corners
      const prev = new Map(), q = [A];
      let hit = null;
      while (q.length && !hit) {
        const X = q.shift();
        for (const e of edges.get(X)) {
          if (e.to === A) { hit = { from: X, prod: e.prod }; break; }
          if (!prev.has(e.to)) { prev.set(e.to, { from: X, prod: e.prod }); q.push(e.to); }
        }
      }
      if (!hit) continue;
      const path = [hit.prod]; let X = hit.from;
      while (X !== A) { const pr = prev.get(X); path.unshift(pr.prod); X = pr.from; }
      out.push({ A, immediate: path.length === 1, path });
    }
    return out;
  }
  function hasCycle(G) {   // A ⇒+ A
    const N = Gr.info(G).N, nul = Gr.nullableSet(G), edges = new Map(G.nonterminals.map((A) => [A, new Set()]));
    for (const p of G.productions) p.rhs.forEach((s, i) => {
      if (N.has(s) && p.rhs.every((t, j) => j === i || nul.has(t))) edges.get(p.A).add(s);
    });
    for (const A of G.nonterminals) {
      const seen = new Set(), st = [...edges.get(A)];
      while (st.length) { const X = st.pop(); if (X === A) return true; if (!seen.has(X)) { seen.add(X); st.push(...edges.get(X)); } }
    }
    return false;
  }
  // Immediate left recursion of one nonterminal: A → A α1 | ... | β1 | ... becomes
  //   A → β1 A' | ...,  A' → α1 A' | ... | ε        (or, with epsFree, A → β | β A', A' → α | α A')
  function immediateRules(A, rules, Aname, epsFree) {
    const alphas = rules.filter((r) => r[0] === A).map((r) => r.slice(1));
    const betas = rules.filter((r) => r[0] !== A);
    if (!alphas.length) return null;
    const newA = [], newB = [];
    for (const b of betas) { newA.push(b.concat([Aname])); if (epsFree) newA.push(b); }
    for (const a of alphas) { newB.push(a.concat([Aname])); if (epsFree) newB.push(a); }
    if (!epsFree) newB.push([]);
    return { alphas, betas, newA, newB };
  }
  function removeImmediate(G, A, opts) {
    opts = opts || {};
    const used = usedNames(G), A2 = fresh(used, A);
    const rules = Gr.info(G).byA.get(A).map((p) => p.rhs);
    const r = immediateRules(A, rules, A2, opts.epsFree);
    if (!r) return { grammar: G, trace: [{ kind: 'none', A, say: A + ' is not immediately left-recursive.' }] };
    const out = []; let placed = false;
    for (const p of G.productions) {
      if (p.A !== A) { out.push([p.A, p.rhs]); continue; }
      if (placed) continue;
      placed = true; r.newA.forEach((rhs) => out.push([A, rhs])); r.newB.forEach((rhs) => out.push([A2, rhs]));
    }
    const say = A + ' → ' + r.alphas.map((a) => A + ' ' + showRhs(G, a)).join(' | ') + (r.betas.length ? ' | ' + r.betas.map((b) => showRhs(G, b)).join(' | ') : '') +
      ' becomes ' + A + ' → ' + (r.newA.length ? r.newA.map((x) => showRhs(G, x)).join(' | ') : '(nothing: every rule of ' + A + ' is left-recursive, so ' + A + ' generates nothing)') + ' and ' + A2 + ' → ' + r.newB.map((x) => showRhs(G, x)).join(' | ') + '.';
    return { grammar: build(G, out, G.start, [A2]), newName: A2, trace: [{ kind: 'immediate', A, B: A2, alphas: r.alphas, betas: r.betas, say }] };
  }
  // General removal (indirect too). The algorithm needs no ε-rules and no cycles A ⇒+ A, so when the
  // grammar has them it first removes ε-rules and unit rules (traced as a preparation step).
  function removeLeftRecursion(G, opts) {
    needCF(G, 'removeLeftRecursion');
    opts = opts || {};
    const trace = [];
    let H = G;
    const epsRules = G.productions.filter((p) => !p.rhs.length && !(p.A === G.start && !G.productions.some((q) => q.rhs.includes(G.start))));
    if (epsRules.length || hasCycle(G)) {
      const e = removeEpsilon(H, { keepEmpty: true }), u = removeUnit(e.grammar);
      H = u.grammar;
      trace.push({ kind: 'prepare', grammar: H, say: 'The method needs a grammar without ε-rules and cycles, so first remove ' + (epsRules.length ? 'the ε-rules and ' : '') + 'the unit rules.' }, ...e.trace, ...u.trace);
    }
    const order = H.nonterminals.slice(), used = usedNames(H);
    trace.push({ kind: 'order', order, say: 'Number the nonterminals ' + order.map((A, i) => A + '=' + (i + 1)).join(', ') + '. Afterwards every rule Ai → Aj … will have j > i.' });
    const rules = new Map(order.map((A) => [A, Gr.info(H).byA.get(A).map((p) => p.rhs.slice())]));
    const added = [], listed = order.slice();   // listed: the print order, each new A' right after its A
    for (let i = 0; i < order.length; i++) {
      const Ai = order[i];
      for (let j = 0; j < i; j++) {
        const Aj = order[j], next = [];
        let did = false;
        for (const r of rules.get(Ai)) {
          if (r[0] === Aj) { did = true; for (const d of rules.get(Aj)) next.push(d.concat(r.slice(1))); }
          else next.push(r);
        }
        if (did) {
          rules.set(Ai, dedupe(next));
          trace.push({ kind: 'substitute', A: Ai, B: Aj, rules: rules.get(Ai), say: 'Replace ' + Aj + ' at the front of ' + Ai + "'s rules by each of its right sides: " + Ai + ' → ' + rules.get(Ai).map((r) => showRhs(H, r)).join(' | ') + '.' });
        }
      }
      const B = fresh(used, Ai);
      const r = immediateRules(Ai, rules.get(Ai), B, !!opts.epsFree);
      if (r) {
        rules.set(Ai, dedupe(r.newA)); rules.set(B, dedupe(r.newB)); added.push(B); listed.splice(listed.indexOf(Ai) + 1, 0, B);
        trace.push({ kind: 'immediate', A: Ai, B, alphas: r.alphas, betas: r.betas,
          say: Ai + ' is immediately left-recursive; it becomes ' + Ai + ' → ' + (r.newA.length ? r.newA.map((x) => showRhs(H, x)).join(' | ') : '(no rules: it only recursed)') + ' and ' + B + ' → ' + r.newB.map((x) => showRhs(H, x)).join(' | ') + '.' });
      } else used.delete(B);
    }
    const pairs = [];
    for (const A of listed) for (const r of rules.get(A)) pairs.push([A, r]);
    const out = build(H, pairs, H.start, added);
    trace.push({ kind: 'done', say: 'No nonterminal is left-recursive any more.' });
    return { grammar: out, trace, added };
  }
  function dedupe(rs) { const s = new Set(); return rs.filter((r) => { const k = r.join('\u0001'); if (s.has(k)) return false; s.add(k); return true; }); }

  // ---------- Greibach normal form ----------
  // Clean up (ε, unit, useless), order the nonterminals, make every rule Ai → Aj… have j > i by substitution
  // and immediate left-recursion removal (the ε-free variant), substitute back from the last nonterminal
  // down, fix the new nonterminals, and finally give terminals after the first position their own
  // nonterminals. Result: every rule is A → a B1 … Bk (plus S → ε when ε is in the language).
  function toGNF(G, opts) {
    needCF(G, 'toGNF');
    opts = Object.assign({ maxRules: 5000 }, opts || {});
    const trace = [];
    const e = removeEpsilon(G, { keepEmpty: false }), u = removeUnit(e.grammar), c = removeUseless(u.grammar);
    trace.push({ kind: 'prepare', grammar: c.grammar, say: 'First remove ε-rules, unit rules and useless symbols.' }, ...e.trace, ...u.trace, ...c.trace);
    let H = c.grammar;
    const emptyIn = e.emptyInLanguage;
    if (c.empty) {
      const Z = build(G, emptyIn ? [[G.start, []]] : [], G.start);
      trace.push({ kind: 'done', say: 'The language ' + (emptyIn ? 'is {ε}' : 'is empty') + '.' });
      return { grammar: Z, emptyInLanguage: emptyIn, trace };
    }
    const N = new Set(H.nonterminals), order = H.nonterminals.slice(), used = usedNames(H);
    const rules = new Map(order.map((A) => [A, Gr.info(H).byA.get(A).map((p) => p.rhs.slice())]));
    const count = () => { let k = 0; for (const rs of rules.values()) k += rs.length; if (k > opts.maxRules) throw new Error('Greibach normal form grew past ' + opts.maxRules + ' rules'); };
    trace.push({ kind: 'order', order, say: 'Number the nonterminals ' + order.map((A, i) => A + '=' + (i + 1)).join(', ') + '.' });
    const Bs = [];
    for (let i = 0; i < order.length; i++) {
      const Ai = order[i];
      for (let j = 0; j < i; j++) {
        const Aj = order[j], next = []; let did = false;
        for (const r of rules.get(Ai)) {
          if (r[0] === Aj) { did = true; for (const d of rules.get(Aj)) next.push(d.concat(r.slice(1))); } else next.push(r);
        }
        if (did) { rules.set(Ai, dedupe(next)); count(); trace.push({ kind: 'substitute', A: Ai, B: Aj, rules: rules.get(Ai), say: 'Substitute for ' + Aj + ' at the front of ' + Ai + ': ' + Ai + ' → ' + rules.get(Ai).map((r) => showRhs(H, r)).join(' | ') + '.' }); }
      }
      const B = fresh(used, Ai);
      const r = immediateRules(Ai, rules.get(Ai), B, true);
      if (r) {
        rules.set(Ai, dedupe(r.newA)); rules.set(B, dedupe(r.newB)); Bs.push(B); N.add(B); count();
        trace.push({ kind: 'immediate', A: Ai, B, say: 'Remove the left recursion of ' + Ai + ': ' + Ai + ' → ' + rules.get(Ai).map((x) => showRhs(H, x)).join(' | ') + '; ' + B + ' → ' + rules.get(B).map((x) => showRhs(H, x)).join(' | ') + '.' });
      } else used.delete(B);
    }
    const lead = (A) => rules.get(A).every((r) => !N.has(r[0]));
    const subFront = (A, kind) => {
      const next = []; let did = false;
      for (const r of rules.get(A)) {
        if (N.has(r[0])) { did = true; for (const d of rules.get(r[0])) next.push(d.concat(r.slice(1))); } else next.push(r);
      }
      if (did) { rules.set(A, dedupe(next)); count(); trace.push({ kind, A, rules: rules.get(A), say: 'Substitute back into ' + A + ' so each rule starts with a terminal: ' + A + ' → ' + rules.get(A).map((x) => showRhs(H, x)).join(' | ') + '.' }); }
    };
    for (let i = order.length - 1; i >= 0; i--) subFront(order[i], 'back-substitute');
    for (const B of Bs) { let guard = 0; while (!lead(B) && guard++ < 50) subFront(B, 'back-substitute'); }
    // terminals after the first position get their own nonterminals
    const tn = new Map(), pairs = [];
    for (const [A, rs] of rules) for (const r of rs) {
      const rhs = r.map((s, i) => {
        if (i === 0 || N.has(s)) return s;
        if (!tn.has(s)) { const X = termName(used, s); tn.set(s, X); trace.push({ kind: 'term', A: X, terminal: s, say: 'The terminal ' + s + ' appears after the first position; add ' + X + ' → ' + s + '.' }); }
        return tn.get(s);
      });
      pairs.push([A, rhs]);
    }
    for (const [t, X] of tn) pairs.push([X, [t]]);
    let start = H.start;
    if (emptyIn) {
      // S → ε is only allowed when S is not on a right side; otherwise a new start copies S's rules
      if (pairs.some((pr) => pr[1].includes(H.start))) {
        start = fresh(used, H.start, [H.start + '0', 'S0']);
        const copies = pairs.filter((pr) => pr[0] === H.start).map((pr) => [start, pr[1]]);
        pairs.unshift([start, []], ...copies);
        trace.push({ kind: 'start', A: start, say: 'ε is in the language and ' + H.start + ' appears on right sides, so a new start ' + start + ' gets ' + H.start + "'s rules and " + start + ' → ε.' });
      } else pairs.unshift([H.start, []]);
    }
    const out = build(H, pairs, start, Bs.concat([...tn.values()], start !== H.start ? [start] : []));
    const cl = removeUseless(out);
    trace.push({ kind: 'done', say: 'Every rule now starts with a terminal followed only by nonterminals: Greibach normal form' + (emptyIn ? ' (with ' + start + ' → ε for the empty string)' : '') + '.' });
    return { grammar: cl.grammar, emptyInLanguage: emptyIn, trace };
  }
  function isGNF(G) {
    const N = Gr.info(G).N;
    return isCF(G) && G.productions.every((p) => (p.rhs.length >= 1 && !N.has(p.rhs[0]) && p.rhs.slice(1).every((s) => N.has(s))) ||
      (p.rhs.length === 0 && p.A === G.start && !G.productions.some((q) => q.rhs.includes(G.start))));
  }

  // ---------- left factoring ----------
  // While some nonterminal has two alternatives with a common prefix, take the longest such prefix α:
  // A → α β1 | α β2 | γ becomes A → α A' | γ and A' → β1 | β2 (ε when a βi is empty).
  function leftFactor(G) {
    needCF(G, 'leftFactor');
    const rules = new Map(G.nonterminals.map((A) => [A, (Gr.info(G).byA.get(A) || []).map((p) => p.rhs.slice())]));
    const order = G.nonterminals.slice(), used = usedNames(G), trace = [], added = [];
    const lcp = (a, b) => { let k = 0; while (k < a.length && k < b.length && a[k] === b[k]) k++; return k; };
    for (let guard = 0; guard < 500; guard++) {
      let best = null;
      for (const A of order) {
        const rs = rules.get(A) || [];
        for (let i = 0; i < rs.length; i++) for (let j = i + 1; j < rs.length; j++) {
          const k = lcp(rs[i], rs[j]);
          if (k > 0 && (!best || k > best.k)) best = { A, k, prefix: rs[i].slice(0, k) };
        }
        if (best) break;   // finish one nonterminal at a time, in order
      }
      if (!best) break;
      const { A, prefix } = best, rs = rules.get(A);
      const pre = prefix.join('\u0001');
      const group = rs.filter((r) => r.length >= prefix.length && r.slice(0, prefix.length).join('\u0001') === pre);
      const rest = rs.filter((r) => !group.includes(r));
      const A2 = fresh(used, A);
      order.splice(order.indexOf(A) + 1, 0, A2); added.push(A2);
      rules.set(A, [prefix.concat([A2]), ...rest]);
      rules.set(A2, dedupe(group.map((r) => r.slice(prefix.length))));
      trace.push({ kind: 'factor', A, B: A2, prefix, alternatives: group,
        say: group.map((r) => A + ' → ' + showRhs(G, r)).join(', ') + ' share the prefix ' + showRhs(G, prefix) + '; write ' + A + ' → ' + showRhs(G, prefix.concat([A2])) + ' and ' + A2 + ' → ' + rules.get(A2).map((r) => showRhs(G, r)).join(' | ') + '.' });
    }
    if (!trace.length) trace.push({ kind: 'none', say: 'No two alternatives of a nonterminal share a first symbol; nothing to factor.' });
    const pairs = [];
    for (const A of order) for (const r of rules.get(A) || []) pairs.push([A, r]);
    return { grammar: build(G, pairs, G.start, added), added, trace };
  }

  // ---------- regular grammars and NFAs ----------
  // Right-linear: each nonterminal is a state; A → w B reads w (through fresh middle states) and moves to B;
  // A → w reads w and moves to a new accepting state; A → ε makes A accepting.
  function rightLinearToNFA(G) {
    const cls = Gr.classify(G);
    if (!cls.rightLinear) throw new Error('the grammar is not right-linear');
    const N = Gr.info(G).N, used = usedNames(G), trace = [];
    const F = fresh(used, 'F', ['F', 'Fin']);
    const states = G.nonterminals.slice(), accept = new Set(), trans = [];
    let mid = 0;
    const newMid = () => { let s; do s = 'q' + ++mid; while (used.has(s)); used.add(s); states.push(s); return s; };
    let needF = false;
    for (const p of G.productions) {
      const last = p.rhs.length && N.has(p.rhs[p.rhs.length - 1]) ? p.rhs[p.rhs.length - 1] : null;
      const w = last ? p.rhs.slice(0, -1) : p.rhs;
      const target = last || F;
      if (!last && !w.length) { accept.add(p.A); trace.push({ kind: 'accept', state: p.A, prod: p.id, say: showProd(G, p) + ': make ' + p.A + ' accepting.' }); continue; }
      if (!last) needF = true;
      if (!w.length) { trans.push({ from: p.A, sym: '', to: target }); trace.push({ kind: 'edge', prod: p.id, edges: [[p.A, '', target]], say: showProd(G, p) + ': an ε-move from ' + p.A + ' to ' + target + '.' }); continue; }
      let cur = p.A; const edges = [];
      w.forEach((a, i) => { const nx = i === w.length - 1 ? target : newMid(); trans.push({ from: cur, sym: a, to: nx }); edges.push([cur, a, nx]); cur = nx; });
      trace.push({ kind: 'edge', prod: p.id, edges, say: showProd(G, p) + ': read ' + show(w) + ' from ' + p.A + ' to ' + target + (w.length > 1 ? ' through new middle states' : '') + '.' });
    }
    if (needF) { states.push(F); accept.add(F); trace.unshift({ kind: 'final', state: F, say: 'Add an accepting state ' + F + ' for rules that end in terminals only.' }); }
    return { nfa: { states, alphabet: G.terminals.slice(), start: G.start, accept: [...accept], trans }, trace };
  }
  // Left-linear: a new start state q0; A → w reads w from q0 into A; A → B w reads w from B into A;
  // the grammar's start symbol is the accepting state (the string is built from its left end).
  function leftLinearToNFA(G) {
    const cls = Gr.classify(G);
    if (!cls.leftLinear) throw new Error('the grammar is not left-linear');
    const N = Gr.info(G).N, used = usedNames(G), trace = [];
    const q0 = fresh(used, 'q', ['q0', 'I']);
    const states = [q0, ...G.nonterminals], trans = [];
    let mid = 0;
    const newMid = () => { let s; do s = 'm' + ++mid; while (used.has(s)); used.add(s); states.push(s); return s; };
    for (const p of G.productions) {
      const first = p.rhs.length && N.has(p.rhs[0]) ? p.rhs[0] : null;
      const w = first ? p.rhs.slice(1) : p.rhs, from = first || q0;
      if (!w.length) { trans.push({ from, sym: '', to: p.A }); trace.push({ kind: 'edge', prod: p.id, edges: [[from, '', p.A]], say: showProd(G, p) + ': an ε-move from ' + from + ' to ' + p.A + '.' }); continue; }
      let cur = from; const edges = [];
      w.forEach((a, i) => { const nx = i === w.length - 1 ? p.A : newMid(); trans.push({ from: cur, sym: a, to: nx }); edges.push([cur, a, nx]); cur = nx; });
      trace.push({ kind: 'edge', prod: p.id, edges, say: showProd(G, p) + ': read ' + show(w) + ' from ' + from + ' into ' + p.A + '.' });
    }
    trace.push({ kind: 'accept', state: G.start, say: 'A string is complete when the whole of ' + G.start + ' has been built, so ' + G.start + ' is the accepting state and ' + q0 + ' the start.' });
    return { nfa: { states, alphabet: G.terminals.slice(), start: q0, accept: [G.start], trans }, trace };
  }
  const edges = (nfa) => nfa.trans || nfa.transitions || [];
  function stateNames(nfa, terminals) {
    const used = new Set(terminals), map = new Map();
    for (const q of nfa.states) {
      const s = String(q), cap = s.charAt(0).toUpperCase() + s.slice(1);
      let name = Gr.NAME.test(cap) && !used.has(cap) ? cap : null;
      if (!name) { let i = map.size; do name = 'Q' + i++; while (used.has(name)); }
      used.add(name); map.set(q, name);
    }
    return map;
  }
  // q -a-> p gives Q → a P; q -ε-> p gives Q → P; accepting q gives Q → ε. Start: the start state.
  function nfaToRightLinear(nfa) {
    const nm = stateNames(nfa, nfa.alphabet), trace = [], pairs = [];
    for (const t of edges(nfa)) {
      const rhs = t.sym === '' ? [nm.get(t.to)] : [t.sym, nm.get(t.to)];
      pairs.push([nm.get(t.from), rhs]);
      trace.push({ kind: 'rule', edge: [t.from, t.sym, t.to], say: 'The move ' + t.from + ' –' + (t.sym || EPS) + '→ ' + t.to + ' gives ' + nm.get(t.from) + ' → ' + rhs.join(' ') + '.' });
    }
    for (const q of nfa.accept) { pairs.push([nm.get(q), []]); trace.push({ kind: 'rule', accept: q, say: q + ' is accepting, so ' + nm.get(q) + ' → ε.' }); }
    const G = Gr.make(nm.get(nfa.start), pairs, { nonterminals: [...nm.values()], terminals: nfa.alphabet });
    return { grammar: G, names: Object.fromEntries(nm), trace };
  }
  // q -a-> p gives P → Q a; the start state gives Q0 → ε; a new start S → F for each accepting F.
  function nfaToLeftLinear(nfa) {
    const nm = stateNames(nfa, nfa.alphabet), trace = [], used = new Set([...nm.values(), ...nfa.alphabet]);
    const S = fresh(used, 'S', ['S', 'S0']);
    const pairs = [];
    for (const q of nfa.accept) { pairs.push([S, [nm.get(q)]]); trace.push({ kind: 'rule', accept: q, say: q + ' is accepting, so ' + S + ' → ' + nm.get(q) + '.' }); }
    for (const t of edges(nfa)) {
      const rhs = t.sym === '' ? [nm.get(t.from)] : [nm.get(t.from), t.sym];
      pairs.push([nm.get(t.to), rhs]);
      trace.push({ kind: 'rule', edge: [t.from, t.sym, t.to], say: 'The move ' + t.from + ' –' + (t.sym || EPS) + '→ ' + t.to + ' gives ' + nm.get(t.to) + ' → ' + rhs.join(' ') + '.' });
    }
    pairs.push([nm.get(nfa.start), []]);
    trace.push({ kind: 'rule', say: 'Reading starts in ' + nfa.start + ', so ' + nm.get(nfa.start) + ' → ε.' });
    const G = Gr.make(S, pairs, { nonterminals: [S, ...nm.values()], terminals: nfa.alphabet });
    return { grammar: G, names: Object.fromEntries(nm), trace };
  }
  // Does a plain NFA accept a word? (used by tests and scenes; ε-closures included)
  function nfaAccepts(nfa, w) {
    const close = (set) => { const st = [...set]; while (st.length) { const q = st.pop(); for (const t of edges(nfa)) if (t.from === q && t.sym === '' && !set.has(t.to)) { set.add(t.to); st.push(t.to); } } return set; };
    let cur = close(new Set([nfa.start]));
    for (const a of w) { const nx = new Set(); for (const t of edges(nfa)) if (t.sym === a && cur.has(t.from)) nx.add(t.to); cur = close(nx); }
    return nfa.accept.some((q) => cur.has(q));
  }

  T.cfg = {
    fresh, nullable, generating, reachable, removeUseless, removeEpsilon, removeUnit,
    toCNF, isCNF, toGNF, isGNF, leftRecursive, hasCycle, removeImmediate, removeLeftRecursion, leftFactor,
    rightLinearToNFA, leftLinearToNFA, nfaToRightLinear, nfaToLeftLinear, nfaAccepts,
  };
})();
