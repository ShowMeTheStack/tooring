// Top-down predictive parsing: FIRST and FOLLOW by fixpoint (every round traced), FIRST of strings, the
// LL(1) table with its conflicts explained, the table-driven parser with tree building and panic-mode
// recovery, a recursive-descent code generator, and FIRST_k / FOLLOW_k with a strong LL(k) check.
// FIRST sets contain ε (T.grammar.EPS) when the symbol or string is nullable; '$' ends the input.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Gr = T.grammar;
  const { EPS, END, show, showProd, showRhs } = Gr;
  const list = (s) => '{' + [...s].join(', ') + '}';

  // ---------- FIRST and FOLLOW ----------
  function firstFollow(G) {
    if (!Gr.info(G).N || G.productions.some((p) => p.A === null)) throw new Error('FIRST/FOLLOW need a context-free grammar');
    const N = Gr.info(G).N, trace = [];
    const first = new Map(G.nonterminals.map((A) => [A, new Set()]));
    const follow = new Map(G.nonterminals.map((A) => [A, new Set()]));
    const F = (X) => (N.has(X) ? first.get(X) : new Set([X]));
    // FIRST, round by round. For A → X1 X2 … add FIRST(X1)∖{ε}; go on to X2 only while the X's are nullable;
    // if all of them are, ε joins FIRST(A).
    trace.push({ kind: 'phase', phase: 'first', say: 'FIRST: start with every set empty and repeat until a whole round adds nothing.' });
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      const before = snapshot(first);
      for (const p of G.productions) {
        const tgt = first.get(p.A);
        let allNull = true;
        for (let i = 0; i < p.rhs.length; i++) {
          const X = p.rhs[i], add = [...F(X)].filter((a) => a !== EPS && !tgt.has(a));
          if (add.length) {
            add.forEach((a) => tgt.add(a)); changed = true;
            trace.push({ kind: 'first', round, A: p.A, added: add, prod: p.id, from: X, pos: i,
              say: 'Add ' + list(add) + ' to FIRST(' + p.A + ') from ' + showProd(G, p) + (N.has(X) ? ', through FIRST(' + X + ')' : ', since it starts with ' + X) + (i ? ' (everything before ' + X + ' can vanish)' : '') + '.' });
          }
          if (!F(X).has(EPS)) { allNull = false; break; }
        }
        if (allNull && !tgt.has(EPS)) {
          tgt.add(EPS); changed = true;
          trace.push({ kind: 'first', round, A: p.A, added: [EPS], prod: p.id, from: null,
            say: 'Add ε to FIRST(' + p.A + '): ' + (p.rhs.length ? 'every symbol of ' + showProd(G, p) + ' can vanish' : showProd(G, p) + ' is an ε-rule') + '.' });
        }
      }
      trace.push({ kind: 'round', phase: 'first', round, changed, sets: snapshot(first), before,
        say: changed ? 'End of FIRST round ' + round + '.' : 'Round ' + round + ' changed nothing, so FIRST is final.' });
    }
    // FOLLOW: $ follows the start; for A → α B β, FIRST(β)∖{ε} follows B, and if β can vanish so does FOLLOW(A).
    trace.push({ kind: 'phase', phase: 'follow', say: 'FOLLOW: put $ in FOLLOW(' + G.start + ') and repeat until nothing changes.' });
    follow.get(G.start).add(END);
    trace.push({ kind: 'follow', round: 0, A: G.start, added: [END], prod: null, say: '$ is in FOLLOW(' + G.start + '): the end of input follows a whole sentence.' });
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      const before = snapshot(follow);
      for (const p of G.productions) p.rhs.forEach((B, i) => {
        if (!N.has(B)) return;
        const beta = p.rhs.slice(i + 1), fb = firstOfSet(G, first, beta), tgt = follow.get(B);
        const add = [...fb].filter((a) => a !== EPS && !tgt.has(a));
        if (add.length) {
          add.forEach((a) => tgt.add(a)); changed = true;
          trace.push({ kind: 'follow', round, A: B, added: add, prod: p.id, pos: i, via: 'first',
            say: 'In ' + showProd(G, p) + ', ' + showRhs(G, beta) + ' comes after ' + B + ', so add FIRST(' + showRhs(G, beta) + ')∖{ε} = ' + list(add) + ' to FOLLOW(' + B + ').' });
        }
        if (fb.has(EPS)) {
          const add2 = [...follow.get(p.A)].filter((a) => !tgt.has(a));
          if (add2.length) {
            add2.forEach((a) => tgt.add(a)); changed = true;
            trace.push({ kind: 'follow', round, A: B, added: add2, prod: p.id, pos: i, via: 'follow', from: p.A,
              say: 'In ' + showProd(G, p) + ', ' + (beta.length ? 'what comes after ' + B + ' can vanish' : B + ' is at the end') + ', so FOLLOW(' + p.A + ') = ' + list(follow.get(p.A)) + ' goes into FOLLOW(' + B + ').' });
          }
        }
      });
      trace.push({ kind: 'round', phase: 'follow', round, changed, sets: snapshot(follow), before,
        say: changed ? 'End of FOLLOW round ' + round + '.' : 'Round ' + round + ' changed nothing, so FOLLOW is final.' });
    }
    const nullable = new Set(G.nonterminals.filter((A) => first.get(A).has(EPS)));
    return { first, follow, nullable, trace };
  }
  function snapshot(m) { const o = {}; for (const [k, v] of m) o[k] = [...v]; return o; }
  function firstOfSet(G, first, seq) {
    const out = new Set();
    for (const X of seq) {
      const f = Gr.isN(G, X) ? first.get(X) : new Set([X]);
      for (const a of f) if (a !== EPS) out.add(a);
      if (!f.has(EPS)) return out;
    }
    out.add(EPS);
    return out;
  }
  // FIRST of a string of symbols, with a step per symbol looked at.
  function firstOf(G, seq, ff) {
    ff = ff || firstFollow(G);
    const trace = [], out = new Set();
    for (const X of seq) {
      const f = Gr.isN(G, X) ? ff.first.get(X) : new Set([X]);
      const add = [...f].filter((a) => a !== EPS);
      add.forEach((a) => out.add(a));
      const go = f.has(EPS);
      trace.push({ kind: 'symbol', sym: X, added: add, nullable: go, say: (Gr.isN(G, X) ? 'FIRST(' + X + ') gives ' : X + ' is a terminal: ') + list(add) + (go ? '; ' + X + ' can vanish, so look further.' : '; stop here.') });
      if (!go) return { set: out, trace };
    }
    out.add(EPS);
    trace.push({ kind: 'all-nullable', say: (seq.length ? 'Every symbol can vanish' : 'The string is empty') + ', so ε is in FIRST(' + showRhs(G, seq) + ').' });
    return { set: out, trace };
  }

  // ---------- the LL(1) table ----------
  function ll1Table(G, ff) {
    ff = ff || firstFollow(G);
    const table = {}, trace = [], N = Gr.info(G).N;
    for (const A of G.nonterminals) table[A] = {};
    const put = (A, a, p, why) => {
      const cell = table[A][a] || (table[A][a] = []);
      if (!cell.includes(p.id)) cell.push(p.id);
      trace.push({ kind: 'entry', A, terminal: a, prod: p.id, reason: why, clash: cell.length > 1,
        say: 'M[' + A + ', ' + a + '] gets ' + showProd(G, p) + (why === 'first' ? ' because ' + a + ' is in FIRST(' + showRhs(G, p.rhs) + ')' : ' because ' + showRhs(G, p.rhs) + ' can vanish and ' + a + ' is in FOLLOW(' + A + ')') + (cell.length > 1 ? ' — a conflict' : '') + '.' });
    };
    for (const p of G.productions) {
      const f = firstOfSet(G, ff.first, p.rhs);
      for (const a of f) if (a !== EPS) put(p.A, a, p, 'first');
      if (f.has(EPS)) for (const b of ff.follow.get(p.A)) put(p.A, b, p, 'follow');
    }
    const conflicts = [];
    for (const A of G.nonterminals) for (const a of Object.keys(table[A])) {
      const ids = table[A][a];
      if (ids.length < 2) continue;
      const ps = ids.map((i) => G.productions[i]);
      const viaFirst = ps.filter((p) => firstOfSet(G, ff.first, p.rhs).has(a));
      const type = viaFirst.length >= 2 ? 'FIRST/FIRST' : 'FIRST/FOLLOW';
      const say = type === 'FIRST/FIRST'
        ? 'Conflict at M[' + A + ', ' + a + ']: ' + viaFirst.map((p) => showRhs(G, p.rhs)).join(' and ') + ' can both begin with ' + a + ', so one symbol of lookahead cannot choose.'
        : 'Conflict at M[' + A + ', ' + a + ']: ' + ps.filter((p) => !viaFirst.includes(p)).map((p) => showRhs(G, p.rhs)).join(', ') + ' can vanish and ' + a + ' can follow ' + A + ', while ' + (viaFirst.length ? showRhs(G, viaFirst[0].rhs) + ' begins with ' + a : 'another rule also vanishes') + '.';
      conflicts.push({ A, terminal: a, prods: ids.slice(), type, say });
      trace.push({ kind: 'conflict', A, terminal: a, prods: ids.slice(), type, say });
    }
    const lr = T.cfg && T.cfg.leftRecursive ? T.cfg.leftRecursive(G) : [];
    trace.push({ kind: 'verdict', ll1: !conflicts.length, say: conflicts.length ? 'The grammar is not LL(1): ' + conflicts.length + ' cell' + (conflicts.length > 1 ? 's hold' : ' holds') + ' more than one rule' + (lr.length ? ' (' + lr.map((x) => x.A).join(', ') + ' ' + (lr.length > 1 ? 'are' : 'is') + ' left-recursive, which always causes this)' : '') + '.' : 'Every cell holds at most one rule: the grammar is LL(1).' });
    return { table, conflicts, ll1: !conflicts.length, first: ff.first, follow: ff.follow, trace, terminals: G.terminals.concat([END]) };
  }

  // ---------- the predictive parser ----------
  // opts.recover: panic mode. When the top is a terminal that does not match, pop it (as if it had been
  // there). When the top is a nonterminal A with an empty cell: if the input symbol is in A's
  // synchronising set (FOLLOW(A) plus opts.sync[A]) pop A, otherwise skip the input symbol.
  function predictive(G, w0, opts) {
    opts = Object.assign({ recover: false, maxSteps: 5000, sync: {} }, opts || {});
    const t = opts.table || ll1Table(G);
    const w = Gr.input(G, w0).concat([END]), N = Gr.info(G).N, trace = [], errors = [];
    const root = { sym: G.start, prod: null, children: null };
    const stack = [{ sym: END, node: null }, { sym: G.start, node: root }];
    let i = 0, steps = 0, accepted = false;
    const view = () => stack.map((s) => s.sym);
    const sync = (A) => new Set([...t.follow.get(A), ...(opts.sync[A] || [])]);
    while (steps++ < opts.maxSteps) {
      const top = stack[stack.length - 1], a = w[i];
      const base = { stack: view(), pos: i, input: w.slice(i) };
      if (top.sym === END && a === END) {
        accepted = !errors.length;
        trace.push(Object.assign(base, { kind: 'accept', action: 'accept', say: errors.length ? 'Both stack and input are at $, but ' + errors.length + ' error' + (errors.length > 1 ? 's were' : ' was') + ' repaired: reject.' : 'Stack and input both end with $: accept.' }));
        break;
      }
      if (!N.has(top.sym)) {
        if (top.sym === a) {
          stack.pop(); i++;
          trace.push(Object.assign(base, { kind: 'match', action: 'match ' + a, say: 'The top ' + a + ' matches the input: pop it and advance.' }));
          continue;
        }
        const msg = 'expected ' + (top.sym === END ? 'the end of input' : top.sym) + ' but found ' + (a === END ? 'the end of input' : a);
        errors.push({ pos: i, message: msg });
        if (!opts.recover || top.sym === END) {
          if (opts.recover && top.sym === END) { // extra input after a complete sentence: skip it
            trace.push(Object.assign(base, { kind: 'skip', action: 'skip ' + a, say: 'Error: ' + msg + '. Skip the extra input ' + a + '.' })); i++; continue;
          }
          trace.push(Object.assign(base, { kind: 'error', action: 'error', say: 'Error: ' + msg + '.' }));
          break;
        }
        stack.pop();
        if (top.node) top.node.missing = true;
        trace.push(Object.assign(base, { kind: 'pop-terminal', action: 'pop ' + top.sym, say: 'Error: ' + msg + '. Pretend ' + top.sym + ' was there: pop it.' }));
        continue;
      }
      const cell = (t.table[top.sym] || {})[a];
      if (cell && cell.length) {
        const p = G.productions[cell[0]];
        stack.pop();
        top.node.prod = p.id;
        top.node.children = p.rhs.map((s) => ({ sym: s, prod: null, children: null }));
        for (let k = p.rhs.length - 1; k >= 0; k--) stack.push({ sym: p.rhs[k], node: top.node.children[k] });
        trace.push(Object.assign(base, { kind: 'expand', action: showProd(G, p), prod: p.id, conflict: cell.length > 1,
          say: 'M[' + top.sym + ', ' + a + '] = ' + showProd(G, p) + ': replace ' + top.sym + ' by ' + showRhs(G, p.rhs) + (p.rhs.length > 1 ? ' (pushed right to left)' : '') + '.' + (cell.length > 1 ? ' The cell has a conflict; the first rule was taken.' : '') }));
        continue;
      }
      const msg = 'no rule for ' + top.sym + ' on ' + (a === END ? '$' : a);
      errors.push({ pos: i, message: msg });
      if (!opts.recover) { trace.push(Object.assign(base, { kind: 'error', action: 'error', say: 'Error: M[' + top.sym + ', ' + a + '] is empty.' })); break; }
      if (sync(top.sym).has(a) || a === END) {
        stack.pop(); top.node.children = []; top.node.error = true;
        trace.push(Object.assign(base, { kind: 'sync-pop', action: 'pop ' + top.sym, say: 'Error: M[' + top.sym + ', ' + a + '] is empty, but ' + a + ' is in the synchronising set of ' + top.sym + ': pop ' + top.sym + ' and carry on.' }));
      } else {
        i++;
        trace.push(Object.assign(base, { kind: 'skip', action: 'skip ' + a, say: 'Error: M[' + top.sym + ', ' + a + '] is empty and ' + a + ' is not a synchronising symbol: skip it.' }));
      }
    }
    if (steps > opts.maxSteps) trace.push({ kind: 'give-up', say: 'Stopped after ' + opts.maxSteps + ' steps.' });
    const finished = !errors.length && accepted;
    // nonterminals never expanded (the parse stopped early) become empty error nodes; iterative, since a
    // runaway left-recursive expansion can make the tree very deep
    for (const todo = [root]; todo.length;) {
      const nd = todo.pop();
      if (nd.children === null && N.has(nd.sym)) { nd.children = []; nd.error = true; } else if (nd.children) todo.push(...nd.children);
    }
    return { word: w.slice(0, -1), accepted: finished, errors, trace, tree: finished ? root : null, partialTree: root };
  }

  // ---------- recursive-descent code generator ----------
  // Readable JavaScript with one function per nonterminal: a switch on the lookahead picks the rule the
  // LL(1) table names. The text is runnable: new Function('tokens', code + 'return parse(tokens);').
  function codegen(G, ff) {
    const t = ll1Table(G, ff), N = Gr.info(G).N;
    const names = new Map(), used = new Set(['parse', 'peek', 'match', 'fail', 'tokens', 'pos', 'node']);
    for (const A of G.nonterminals) {
      let b = 'parse_' + A.replace(/'/g, '_p').replace(/[^A-Za-z0-9_]/g, '_');
      let n = b, k = 1; while (used.has(n)) n = b + '_' + k++;
      used.add(n); names.set(A, n);
    }
    const q = (s) => JSON.stringify(s);
    const lines = [];
    const emit = (text, info) => lines.push(Object.assign({ text }, info || {}));
    emit('// Recursive-descent parser: one function per nonterminal, choosing a rule by the next token.');
    emit('function parse(tokens) {');
    emit('  let pos = 0;');
    emit("  const peek = () => (pos < tokens.length ? tokens[pos] : '$');");
    emit('  const fail = (where, expected) => { throw new Error(where + ": expected one of " + expected.join(" ") + " but found " + peek()); };');
    emit('  function match(t) { if (peek() !== t) fail("match", [t]); pos++; return { sym: t, prod: null, children: null }; }');
    for (const A of G.nonterminals) {
      const row = t.table[A] || {};
      const byProd = new Map();
      for (const a of t.terminals) if (row[a]) { const id = row[a][0]; if (!byProd.has(id)) byProd.set(id, []); byProd.get(id).push(a); }
      emit('');
      emit('  // ' + A + (Gr.info(G).byA.get(A).length ? ' → ' + Gr.info(G).byA.get(A).map((p) => showRhs(G, p.rhs)).join(' | ') : ' has no rules'), { A });
      emit('  function ' + names.get(A) + '() {', { A });
      emit('    switch (peek()) {', { A });
      for (const [id, terms] of byProd) {
        const p = G.productions[id];
        const clash = terms.some((a) => row[a].length > 1);
        emit('      ' + terms.map((a) => 'case ' + q(a) + ':').join(' ') + '  // ' + showProd(G, p) + (clash ? '  (conflict: other rules also fit here)' : ''), { A, prod: id });
        const calls = p.rhs.map((s) => (N.has(s) ? names.get(s) + '()' : 'match(' + q(s) + ')'));
        emit('        return { sym: ' + q(A) + ', prod: ' + id + ', children: [' + calls.join(', ') + '] };', { A, prod: id });
      }
      const expected = t.terminals.filter((a) => row[a]);
      emit('      default: fail(' + q(A) + ', ' + JSON.stringify(expected) + ');', { A });
      emit('    }', { A });
      emit('  }', { A });
    }
    emit('');
    emit('  const tree = ' + names.get(G.start) + '();');
    emit("  if (peek() !== '$') fail('end', ['$']);");
    emit('  return tree;');
    emit('}');
    return { code: lines.map((l) => l.text).join('\n'), lines, functions: Object.fromEntries(names), ll1: t.ll1, conflicts: t.conflicts };
  }

  // ---------- FIRST_k, FOLLOW_k and strong LL(k) ----------
  // Strings are kept as arrays; sets as Maps from a key to the array. x ⊕k y is the first k symbols of xy.
  const key = (x) => x.join('\u0001');
  function concatK(A, B, k) {
    const out = new Map();
    for (const x of A.values()) {
      if (x.length >= k) { out.set(key(x.slice(0, k)), x.slice(0, k)); continue; }
      for (const y of B.values()) { const z = x.concat(y).slice(0, k); out.set(key(z), z); }
    }
    return out;
  }
  const single = (x) => new Map([[key(x), x]]);
  function firstKOf(G, F, seq, k) {
    let acc = single([]);
    // no early stop: FIRST_k counts only strings the whole of seq can finish deriving
    for (const X of seq) acc = concatK(acc, Gr.isN(G, X) ? F.get(X) : single([X]), k);
    return acc;
  }
  function firstK(G, k) {
    const F = new Map(G.nonterminals.map((A) => [A, new Map()])), trace = [];
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      for (const p of G.productions) {
        // a rule contributes only once all of its nonterminals have something (otherwise ⊕ gives ∅)
        const got = firstKOf(G, F, p.rhs, k), tgt = F.get(p.A), add = [];
        for (const [kk, x] of got) if (!tgt.has(kk)) { tgt.set(kk, x); add.push(x); }
        if (add.length) { changed = true; trace.push({ kind: 'firstk', round, A: p.A, prod: p.id, added: add, say: 'Round ' + round + ': ' + showProd(G, p) + ' adds ' + add.map(show).join(', ') + ' to FIRST' + k + '(' + p.A + ').' }); }
      }
      trace.push({ kind: 'round', round, changed, say: changed ? 'End of round ' + round + '.' : 'Round ' + round + ' added nothing: FIRST' + k + ' is final.' });
    }
    const out = {}; for (const [A, m] of F) out[A] = [...m.values()].sort((a, b) => a.length - b.length || (key(a) < key(b) ? -1 : 1));
    return { sets: out, maps: F, trace };
  }
  function followK(G, k, FK) {
    FK = FK || firstK(G, k);
    const F = FK.maps, Fo = new Map(G.nonterminals.map((A) => [A, new Map()])), trace = [];
    Fo.get(G.start).set(END, [END]);
    for (let round = 1, changed = true; changed; round++) {
      changed = false;
      for (const p of G.productions) p.rhs.forEach((B, i) => {
        if (!Gr.isN(G, B)) return;
        const got = concatK(firstKOf(G, F, p.rhs.slice(i + 1), k), Fo.get(p.A), k), tgt = Fo.get(B), add = [];
        for (const [kk, x] of got) if (!tgt.has(kk)) { tgt.set(kk, x); add.push(x); }
        if (add.length) { changed = true; trace.push({ kind: 'followk', round, A: B, prod: p.id, added: add, say: 'Round ' + round + ': in ' + showProd(G, p) + ', add ' + add.map(show).join(', ') + ' to FOLLOW' + k + '(' + B + ').' }); }
      });
    }
    const out = {}; for (const [A, m] of Fo) out[A] = [...m.values()];
    return { sets: out, maps: Fo, trace };
  }
  // Strong LL(k): for each nonterminal, the sets FIRST_k(α FOLLOW_k(A)) of its alternatives are disjoint.
  function strongLLk(G, k) {
    const FK = firstK(G, k), FO = followK(G, k, FK), conflicts = [], trace = [], lookahead = {};
    for (const A of G.nonterminals) {
      const alts = Gr.info(G).byA.get(A).map((p) => ({ p, set: concatK(firstKOf(G, FK.maps, p.rhs, k), FO.maps.get(A), k) }));
      lookahead[A] = alts.map((x) => ({ prod: x.p.id, strings: [...x.set.values()] }));
      for (let i = 0; i < alts.length; i++) for (let j = i + 1; j < alts.length; j++) {
        const both = [...alts[i].set.keys()].filter((x) => alts[j].set.has(x)).map((x) => alts[i].set.get(x));
        if (both.length) {
          const c = { A, prods: [alts[i].p.id, alts[j].p.id], strings: both, say: showProd(G, alts[i].p) + ' and ' + showProd(G, alts[j].p) + ' can both be chosen when the next ' + k + ' symbols are ' + both.map(show).join(', ') + '.' };
          conflicts.push(c); trace.push(Object.assign({ kind: 'conflict' }, c));
        }
      }
    }
    trace.push({ kind: 'verdict', say: conflicts.length ? 'Not strong LL(' + k + ').' : 'Strong LL(' + k + '): ' + k + ' symbols of lookahead always pick the rule.' });
    return { ok: !conflicts.length, conflicts, lookahead, first: FK.sets, follow: FO.sets, trace };
  }

  T.ll = { firstFollow, firstOf, ll1Table, predictive, codegen, firstK, followK, strongLLk };
})();
