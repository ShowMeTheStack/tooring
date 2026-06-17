// The LR family: LR(0) items, closure and goto, the canonical LR(0) and LR(1) collections, LALR(1) three
// ways (merging LR(1) states with equal cores, propagating lookaheads between LR(0) kernels, and the
// relations method over nonterminal transitions), the LR(0)/SLR(1)/LALR(1)/LR(1) tables with their
// conflicts, yacc-style precedence, the shift-reduce driver and a classifier.
//
// PUBLIC API (T.lr). G is a context-free grammar from T.grammar; every result carries a trace of
// { kind, say, ...data } steps.
//   augment(G)                     → aug: G with a fresh start S' and rule 0 S' → S (rule k of aug is rule
//                                    k−1 of G). aug.original === G.
//   closure0(aug, kernel)          → { items, trace }       items are { p, d } (rule, dot position)
//                                    trace kinds: 'kernel', 'closure'
//   goto0(aug, items, X)           → kernel items after moving the dot over X
//   lr0Collection(G)               → { aug, states: [{ id, kernel, items, trans: { X: id } }], trace }
//                                    trace kinds: 'state', 'closure', 'transition'
//   closure1(aug, kernel)          → { items, trace }       items are { p, d, la: [terminals] }
//   lr1Collection(G)               → same shape, items with lookaheads; trace adds 'closure' with la
//   lalrByMerge(G)                 → LALR states numbered like the LR(0) collection; trace 'merge'
//   lalrByPropagation(G)           → same, by spontaneous lookaheads and propagation from each kernel item
//                                    with the dummy lookahead '#'; trace 'spontaneous', 'propagates',
//                                    'pass', 'add'
//   lalrByRelations(G)             → lookaheads of complete items only, via DR, reads, includes and
//                                    lookback with the digraph traversal; trace 'dr', 'reads',
//                                    'includes', 'lookback', 'read', 'follow', 'la'
//   buildTable(G, kind, opts)      → table; kind 'lr0' | 'slr' | 'lalr' | 'lr1'; opts.precedence (default
//                                    true) uses %left/%right/%nonassoc; opts.lalr 'propagation' | 'merge'
//                                    table = { kind, G, aug, states, terminals, nonterminals,
//                                      action[s][a], goto[s][A], cells[s][a] (every candidate),
//                                      conflicts, resolutions, trace }
//                                    trace kinds: 'shift', 'reduce', 'accept', 'goto', 'conflict', 'resolve'
//   parse(table, input, opts)      → { accepted, tree, trace, error }; opts.maxSteps (default 10000),
//                                    opts.trace false keeps only the final step (fast recognition)
//                                    trace kinds: 'start', 'shift', 'reduce', 'accept', 'error', 'limit'
//   classify(G)                    → { verdict: 'LR(0)'|'SLR(1)'|'LALR(1)'|'LR(1)'|null, levels, reasons, trace }
//   itemText(aug, item), actionText(action)
// Actions: { type: 'shift', state } | { type: 'reduce', prod } (aug rule id) | { type: 'accept' } |
// { type: 'error', why } (a %nonassoc cell). The accept action sits in the $ column of the state holding
// S' → S •. In the LR(0) table a complete item reduces on every terminal and on $.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Gr = () => T.grammar;
  const END = '$', DUMMY = '#';

  // ---------- the augmented grammar ----------
  const augCache = new WeakMap();
  function augment(G) {
    if (augCache.has(G)) return augCache.get(G);
    if (!Gr().info(G).cf) throw new Error('LR parsing needs a context-free grammar');
    let S2 = G.start + "'";
    while (G.nonterminals.includes(S2) || G.terminals.includes(S2)) S2 += "'";
    const prods = [{ A: S2, rhs: [G.start] }].concat(G.productions.map((p) => ({ A: p.A, rhs: p.rhs, prec: p.prec })));
    // every terminal is passed as a token so a terminal written as a capital letter stays a terminal
    const aug = Gr().make(S2, prods, { nonterminals: G.nonterminals, terminals: G.terminals, tokens: G.terminals, precedence: G.precedence, words: G.words });
    aug.original = G;
    augCache.set(G, aug);
    return aug;
  }
  const isN = (aug, s) => Gr().isN(aug, s);

  // ---------- FIRST and FOLLOW (private, untraced) ----------
  const ffCache = new WeakMap();
  function firstFollow(aug) {
    if (ffCache.has(aug)) return ffCache.get(aug);
    const N = Gr().info(aug).N, nullable = new Set(), first = new Map(), follow = new Map();
    for (const A of aug.nonterminals) { first.set(A, new Set()); follow.set(A, new Set()); }
    let changed = true;
    while (changed) {
      changed = false;
      for (const p of aug.productions) {
        const f = first.get(p.A); let all = true;
        for (const s of p.rhs) {
          if (!N.has(s)) { if (!f.has(s)) { f.add(s); changed = true; } all = false; break; }
          for (const x of first.get(s)) if (!f.has(x)) { f.add(x); changed = true; }
          if (!nullable.has(s)) { all = false; break; }
        }
        if (all && !nullable.has(p.A)) { nullable.add(p.A); changed = true; }
      }
    }
    follow.get(aug.start).add(END);
    changed = true;
    while (changed) {
      changed = false;
      for (const p of aug.productions) {
        for (let i = 0; i < p.rhs.length; i++) {
          const B = p.rhs[i];
          if (!N.has(B)) continue;
          const r = seqFirst({ N, nullable, first }, p.rhs.slice(i + 1));
          const fb = follow.get(B);
          for (const x of r.set) if (!fb.has(x)) { fb.add(x); changed = true; }
          if (r.nullable) for (const x of follow.get(p.A)) if (!fb.has(x)) { fb.add(x); changed = true; }
        }
      }
    }
    const ff = { N, nullable, first, follow };
    ffCache.set(aug, ff);
    return ff;
  }
  // FIRST of a string of symbols; anything that is not a nonterminal (including '#' and '$') is a terminal.
  function seqFirst(ff, seq) {
    const set = new Set();
    for (const s of seq) {
      if (!ff.N.has(s)) { set.add(s); return { set, nullable: false }; }
      for (const x of ff.first.get(s)) set.add(x);
      if (!ff.nullable.has(s)) return { set, nullable: false };
    }
    return { set, nullable: true };
  }

  // ---------- display ----------
  function itemText(aug, it) {
    const p = aug.productions[it.p], sh = (s) => Gr().showSym(aug, s);
    const body = p.rhs.slice(0, it.d).map(sh).concat(['•'], p.rhs.slice(it.d).map(sh)).join(' ');
    const core = p.A + ' → ' + body;
    if (it.la === undefined) return core;
    return '[' + core + ', ' + [].concat(it.la).join('/') + ']';
  }
  function actionText(a) {
    if (!a) return '';
    return a.type === 'shift' ? 's' + a.state : a.type === 'reduce' ? 'r' + a.prod : a.type === 'accept' ? 'acc' : 'err';
  }
  const coreKey = (it) => it.p + '.' + it.d;
  const sortItems = (items) => items.slice().sort((a, b) => a.p - b.p || a.d - b.d);
  const nextSym = (aug, it) => aug.productions[it.p].rhs[it.d];
  const laList = (set) => [...set].sort((a, b) => (a === END ? 1 : b === END ? -1 : a < b ? -1 : a > b ? 1 : 0));

  // ---------- LR(0) ----------
  function closure0(aug, kernel) {
    const items = [], seen = new Set(), trace = [];
    for (const it of kernel) { const k = coreKey(it); if (!seen.has(k)) { seen.add(k); items.push({ p: it.p, d: it.d }); trace.push({ kind: 'kernel', item: { p: it.p, d: it.d }, say: itemText(aug, it) + ' is in the kernel.' }); } }
    const byA = Gr().info(aug).byA;
    for (let i = 0; i < items.length; i++) {
      const B = nextSym(aug, items[i]);
      if (B === undefined || !isN(aug, B)) continue;
      for (const q of byA.get(B)) {
        const it = { p: q.id, d: 0 }, k = coreKey(it);
        if (seen.has(k)) continue;
        seen.add(k); items.push(it);
        trace.push({ kind: 'closure', item: it, from: items[i], say: 'The dot in ' + itemText(aug, items[i]) + ' stands before ' + B + ', so add ' + itemText(aug, it) + '.' });
      }
    }
    return { items, trace };
  }
  function goto0(aug, items, X) {
    return sortItems(items.filter((it) => nextSym(aug, it) === X).map((it) => ({ p: it.p, d: it.d + 1 })));
  }
  // Symbols after a dot, in the order they first appear in the state (so states are numbered predictably).
  function symbolsAfterDot(aug, items) {
    const out = [];
    for (const it of items) { const X = nextSym(aug, it); if (X !== undefined && !out.includes(X)) out.push(X); }
    return out;
  }
  const lr0Cache = new WeakMap();
  function lr0Collection(G) {
    if (lr0Cache.has(G)) return lr0Cache.get(G);
    const aug = augment(G), states = [], index = new Map(), trace = [];
    const kkey = (kernel) => kernel.map(coreKey).join(' ');
    const add = (kernel, from, X) => {
      const k = kkey(kernel);
      if (index.has(k)) return index.get(k);
      const c = closure0(aug, kernel), id = states.length;
      states.push({ id, kernel, items: c.items, trans: {} });
      index.set(k, id);
      trace.push({ kind: 'state', state: id, kernel, items: c.items, from, symbol: X,
        say: 'State ' + id + (from === undefined ? ' starts from ' + itemText(aug, kernel[0]) : ' is goto(' + from + ', ' + X + ')') + ' and has ' + c.items.length + ' item' + (c.items.length === 1 ? '' : 's') + '.' });
      for (const st of c.trace) if (st.kind === 'closure') trace.push(Object.assign({ state: id }, st));
      return id;
    };
    add([{ p: 0, d: 0 }]);
    for (let s = 0; s < states.length; s++) {
      for (const X of symbolsAfterDot(aug, states[s].items)) {
        const kernel = goto0(aug, states[s].items, X), existed = index.has(kkey(kernel));
        const t = add(kernel, s, X);
        states[s].trans[X] = t;
        trace.push({ kind: 'transition', from: s, symbol: X, to: t, existing: existed,
          say: 'On ' + X + ', state ' + s + ' goes to ' + (existed ? 'the existing state ' : 'state ') + t + '.' });
      }
    }
    const r = { aug, states, trace };
    lr0Cache.set(G, r);
    return r;
  }

  // ---------- LR(1) ----------
  // A state is kept as Map(core key → Set of lookaheads); items with the same core are shown merged.
  function closure1(aug, kernel) {
    const ff = firstFollow(aug), byA = Gr().info(aug).byA;
    const m = new Map(), order = [], trace = [], work = [];
    // a = null only makes sure the core is present: an item whose lookahead set comes out empty (when
    // what follows can generate nothing) still belongs to the state, just as in the LR(0) closure
    const put = (p, d, a) => {
      const k = p + '.' + d;
      if (!m.has(k)) { m.set(k, new Set()); order.push({ p, d }); work.push([p, d, null]); }
      const s = m.get(k);
      if (a === null || s.has(a)) return false;
      s.add(a); work.push([p, d, a]); return true;
    };
    for (const it of kernel) {
      put(it.p, it.d, null);
      for (const a of [].concat(it.la)) if (put(it.p, it.d, a)) trace.push({ kind: 'kernel', item: { p: it.p, d: it.d, la: a }, say: itemText(aug, { p: it.p, d: it.d, la: a }) + ' is in the kernel.' });
    }
    while (work.length) {
      const [p, d, a] = work.shift();
      const rhs = aug.productions[p].rhs, B = rhs[d];
      if (B === undefined || !ff.N.has(B)) continue;
      if (a === null) { for (const q of byA.get(B)) put(q.id, 0, null); continue; }
      const beta = rhs.slice(d + 1), f = seqFirst(ff, beta.concat([a])).set;
      for (const q of byA.get(B)) for (const b of laList(f)) {
        if (put(q.id, 0, b)) trace.push({ kind: 'closure', item: { p: q.id, d: 0, la: b }, from: { p, d, la: a },
          say: 'From ' + itemText(aug, { p, d, la: a }) + ' add ' + itemText(aug, { p: q.id, d: 0, la: b }) + ', since ' + b + ' is in FIRST(' + (beta.length ? beta.join(' ') + ' ' : '') + a + ').' });
      }
    }
    const items = order.map((it) => ({ p: it.p, d: it.d, la: laList(m.get(it.p + '.' + it.d)) }));
    return { items, trace };
  }
  function goto1(aug, items, X) {
    return sortItems(items.filter((it) => nextSym(aug, it) === X).map((it) => ({ p: it.p, d: it.d + 1, la: it.la.slice() })));
  }
  const fullKey = (items) => sortItems(items).map((it) => coreKey(it) + ':' + it.la.join(',')).join(' ');
  const coresKey = (items) => sortItems(items).map(coreKey).join(' ');
  const lr1Cache = new WeakMap();
  function lr1Collection(G) {
    if (lr1Cache.has(G)) return lr1Cache.get(G);
    const aug = augment(G), states = [], index = new Map(), trace = [];
    const add = (kernel, from, X) => {
      const k = fullKey(kernel);
      if (index.has(k)) return index.get(k);
      const c = closure1(aug, kernel), id = states.length;
      states.push({ id, kernel, items: c.items, trans: {} });
      index.set(k, id);
      trace.push({ kind: 'state', state: id, kernel, items: c.items, from, symbol: X,
        say: 'State ' + id + (from === undefined ? ' starts from ' + itemText(aug, kernel[0]) : ' is goto(' + from + ', ' + X + ')') + ' with ' + c.items.length + ' item core' + (c.items.length === 1 ? '' : 's') + '.' });
      for (const st of c.trace) if (st.kind === 'closure') trace.push(Object.assign({ state: id }, st));
      return id;
    };
    add([{ p: 0, d: 0, la: [END] }]);
    for (let s = 0; s < states.length; s++) {
      for (const X of symbolsAfterDot(aug, states[s].items)) {
        const kernel = goto1(aug, states[s].items, X), existed = index.has(fullKey(kernel));
        const t = add(kernel, s, X);
        states[s].trans[X] = t;
        trace.push({ kind: 'transition', from: s, symbol: X, to: t, existing: existed, say: 'On ' + X + ', state ' + s + ' goes to ' + (existed ? 'the existing state ' : 'state ') + t + '.' });
      }
    }
    const r = { aug, states, trace };
    lr1Cache.set(G, r);
    return r;
  }

  // ---------- LALR(1) by merging LR(1) states with the same core ----------
  function lalrByMerge(G) {
    const lr0 = lr0Collection(G), lr1 = lr1Collection(G), aug = lr0.aug, trace = [];
    const byCore = new Map(lr0.states.map((s) => [coresKey(s.kernel), s.id]));
    const groups = lr0.states.map(() => []);
    for (const s of lr1.states) groups[byCore.get(coresKey(s.kernel))].push(s.id);
    const states = lr0.states.map((s0) => {
      const ids = groups[s0.id];
      const mergeItems = (pick) => {
        const m = new Map();
        for (const id of ids) for (const it of pick(lr1.states[id])) { const k = coreKey(it); if (!m.has(k)) m.set(k, new Set()); it.la.forEach((a) => m.get(k).add(a)); }
        return (pick === kern ? s0.kernel : s0.items).map((it) => ({ p: it.p, d: it.d, la: laList(m.get(coreKey(it)) || []) }));
      };
      const kern = (s) => s.kernel, all = (s) => s.items;
      const st = { id: s0.id, kernel: mergeItems(kern), items: mergeItems(all), trans: Object.assign({}, s0.trans), from: ids };
      trace.push({ kind: 'merge', state: s0.id, lr1States: ids, items: st.items,
        say: ids.length > 1 ? 'LR(1) states ' + ids.join(', ') + ' share a core, so they merge into state ' + s0.id + ' with the union of their lookaheads.'
          : 'LR(1) state ' + ids[0] + ' has a core of its own and becomes state ' + s0.id + '.' });
      return st;
    });
    return { aug, states, lr1, trace };
  }

  // ---------- LALR(1) by propagating lookaheads between LR(0) kernels ----------
  function lalrByPropagation(G) {
    const lr0 = lr0Collection(G), aug = lr0.aug, trace = [];
    const la = lr0.states.map((s) => new Map(s.kernel.map((it) => [coreKey(it), new Set()])));
    const links = lr0.states.map((s) => new Map(s.kernel.map((it) => [coreKey(it), []])));
    la[0].get('0.0').add(END);
    trace.push({ kind: 'spontaneous', state: 0, item: { p: 0, d: 0 }, la: END, say: 'The end marker $ is the lookahead of ' + itemText(aug, { p: 0, d: 0 }) + ' in state 0.' });
    // Determine, for each kernel item, which lookaheads arise on their own and where its own lookaheads flow.
    for (const s of lr0.states) {
      for (const k of s.kernel) {
        const c = closure1(aug, [{ p: k.p, d: k.d, la: [DUMMY] }]);
        for (const it of c.items) {
          const X = nextSym(aug, it);
          if (X === undefined) continue;
          const t = s.trans[X], tk = (it.p + '.' + (it.d + 1));
          for (const a of it.la) {
            if (a === DUMMY) {
              const lst = links[s.id].get(coreKey(k));
              if (!lst.some(([ts, tkk]) => ts === t && tkk === tk)) {
                lst.push([t, tk]);
                trace.push({ kind: 'propagates', from: { state: s.id, item: k }, to: { state: t, item: { p: it.p, d: it.d + 1 } },
                  say: 'Lookaheads of ' + itemText(aug, k) + ' in state ' + s.id + ' propagate to ' + itemText(aug, { p: it.p, d: it.d + 1 }) + ' in state ' + t + '.' });
              }
            } else if (!la[t].get(tk).has(a)) {
              la[t].get(tk).add(a);
              trace.push({ kind: 'spontaneous', state: t, item: { p: it.p, d: it.d + 1 }, la: a, because: { state: s.id, item: k },
                say: a + ' is generated spontaneously for ' + itemText(aug, { p: it.p, d: it.d + 1 }) + ' in state ' + t + ' (closing ' + itemText(aug, k) + ' in state ' + s.id + ').' });
            }
          }
        }
      }
    }
    // Passes: push every kernel item's lookaheads along its links until nothing changes.
    let pass = 0, changed = true;
    while (changed) {
      changed = false; pass++;
      const added = [];
      for (const s of lr0.states) for (const [k, lst] of links[s.id]) for (const [t, tk] of lst) for (const a of la[s.id].get(k)) {
        if (la[t].get(tk).has(a)) continue;
        la[t].get(tk).add(a); changed = true;
        const [p, d] = tk.split('.').map(Number), [p0, d0] = k.split('.').map(Number);
        added.push({ state: t, item: { p, d }, la: a });
        trace.push({ kind: 'add', pass, state: t, item: { p, d }, la: a, from: { state: s.id, item: { p: p0, d: d0 } },
          say: 'Pass ' + pass + ': ' + a + ' flows from ' + itemText(aug, { p: p0, d: d0 }) + ' in state ' + s.id + ' to ' + itemText(aug, { p, d }) + ' in state ' + t + '.' });
      }
      trace.push({ kind: 'pass', pass, added, say: 'Pass ' + pass + ' added ' + added.length + ' lookahead' + (added.length === 1 ? '' : 's') + (added.length ? '.' : '; nothing changes, so the lookaheads are final.') });
    }
    const states = lr0.states.map((s) => {
      const kernel = s.kernel.map((it) => ({ p: it.p, d: it.d, la: laList(la[s.id].get(coreKey(it))) }));
      const c = closure1(aug, kernel);
      const m = new Map(c.items.map((it) => [coreKey(it), it.la]));
      return { id: s.id, kernel, items: s.items.map((it) => ({ p: it.p, d: it.d, la: m.get(coreKey(it)) || [] })), trans: Object.assign({}, s.trans) };
    });
    return { aug, states, passes: pass, trace };
  }

  // ---------- LALR(1) lookaheads through relations on nonterminal transitions ----------
  // For each transition (p, A): DR = terminals readable right after it; reads: through nullable
  // nonterminals; Read = DR closed under reads; includes: (p, A) includes (p', B) when B → β A γ, γ ⇒* ε
  // and p' reaches p on β; Follow = Read closed under includes; a complete item A → ω in state q gets the
  // Follow of every (p, A) from which ω leads to q (lookback).
  function lalrByRelations(G) {
    const lr0 = lr0Collection(G), aug = lr0.aug, ff = firstFollow(aug), trace = [], S = lr0.states;
    const nts = [], idx = new Map();
    for (const s of S) for (const X of Object.keys(s.trans)) if (ff.N.has(X)) { idx.set(s.id + ' ' + X, nts.length); nts.push({ p: s.id, A: X }); }
    const name = (i) => '(' + nts[i].p + ', ' + nts[i].A + ')';
    const run = (p, seq) => { for (const X of seq) { p = S[p].trans[X]; if (p === undefined) return undefined; } return p; };
    const DR = nts.map((x, i) => {
      const r = S[x.p].trans[x.A], set = new Set(Object.keys(S[r].trans).filter((t) => !ff.N.has(t)));
      if (S[r].items.some((it) => it.p === 0 && it.d === 1)) set.add(END);
      trace.push({ kind: 'dr', trans: i, set: laList(set), say: 'DR' + name(i) + ' = {' + laList(set).join(', ') + '}: terminals state ' + r + ' can shift' + (set.has(END) ? ', and $ since it accepts' : '') + '.' });
      return set;
    });
    const reads = nts.map((x, i) => {
      const r = S[x.p].trans[x.A], out = [];
      for (const C of Object.keys(S[r].trans)) if (ff.N.has(C) && ff.nullable.has(C)) {
        const j = idx.get(r + ' ' + C); out.push(j);
        trace.push({ kind: 'reads', from: i, to: j, say: name(i) + ' reads ' + name(j) + ' because ' + C + ' can vanish.' });
      }
      return out;
    });
    const includes = nts.map(() => []);
    for (let j = 0; j < nts.length; j++) {
      const { p: p0, A: B } = nts[j];
      for (const q of aug.productions) {
        if (q.A !== B) continue;
        let p = p0;
        for (let k = 0; k < q.rhs.length && p !== undefined; k++) {
          const X = q.rhs[k];
          if (ff.N.has(X) && seqFirst(ff, q.rhs.slice(k + 1)).nullable) {
            const i = idx.get(p + ' ' + X);
            if (i !== undefined && !includes[i].includes(j)) {
              includes[i].push(j);
              trace.push({ kind: 'includes', from: i, to: j, prod: q.id, say: name(i) + ' includes ' + name(j) + ' through ' + Gr().showProd(aug, q) + '.' });
            }
          }
          p = S[p].trans[X];
        }
      }
    }
    // the digraph traversal: sets flow backwards along edges, and a strongly connected group shares one set
    function digraph(base, edges, label) {
      const F = base.map((s) => new Set(s)), N = new Array(base.length).fill(0), stack = [];
      const visit = (x) => {
        stack.push(x); const d = stack.length; N[x] = d;
        for (const y of edges[x]) {
          if (N[y] === 0) visit(y);
          N[x] = Math.min(N[x], N[y]);
          for (const a of F[y]) F[x].add(a);
        }
        if (N[x] === d) { for (;;) { const top = stack.pop(); N[top] = Infinity; if (top === x) break; F[top] = new Set(F[x]); } }
      };
      for (let x = 0; x < base.length; x++) if (N[x] === 0) visit(x);
      F.forEach((s, i) => trace.push({ kind: label, trans: i, set: laList(s), say: (label === 'read' ? 'Read' : 'Follow') + name(i) + ' = {' + laList(s).join(', ') + '}.' }));
      return F;
    }
    const Read = digraph(DR, reads, 'read');
    const Fol = digraph(Read, includes, 'follow');
    const states = S.map((s) => ({ id: s.id, trans: Object.assign({}, s.trans), items: [] }));
    for (const s of S) for (const it of s.items) {
      const q = aug.productions[it.p];
      if (it.d !== q.rhs.length || it.p === 0) continue;
      const set = new Set(), from = [];
      for (let p = 0; p < S.length; p++) {
        if (run(p, q.rhs) !== s.id) continue;
        const i = idx.get(p + ' ' + q.A);
        if (i === undefined) continue;
        from.push(i);
        trace.push({ kind: 'lookback', state: s.id, prod: q.id, trans: i, say: '(' + s.id + ', ' + Gr().showProd(aug, q) + ') looks back to ' + name(i) + '.' });
        for (const a of Fol[i]) set.add(a);
      }
      states[s.id].items.push({ p: it.p, d: it.d, la: laList(set) });
      trace.push({ kind: 'la', state: s.id, item: { p: it.p, d: it.d }, la: laList(set), say: 'In state ' + s.id + ', reduce by ' + Gr().showProd(aug, q) + ' on {' + laList(set).join(', ') + '}.' });
    }
    return { aug, transitions: nts, DR: DR.map(laList), Read: Read.map(laList), Follow: Fol.map(laList), states, trace };
  }

  // ---------- tables ----------
  function tokenPrec(G, a) { return G.precedence && G.precedence[a] ? G.precedence[a] : null; }
  function rulePrec(G, prod) {
    if (prod.prec) return tokenPrec(G, prod.prec);
    for (let i = prod.rhs.length - 1; i >= 0; i--) if (!Gr().isN(G, prod.rhs[i]) && tokenPrec(G, prod.rhs[i])) return tokenPrec(G, prod.rhs[i]);
    return null;
  }
  const sameAction = (a, b) => a.type === b.type && a.state === b.state && a.prod === b.prod;
  function buildTable(G, kind, opts) {
    opts = Object.assign({ precedence: true, lalr: 'propagation' }, opts || {});
    kind = kind || 'lalr';
    let coll;
    if (kind === 'lr0' || kind === 'slr') coll = lr0Collection(G);
    else if (kind === 'lr1') coll = lr1Collection(G);
    else if (kind === 'lalr') coll = opts.lalr === 'merge' ? lalrByMerge(G) : lalrByPropagation(G);
    else throw new Error('unknown table kind ' + kind);
    const aug = coll.aug, ff = firstFollow(aug), states = coll.states, trace = [];
    const terminals = G.terminals.concat([END]), nonterminals = G.nonterminals.slice();
    const cells = states.map(() => ({})), action = states.map(() => ({})), gotoT = states.map(() => ({}));
    const why = states.map(() => ({}));   // the items behind each candidate action
    const offer = (s, a, act, item) => {
      const c = (cells[s][a] = cells[s][a] || []);
      if (!c.some((x) => sameAction(x, act))) c.push(act);
      (why[s][a] = why[s][a] || []).push({ action: act, item });
    };
    for (const st of states) {
      for (const [X, t] of Object.entries(st.trans)) {
        if (ff.N.has(X)) { gotoT[st.id][X] = t; trace.push({ kind: 'goto', state: st.id, symbol: X, to: t, say: 'goto[' + st.id + ', ' + X + '] = ' + t + '.' }); }
      }
      for (const it of st.items) {
        const q = aug.productions[it.p], X = q.rhs[it.d];
        if (X !== undefined) {
          if (!ff.N.has(X)) {
            offer(st.id, X, { type: 'shift', state: st.trans[X] }, it);
            trace.push({ kind: 'shift', state: st.id, symbol: X, to: st.trans[X], item: it, say: itemText(aug, { p: it.p, d: it.d }) + ' in state ' + st.id + ' shifts ' + X + ' to state ' + st.trans[X] + '.' });
          }
          continue;
        }
        if (it.p === 0) {
          offer(st.id, END, { type: 'accept' }, it);
          trace.push({ kind: 'accept', state: st.id, item: it, say: 'State ' + st.id + ' holds ' + itemText(aug, { p: 0, d: 1 }) + ', so it accepts on $.' });
          continue;
        }
        let la, src;
        if (kind === 'lr0') { la = terminals; src = 'every terminal (LR(0) uses no lookahead)'; }
        else if (kind === 'slr') { la = laList(ff.follow.get(q.A)); src = 'FOLLOW(' + q.A + ')'; }
        else { la = it.la; src = 'the item\'s lookaheads'; }
        for (const a of la) offer(st.id, a, { type: 'reduce', prod: it.p }, it);
        trace.push({ kind: 'reduce', state: st.id, prod: it.p, on: la.slice(), item: it,
          say: 'State ' + st.id + ' reduces by ' + Gr().showProd(aug, q) + ' on ' + (la.length ? '{' + la.join(', ') + '}' : 'nothing') + ', from ' + src + '.' });
      }
    }
    // settle each cell
    const conflicts = [], resolutions = [];
    for (const st of states) {
      for (const a of terminals) {
        const c = cells[st.id][a];
        if (!c) continue;
        if (c.length === 1) { action[st.id][a] = c[0]; continue; }
        const items = (why[st.id][a] || []).map((w) => ({ item: w.item, text: itemText(aug, w.item.la ? { p: w.item.p, d: w.item.d, la: a } : w.item), action: w.action }));
        const reds = c.filter((x) => x.type !== 'shift').sort((x, y) => (x.type === 'accept' ? 0 : x.prod) - (y.type === 'accept' ? 0 : y.prod));
        const sh = c.find((x) => x.type === 'shift');
        let red = reds[0] || null;
        if (reds.length > 1) {
          const conf = { state: st.id, symbol: a, type: 'reduce/reduce', actions: reds.slice(), items: items.filter((x) => x.action.type !== 'shift'), chosen: red,
            say: 'State ' + st.id + ' on ' + a + ' could reduce by ' + reds.map((x) => (x.type === 'accept' ? 'accepting' : Gr().showProd(aug, aug.productions[x.prod]))).join(' or by ') + '; the earlier rule wins by default.' };
          conflicts.push(conf); trace.push(Object.assign({ kind: 'conflict' }, conf));
        }
        let chosen = red || sh;
        if (sh && red) {
          const tp = tokenPrec(G, a), rp = red.type === 'reduce' ? rulePrec(G, G.productions[red.prod - 1]) : null;
          const rtext = Gr().showProd(aug, aug.productions[red.prod || 0]);
          if (opts.precedence && tp && rp) {
            let decided, reason;
            if (tp.level > rp.level) { decided = 'shift'; reason = a + ' binds tighter than the rule ' + rtext; }
            else if (tp.level < rp.level) { decided = 'reduce'; reason = 'the rule ' + rtext + ' binds tighter than ' + a; }
            else if (tp.assoc === 'left') { decided = 'reduce'; reason = 'equal precedence and ' + a + ' is left-associative'; }
            else if (tp.assoc === 'right') { decided = 'shift'; reason = 'equal precedence and ' + a + ' is right-associative'; }
            else { decided = 'error'; reason = 'equal precedence and ' + a + ' is non-associative, so the input is an error here'; }
            chosen = decided === 'shift' ? sh : decided === 'reduce' ? red : { type: 'error', why: 'nonassoc' };
            const res = { state: st.id, symbol: a, shift: sh, reduce: red, decided, chosen, items: items, say: 'State ' + st.id + ' on ' + a + ': ' + decided + ', because ' + reason + '.' };
            resolutions.push(res); trace.push(Object.assign({ kind: 'resolve' }, res));
          } else {
            chosen = sh;
            const conf = { state: st.id, symbol: a, type: 'shift/reduce', actions: [sh, red], items: items, chosen: sh,
              say: 'State ' + st.id + ' on ' + a + ' could shift to state ' + sh.state + ' or reduce by ' + rtext + '; shift wins by default.' };
            conflicts.push(conf); trace.push(Object.assign({ kind: 'conflict' }, conf));
          }
        }
        action[st.id][a] = chosen;
      }
    }
    return { kind, G, aug, states, terminals, nonterminals, action, goto: gotoT, cells, conflicts, resolutions, trace };
  }

  // ---------- the shift-reduce driver ----------
  function parse(table, input, opts) {
    opts = Object.assign({ maxSteps: 10000, trace: true }, opts || {});
    const { G, aug } = table;
    const w = Gr().input(G, input), inp = w.concat([END]);
    const stack = [0], syms = [], nodes = [], trace0 = [];
    let i = 0;
    // without a trace only the last step is kept, and the narration is still built for it
    const trace = opts.trace ? trace0 : { push: (x) => { trace0[0] = x; } };
    const snap = (extra) => Object.assign({ stack: stack.slice(), symbols: syms.slice(), input: inp.slice(i) }, extra);
    trace.push(snap({ kind: 'start', say: 'Start in state 0 with the whole input ' + Gr().show(w) + ' followed by $.' }));
    for (let n = 0; n < opts.maxSteps; n++) {
      const s = stack[stack.length - 1], a = inp[i], act = table.action[s][a];
      if (!act || act.type === 'error') {
        const expected = table.terminals.filter((t) => table.action[s][t] && table.action[s][t].type !== 'error');
        const msg = act ? 'the precedence declarations make ' + a + ' an error here (non-associative)' :
          'state ' + s + ' has no action on ' + a + '; expected ' + (expected.length ? expected.join(', ') : 'nothing');
        trace.push(snap({ kind: 'error', state: s, symbol: a, expected, say: 'Error: ' + msg + '.' }));
        return { accepted: false, tree: null, trace: trace0, error: { position: i, symbol: a, expected, message: msg } };
      }
      if (act.type === 'shift') {
        trace.push(snap({ kind: 'shift', state: s, symbol: a, to: act.state, action: 's' + act.state, say: 'Shift ' + a + ' and go to state ' + act.state + '.' }));
        stack.push(act.state); syms.push(a); nodes.push({ sym: a, prod: null, children: null }); i++;
      } else if (act.type === 'reduce') {
        const q = aug.productions[act.prod], k = q.rhs.length;
        const handle = { start: syms.length - k, end: syms.length };
        const before = snap({});
        stack.splice(stack.length - k, k); syms.splice(syms.length - k, k);
        const kids = nodes.splice(nodes.length - k, k);
        const t = stack[stack.length - 1], g = table.goto[t][q.A];
        trace.push(Object.assign(before, { kind: 'reduce', state: s, symbol: a, prod: act.prod, handle, exposed: t, goto: g, action: 'r' + act.prod,
          say: 'Reduce by ' + Gr().showProd(aug, q) + ': the handle ' + (k ? Gr().show(q.rhs) : 'ε') + ' comes off, state ' + t + ' is exposed, and goto(' + t + ', ' + q.A + ') = ' + g + '.' }));
        if (g === undefined) return { accepted: false, tree: null, trace: trace0, error: { position: i, symbol: a, expected: [], message: 'no goto entry' } };
        stack.push(g); syms.push(q.A); nodes.push({ sym: q.A, prod: act.prod - 1, children: kids });
      } else {
        trace.push(snap({ kind: 'accept', state: s, action: 'acc', say: 'Accept: the input reduced to ' + G.start + '.' }));
        return { accepted: true, tree: nodes[0], trace: trace0, error: null };
      }
    }
    trace.push(snap({ kind: 'limit', say: 'Stopped after ' + opts.maxSteps + ' steps.' }));
    return { accepted: false, tree: null, trace: trace0, error: { position: i, message: 'step limit' } };
  }

  // ---------- classification ----------
  function classify(G) {
    const order = [['lr0', 'LR(0)'], ['slr', 'SLR(1)'], ['lalr', 'LALR(1)'], ['lr1', 'LR(1)']];
    const levels = {}, reasons = [], trace = [];
    let verdict = null;
    for (const [k, nm] of order) {
      const t = buildTable(G, k, { precedence: false });
      levels[k] = { ok: t.conflicts.length === 0, conflicts: t.conflicts, states: t.states.length };
      const say = t.conflicts.length ? 'Not ' + nm + ': ' + t.conflicts.length + ' conflict' + (t.conflicts.length === 1 ? '' : 's') + ', first: ' + t.conflicts[0].say
        : 'The ' + nm + ' table (' + t.states.length + ' states) has no conflicts, so the grammar is ' + nm + '.';
      reasons.push(say); trace.push({ kind: 'level', table: k, ok: !t.conflicts.length, conflicts: t.conflicts, say });
      if (!t.conflicts.length && !verdict) verdict = nm;
    }
    if (!verdict) trace.push({ kind: 'none', say: 'Even canonical LR(1) has conflicts: the grammar is not LR(1). Either it is ambiguous or it needs more than one token of lookahead.' });
    return { verdict, levels, reasons, trace };
  }

  T.lr = {
    END, DUMMY, augment, closure0, goto0, lr0Collection, closure1, goto1, lr1Collection,
    lalrByMerge, lalrByPropagation, lalrByRelations, buildTable, parse, classify, itemText, actionText,
  };
})();
