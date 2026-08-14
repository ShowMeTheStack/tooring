// Pushdown automata (part 3): a run with the stack dropping and lifting its cells beside the diagram; a
// nondeterministic run as a tree of configurations growing layer by layer with the accepting branch lit;
// final state and empty stack turned into each other by machines that grow new states in place; a grammar
// turned into a PDA top-down (expand and match) and bottom-up (shift and reduce); a PDA turned into a
// grammar of triples [p X q] read off the "mountain" of its stack; and determinism, with the competing
// moves in red and the number of live configurations per step.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CF = (T.CF = T.CF || {});
  // every stage item of these topics carries the class cf, so the styles in styles-cf.css stay with them
  const topic = (t) => { const run = t.run; t.run = (inp) => CF.mark(run(inp)); return T.topic(t); };
  const Geo = T.geom;

  T.family({ id: 'pda', part: 'context-free', order: 40, title: 'Pushdown automata', blurb: 'A finite control with a stack: runs, nondeterminism as a tree, the two ways to accept, and the two-way bridge between grammars and machines.' });

  const ANBN = 'start q0\nstack-start Z\naccept q2\nq0, a, Z -> q0, A Z\nq0, a, A -> q0, A A\nq0, b, A -> q1, ε\nq1, b, A -> q1, ε\nq1, ε, Z -> q2, Z';
  const WCW = 'start q0\nstack-start Z\naccept q2\nq0, a, ε -> q0, A\nq0, b, ε -> q0, B\nq0, c, ε -> q1, ε\nq1, a, A -> q1, ε\nq1, b, B -> q1, ε\nq1, ε, Z -> q2, Z';
  const WWR = 'start q0\nstack-start Z\naccept q2\nq0, a, ε -> q0, A\nq0, b, ε -> q0, B\nq0, ε, ε -> q1, ε\nq1, a, A -> q1, ε\nq1, b, B -> q1, ε\nq1, ε, Z -> q2, Z';
  const BRACK = 'start q\nstack-start Z\naccept-by empty\nq, (, ε -> q, X\nq, ), X -> q, ε\nq, ε, Z -> q, ε';
  const ANBN_E = 'start p\nstack-start Z\naccept-by empty\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> q, ε\nq, b, A -> q, ε\nq, ε, Z -> q, ε\np, ε, Z -> p, ε';
  const EPSCLASH = 'start q0\nstack-start Z\naccept q2\nq0, a, Z -> q0, A Z\nq0, a, A -> q0, A A\nq0, b, A -> q1, ε\nq1, b, A -> q1, ε\nq1, ε, Z -> q2, Z\nq0, ε, Z -> q2, Z';

  const pdaIn = (def, o) => ({ id: 'm', kind: 'machine', machine: 'pda', label: 'Pushdown automaton', def, check: (v) => CF.checkPda(v, Object.assign({ maxStates: 6 }, o || {})) });
  const wordCheck = (inp) => { const { P } = CF.pda(inp.m); const bad = [...inp.w].find((c) => !P.input.includes(c)); return bad !== undefined ? 'Input: "' + bad + '" is not in the input alphabet {' + P.input.join(', ') + '}' : null; };
  /** The run to show: an accepting path if there is one, else the path that got furthest */
  function bestPath(P, w, opts) {
    const sim = T.pda.simulate(P, w, Object.assign({ maxConfigs: 4000 }, opts || {}));
    if (sim.accepted) return { sim, path: sim.paths[0], accepted: true };
    let best = sim.configs[0];
    for (const c of sim.configs) if (c.pos > best.pos || (c.pos === best.pos && c.depth > best.depth)) best = c;
    return { sim, path: T.pda.pathTo(sim, best.id), accepted: false };
  }
  /** Diagram, stack and input for one configuration; opts: {taken, prefix, good, bad} */
  function runScene(M, pos, P, w, c, opts) {
    opts = opts || {};
    const g = K.graph.draw(M, { pos, active: opts.good || opts.bad ? [] : [c.state], good: opts.good ? [c.state] : [], bad: opts.bad ? [c.state] : [], taken: opts.taken || [], prefix: opts.prefix || 'g', startHot: opts.start });
    const sx = g.box.x + g.box.w + 70;
    const st = CF.stack(c.stack, { x: sx, y: g.box.y + g.box.h, prefix: 'k', max: 9, topLabel: '← top' });
    const iy = g.box.y + g.box.h + 70;
    const s = K.string.draw({ text: w, pos: c.pos, x: g.box.x + Math.max(0, (g.box.w - Math.max(1, w.length) * 44) / 2), y: iy, cw: 44, label: 'input', headText: c.pos >= w.length ? 'end' : 'next', prefix: 'in' });
    return g.items.concat(st.items, s.items);
  }

  // ---- a run ---------------------------------------------------------------------------------------------------
  topic({
    id: 'pda-run', family: 'pda', order: 10, title: 'A PDA runs, its stack beside it',
    blurb: 'Each move reads one symbol or nothing, pops the top of the stack, and pushes a string in its place. The stack is the memory a finite automaton lacks: here it counts the a and pays them back with b.',
    inputs: [pdaIn(ANBN), { id: 'w', kind: 'string', label: 'Input', def: 'aabb', max: 10 }],
    presets: [
      { label: 'aⁿbⁿ: aabb', values: { m: ANBN, w: 'aabb' } },
      { label: 'Stuck at once: ba', values: { m: ANBN, w: 'ba' } },
      { label: 'Read it all, still not accepting: aab', values: { m: ANBN, w: 'aab' } },
      { label: 'The empty input ε', values: { m: ANBN, w: '' } },
      { label: 'Brackets, by empty stack: (()())', values: { m: BRACK, w: '(()())' } },
      { label: 'Middle marker c: abcba', values: { m: WCW, w: 'abcba' } },
    ],
    check: wordCheck,
    counters: [{ id: 'moves', label: 'moves' }, { id: 'read', label: 'symbols read' }, { id: 'height', label: 'stack height' }],
    run(inp) {
      const { P, M } = CF.pda(inp.m);
      const w = T.pda.word(P, inp.w), n = w.length;
      const pos = K.graph.layout(M).pos;
      const { path, accepted } = bestPath(P, w);
      const det = T.pda.deterministic(P).deterministic;
      const F = new T.Frames(['moves', 'read', 'height']);
      const c0 = path[0];
      F.set('height', c0.stack.length);
      F.add({ items: runScene(M, pos, P, w, c0, { start: true }), say: 'Start in ' + P.start + ' with ' + (c0.stack.length ? 'only ' + T.pda.showStack(c0.stack) + ' on the stack' : 'an empty stack') + ', reading ' + CF.show(w) + '. The machine accepts ' + (P.acceptBy === 'empty' ? 'when the input is used up and the stack is empty.' : 'when the input is used up in an accepting state (double ring).') + (det ? '' : ' It is nondeterministic; the run shown is ' + (accepted ? 'a choice of moves that works.' : 'the one that gets furthest.')), meta: { top: path[1] ? (path[1].stack[0] || 'empty') : null, syms: P.stack } });
      for (let i = 1; i < path.length; i++) {
        const a = path[i - 1], b = path[i], t = P.transitions[b.via];
        F.count('moves'); if (t.read) F.count('read'); F.set('height', b.stack.length);
        const pushTxt = t.push.length ? 'push ' + T.pda.showStack(t.push) : 'push nothing';
        F.add({ items: runScene(M, pos, P, w, b, { taken: [CF.edgeOf(t)] }), say: (t.read ? 'Read ' + t.read : 'Read nothing (an ε-move)') + ', ' + (t.pop ? 'pop ' + t.pop : 'leave the stack alone') + ', ' + pushTxt + ', go to ' + t.to + ': ' + CF.config(P, a, w) + ' ⊢ ' + CF.config(P, b, w) + '.', hl: { delta: [String(t.id)] }, meta: { top: path[i + 1] ? (path[i + 1].stack[0] || 'empty') : null, syms: P.stack } });
      }
      const end = path[path.length - 1];
      let say;
      if (accepted) say = 'All input is read and ' + (P.acceptBy === 'empty' ? 'the stack is empty' : end.state + ' is accepting') + ': ' + CF.show(w) + ' is accepted.';
      else if (end.pos < n) say = 'Stuck: in ' + end.state + ' with ' + w[end.pos] + ' next and ' + (end.stack[0] || 'an empty stack') + ' on top there is no move, so this run dies before reading the whole input. ' + CF.show(w) + ' is rejected.';
      else say = 'The input is used up, but ' + (P.acceptBy === 'empty' ? 'the stack still holds ' + T.pda.showStack(end.stack) : end.state + ' is not accepting') + ' and no ε-move helps. ' + CF.show(w) + ' is rejected.';
      F.add({ items: runScene(M, pos, P, w, end, accepted ? { good: true } : { bad: true }), say, mark: accepted ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [CF.pdaTuple(P), CF.pdaTable(P)] } };
    },
    predict: [
      { at: (f, i) => i >= 1 && i <= 4 && f.meta && f.meta.top, once: false, pick: 'option', options: (fr, i) => fr[i].meta.syms.concat(['empty']), ask: 'After the next move, what will be on top of the stack?', answer: (fr, i) => fr[i].meta.top, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A move (q, a, A) → (p, B A) does what to the stack?', options: ['Pops A, pushes B A: B lands on top of A', 'Pushes A', 'Pops A and B', 'Nothing'], answer: 0, why: 'The popped A is put back with B above it: a push of B in effect.' },
      { q: 'Why can a PDA accept aⁿbⁿ when no DFA can?', options: ['Its stack can count without a bound', 'It has more states', 'It reads backwards', 'It has ε-moves'], answer: 0, why: 'One stack symbol per a, popped by each b: the count can be as large as needed.' },
      { q: 'The input is used up, the state is not accepting and no ε-move applies. The PDA…', options: ['rejects on this run', 'accepts', 'loops', 'pops the rest of the stack'], answer: 0, why: 'Acceptance by final state needs an accepting state at the end of the input.' },
      { q: 'What does a move with pop ε do?', options: ['It ignores the stack and removes nothing', 'It empties the stack', 'It pops ε, which is an error', 'It reads ε'], answer: 0, why: 'Popping nothing lets the move fire whatever is on top.' },
    ],
  });

  // ---- the tree of configurations ------------------------------------------------------------------------------
  topic({
    id: 'pda-tree', family: 'pda', order: 20, title: 'Nondeterminism as a tree of configurations',
    blurb: 'Where several moves apply, the machine splits. Every configuration (state, input left, stack) is a node; the word is accepted when some branch accepts. Even palindromes need a guess: where is the middle?',
    inputs: [pdaIn(WWR), { id: 'w', kind: 'string', label: 'Input', def: 'abba', max: 6 }],
    presets: [
      { label: 'Guess the middle: abba', values: { m: WWR, w: 'abba' } },
      { label: 'No branch accepts: aba', values: { m: WWR, w: 'aba' } },
      { label: 'ε: guess at once', values: { m: WWR, w: '' } },
      { label: 'A deterministic machine: one branch', values: { m: WCW, w: 'aca' } },
    ],
    check: wordCheck,
    counters: [{ id: 'configs', label: 'configurations' }, { id: 'live', label: 'live branches' }, { id: 'dead', label: 'dead ends' }],
    run(inp) {
      const { P } = CF.pda(inp.m);
      const w = T.pda.word(P, inp.w);
      const run = T.pda.stepper(P, w, { maxConfigs: 70, keep: true });
      const layers = [[run.configs[0]]];
      while (!run.done && layers.length < 14) { const r = run.step(); if (!r.created.length) break; layers.push(r.created.slice()); }
      const all = run.configs;
      const acc = run.acceptIds.length ? T.pda.pathTo(run, run.acceptIds[0]).map((c) => 'c' + c.id) : [];
      const F = new T.Frames(['configs', 'live', 'dead']);
      const label = (c) => c.state + ' · ' + (w.slice(c.pos).join('') || 'ε') + ' · ' + T.pda.showStack(c.stack);
      const wd = Math.max(...all.map((c) => Geo.textWidth(label(c), 14, { mono: true }))) + 26;
      const build = (upto, final) => {
        const byP = new Map();
        for (const c of all) if (c.depth <= upto && c.parent !== null) { if (!byP.has(c.parent)) byP.set(c.parent, []); byP.get(c.parent).push(c); }
        const node = (c) => {
          const dead = c.dead && c.depth < upto;
          const cls = ['conf', c.accepting ? 'good' : dead ? 'reject' : c.depth === upto ? 'alive' : '', final && !acc.includes('c' + c.id) && acc.length ? 'pruned' : ''].filter(Boolean).join(' ');
          const k = { id: 'c' + c.id, label: label(c), cls, w: wd };
          const ch = byP.get(c.id);
          if (ch) k.children = ch.map(node);
          return k;
        };
        return K.tree.draw(node(all[0]), { prefix: 'ct', gapX: 14, gapY: 74, path: final ? acc : [] }).items;
      };
      F.set('configs', 1).set('live', 1);
      F.add({ items: build(0, false), say: 'The root is the start configuration (' + P.start + ', ' + CF.show(w) + ', ' + T.pda.showStack(all[0].stack) + '): state · input left · stack, top first. Each layer below makes every possible move from the layer above.' });
      for (let d = 1; d < layers.length; d++) {
        const L = layers[d];
        F.set('configs', all.filter((c) => c.depth <= d).length).set('live', L.length).set('dead', all.filter((c) => c.dead && c.depth < d).length);
        const accNow = L.filter((c) => c.accepting);
        const split = layers[d - 1].filter((c) => L.filter((x) => x.parent === c.id).length > 1);
        F.add({ items: build(d, false), say: 'Layer ' + d + ': ' + L.length + ' configuration' + (L.length === 1 ? '' : 's') + '. ' + (split.length ? split.length + ' of the previous layer split, because more than one move applied (reading the next symbol, or guessing with an ε-move). ' : '') + (accNow.length ? 'One of them has read everything and accepts!' : ''), meta: { onPath: acc.filter((id) => L.some((c) => 'c' + c.id === id)).map((id) => 'ct:n:' + id) } });
      }
      F.set('dead', all.filter((c) => c.dead).length);
      F.add({ items: build(layers.length, true), say: acc.length ? 'Some branch accepts, so ' + CF.show(w) + ' is accepted; its path is lit. The other branches guessed wrong and died, which does not matter: one success is enough.' : 'Every branch died' + (run.complete ? '' : ' or hit the search limit') + ': no sequence of guesses works, so ' + CF.show(w) + ' is rejected. A nondeterministic machine rejects only when all its choices fail.', mark: acc.length ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [CF.pdaTuple(P), CF.pdaTable(P)] } };
    },
    predict: [
      { at: (f, i) => i >= 2 && f.meta && f.meta.onPath && f.meta.onPath.length, once: true, pick: 'item', ask: 'Click the configuration in the newest layer that lies on an accepting run.', answer: (fr, i) => fr[i].meta.onPath, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A nondeterministic PDA accepts a word when…', options: ['at least one branch accepts', 'every branch accepts', 'most branches accept', 'the first branch accepts'], answer: 0, why: 'Nondeterminism means the machine may guess: one good guess is enough.' },
      { q: 'Why does the even-palindrome machine need nondeterminism?', options: ['It must guess where the middle is', 'It has two stack symbols', 'It reads ε', 'It never needs it'], answer: 0, why: 'Nothing in the input marks the middle; with a marker c the guess disappears.' },
      { q: 'A configuration is…', options: ['state, remaining input and stack', 'a state', 'a move', 'the stack only'], answer: 0, why: 'These three determine everything the machine can still do.' },
      { q: 'An odd-length word for the palindrome machine wwᴿ…', options: ['has no accepting branch', 'is accepted by the middle guess', 'loops forever', 'is accepted if it starts with a'], answer: 0, why: 'wwᴿ always has even length, so every guess fails.' },
    ],
  });

  // ---- final state and empty stack -----------------------------------------------------------------------------
  topic({
    id: 'pda-accept', family: 'pda', order: 30, title: 'Final state or empty stack: either way',
    blurb: 'A PDA can accept in an accepting state, or when its stack is empty. A bottom marker and one or two new states turn either kind into the other, accepting exactly the same words.',
    inputs: [pdaIn(ANBN), { id: 'w', kind: 'string', label: 'Input to try on the new machine', def: 'ab', max: 6 }],
    presets: [
      { label: 'Final state → empty stack', values: { m: ANBN, w: 'ab' } },
      { label: 'Empty stack → final state', values: { m: BRACK, w: '()' } },
      { label: 'A word the old machine rejects', values: { m: ANBN, w: 'aab' } },
    ],
    check: wordCheck,
    counters: [{ id: 'states', label: 'states' }, { id: 'moves', label: 'moves' }],
    run(inp) {
      const { P } = CF.pda(inp.m);
      const toE = P.acceptBy === 'final';
      const r = toE ? T.pda.toEmpty(P) : T.pda.toFinal(P);
      const Q = r.pda;
      const M2 = T.Machine.parse(T.pda.toString(Q));
      const pos = K.graph.layout(M2).pos;
      const F = new T.Frames(['states', 'moves']);
      const sub = (states, ids) => ({ kind: 'pda', states, start: states.includes(Q.start) ? Q.start : P.start, accept: Q.acceptBy === 'final' ? Q.accept.filter((q) => states.includes(q)) : P.accept, trans: M2.trans.filter((t, i) => ids.includes(i)) });
      // M2.trans follows Q.transitions one for one: the bottom move, the old moves, then the new ones
      const nOld = P.transitions.length;
      const oldIds = Q.transitions.map((t, i) => i).filter((i) => i >= 1 && i <= nOld);
      const m1 = Object.assign(sub(P.states, oldIds), { start: P.start, accept: P.acceptBy === 'final' ? P.accept : [] });
      F.set('states', P.states.length).set('moves', nOld);
      F.add({ items: K.graph.draw(m1, { pos }).items, say: 'The machine accepts ' + (toE ? 'by final state (' + P.accept.join(', ') + ')' : 'by empty stack') + '. Build one that accepts the same words ' + (toE ? 'by empty stack' : 'by final state') + '.' });
      const bot = r.trace.find((s) => s.kind === 'bottom');
      const m2 = sub([Q.start, ...P.states], [0, ...oldIds]);
      m2.accept = P.acceptBy === 'final' ? P.accept : [];
      F.set('states', P.states.length + 1).set('moves', nOld + 1);
      F.add({ items: K.graph.draw(m2, { pos, hot: [Q.start], edgeCls: { [Q.start + '>' + P.start]: 'taken' }, from: { [Q.start]: 'g:s:' + P.start } }).items, say: bot.say + (toE ? ' Without it the old machine might empty its stack by accident, halfway through a word, and the new one would accept wrongly.' : ''), meta: { q: toE ? 'drain' : 'finish' } });
      const last = r.trace.find((s) => s.kind === 'drain' || s.kind === 'finish');
      const newIds = Q.transitions.map((t, i) => i).filter((i) => i > nOld);
      const ec = {};
      for (const i of newIds) ec[Q.transitions[i].from + '>' + Q.transitions[i].to] = 'taken';
      const m3 = T.Machine.parse(T.pda.toString(Q));
      F.set('states', Q.states.length).set('moves', Q.transitions.length);
      F.add({ items: K.graph.draw(m3, { pos, hot: [last.state], edgeCls: ec }).items, say: last.say });
      // run a word on the new machine
      const w = T.pda.word(Q, inp.w);
      const { path, accepted } = bestPath(Q, w);
      const old = T.pda.accepts(P, T.pda.word(P, inp.w)).accepted;
      F.add({ items: runScene(m3, pos, Q, w, path[0], { start: true }), say: 'Now run ' + CF.show(w) + ' on the new machine, starting with only ' + Q.startStack + ' on the stack.' });
      path.slice(1).forEach((c, i) => {
        const t = Q.transitions[c.via];
        F.add({ items: runScene(m3, pos, Q, w, c, { taken: [CF.edgeOf(t)] }), say: T.pda.showT(t) + ': ' + CF.config(Q, path[i], w) + ' ⊢ ' + CF.config(Q, c, w) + (t.id > nOld ? ' (a new move)' : t.id === 0 ? ' (the new start move)' : '') + '.', hl: { delta: [String(t.id)] } });
      });
      const end = path[path.length - 1];
      F.add({ items: runScene(m3, pos, Q, w, end, accepted ? { good: true } : { bad: true }), say: (accepted ? 'The new machine accepts ' + CF.show(w) + (Q.acceptBy === 'empty' ? ': its stack is empty, ⊥ included.' : ' in ' + end.state + '.') : 'The new machine rejects ' + CF.show(w) + '.') + ' The old one ' + (old ? 'accepts' : 'rejects') + ' it too: the same language, a different way of saying yes.', mark: accepted ? 'accepted' : 'rejected' });
      return { frames: F.list, def: { sections: [CF.pdaTable(P, 'old', 'Old moves'), CF.pdaTable(Q, 'delta', 'New moves')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.q, once: true, pick: 'option', options: ['A state that pops everything once an accepting state is reached', 'An accepting state entered when ⊥ shows on top', 'Nothing more is needed'], ask: 'What does the construction add next?', answer: (fr, i) => (fr[i].meta.q === 'drain' ? 'A state that pops everything once an accepting state is reached' : 'An accepting state entered when ⊥ shows on top'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why a new bottom marker ⊥ when turning final-state acceptance into empty stack?', options: ['So the old machine cannot empty the stack by itself and be taken to accept', 'To make it deterministic', 'To count symbols', 'It is not needed'], answer: 0, why: 'Only the new drain state can pop ⊥, and it is entered only from accepting states.' },
      { q: 'Empty stack to final state: when does the new machine enter its accepting state?', options: ['When ⊥ appears on top, meaning the old stack is empty', 'After every move', 'When the input ends', 'Never'], answer: 0, why: 'Seeing ⊥ is how the new machine notices the old stack has run out.' },
      { q: 'Do the two kinds of acceptance recognise the same class of languages?', options: ['Yes, for nondeterministic PDAs', 'No, empty stack is weaker', 'No, final state is weaker', 'Only for regular languages'], answer: 0, why: 'The two constructions convert either way. (For deterministic PDAs, empty stack is weaker.)' },
    ],
  });

  // ---- CFG → PDA, top down ------------------------------------------------------------------------------------
  const GRAM = 'S → a S b | c';
  const EXPR = 'E → E + T | T\nT → ( E ) | x';
  function movesPanel(G, kind, x, y, lit) {
    const items = [];
    const mv = kind === 'top' ? G.productions.map((p) => ({ k: 'e' + p.id, t: 'ε, ' + p.A + ' → ' + (p.rhs.length ? p.rhs.join('') : 'ε'), cls: 'expand' })).concat(G.terminals.map((a) => ({ k: 'm' + a, t: a + ', ' + a + ' → ε', cls: 'match' })))
      : G.terminals.map((a) => ({ k: 's' + a, t: 'shift ' + a })).concat(G.productions.map((p) => ({ k: 'r' + p.id, t: 'reduce ' + CF.prod(G, p) })));
    const w = Math.max(...mv.map((m) => Geo.textWidth(m.t, 15, { mono: true }))) + 24;
    items.push({ key: 'mv:title', kind: 'text', x, y: y - 14, text: kind === 'top' ? 'moves of the one state q' : 'moves', cls: 'title' });
    mv.forEach((m, i) => items.push({ key: 'mv:' + m.k, kind: 'cell', x, y: y + i * 42, w, h: 36, text: m.t, size: 15, cls: 'mono chip' + (lit && lit.includes(m.k) ? ' hot' : '') }));
    return { items, w, h: mv.length * 42 };
  }
  topic({
    id: 'pda-topdown', family: 'pda', order: 40, title: 'From a grammar to a PDA: expand and match',
    blurb: 'One state is enough. The stack holds what is still to be matched: a nonterminal on top is expanded by a rule, a terminal on top is matched against the input. Read input plus stack is always a leftmost sentential form.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: GRAM, check: (v) => CF.checkGrammar(v, { maxRules: 8 }) }, { id: 'w', kind: 'string', label: 'Word', def: 'aacbb', max: 7 }],
    presets: [
      { label: 'aⁿcbⁿ: aacbb', values: { g: GRAM, w: 'aacbb' } },
      { label: 'Expressions: x+(x)', values: { g: EXPR, w: 'x+(x)' } },
      { label: 'With ε: aabb', values: { g: 'S → a S b | ε', w: 'aabb' } },
    ],
    check: (inp) => { const G = CF.grammar(inp.g); const e = CF.checkWord(G, inp.w); if (e) return e; return T.grammar.parseTrees(G, CF.word(G, inp.w), 1).length ? null : 'Word: not in the language, so no run accepts it'; },
    counters: [{ id: 'expand', label: 'expands' }, { id: 'match', label: 'matches' }, { id: 'height', label: 'stack height' }],
    run(inp) {
      const G = CF.grammar(inp.g), w = CF.word(G, inp.w);
      const tree = T.grammar.parseTrees(G, w, 1)[0];
      const d = T.grammar.derivationOf(G, tree, 'leftmost');
      const F = new T.Frames(['expand', 'match', 'height']);
      const mp = movesPanel(G, 'top', 0, 0);
      const sx = mp.w + 90;
      const scene = (stack, pos, lit, note) => {
        const items = movesPanel(G, 'top', 0, 0, lit).items;
        items.push(...K.string.draw({ text: w, pos, x: sx, y: -6, cw: 40, prefix: 'in', label: '' }).items);
        const st = CF.stack(stack, { x: sx, y: Math.max(mp.h, 330) + 20, prefix: 'k', max: 7 });
        items.push(...st.items);
        const form = w.slice(0, pos).concat(stack);
        items.push(...CF.form(G, form.map((s, i) => ({ s, id: 'f' + i })), { prefix: 'lf', x: sx + 150, y: 140, h: 36, cls: (f, i) => (i < pos ? 'read' : '') }).items);
        items.push({ key: 'lfl', kind: 'text', x: sx + 150, y: 126, text: 'read + stack', cls: 'title' });
        if (note) items.push({ key: 'note', kind: 'text', x: sx + 150, y: 210, text: note, cls: 'hot' });
        return items;
      };
      F.add({ items: scene([G.start], 0, G.productions.map((p) => 'e' + p.id)), say: 'Every rule A → α becomes an expand move (q, ε, A) → (q, α): replace A on top by its right side. Every terminal a becomes a match move (q, a, a) → (q, ε). The stack starts with ' + G.start + ', and the machine accepts by empty stack.' });
      let stack = [G.start], pos = 0, k = 0;
      F.set('height', 1);
      const steps = d.steps;
      let guard = 0;
      while ((stack.length || pos < w.length) && guard++ < 80) {
        const top = stack[0];
        if (CF.isN(G, top)) {
          const p = G.productions[steps[k++].prod];
          const nextIsExpand = true;
          F.list[F.length - 1].meta = { next: 'Expand', nextIsExpand };
          stack = p.rhs.concat(stack.slice(1));
          F.count('expand').set('height', stack.length);
          F.add({ items: scene(stack, pos, ['e' + p.id], 'expand'), say: 'Top is the nonterminal ' + top + ': expand it by ' + CF.prod(G, p) + ' (the machine guesses the rule; this is the guess that works). Read so far plus the stack: ' + CF.show(w.slice(0, pos).concat(stack)) + '.' });
        } else {
          F.list[F.length - 1].meta = { next: 'Match' };
          stack = stack.slice(1); pos++;
          F.count('match').set('height', stack.length);
          F.add({ items: scene(stack, pos, ['m' + top], 'match'), say: 'Top is the terminal ' + top + ' and so is the next input symbol: match, reading it and popping it.' });
        }
      }
      F.add({ items: scene([], w.length, []), say: 'The input is read and the stack is empty: accepted. The expand moves, in order, are exactly the leftmost derivation ' + d.forms.map(CF.show).join(' ⇒ ') + '.', mark: 'accepted' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), { id: 'der', kind: 'math', title: 'Leftmost derivation', text: d.forms.map((f, i) => (i ? '⇒ ' : '  ') + CF.show(f)).join('\n') }] } };
    },
    predict: [
      { at: (f, i) => i >= 1 && f.meta && f.meta.next, once: false, pick: 'option', options: ['Expand', 'Match'], ask: 'Expand or match next?', answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'The top-down PDA has how many states?', options: ['One (plus none needed)', 'One per nonterminal', 'One per rule', 'Two'], answer: 0, why: 'All the information lives on the stack.' },
      { q: 'What is on the stack in the middle of a run?', options: ['The rest of a leftmost sentential form, still to be matched', 'The input read so far', 'The parse tree', 'The rules used'], answer: 0, why: 'Matched input followed by the stack is always a leftmost sentential form.' },
      { q: 'Where is the nondeterminism?', options: ['Choosing which rule to expand a nonterminal by', 'Matching terminals', 'The start', 'There is none'], answer: 0, why: 'A nonterminal with several rules gives several expand moves on the same top.' },
      { q: 'The stack top is the terminal b, the next input is a. What happens?', options: ['This branch dies', 'Expand b', 'Push a', 'Accept'], answer: 0, why: 'A match needs the same terminal on top and in the input.' },
    ],
  });

  // ---- CFG → PDA, bottom up ----------------------------------------------------------------------------------
  topic({
    id: 'pda-bottomup', family: 'pda', order: 50, title: 'From a grammar to a PDA: shift and reduce',
    blurb: 'The other way round: shift input symbols onto the stack, and when the top spells a right side, reduce it to its left side. Reaching the start symbol alone accepts. The reductions are a rightmost derivation, backwards.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: GRAM, check: (v) => CF.checkGrammar(v, { maxRules: 8 }) }, { id: 'w', kind: 'string', label: 'Word', def: 'aacbb', max: 7 }],
    presets: [
      { label: 'aⁿcbⁿ: aacbb', values: { g: GRAM, w: 'aacbb' } },
      { label: 'Expressions: x+x+x', values: { g: EXPR, w: 'x+x+x' } },
      { label: 'An ε-rule reduces from nothing: ab', values: { g: 'S → a S b | ε', w: 'ab' } },
    ],
    check: (inp) => { const G = CF.grammar(inp.g); const e = CF.checkWord(G, inp.w); if (e) return e; return T.grammar.parseTrees(G, CF.word(G, inp.w), 1).length ? null : 'Word: not in the language, so no run accepts it'; },
    counters: [{ id: 'shift', label: 'shifts' }, { id: 'reduce', label: 'reduces' }, { id: 'height', label: 'stack height' }],
    run(inp) {
      const G = CF.grammar(inp.g), w = CF.word(G, inp.w);
      const tree = T.grammar.parseTrees(G, w, 1)[0];
      const d = T.grammar.derivationOf(G, tree, 'rightmost');
      const F = new T.Frames(['shift', 'reduce', 'height']);
      const mp = movesPanel(G, 'bottom', 0, 0);
      const sx = mp.w + 90;
      const scene = (stack, pos, lit, note) => {
        const items = movesPanel(G, 'bottom', 0, 0, lit).items;
        items.push(...K.string.draw({ text: w, pos, x: sx, y: -6, cw: 40, prefix: 'in' }).items);
        items.push({ key: 'stl', kind: 'text', x: sx, y: 126, text: 'stack, top right', cls: 'title' });
        items.push(...CF.form(G, [{ s: '⊥', id: 'bot' }].concat(stack.map((x) => ({ s: x.s, id: x.id }))), { prefix: 'st', x: sx, y: 140, h: 40, cls: (f, i) => (i === 0 ? 'read' : note === 'reduce' && i === stack.length ? 'new' : '') }).items);
        if (note) items.push({ key: 'note', kind: 'text', x: sx, y: 220, text: note, cls: 'hot' });
        return items;
      };
      // walk the rightmost derivation backwards: each step undone is one reduction
      let n = 0;
      let stack = [], pos = 0;
      F.add({ items: scene(stack, 0, []), say: 'Shift moves push the next input symbol; a reduce move pops a right side (top first) and pushes its left side. The stack starts with only the bottom marker ⊥.' });
      for (let k = d.steps.length - 1; k >= 0; k--) {
        const st = d.steps[k], p = G.productions[st.prod];
        const need = st.pos + p.rhs.length;
        while (stack.length < need) {
          F.list[F.length - 1].meta = { next: 'Shift' };
          stack = stack.concat([{ s: w[pos], id: 'w' + pos }]); pos++;
          F.count('shift').set('height', stack.length);
          F.add({ items: scene(stack, pos, ['s' + stack[stack.length - 1].s], 'shift'), say: 'Shift ' + stack[stack.length - 1].s + '. The stack followed by the rest of the input, ' + CF.show(stack.map((x) => x.s).concat(w.slice(pos))) + ', is a right sentential form.' });
        }
        F.list[F.length - 1].meta = { next: 'Reduce' };
        const popped = stack.slice(st.pos);
        stack = stack.slice(0, st.pos).concat([{ s: p.A, id: 'r' + n++ }]);
        F.count('reduce').set('height', stack.length);
        F.add({ items: scene(stack, pos, ['r' + p.id], 'reduce'), say: (popped.length ? 'The top ' + CF.show(popped.map((x) => x.s)) + ' is the right side of ' + CF.prod(G, p) + ': reduce, popping it and pushing ' + p.A + '.' : 'Reduce by the ε-rule ' + CF.prod(G, p) + ': push ' + p.A + ' without popping anything.') + ' (The machine guesses when to reduce; this is the guess that works.)', hl: { g: [p.id] } });
      }
      F.add({ items: scene(stack, pos, []), say: 'Only ' + G.start + ' is left above ⊥ and the input is used up: pop both and accept. Read bottom to top, the reductions undo the rightmost derivation ' + d.forms.map(CF.show).join(' ⇒ ') + '.', mark: 'accepted' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), { id: 'der', kind: 'math', title: 'Rightmost derivation (read upwards)', text: d.forms.map((f, i) => (i ? '⇒ ' : '  ') + CF.show(f)).join('\n') }] } };
    },
    predict: [
      { at: (f, i) => i >= 1 && f.meta && f.meta.next, once: false, pick: 'option', options: ['Shift', 'Reduce'], ask: 'Shift or reduce next?', answer: (fr, i) => fr[i].meta.next, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A reduce by A → x y needs what on top of the stack?', options: ['y on top, x under it', 'x on top', 'A', 'the input x y'], answer: 0, why: 'The right side is on the stack in order, its last symbol on top; it is popped top first.' },
      { q: 'The reductions of an accepting run, in order, are…', options: ['a rightmost derivation read backwards', 'a leftmost derivation', 'a random order', 'the top-down expansions'], answer: 0, why: 'Bottom-up parsing rebuilds the tree from the leaves, undoing the last rightmost step first.' },
      { q: 'Where is the guessing in the shift-reduce PDA?', options: ['Whether to shift or reduce, and by which rule', 'Only at the start', 'In matching', 'Nowhere'], answer: 0, why: 'Deterministic LR parsers settle exactly these choices with a table.' },
    ],
  });

  // ---- PDA → CFG -----------------------------------------------------------------------------------------------
  topic({
    id: 'pda-to-cfg', family: 'pda', order: 60, title: 'From a PDA to a grammar: triples [p X q]',
    blurb: 'The nonterminal [p X q] stands for every input that takes the machine from state p, with X on top, to state q with that X gone. Each move becomes rules; the parse tree of a word is the shape of its stack over time.',
    inputs: [pdaIn(ANBN_E, { maxStates: 3 }), { id: 'w', kind: 'string', label: 'Word to draw', def: 'aabb', max: 5 }],
    presets: [
      { label: 'aⁿbⁿ by empty stack: aabb', values: { m: ANBN_E, w: 'aabb' } },
      { label: 'Brackets: (())', values: { m: BRACK, w: '(())' } },
      { label: 'ε', values: { m: ANBN_E, w: '' } },
    ],
    check: (inp) => { const e = wordCheck(inp); if (e) return e; const { P } = CF.pda(inp.m); if (P.acceptBy !== 'empty') return 'Machine: this topic starts from acceptance by empty stack (the final-state topic converts one)'; if (!T.pda.accepts(P, T.pda.word(P, inp.w)).accepted) return 'Word: the machine does not accept it'; return null; },
    counters: [{ id: 'raw', label: 'rules made' }, { id: 'kept', label: 'useful rules' }],
    run(inp) {
      const { P, M } = CF.pda(inp.m);
      const res = T.pda.toCFG(P);
      const Q = res.pda;
      const pos = K.graph.layout(M).pos;
      const F = new T.Frames(['raw', 'kept']);
      const g0 = K.graph.draw(M, { pos });
      const px = g0.box.x + g0.box.w + 80;
      const panel = (title, lines, lit) => {
        const items = [{ key: 'pt', kind: 'text', x: px, y: g0.box.y - 6, text: title, cls: 'title' }];
        lines.slice(0, 7).forEach((l, i) => items.push({ key: 'pl:' + l, kind: 'cell', x: px, y: g0.box.y + 8 + i * 42, w: Math.max(...lines.slice(0, 7).map((x) => Geo.textWidth(x, 14, { mono: true }))) + 22, h: 36, text: l, size: 14, cls: 'mono chip' + (lit && lit.includes(l) ? ' good' : '') }));
        if (lines.length > 7) items.push({ key: 'pmore', kind: 'text', x: px, y: g0.box.y + 8 + 7 * 42 + 18, text: '+ ' + (lines.length - 7) + ' more', cls: '' });
        return items;
      };
      const useful = new Set(res.grammar.productions.map((p) => p.A + ' → ' + (p.rhs.length ? p.rhs.join(' ') : 'ε')));
      F.add({ items: g0.items.concat(panel('meaning', ['[p,X,q]: from p with X on top', 'to q, with X popped'])), say: 'The idea: a nonterminal [p,X,q] for every two states and a stack symbol. It should generate exactly the inputs the machine reads while going from p with X on top to q with X removed (and whatever was under X untouched). The start rules: S → [' + Q.start + ',' + Q.startStack + ',q] for every state q.' });
      let raw = Q.states.length;
      for (const s of res.trace.filter((x) => x.kind === 'transition').slice(0, 6)) {
        const t = s.transition;
        raw += s.rules.length; F.set('raw', raw);
        F.add({ items: K.graph.draw(M, { pos, taken: [CF.edgeOf(t)] }).items.concat(panel('rules from this move', s.rules, s.rules.filter((r) => useful.has(r)))), say: s.say + (s.rules.length > 1 ? ' The states in between are unknown, so every choice is written down; most will turn out useless.' : '') });
      }
      F.set('raw', res.raw.productions.length).set('kept', res.grammar.productions.length);
      const cl = res.trace.find((x) => x.kind === 'cleanup' && x.before !== undefined);
      const cutG = F.length;
      const gr = CF.rules(res.grammar, { prefix: 'gr', x: 0, y: 0, maxW: 760 });
      F.add({ items: gr.items, say: cl.say + ' The useful ones (green above) remain: these describe the language of the machine.' });
      // the stack over time for the word, and the tree of triples it gives
      const w = T.pda.word(Q, inp.w);
      const sim = T.pda.simulate(Q, w, { stopAtAccept: true });
      const path = sim.paths[0];
      const moves = path.slice(1).map((c, i) => ({ t: Q.transitions[c.via], i }));
      let mi = 0, idc = 0;
      const recs = [];
      const node = (X, depth) => {
        const m = moves[mi++];
        if (!m) throw new Error('run ended early');
        const t = m.t, start = m.i, p = t.from;
        const push = t.pop === '' ? t.push.concat([X]) : t.push;
        const kids = [];
        if (t.read) kids.push({ sym: t.read, children: null });
        let s = t.to;
        const me = { sym: '', prod: 0, children: kids, id: 'k' + idc++ };
        for (const Y of push) { const c = node(Y, depth + 1); kids.push(c.n); s = c.q; }
        me.sym = '[' + p + ',' + X + ',' + s + ']';
        if (!kids.length) kids.push({ sym: 'ε', children: [] });
        recs.push({ n: me, from: start, to: mi, depth });
        return { n: me, q: s };
      };
      let root = null;
      try { const r = node(Q.startStack, 1); root = { sym: 'S', children: [r.n], id: 'root' }; recs.push({ n: root, from: 0, to: mi, depth: 0 }); } catch (e) { root = null; }
      const def = { sections: [CF.pdaTable(P), CF.gsec(res.grammar, 'g', 'Grammar (useful rules)')] };
      if (!root) return { frames: CF.phaseViews(F.list, [0, cutG]), def };
      const CWm = 42, CHm = 30;
      const mountain = (lit) => {
        const items = [{ key: 'mt', kind: 'text', x: 0, y: -16, text: 'the stack after each move', cls: 'title' }];
        path.forEach((c, i) => {
          const inR = lit && i >= lit.from && i <= lit.to;
          c.stack.slice().reverse().forEach((X, j) => items.push({ key: 'm:' + i + ':' + j, kind: 'cell', x: i * (CWm + 6), y: 150 - (j + 1) * (CHm + 2), w: CWm, h: CHm, text: X, size: 15, cls: 'mono stack' + (inR ? ' hot' : '') }));
          items.push({ key: 'ms:' + i, kind: 'text', x: i * (CWm + 6) + CWm / 2, y: 172, text: c.state, anchor: 'middle', cls: inR ? 'hot' : '' });
        });
        return items;
      };
      const order = recs.slice().sort((a, b) => a.depth - b.depth || a.from - b.from);
      const shown = new Set();
      const kit = (n) => {
        const leaf = !n.children || (n.children.length === 0);
        const k = { id: n.id || ('l' + Math.random()), label: n.sym, cls: n.sym.startsWith('[') || n.sym === 'S' ? 'nt' : 't', mono: true };
        if (!leaf && shown.has(n.id)) k.children = n.children.map((c, i) => (c.id ? kit(c) : { id: n.id + '.' + i, label: c.sym, cls: 't eps', mono: true }));
        return k;
      };
      const treeAt = (hot) => K.tree.draw(kit(root), { prefix: 'tt', y: 260, gapX: 12, hot: hot ? [hot] : [] }).items;
      shown.add('root');
      const cut = F.length;
      F.add({ items: mountain(null).concat(treeAt(null)), say: 'Now the word ' + CF.show(w) + '. Above, the stack after each move of an accepting run (bottom at the bottom). Each stack symbol lives for a stretch of time; the triple for it names the state where it is on top and the state when it is gone.' });
      for (const r of order.filter((x) => x.n.id !== 'root').slice(0, 9)) {
        shown.add(r.n.id);
        const parentIn = recs.find((x) => x.n.children && x.n.children.includes(r.n));
        if (parentIn) shown.add(parentIn.n.id);
        F.add({ items: mountain(r).concat(treeAt(r.n.id)), say: r.n.sym + ' covers moves ' + (r.from + 1) + ' to ' + r.to + ', reading ' + (CF.show(w.slice(path[r.from].pos, path[r.to].pos))) + ': the lit stretch of the stack, where ' + r.n.sym.split(',')[1] + ' sits until it is popped.' });
      }
      for (const r of recs) shown.add(r.n.id);
      F.add({ items: mountain(null).concat(treeAt(null)), say: 'The whole tree: every triple splits into the triples of the symbols its move pushed, in the order they are popped. Its yield is ' + CF.show(w) + ', so the grammar generates exactly what the machine accepts.', mark: 'same language' });
      CF.phaseViews(F.list, [0, cutG, cut]);
      return { frames: F.list, def };
    },
    predict: [
      { at: (f, i, fr) => i === 1, once: true, pick: 'option', options: ['1', '2', '4', '8'], ask: 'A move pushes two symbols and the machine has two states. How many rules does it give?', answer: () => '4', explain: 'Two unknown in-between states, each one of 2: 2 × 2 = 4 rules.' },
    ],
    quiz: [
      { q: 'What does [p, X, q] generate?', options: ['The inputs that take the machine from p with X on top to q with X popped', 'The words starting in p', 'The stack contents', 'All words'], answer: 0, why: 'It is the net effect of removing one stack symbol.' },
      { q: 'A move (p, a, X) → (r, ε) gives which rule?', options: ['[p,X,r] → a', '[p,X,q] → a [r,X,q]', 'S → a', '[r,X,p] → a'], answer: 0, why: 'X is popped at once, reading a, ending in r.' },
      { q: 'Why does the construction want acceptance by empty stack?', options: ['Then the whole word is the removal of the start symbol: S → [q0,Z,q]', 'Final states cannot be converted', 'It is shorter', 'It is not needed'], answer: 0, why: 'The triples track popping; the empty stack is the natural end.' },
      { q: 'Most generated rules are useless because…', options: ['the in-between states are guessed in every way, and most guesses are impossible', 'the machine is wrong', 'ε-moves', 'they are duplicates'], answer: 0, why: 'Cleanup removes the triples that generate nothing or cannot be reached.' },
    ],
  });

  // ---- determinism ---------------------------------------------------------------------------------------------
  topic({
    id: 'dpda', family: 'pda', order: 70, title: 'Deterministic PDAs, and a language that needs a guess',
    blurb: 'A PDA is deterministic when no two moves can ever apply at once. With a middle marker c, wcwᴿ is deterministic; without it, wwᴿ needs to guess the middle, and the live configurations multiply.',
    inputs: [pdaIn(WWR), { id: 'w', kind: 'string', label: 'Input', def: 'abba', max: 7 }],
    presets: [
      { label: 'wwᴿ: must guess', values: { m: WWR, w: 'abba' } },
      { label: 'wcwᴿ: the marker says when', values: { m: WCW, w: 'abcba' } },
      { label: 'aⁿbⁿ: deterministic', values: { m: ANBN, w: 'aabb' } },
      { label: 'An ε-move that competes', values: { m: EPSCLASH, w: 'aabb' } },
    ],
    check: wordCheck,
    counters: [{ id: 'conf', label: 'competing pairs' }, { id: 'live', label: 'live configurations' }],
    run(inp) {
      const { P, M } = CF.pda(inp.m);
      const pos = K.graph.layout(M).pos;
      const d = T.pda.deterministic(P);
      const F = new T.Frames(['conf', 'live']);
      const g0 = K.graph.draw(M, { pos });
      const bars = (counts, upto) => {
        const items = [];
        const by = g0.box.y + g0.box.h + 200;
        items.push({ key: 'b:t', kind: 'text', x: g0.box.x, y: by - 160, text: 'live configurations after each step', cls: 'title' });
        counts.forEach((c, i) => {
          if (i > upto) return;
          const x = g0.box.x + 10 + i * 34;
          for (let j = 0; j < Math.min(c, 6); j++) items.push({ key: 'b:' + i + ':' + j, kind: 'token', x: x + 10, y: by - 12 - j * 22, r: 8, cls: c > 1 ? 'bad' : 'good' });
          items.push({ key: 'b:n:' + i, kind: 'text', x: x + 10, y: by + 14, text: c > 6 ? c + '' : String(i), anchor: 'middle', cls: c > 6 ? 'bad' : '' });
        });
        return items;
      };
      F.add({ items: g0.items, say: 'Is this machine deterministic? Two moves compete when they leave the same state, could read the same thing (the same symbol, or one reads nothing) and could pop the same thing (the same symbol, or one ignores the stack).', meta: { det: d.deterministic ? 'Yes' : 'No' } });
      d.conflicts.slice(0, 3).forEach((c) => {
        const a = P.transitions[c.a], b = P.transitions[c.b];
        F.count('conf');
        F.add({ items: K.graph.draw(M, { pos, hot: [a.from], edgeCls: { [CF.edgeOf(a)]: 'bad', [CF.edgeOf(b)]: 'bad' } }).items, say: T.pda.showT(a) + ' and ' + T.pda.showT(b) + ' compete: ' + c.why + '.', hl: { delta: [String(a.id), String(b.id)] } });
      });
      F.set('conf', d.conflicts.length);
      F.add({ items: g0.items, say: d.trace[d.trace.length - 1].say });
      const w = T.pda.word(P, inp.w);
      const run = T.pda.stepper(P, w, { maxConfigs: 400 });
      const counts = [1];
      while (!run.done && counts.length < 16) { run.step(); if (run.frontier.length) counts.push(run.frontier.length); else break; }
      counts.forEach((c, i) => {
        F.set('live', c);
        F.add({ items: g0.items.concat(bars(counts, i)), say: i === 0 ? 'Now run ' + CF.show(w) + ' and count the configurations alive after each step.' : 'Step ' + i + ': ' + c + ' live configuration' + (c === 1 ? '' : 's') + '.' + (c > 1 ? ' The machine is following several guesses at once.' : '') });
      });
      const max = Math.max(...counts);
      F.add({ items: g0.items.concat(bars(counts, counts.length)), say: (max === 1 ? 'Never more than one configuration: a deterministic machine reads the input in one pass with no going back, which is what a practical parser does.' : 'Up to ' + max + ' configurations at once. For wwᴿ no deterministic PDA exists at all: after reading w the machine would have to know whether the middle has come, and one can show that whatever it keeps on its stack cannot settle that for every continuation. Deterministic context-free languages are a strict subclass, the ones LR parsers handle.') + (run.accepted ? ' ' + CF.show(w) + ' is accepted.' : ' ' + CF.show(w) + ' is rejected.') });
      return { frames: F.list, def: { sections: [CF.pdaTuple(P), CF.pdaTable(P)] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Is this PDA deterministic?', answer: (fr) => fr[0].meta.det, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Two moves from q: (q, ε, Z) and (q, a, Z). Do they compete?', options: ['Yes: with Z on top, either can fire whatever comes next', 'No, they read different things', 'Only on input ε', 'Only if both push'], answer: 0, why: 'An ε-move competes with every read move on the same top.' },
      { q: 'Why is wcwᴿ deterministic but wwᴿ apparently not?', options: ['The c tells the machine when to stop pushing and start popping', 'wcwᴿ is regular', 'wwᴿ is not context-free', 'They are both deterministic'], answer: 0, why: 'Without a marker the switch point must be guessed.' },
      { q: 'Deterministic context-free languages are closed under…', options: ['complement', 'union', 'intersection', 'reversal'], answer: 0, why: 'A deterministic machine can swap accepting and rejecting (with care for ε-moves and stuck runs); general context-free languages are not closed under complement.' },
      { q: 'Which parsers recognise exactly the deterministic context-free languages?', options: ['LR(1) parsers', 'CYK', 'Earley', 'DFAs'], answer: 0, why: 'Every DCFL has an LR(1) grammar, and LR parsers are deterministic PDAs.' },
    ],
  });
})();
