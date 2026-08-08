// Decision procedures for regular languages, each an algorithm on the machine's graph: emptiness as
// reachability spreading from the start, finiteness as a cycle among the useful states, equivalence as a
// breadth-first walk over pairs that stops at the first pair that disagrees, and counting the accepted
// strings of each length by dynamic programming down the columns of a table.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, R = T.Reg, FA = T.FA;

  T.family({ id: 'decide', part: 'regular', order: 80, title: 'Decision procedures', blurb: 'Questions about a regular language that a program can always answer: is it empty, is it finite, are two machines equal, how many strings of each length.' });

  const movePos = (pos, dx, dy) => { const o = {}; for (const q in pos) o[q] = { x: pos[q].x + dx, y: pos[q].y + dy }; return o; };
  const complete = (m, sigma) => { const x = FA.make(Object.assign({}, m, { alphabet: sigma })); return FA.isComplete(x) ? x : FA.complete(x, 'dead').fa; };

  // ---- emptiness --------------------------------------------------------------------------------------------------
  const REACH = 'start s\naccept f\ns -a-> s\ns -b-> t\nt -b-> s\nt -a-> u\nu -b-> f\nu -a-> t';
  const CUT_OFF = 'start s\naccept f\ns -a-> t\nt -b-> s\nt -a-> t\nu -a-> f\nf -b-> u';
  const NO_ACC = 'start p\np -a-> q\nq -a,b-> p';
  const START_ACC = 'start s\naccept s\ns -a-> t\nt -b-> s';
  const EPS_NFA = 'start s\naccept f\ns -ε-> t\nt -a-> u\nu -ε-> f\ns -b-> s';
  T.topic({
    id: 'decide-empty', family: 'decide', order: 10, title: 'Is the language empty?',
    blurb: 'A language is empty exactly when no accepting state can be reached. Spread out from the start one layer at a time; the first accepting state found gives a shortest witness.',
    inputs: [R.machineInput({ id: 'm', label: 'Machine', def: REACH, kind: 'nfa', max: 7 })],
    presets: [
      { label: 'Reachable after a few moves', values: { m: REACH } },
      { label: 'The accepting state is cut off: ∅', values: { m: CUT_OFF } },
      { label: 'No accepting state at all: ∅', values: { m: NO_ACC } },
      { label: 'The start accepts: ε is a witness', values: { m: START_ACC } },
      { label: 'An NFA with ε-moves', values: { m: EPS_NFA } },
    ],
    counters: [{ id: 'seen', label: 'states reached' }, { id: 'layers', label: 'layers' }],
    run(inp) {
      const fa = R.fa(inp.m), d = R.dia(fa);
      const pos = K.graph.layout(d).pos;
      const F = new T.Frames(['seen', 'layers']);
      const dt = R.delta(fa);
      const parent = new Map([[fa.start, null]]);
      let layer = [fa.start];
      const seen = new Set(layer);
      const used = [];
      const draw = (o) => K.graph.draw(d, Object.assign({ pos }, o)).items;
      const accs = new Set(fa.accept);
      const willEmpty = FA.isEmpty(fa).empty;
      F.set('seen', 1).set('layers', 1);
      F.add({ items: draw({ hot: [fa.start], startHot: true }), say: 'Start from ' + fa.start + ', the only state reachable by reading nothing (yet). ' + (fa.accept.length ? 'The question: can any of ' + R.set(fa.accept) + ' be reached?' : 'There is no accepting state at all, so nothing can ever be accepted; the search shows it anyway.'), hl: { delta: [dt.row(fa.start)] }, meta: { empty: willEmpty ? 'Empty' : 'Not empty', next: null } });
      let found = accs.has(fa.start) ? fa.start : null;
      while (!found && layer.length) {
        const next = [];
        const edges = [];
        for (const q of layer) for (const e of fa.trans) if (e.from === q && !seen.has(e.to)) { seen.add(e.to); next.push(e.to); parent.set(e.to, e); edges.push(e.from + '>' + e.to); }
        if (!next.length) break;
        used.push(...edges);
        F.list[F.list.length - 1].meta.next = next;
        F.set('seen', seen.size).count('layers');
        const hit = next.find((q) => accs.has(q));
        F.add({ items: draw({ active: [...seen].filter((q) => !next.includes(q)), hot: next, taken: edges }), say: 'One more move reaches ' + R.set(next) + (hit ? ', and ' + hit + ' accepts.' : ': none of them accepts, so keep going.'), hl: { delta: next.map(dt.row) }, meta: {} });
        layer = next;
        if (hit) found = hit;
      }
      if (found) {
        const path = [];
        for (let q = found; parent.get(q); q = parent.get(q).from) path.unshift(parent.get(q));
        const w = path.map((e) => e.sym).join('');
        const g = R.bounds(draw({}));
        const cw = 46, sx = g.x + g.w / 2 - Math.max(1, [...w].length) * cw / 2;
        F.add({ items: draw({ active: [...seen], good: [found], taken: path.map((e) => e.from + '>' + e.to) }).concat(K.string.draw({ text: [...w], x: sx, y: g.y + g.h + 50, cw, label: 'witness', head: false }).items), say: 'Follow the arrows back from ' + found + ' to the start: ' + (path.length ? path.map((e) => e.from + ' -' + R.sym(e.sym) + '-> ' + e.to).join(', ') : 'no moves at all') + '. So ' + R.w(w) + ' is accepted and the language is not empty.', mark: 'not empty' });
      } else {
        const never = fa.states.filter((q) => !seen.has(q));
        F.add({ items: draw({ active: [...seen], dim: never }), say: 'Nothing new can be reached. The reachable states ' + R.set([...seen]) + ' include no accepting state' + (never.length ? ' (' + R.set(never) + ' cannot be reached at all' + (never.some((q) => accs.has(q)) ? ', accepting or not' : '') + ')' : '') + ', so the language is empty: ∅.', mark: 'empty' });
      }
      return { frames: F.list, def: { sections: [R.tuple(fa), dt.section, { id: 'alg', kind: 'math', title: 'The test', text: 'L(M) = ∅  ⇔  no accepting state is\nreachable from q₀ in the graph of M' }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Empty', 'Not empty'], ask: 'Before searching: is this language empty?', answer: (fr) => fr[0].meta.empty, explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i) => i === 1 && f.meta && f.meta.next && f.meta.next.length, once: true, pick: 'item', ask: 'Which states will one more move reach? Click one.', answer: (fr, i) => fr[i].meta.next.map((q) => 'g:s:' + q), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'The machine has an accepting state. Is its language therefore non-empty?', options: ['Yes', 'No: the accepting state may be unreachable from the start', 'Only for DFAs', 'Only without ε-moves'], answer: 1, why: 'An accepting state that no path from the start reaches accepts nothing.' },
      { q: 'A machine has n states. How long can the shortest accepted string be, at most?', options: ['n − 1', 'n', '2ⁿ', 'Unbounded'], answer: 0, why: 'A shortest path to an accepting state visits no state twice, so it uses at most n − 1 moves.' },
      { q: 'Do the symbols on the arrows matter for the emptiness test?', options: ['Yes, each must be checked', 'No: only whether an arrow exists', 'Only ε-moves matter', 'Only for NFAs'], answer: 1, why: 'Any arrow can be taken by reading its symbol, so emptiness is plain reachability in the graph.' },
      { q: 'How can you decide whether L(A) ⊆ L(B) with the emptiness test?', options: ['It cannot be done', 'Test whether L(A) ∩ complement of L(B) is empty', 'Test whether L(A) is empty', 'Compare the numbers of states'], answer: 1, why: 'A ⊆ B exactly when no string is in A but not in B; that language has a DFA built by a product.' },
    ],
  });

  // ---- finiteness ------------------------------------------------------------------------------------------------------
  const LOOP_USEFUL = 'start s\naccept f\ns -a-> t\nt -b-> t\nt -a-> f';
  const LOOP_DEAD = 'start s\naccept f\ns -a-> f\ns -b-> d\nd -a,b-> d';
  const LOOP_UNREACH = 'start s\naccept f\ns -a-> f\nu -a-> u\nu -b-> f';
  const FINITE = 'start s\naccept x y\ns -a-> p\ns -b-> q\np -b-> x\nq -a-> y\nx -b-> y';
  const CYCLE2 = 'start s\naccept f\ns -a-> p\np -b-> q\nq -a-> p\nq -b-> f';
  T.topic({
    id: 'decide-finite', family: 'decide', order: 20, title: 'Is the language finite?',
    blurb: 'Infinitely many strings need a loop that a run can go round as often as it likes, on its way from the start to acceptance. Keep only the useful states, then look for a cycle.',
    inputs: [R.machineInput({ id: 'm', label: 'Machine', def: LOOP_USEFUL, kind: 'nfa', max: 7, eps: false })],
    presets: [
      { label: 'A useful loop: infinite', values: { m: LOOP_USEFUL } },
      { label: 'A loop of two states: infinite', values: { m: CYCLE2 } },
      { label: 'The only loop is dead: finite', values: { m: LOOP_DEAD } },
      { label: 'The only loop is unreachable: finite', values: { m: LOOP_UNREACH } },
      { label: 'No loop at all: finite', values: { m: FINITE } },
    ],
    counters: [{ id: 'useful', label: 'useful states' }, { id: 'pumped', label: 'copies of y' }],
    run(inp) {
      const fa = R.fa(inp.m), d = R.dia(fa);
      const pos = K.graph.layout(d).pos;
      const F = new T.Frames(['useful', 'pumped']);
      const reach = new Set(FA.reachable(fa));
      const co = new Set(fa.accept);
      for (let ch = true; ch;) { ch = false; for (const e of fa.trans) if (co.has(e.to) && !co.has(e.from)) { co.add(e.from); ch = true; } }
      const unreach = fa.states.filter((q) => !reach.has(q));
      const dead = fa.states.filter((q) => reach.has(q) && !co.has(q));
      const useful = fa.states.filter((q) => reach.has(q) && co.has(q));
      const res = FA.isFinite(fa);
      const draw = (o) => K.graph.draw(d, Object.assign({ pos }, o)).items;
      const loopsAt = fa.states.filter((q) => fa.trans.some((e) => e.from === q && (e.to === q || true)));
      void loopsAt;
      F.add({ items: draw({}), say: 'The language is infinite exactly when some cycle can be gone round on a path from the start to acceptance. Cycles elsewhere do not count.', meta: { finite: res.finite ? 'Finite' : 'Infinite' } });
      F.add({ items: draw({ dim: unreach, active: [...reach] }), say: unreach.length ? R.set(unreach) + ' cannot be reached from ' + fa.start + ': whatever loops ' + (unreach.length === 1 ? 'it has' : 'they have') + ' never matter.' : 'Every state can be reached from ' + fa.start + '.' });
      F.set('useful', useful.length);
      F.add({ items: draw({ dim: unreach.concat(dead), dead, active: useful }), say: dead.length ? 'From ' + R.set(dead) + ' no accepting state can be reached: a run there is already lost, so loops there add no strings. Useful states: ' + R.set(useful) + '.' : 'Every reachable state can still reach acceptance, so the useful states are ' + R.set(useful) + '.', meta: { useful } });
      const g = R.bounds(draw({}));
      if (!res.finite) {
        const cyc = res.cycle.map((e) => e.from + '>' + e.to);
        const cs = res.cycle.map((e) => e.from);
        F.add({ items: draw({ dim: unreach.concat(dead), dead, hot: cs, taken: cyc }), say: 'Among the useful states there is a cycle: ' + cs.join(' → ') + ' → ' + cs[0] + ', reading ' + res.y + '. So the language is infinite.', meta: { cycle: true } });
        const sy = g.y + g.h + 50;
        const at = (i) => { const n = [...res.x].length + i * [...res.y].length + [...res.z].length; return { x: g.x + g.w / 2 - Math.max(1, Math.min(n, 12)) * 23, y: sy }; };
        for (const i of [1, 2, 3, 0]) {
          F.set('pumped', i);
          const w = res.x + res.y.repeat(i) + res.z;
          F.add({ items: draw({ dim: unreach.concat(dead), dead, hot: cs, taken: cyc }).concat(K.string.pump({ x: res.x, y: res.y, z: res.z, i, at: at(i), cw: 46 }).items), say: 'x = ' + R.w(res.x) + ' leads to the cycle, y = ' + res.y + ' goes round it, z = ' + R.w(res.z) + ' finishes. Going round ' + i + ' time' + (i === 1 ? '' : 's') + ' gives ' + R.w(w) + ', accepted' + (i === 0 ? ' too.' : '.') + (i === 0 ? ' Every number of turns gives a different accepted string: infinitely many.' : ''), mark: i === 0 ? 'infinite' : undefined });
        }
      } else {
        const words = res.words;
        F.add({ items: draw({ dim: unreach.concat(dead), dead, active: useful }), say: 'There is no cycle among the useful states' + (unreach.length || dead.length ? ' (the loops in the faded part do not count)' : '') + ', so every accepted path is shorter than ' + useful.length + ' moves: the language is finite.', meta: { cycle: false } });
        const shown = words.slice(0, 10);
        const cw = Math.max(46, ...shown.map((w) => [...R.w(w)].length * 11 + 18));
        const x0 = g.x + g.w / 2 - (shown.length * (cw + 8)) / 2;
        const cells = shown.map((w, i) => ({ key: 'word:' + i, kind: 'cell', x: x0 + i * (cw + 8), y: g.y + g.h + 50, w: cw, h: 40, text: R.w(w), cls: 'mono good' }));
        if (!shown.length) cells.push(R.caption('word:none', g.x + g.w / 2, g.y + g.h + 70, 'no strings at all: ∅', 'bad'));
        F.add({ items: draw({ dim: unreach.concat(dead), dead, good: fa.accept.filter((q) => useful.includes(q)) }).concat(cells), say: 'All of them, by enumeration: ' + (words.length ? words.map(R.w).join(', ') + ' — ' + R.plural(words.length, 'string') + '.' : 'none; the language is empty, which is finite too.'), mark: 'finite' });
      }
      return { frames: F.list, def: { sections: [R.tuple(fa), R.delta(fa).section, { id: 'alg', kind: 'math', title: 'The test', text: 'useful = reachable from q₀ and can reach F\nL(M) infinite  ⇔  a cycle among the useful states' }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Finite', 'Infinite'], ask: 'Is this language finite or infinite?', answer: (fr) => fr[0].meta.finite, explain: (fr) => fr.find((x) => x.meta && x.meta.cycle !== undefined).say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.useful && fr[i + 1].meta.useful.length, once: true, pick: 'item', ask: 'Click a useful state: reachable from the start, and able to reach acceptance.', answer: (fr, i) => fr[i + 1].meta.useful.map((q) => 'g:s:' + q), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A DFA has a loop on its dead state. Is its language infinite?', options: ['Yes', 'No, not because of that loop: no accepting state can follow it', 'Only if the loop reads two symbols', 'Always'], answer: 1, why: 'Strings that go round the dead loop are all rejected, so the loop adds nothing.' },
      { q: 'Why must the cycle lie among useful states?', options: ['So that a run can reach it from the start and still reach acceptance after it', 'For speed', 'Because NFAs need it', 'It need not'], answer: 0, why: 'Only then does going round it k times give an accepted string for every k.' },
      { q: 'A finite language is accepted by a DFA with n useful states. How long can its strings be?', options: ['At most n − 1', 'At most n', 'At most 2n', 'Any length'], answer: 0, why: 'Without a cycle a path visits each useful state at most once.' },
      { q: 'Why does the test remove ε-moves first?', options: ['To make it faster', 'Because a cycle of ε-moves reads nothing and so does not make the language infinite', 'Because DFAs have none', 'It does not'], answer: 1, why: 'Only a cycle that reads at least one symbol produces longer and longer strings.' },
      { q: 'The language is infinite. What does the cycle give you?', options: ['A pumping decomposition x yⁱ z, all accepted', 'The shortest string', 'The number of strings', 'A minimal DFA'], answer: 0, why: 'x reaches the cycle, y goes round it, z reaches acceptance: every x yⁱ z is accepted.' },
    ],
  });

  // ---- equivalence -----------------------------------------------------------------------------------------------------
  const EVEN_A1 = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const EVEN_A2 = 'start p\naccept p r\np -a-> q\nq -a-> r\nr -a-> s\ns -a-> p\np -b-> p\nq -b-> q\nr -b-> r\ns -b-> s';
  const ENDS_AB = 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x';
  const HAS_AB = 'start u\naccept w\nu -a-> v\nu -b-> u\nv -a-> v\nv -b-> w\nw -a,b-> w';
  const PLUS_A = 'start s\naccept t\ns -a-> t\nt -a-> t';
  const STAR_A = 'start s\naccept s\ns -a-> s';
  const AB_PART = 'start s\naccept t\ns -a-> t\nt -b-> s';
  const AB_FULL = 'start s\naccept t\ns -a-> t\nt -b-> s\ns -b-> d\nt -a-> d\nd -a,b-> d';
  T.topic({
    id: 'decide-equiv', family: 'decide', order: 30, title: 'Are two DFAs equivalent?',
    blurb: 'Run both machines together over all strings at once: walk the reachable pairs of states breadth first. The first pair where one accepts and the other does not gives a shortest counterexample.',
    inputs: [R.machineInput({ id: 'a', label: 'DFA A', def: ENDS_AB, kind: 'dfa', max: 4 }), R.machineInput({ id: 'b', label: 'DFA B', def: HAS_AB, kind: 'dfa', max: 4 })],
    presets: [
      { label: 'Ends with ab vs contains ab', values: { a: ENDS_AB, b: HAS_AB } },
      { label: 'Even a\'s, two different machines: equal', values: { a: EVEN_A1, b: EVEN_A2 } },
      { label: 'a⁺ vs a*: they differ on ε', values: { a: PLUS_A, b: STAR_A } },
      { label: 'Missing moves vs a dead state: equal', values: { a: AB_PART, b: AB_FULL } },
    ],
    check: (inp) => { const a = R.fa(inp.a), b = R.fa(inp.b), s = [...new Set(a.alphabet.concat(b.alphabet))]; if (s.length > 2) return 'The two machines together read at most 2 symbols'; for (const [m, n] of [[a, 'A'], [b, 'B']]) if (complete(m, s.sort()).states.length > 5) return 'DFA ' + n + ': at most 5 states once completed'; return null; },
    counters: [{ id: 'pairs', label: 'pairs visited' }],
    run(inp) {
      const a0 = R.fa(inp.a), b0 = R.fa(inp.b), sigma = [...new Set(a0.alphabet.concat(b0.alphabet))].sort();
      const A = complete(a0, sigma), B = complete(b0, sigma);
      const da = R.dia(A), db = R.dia(B);
      const pa0 = K.graph.layout(da).pos, pb0 = K.graph.layout(db).pos;
      const ba = R.bounds(K.graph.draw(da, { pos: pa0 }).items), bb0 = R.bounds(K.graph.draw(db, { pos: pb0 }).items);
      const pa = movePos(pa0, -ba.x, -ba.y), pb = movePos(pb0, ba.w + 120 - bb0.x, (ba.h - bb0.h) / 2 - bb0.y);
      const dA = FA._deltaMap(A), dB = FA._deltaMap(B), accA = new Set(A.accept), accB = new Set(B.accept);
      const both = (o) => {
        const ga = K.graph.draw(da, { prefix: 'ga', pos: pa, active: o.p ? [o.p] : [], taken: o.ta || [], good: o.ga || [], bad: o.ba || [] });
        const gb = K.graph.draw(db, { prefix: 'gb', pos: pb, active: o.q ? [o.q] : [], taken: o.tb || [], good: o.gb || [], bad: o.bb || [] });
        const xa = R.bounds(ga.items), xb = R.bounds(gb.items);
        return ga.items.concat(gb.items, [R.caption('cap:a', xa.x, Math.min(xa.y, xb.y) - 16, 'A', 'title', 'start'), R.caption('cap:b', xb.x, Math.min(xa.y, xb.y) - 16, 'B', 'title', 'start')]);
      };
      const top = R.bounds(both({}));
      const rows = [];
      const table = (hot) => K.table.draw({ rows: rows.map((r) => [r.pair, R.w(r.by), r.A, r.B]), colHead: ['pair', 'reached by', 'A', 'B'], x: top.x + top.w / 2 - 170, y: top.y + top.h + 40, maxRows: 7, focus: hot === undefined ? undefined : [hot, 0], hot: hot === undefined ? [] : [[hot, 0], [hot, 1], [hot, 2], [hot, 3]], cls: (r, c) => (c >= 2 && rows[r] ? (rows[r].agree ? '' : 'bad') : ''), size: 15, prefix: 'tb' }).items;
      const F = new T.Frames(['pairs']);
      const verdict = FA.equivalent(A, B);
      F.add({ items: both({ p: A.start, q: B.start }), say: 'Feed every string to both machines at once. After any string, A is in some state p and B in some state q; the machines agree on that string when p and q both accept or both reject. Start with the pair (' + A.start + ', ' + B.start + ') for ε.', meta: { equal: verdict.equal ? 'Equivalent' : 'Not equivalent' } });
      const seen = new Map([[A.start + '|' + B.start, null]]);
      const queue = [[A.start, B.start, '']];
      let bad = null;
      while (queue.length) {
        const [p, q, w] = queue.shift();
        const agree = accA.has(p) === accB.has(q);
        rows.push({ pair: '(' + p + ', ' + q + ')', by: w, A: accA.has(p) ? 'accept' : 'reject', B: accB.has(q) ? 'accept' : 'reject', agree });
        F.count('pairs');
        const nexts = sigma.map((c) => [dA.get(p).get(c), dB.get(q).get(c), w + c]);
        F.add({ items: both({ p, q }).concat(table(rows.length - 1)), say: 'Pair (' + p + ', ' + q + '), first reached by ' + R.w(w) + ': A ' + (accA.has(p) ? 'accepts' : 'rejects') + ' and B ' + (accB.has(q) ? 'accepts' : 'rejects') + (agree ? '. They agree; queue the pairs its moves reach: ' + nexts.map((n) => '(' + n[0] + ', ' + n[1] + ')').join(', ') + '.' : '. They disagree!'), meta: { pair: [p, q], agree } });
        if (!agree) { bad = w; break; }
        for (const [p2, q2, w2] of nexts) { const k = p2 + '|' + q2; if (!seen.has(k)) { seen.set(k, w2); queue.push([p2, q2, w2]); } }
      }
      if (bad === null) {
        F.add({ items: both({}).concat(table()), say: 'No new pairs: all ' + rows.length + ' reachable pairs agree. Every string leads to one of these pairs, so A and B accept exactly the same strings.', mark: 'equivalent' });
      } else {
        const ws = [...bad];
        let p = A.start, q = B.start;
        const g = R.bounds(both({}).concat(table()));
        const cw = 46, sx = top.x + top.w / 2 - Math.max(1, ws.length) * cw / 2, sy = g.y + g.h + 40;
        const str = (i) => K.string.draw({ text: ws, pos: i, x: sx, y: sy, cw, label: 'counterexample', headText: i >= ws.length ? 'end' : 'next' }).items;
        F.add({ items: both({ p, q }).concat(table(rows.length - 1), str(0)), say: R.w(bad) + ' is a shortest string on which they differ. Trace it on both machines, starting in ' + p + ' and ' + q + '.' });
        ws.forEach((c, i) => {
          const p2 = dA.get(p).get(c), q2 = dB.get(q).get(c);
          F.add({ items: both({ p: p2, q: q2, ta: [p + '>' + p2], tb: [q + '>' + q2] }).concat(table(rows.length - 1), str(i + 1)), say: 'Read ' + c + ': A goes ' + p + ' → ' + p2 + ', B goes ' + q + ' → ' + q2 + '.' });
          p = p2; q = q2;
        });
        const okA = accA.has(p);
        F.add({ items: both({ ga: okA ? [p] : [], ba: okA ? [] : [p], gb: okA ? [] : [q], bb: okA ? [q] : [] }).concat(table(rows.length - 1), str(ws.length)), say: (okA ? 'A accepts ' + R.w(bad) + ' and B rejects it' : 'B accepts ' + R.w(bad) + ' and A rejects it') + ': the machines are not equivalent.', mark: 'differ' });
      }
      return { frames: F.list, def: { sections: [R.tuple(A, 'A (completed)'), R.tuple(B, 'B (completed)', 'tupleB'), { id: 'alg', kind: 'math', title: 'The test', text: 'visit pairs (p, q) reachable from (q₀ᴬ, q₀ᴮ)\nequal  ⇔  in every pair, p ∈ Fᴬ ⇔ q ∈ Fᴮ' }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Equivalent', 'Not equivalent'], ask: 'Do these two DFAs accept the same language?', answer: (fr) => fr[0].meta.equal, explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => i > 0 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.pair && fr[i].meta && fr[i].meta.pair && i >= 2, once: true, pick: 'option', options: ['They agree', 'They disagree'], ask: (fr, i) => 'Next pair: (' + fr[i + 1].meta.pair.join(', ') + '). Will A and B agree there?', answer: (fr, i) => (fr[i + 1].meta.agree ? 'They agree' : 'They disagree'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A has 4 states and B has 5. How many pairs can the search visit, at most?', options: ['9', '20', '2⁹', 'Infinitely many'], answer: 1, why: 'Each pair is (state of A, state of B): at most 4 × 5 = 20, so the search always ends.' },
      { q: 'Why does breadth-first search give a shortest counterexample?', options: ['It visits pairs in order of the length of the string that first reaches them', 'It tries short strings at random', 'It minimises both machines', 'It does not'], answer: 0, why: 'Pairs reached by shorter strings are visited first, so the first disagreeing pair comes with a shortest string.' },
      { q: 'Two DFAs with different numbers of states…', options: ['are never equivalent', 'may still be equivalent', 'are equivalent if both are complete', 'cannot be compared'], answer: 1, why: 'A machine may have redundant states; only the language matters.' },
      { q: 'Equivalence can also be decided with…', options: ['the emptiness test on the symmetric difference', 'the pumping lemma', 'counting states', 'nothing else'], answer: 0, why: 'A and B are equal exactly when (A − B) ∪ (B − A) is empty, and that language has a product DFA.' },
      { q: 'Why are the machines completed first?', options: ['So that every pair has a move on every symbol, and a dying run is a real rejecting state', 'To make them minimal', 'For speed', 'They need not be'], answer: 0, why: 'A pair needs both machines to move; the dead state stands for a rejecting run.' },
    ],
  });

  // ---- counting -----------------------------------------------------------------------------------------------------------
  const NO_BB = 'start o\naccept o b\no -a-> o\no -b-> b\nb -a-> o';
  const EVEN_A = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const FIN = 'start s\naccept t u\ns -a-> t\nt -b-> u\ns -b-> t';
  const ALL = 'start s\naccept s\ns -a,b-> s';
  T.topic({
    id: 'decide-count', family: 'decide', order: 40, title: 'Counting the strings of each length',
    blurb: 'How many strings of length k does a DFA accept? Count, for each state, the strings of length k that lead there: each column of the table is the sum of moves out of the column before.',
    inputs: [R.machineInput({ id: 'm', label: 'DFA', def: NO_BB, kind: 'dfa', max: 5 }), { id: 'n', kind: 'number', label: 'Up to length', def: 5, min: 2, max: 7 }],
    presets: [
      { label: 'No two b\'s in a row: Fibonacci', values: { m: NO_BB, n: 6 } },
      { label: 'Even number of a\'s: half of everything', values: { m: EVEN_A, n: 5 } },
      { label: 'A finite language: counts drop to 0', values: { m: FIN, n: 4 } },
      { label: 'Every string: 2ᵏ', values: { m: ALL, n: 6 } },
    ],
    counters: [{ id: 'len', label: 'length done' }, { id: 'total', label: 'accepted so far' }],
    run(inp) {
      const fa = R.fa(inp.m), d = R.dia(fa), n = inp.n;
      const pos = K.graph.layout(d).pos;
      const g0 = K.graph.draw(d, { pos });
      const gb = R.bounds(g0.items);
      const Q = fa.states;
      const cnt = Q.map(() => new Array(n + 1).fill(null));
      const si = (q) => Q.indexOf(q);
      cnt[si(fa.start)][0] = 0;
      const tx = gb.x + gb.w + 60, ty = gb.y + gb.h / 2 - (34 + Q.length * 40) / 2;
      const table = (hot, arrows) => K.table.draw({ rows: cnt.map((r) => r.map((v) => (v === null ? '' : String(v)))), rowHead: Q.map((q) => (fa.accept.includes(q) ? '* ' : '') + q), colHead: Array.from({ length: n + 1 }, (_, k) => String(k)), corner: 'k', x: tx, y: ty, cw: 46, ch: 40, hot: hot || [], arrows: arrows || [], cls: (r, c) => (fa.accept.includes(Q[r]) && cnt[r][c] > 0 ? 'good' : ''), prefix: 'ct', size: 16 }).items;
      const tb = R.bounds(table());
      const totals = [];
      const bars = () => {
        const max = Math.max(1, ...totals);
        const base = tb.y + tb.h + 158, H = 90, bw = 30;
        const items = [R.caption('bar:t', tb.x, tb.y + tb.h + 26, 'accepted strings of each length', 'title', 'start')];
        totals.forEach((v, k) => {
          const h = Math.max(3, (v / max) * H), x = tx + 50 + k * 46 + 8;
          items.push({ key: 'bar:' + k, kind: 'cell', x, y: base - h, w: bw, h, text: '', cls: 'act', enter: 'grow' });
          items.push({ key: 'bar:v' + k, kind: 'text', x: x + bw / 2, y: base - h - 7, text: String(v), anchor: 'middle', cls: 'strong' });
          items.push({ key: 'bar:k' + k, kind: 'text', x: x + bw / 2, y: base + 18, text: String(k), anchor: 'middle', cls: 'title' });
        });
        return items;
      };
      const F = new T.Frames(['len', 'total']);
      for (const q of Q) cnt[si(q)][0] = q === fa.start ? 1 : 0;
      const shown = cnt.map((r) => r.slice());
      for (const r of cnt) r.fill(null);
      F.add({ items: g0.items.concat(table()), say: 'Row q, column k will hold how many strings of length k lead from ' + fa.start + ' to q. The accepted ones are the strings ending in an accepting row (marked *).' });
      for (let i = 0; i < Q.length; i++) cnt[i][0] = shown[i][0];
      totals.push(fa.accept.includes(fa.start) ? 1 : 0);
      F.set('len', 0).set('total', totals[0]);
      F.add({ items: K.graph.draw(d, { pos, active: [fa.start] }).items.concat(table(Q.map((_, i) => [i, 0])), bars()), say: 'Length 0: only ε, which leads to ' + fa.start + '. So the column is 1 for ' + fa.start + ' and 0 elsewhere; ' + totals[0] + ' accepted string of length 0.', hl: { rec: ['0'] }, meta: { k: 0, total: totals[0] } });
      const del = FA._deltaMap(fa);
      for (let k = 1; k <= n; k++) {
        const arrows = [];
        const into = Q.map(() => []);
        for (const p of Q) for (const a of fa.alphabet) { const q = del.get(p).get(a); if (q === undefined) continue; if (cnt[si(p)][k - 1] > 0) { into[si(q)].push({ p, a, v: cnt[si(p)][k - 1] }); const key = si(p) + '>' + si(q); if (!arrows.some((x) => x.key === key)) arrows.push({ key, from: [si(p), k - 1], to: [si(q), k], bend: si(p) === si(q) ? 0 : (si(p) < si(q) ? 18 : -18) }); } }
        for (let i = 0; i < Q.length; i++) cnt[i][k] = into[i].reduce((s, x) => s + x.v, 0);
        const tot = Q.reduce((s, q, i) => s + (fa.accept.includes(q) ? cnt[i][k] : 0), 0);
        totals.push(tot);
        F.set('len', k).count('total', tot);
        const ex = Q.map((q, i) => [q, i]).find(([, i]) => into[i].length > 1) || Q.map((q, i) => [q, i]).find(([, i]) => into[i].length);
        const why = ex ? ' For example ' + ex[0] + ' gets ' + cnt[ex[1]][k] + ' = ' + into[ex[1]].map((x) => x.v + ' from ' + x.p + ' on ' + x.a).join(' + ') + '.' : ' Nothing moves on: every count is 0.';
        F.add({ items: K.graph.draw(d, { pos, active: Q.filter((q) => cnt[si(q)][k] > 0) }).items.concat(table(Q.map((_, i) => [i, k]), arrows.map((x) => ({ from: x.from, to: x.to, bend: x.bend }))), bars()), say: 'Length ' + k + ': each state adds up the counts of the states that move into it.' + why + ' Accepted: ' + tot + '.', hl: { rec: ['1'] }, meta: { k, total: tot, col: cnt.map((r) => r[k]) } });
      }
      F.add({ items: g0.items.concat(table(), bars()), say: 'The accepted counts for lengths 0 to ' + n + ' are ' + totals.join(', ') + '. Each column took one pass over the moves, so this is fast even when the strings themselves are far too many to list.', mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(fa), R.delta(fa).section, { id: 'rec', kind: 'math', title: 'The recurrence', text: 'N(q, 0) = 1 if q = q₀, else 0\nN(q, k) = Σ N(p, k−1) over moves p -a-> q\naccepted of length k = Σ N(f, k), f ∈ F' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 2, once: true, pick: 'option', options: (fr) => R.numberOptions(fr.find((x) => x.meta && x.meta.k === 2).meta.total), ask: 'How many strings of length 2 will be accepted?', answer: (fr, i) => String(fr[i + 1].meta.total), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 3 && Math.max(...fr[i + 1].meta.col) > 0, once: true, pick: 'item', ask: 'Which state will be reached by the most strings of length 3? Click its cell in column 3.', answer: (fr, i) => { const c = fr[i + 1].meta.col, m = Math.max(...c); return c.map((v, r) => (v === m ? 'ct:' + r + ',3' : null)).filter(Boolean); }, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does this method need a DFA, not an NFA?', options: ['NFAs have no tables', 'An NFA may have several paths for one string, so it would count paths, not strings', 'NFAs are slower', 'It works for both'], answer: 1, why: 'In a DFA each string has exactly one path, so counting paths counts strings.' },
      { q: 'In the DFA for "no two b\'s in a row", the counts are 1, 2, 3, 5, 8, …. Why?', options: ['A coincidence', 'A string of length k ends in a (any good string of length k−1, then a) or in ab (any of length k−2, then ab)', 'Because there are two symbols', 'Because the DFA has two states'], answer: 1, why: 'That split gives N(k) = N(k−1) + N(k−2), the Fibonacci rule.' },
      { q: 'A DFA has s states and alphabet size m. How much work is one column?', options: ['about s · m additions', '2ᵏ', 'k!', 's²ᵏ'], answer: 0, why: 'Each of the s · m moves adds one count into the next column.' },
      { q: 'The counts become 0 from some length on. What does that say about the language?', options: ['It is empty', 'It is finite', 'It is infinite', 'Nothing'], answer: 1, why: 'No accepted string has that length or more, so there are finitely many.' },
    ],
  });
})();
