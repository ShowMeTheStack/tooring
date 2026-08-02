// Closure properties of the regular languages, each shown as the construction that proves it: the product
// of two DFAs as a grid of pair states (union, intersection, difference), concatenation, union and star by
// gluing NFAs with ε-moves (and the tempting wrong way to build a star), reversal by turning every arrow
// around, homomorphisms and their inverses, and the right quotient by another language.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg, FA = T.FA;

  T.family({ id: 'closure', part: 'regular', order: 40, title: 'Closure properties', blurb: 'Combine regular languages and the result is regular again: each closure property is a construction you can watch, from product grids to ε-glue.' });

  /** Rename the keys (and edge ends) of items from one prefix to another */
  const rekey = (items, a, b) => items.map((it) => { const o = Object.assign({}, it); for (const k of ['key', 'from', 'to']) if (typeof o[k] === 'string' && o[k].startsWith(a + ':')) o[k] = b + o[k].slice(a.length); return o; });
  /** Edges of a dense generated machine may cross each other */
  const crossOk = (items) => items.map((it) => (it.kind === 'edge' && /\btr\b/.test(it.cls || '') ? Object.assign({}, it, { audit: 'edge-x' }) : it));
  /** A shaded box around a drawing, with a caption above it */
  const frameBox = (key, b, cls, text, pad) => { pad = pad === undefined ? 22 : pad; return [{ key, kind: 'region', x: b.x - pad, y: b.y - pad, w: b.w + 2 * pad, h: b.h + 2 * pad, cls, rx: 18 }, R.caption(key + ':t', b.x - pad + 4, b.y - pad - 12, text, 'title', 'start')]; };
  /** Shift a position map */
  const movePos = (pos, dx, dy) => { const o = {}; for (const q in pos) o[q] = { x: pos[q].x + dx, y: pos[q].y + dy }; return o; };
  const boxOfPos = (pos) => { const xs = Object.values(pos).map((p) => p.x), ys = Object.values(pos).map((p) => p.y); return { x: Math.min(...xs), y: Math.min(...ys), w: Math.max(...xs) - Math.min(...xs), h: Math.max(...ys) - Math.min(...ys) }; };
  /** Machine text check for the alphabet {a, b} family of examples: a friendly wrapper */
  const sample = (fa, n) => FA.enumerate(fa, { max: n || 4, maxLen: 6 }).map(R.w);
  const listOr = (xs, none) => (xs.length ? xs.join(', ') : none || 'nothing');

  // ---- product ----------------------------------------------------------------------------------------------------
  const EVEN_A = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const ENDS_B = 'start x\naccept y\nx -a-> x\nx -b-> y\ny -a-> x\ny -b-> y';
  const STARTS_A = 'start s\naccept t\ns -a-> t\nt -a,b-> t';
  const NO_A = 'start n\naccept n\nn -b-> n';
  const OPN = { union: { sym: '∪', rule: 'either part accepts' }, intersection: { sym: '∩', rule: 'both parts accept' }, difference: { sym: '−', rule: 'A accepts and B does not' } };
  const complete = (m, sigma) => { const x = FA.make(Object.assign({}, m, { alphabet: sigma })); return FA.isComplete(x) ? x : FA.complete(x, 'dead').fa; };
  const sigmaOf = (a, b) => [...new Set([...a.alphabet, ...b.alphabet])].sort();

  T.topic({
    id: 'closure-product', family: 'closure', order: 10, title: 'The product construction',
    blurb: 'Run two DFAs side by side: a state of the product is a pair, one state from each. Union, intersection and difference differ only in which pairs accept.',
    inputs: [
      R.machineInput({ id: 'a', label: 'DFA A', def: EVEN_A, kind: 'dfa', max: 4 }),
      R.machineInput({ id: 'b', label: 'DFA B', def: ENDS_B, kind: 'dfa', max: 4 }),
      { id: 'op', kind: 'choice', label: 'Operation', def: 'intersection', options: [{ value: 'intersection', label: 'A ∩ B' }, { value: 'union', label: 'A ∪ B' }, { value: 'difference', label: 'A − B' }] },
    ],
    presets: [
      { label: 'Even a\'s ∩ ends in b', values: { a: EVEN_A, b: ENDS_B, op: 'intersection' } },
      { label: 'Even a\'s ∪ ends in b', values: { a: EVEN_A, b: ENDS_B, op: 'union' } },
      { label: 'Ends in b − even a\'s', values: { a: ENDS_B, b: EVEN_A, op: 'difference' } },
      { label: 'Missing moves: each machine is completed first', values: { a: STARTS_A, b: ENDS_B, op: 'intersection' } },
      { label: 'Disjoint: starts with a ∩ no a at all = ∅', values: { a: STARTS_A, b: NO_A, op: 'intersection' } },
    ],
    check: (inp) => {
      const a = R.fa(inp.a), b = R.fa(inp.b), s = sigmaOf(a, b);
      if (s.length > 2) return 'The two machines together read at most 2 symbols, so the grid stays readable';
      for (const [m, n] of [[a, 'A'], [b, 'B']]) if (complete(m, s).states.length > 4) return 'DFA ' + n + ': at most 4 states once its missing moves go to a dead state';
      return null;
    },
    counters: [{ id: 'pairs', label: 'pairs reached' }, { id: 'moves', label: 'moves made' }],
    run(inp) {
      const a0 = R.fa(inp.a), b0 = R.fa(inp.b), sigma = sigmaOf(a0, b0);
      const A = complete(a0, sigma), B = complete(b0, sigma);
      const op = inp.op, O = OPN[op];
      const P = FA.product(A, B, op);
      const nm = (p, q) => '(' + p + ',' + q + ')';
      const all = [];
      for (const p of A.states) for (const q of B.states) all.push(nm(p, q));
      const wMax = Math.max(...all.map((q) => K.graph.shape(q).w));
      const gx = Math.max(150, wMax + 80), gy = 130;
      const gpos = {};
      A.states.forEach((p, i) => B.states.forEach((q, j) => { gpos[nm(p, q)] = { x: j * gx, y: i * gy }; }));
      // the two parts, stacked on the left of the grid
      const da = R.dia(A), db = R.dia(B);
      const la = K.graph.layout(da).pos, lb = K.graph.layout(db).pos;
      const ba = R.bounds(K.graph.draw(da, { pos: la }).items), bb = R.bounds(K.graph.draw(db, { pos: lb }).items);
      const colW = Math.max(ba.w, bb.w);
      const gridH = (A.states.length - 1) * gy;
      const leftX = -90 - colW - 40;
      const pa = movePos(la, leftX + (colW - ba.w) / 2 - ba.x, -40 - ba.y);
      const pb = movePos(lb, leftX + (colW - bb.w) / 2 - bb.x, -40 + ba.h + 90 - bb.y);
      void gridH;
      const parts = (o) => {
        o = o || {};
        const ga = K.graph.draw(da, { prefix: 'ga', pos: pa, active: o.p ? [o.p] : [], taken: o.ta || [] });
        const gb = K.graph.draw(db, { prefix: 'gb', pos: pb, active: o.q ? [o.q] : [], taken: o.tb || [] });
        const xa = R.bounds(ga.items), xb = R.bounds(gb.items);
        return ga.items.concat(gb.items, [R.caption('cap:a', xa.x, xa.y - 14, 'A', 'title', 'start'), R.caption('cap:b', xb.x, xb.y - 14, 'B', 'title', 'start')]);
      };
      const F = new T.Frames(['pairs', 'moves']);
      const reached = new Set();
      const trans = [];
      const grid = (o) => {
        o = o || {};
        const m = { kind: 'dfa', states: all, start: o.start ? P.fa.start : null, accept: o.accept ? P.fa.accept : [], trans: trans.slice(), pos: {} };
        const g = K.graph.draw(m, Object.assign({ pos: gpos, dim: all.filter((x) => !reached.has(x)), hideStart: !o.start }, o.g || {}));
        const gb = R.bounds(g.items);
        return crossOk(g.items).concat([R.caption('cap:g', gb.x, gb.y - 14, 'A × B, ' + all.length + ' pairs', 'title', 'start')]);
      };
      const dt = R.delta(P.fa);
      F.add({ items: parts().concat(grid()), say: 'To run A and B on the same input at once, remember both states: every pair (state of A, state of B) is a possible state, ' + A.states.length + ' × ' + B.states.length + ' = ' + all.length + ' of them, faint until the product reaches them.' + (A.states.length > a0.states.length || B.states.length > b0.states.length ? ' (Missing moves were first sent to a dead state, so both machines are complete.)' : '') });
      reached.add(P.fa.start);
      F.set('pairs', 1);
      F.add({ items: parts({ p: A.start, q: B.start }).concat(grid({ start: true, g: { hot: [P.fa.start] } })), say: 'Both start together, so the product starts in the pair ' + P.fa.start + '.', hl: { delta: [dt.row(P.fa.start)] } });
      // breadth first, a frame per pair: where each symbol takes both parts
      const order = [];
      for (const s of P.trace) if (s.kind === 'pair-edge' && !order.includes(s.from)) order.push(s.from);
      order.forEach((from, k) => {
        const moves = P.trace.filter((s) => s.kind === 'pair-edge' && s.from === from);
        const [p, q] = P.pairs[from];
        const fresh = moves.filter((s) => !reached.has(s.to)).map((s) => s.to);
        for (const s of moves) { trans.push({ from, to: s.to, label: s.sym }); reached.add(s.to); }
        F.set('pairs', reached.size).count('moves', moves.length);
        F.add({ items: parts({ p, q, ta: moves.map((s) => p + '>' + s.pair[0]), tb: moves.map((s) => q + '>' + s.pair[1]) }).concat(grid({ start: true, g: { hot: [from], taken: moves.map((s) => from + '>' + s.to) } })), say: 'From ' + from + ': ' + moves.map((s) => 'on ' + s.sym + ', A goes ' + p + ' → ' + s.pair[0] + ' and B goes ' + q + ' → ' + s.pair[1] + ', so ' + s.to).join('; ') + '.' + (fresh.length ? ' New: ' + fresh.join(', ') + '.' : ' No new pair.'), hl: { delta: moves.map((s) => dt.rc(from, s.sym)) }, meta: { bfs: k, from, moves: moves.map((s) => ({ sym: s.sym, to: s.to })) } });
      });
      const never = all.filter((x) => !reached.has(x));
      F.add({ items: parts().concat(grid({ start: true, accept: true, g: { good: P.fa.accept } })), say: 'For ' + op + ', a pair accepts when ' + O.rule + ': ' + (P.fa.accept.length ? P.fa.accept.join(', ') : 'no reachable pair does') + '.' + (never.length ? ' ' + R.plural(never.length, 'pair is', 'pairs are') + ' never reached and can be left out.' : ' Every pair is reachable.'), hl: { tuple: ['3'] }, meta: { acc: P.fa.accept.length } });
      // the languages compared on every short string
      const inA = FA.acceptor(A), inB = FA.acceptor(B), inP = FA.acceptor(P.fa);
      const gb = R.bounds(grid({ start: true }));
      const pyr = R.pyramid({ alphabet: sigma, maxLen: 3, member: (w) => inP(w), x: gb.x + gb.w / 2, y: gb.y + gb.h + 70, label: 'strings up to length 3 in A ' + O.sym + ' B' });
      const shown = R.upTo(sigma, 3);
      const ex = (f) => shown.filter(f).slice(0, 3).map(R.w);
      F.add({ items: parts().concat(grid({ start: true, accept: true, g: { good: P.fa.accept } }), pyr.items), say: 'The lit strings are accepted by the product: ' + listOr(ex((w) => inP(w)), 'none at all') + '. In A only: ' + listOr(ex((w) => inA(w) && !inB(w)), 'none') + '; in B only: ' + listOr(ex((w) => !inA(w) && inB(w)), 'none') + '; in both: ' + listOr(ex((w) => inA(w) && inB(w)), 'none') + '.', mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(P.fa, 'The product A ' + O.sym + ' B'), { id: 'rule', kind: 'math', title: 'Its moves and accepting pairs', text: 'δ((p, q), a) = (δA(p, a), δB(q, a))\n(p, q) accepts when ' + O.rule }, dt.section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.bfs === 1, once: true, pick: 'item', ask: (fr, i) => 'From ' + fr[i + 1].meta.from + ', which pair does ' + fr[i + 1].meta.moves[0].sym + ' lead to? Click it in the grid.', answer: (fr, i) => 'g:s:' + fr[i + 1].meta.moves[0].to, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.acc !== undefined, once: true, pick: 'option', options: (fr) => { const f = fr.find((x) => x.meta && x.meta.acc !== undefined); return R.numberOptions(f.meta.acc); }, ask: 'How many of the reached pairs will accept?', answer: (fr, i) => String(fr[i + 1].meta.acc), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A has 3 states and B has 5. At most how many states does their product have?', options: ['8', '15', '35', '2⁸'], answer: 1, why: 'One per pair: 3 × 5 = 15, fewer when some pairs are unreachable.' },
      { q: 'What changes between the product for A ∩ B and for A ∪ B?', options: ['The moves', 'The start pair', 'Only which pairs accept', 'The number of pairs'], answer: 2, why: 'The pairs and moves are the same; ∩ accepts when both parts accept, ∪ when either does.' },
      { q: 'Why must both machines be complete before building the product for A ∪ B?', options: ['They need not be', 'Otherwise a string that dies in B but is accepted by A would have no run in the product', 'To make the product smaller', 'Because union needs ε-moves'], answer: 1, why: 'A pair needs both parts to move; a missing move in one part would kill the pair even though the other part may still accept.' },
      { q: 'A − B can also be written as…', options: ['A ∩ B', 'A ∩ (complement of B)', 'A ∪ B', 'B − A'], answer: 1, why: 'A string is in A − B when A accepts it and B does not: intersect A with the complement of B.' },
      { q: 'The product for A ∩ B has no reachable accepting pair. What does that tell you?', options: ['A is empty', 'B is empty', 'No string is in both languages', 'The product is wrong'], answer: 2, why: 'Every string leads to some reachable pair; if none of those accepts, no string is accepted by both.' },
    ],
  });

  // ---- gluing: concatenation, union and star ----------------------------------------------------------------------------
  const AB = 'start p\naccept r\np -a-> q\nq -b-> r\nr -b-> r';
  const BA = 'start u\naccept w\nu -b-> v\nv -a-> w';
  const ASTAR_B = 'start s\naccept f\ns -a-> s\ns -b-> f';
  const ODD_A = 'start e\naccept o\ne -a-> o\no -a-> e';
  T.topic({
    id: 'closure-glue', family: 'closure', order: 20, title: 'Concatenation, union and star by gluing',
    blurb: 'Put the machines side by side and join them with ε-moves: from A\'s accepting states into B for concatenation, from a new start into both for union, and back to the start for star.',
    inputs: [
      { id: 'op', kind: 'choice', label: 'Construction', def: 'concat', options: [{ value: 'concat', label: 'concatenation A·B' }, { value: 'union', label: 'union A ∪ B' }, { value: 'star', label: 'star A*' }, { value: 'wrong', label: 'star, the tempting wrong way' }] },
      R.machineInput({ id: 'a', label: 'Machine A', def: AB, kind: 'nfa', max: 4 }),
      R.machineInput({ id: 'b', label: 'Machine B (not used by star)', def: BA, kind: 'nfa', max: 4 }),
    ],
    presets: [
      { label: 'ab⁺ then ba: concatenation', values: { op: 'concat', a: AB, b: BA } },
      { label: 'ab⁺ or ba: union', values: { op: 'union', a: AB, b: BA } },
      { label: 'Star of ab⁺', values: { op: 'star', a: AB } },
      { label: 'Why star needs a new start: (a*b)*', values: { op: 'wrong', a: ASTAR_B } },
      { label: 'Star of an odd number of a\'s: ε gets in', values: { op: 'star', a: ODD_A } },
    ],
    counters: [{ id: 'eps', label: 'ε-moves added' }, { id: 'states', label: 'states' }],
    run(inp) {
      const op = inp.op;
      const A = R.fa(inp.a);
      const B = op === 'concat' || op === 'union' ? FA.disjoint(A, R.fa(inp.b)) : null;
      const F = new T.Frames(['eps', 'states']);
      const da = R.dia(A);
      const la = K.graph.layout(da).pos;
      const ba = R.bounds(K.graph.draw(da, { pos: la }).items);
      let pa = movePos(la, -ba.x, -ba.y), pb = null;
      if (B) {
        const db = R.dia(B), lb = K.graph.layout(db).pos, bb = R.bounds(K.graph.draw(db, { pos: lb }).items);
        pb = op === 'concat' ? movePos(lb, ba.w + 150 - bb.x, (ba.h - bb.h) / 2 - bb.y) : movePos(lb, (ba.w - bb.w) / 2 - bb.x, ba.h + 110 - bb.y);
      }
      const pos = Object.assign({}, pa, pb || {});
      // the new state of union and star sits to the left, level with the start(s)
      const S = op === 'union' ? FA.unionNFA(A, B) : op === 'concat' ? FA.concatNFA(A, B) : FA.starNFA(A);
      const newS = op === 'union' || op === 'star' || op === 'wrong' ? FA.freshName(new Set(A.states.concat(B ? B.states : [])), 's') : null;
      if (newS) pos[newS] = { x: -130, y: op === 'union' ? (pos[A.start].y + pos[B.start].y) / 2 : pos[A.start].y };
      const boxA = R.bounds(K.graph.draw(da, { pos: pa }).items), boxB = B ? R.bounds(K.graph.draw(R.dia(B), { pos: pb }).items) : null;
      const regions = frameBox('rgA', boxA, 'r1', 'A').concat(B ? frameBox('rgB', boxB, 'r2', 'B') : []);
      // a drawing of any stage of the gluing: the states, moves and starts given
      const draw = (states, trans, accept, o) => {
        o = o || {};
        const m = { kind: 'nfa', states, start: o.start, accept, trans: R.dia(FA.make({ states, start: o.start || states[0], accept, trans })).trans, pos: {} };
        let items = K.graph.draw(m, Object.assign({ pos, hideStart: !o.start }, o.g || {})).items;
        // a second start arrow, for B while it is still a machine of its own
        if (o.start2) {
          const g2 = K.graph.draw(R.dia(B), { prefix: 'tmp', pos: pb });
          items = items.concat(rekey(g2.items.filter((it) => it.key === 'tmp:start' || it.key === 'tmp:startDot'), 'tmp', 'g').map((it) => Object.assign({}, it, { key: 'gB' + it.key.slice(1) })));
        }
        return regions.concat(items);
      };
      const eps = (from, to) => ({ from, sym: '', to });
      const both = A.trans.concat(B ? B.trans : []);
      const stA = A.states.concat(B ? B.states : []);
      F.set('states', stA.length);
      const exA = sample(A, 3), exB = B ? sample(B, 3) : [];
      F.add({ items: draw(stA, both, A.accept.concat(B ? B.accept : []), { start: A.start, start2: !!B }), say: B ? 'A accepts ' + (exA.length ? listOr(exA, 'nothing') + ' and more' : 'nothing') + '; B accepts ' + (exB.length ? listOr(exB, 'nothing') + ' and more' : 'nothing') + '. ' + (op === 'concat' ? 'A word of A·B is a word of A followed by a word of B.' : 'A word of A ∪ B is a word of either.') : 'A accepts ' + (exA.length ? listOr(exA, 'nothing') + ' and more' : 'nothing') + '. A word of A* is any number of words of A, one after another, including none at all.' });
      const sampleOf = (m, avoid) => { const ws = FA.enumerate(m, { max: 30, maxLen: 8 }); return ws.find((w) => !avoid || !avoid(w)) || ws[0]; };
      const pathOf = (m, w) => { const r = FA.paths(m, w, 1); return r.paths.length ? r.paths[0] : []; };
      const lit = (path) => path.map((e) => e.from + '>' + e.to);
      const finalSay = (m, w, extra) => (w === undefined ? 'This machine accepts nothing, so there is nothing to trace.' : 'One accepting path for ' + R.w(w) + ' is lit' + (extra || '') + '.');
      if (op === 'concat') {
        const link = A.accept.map((f) => eps(f, B.start));
        F.count('eps', link.length);
        F.add({ items: draw(stA, both.concat(link), A.accept.concat(B.accept), { start: A.start, g: { taken: link.map((e) => e.from + '>' + e.to), hot: [B.start] } }), say: 'Glue: an ε-move from each accepting state of A (' + listOr(A.accept, 'there are none') + ') to B\'s start ' + B.start + '. After a word of A the machine may jump, without reading, into B. B\'s own start arrow goes.', meta: { glue: true } });
        F.add({ items: draw(stA, both.concat(link), B.accept, { start: A.start, g: { good: B.accept } }), say: 'Only B\'s accepting states ' + R.set(B.accept) + ' accept now: reaching the end of A is just half the job.', hl: { tuple: ['3'] } });
        const w = sampleOf(S.fa, (x) => FA.accepts(A, x));
        const path = w === undefined ? [] : pathOf(S.fa, w);
        F.add({ items: draw(stA, both.concat(link), B.accept, { start: A.start, g: { taken: lit(path) } }), say: finalSay(S.fa, w, path.length ? ': it reads ' + R.w(path.slice(0, path.findIndex((e) => e.sym === '' && e.to === B.start)).map((e) => e.sym).join('')) + ' in A, crosses the ε-bridge, and reads the rest in B' : ''), mark: 'done' });
      } else if (op === 'union') {
        const link = [eps(newS, A.start), eps(newS, B.start)];
        F.set('states', stA.length + 1).count('eps', 2);
        F.add({ items: draw([newS].concat(stA), both.concat(link), A.accept.concat(B.accept), { start: newS, g: { taken: [newS + '>' + A.start, newS + '>' + B.start], hot: [newS], from: { [newS]: ['g:s:' + A.start, 'g:s:' + B.start] } } }), say: 'A new start ' + newS + ' with ε-moves to ' + A.start + ' and ' + B.start + ': before reading anything the machine guesses which of the two it is going to run. Both old start arrows go.', meta: { glue: true } });
        const w1 = sampleOf(S.fa), w2 = sampleOf(S.fa, (x) => FA.accepts(A, x));
        F.add({ items: draw([newS].concat(stA), both.concat(link), A.accept.concat(B.accept), { start: newS, g: { good: A.accept.concat(B.accept) } }), say: 'All the old accepting states still accept. So ' + R.w(w1) + (w2 !== undefined && w2 !== w1 ? ' and ' + R.w(w2) : '') + ' are accepted: one through A, ' + (w2 !== undefined && w2 !== w1 ? 'one through B.' : 'and any word of B through B.'), hl: { tuple: ['3'] } });
        const path = w2 === undefined ? [] : pathOf(S.fa, w2);
        F.add({ items: draw([newS].concat(stA), both.concat(link), A.accept.concat(B.accept), { start: newS, g: { taken: lit(path) } }), say: finalSay(S.fa, w2, ', taking the ε-move into B'), mark: 'done' });
      } else {
        // star, done right, or the tempting way first
        const back = A.accept.filter((f) => f !== A.start || true).map((f) => eps(f, A.start));
        if (op === 'wrong') {
          const W = FA.make({ states: A.states, start: A.start, accept: [...new Set(A.accept.concat([A.start]))], trans: A.trans.concat(back) });
          const inStar = FA.acceptor(S.fa);
          const bad = FA.enumerate(W, { max: 200, maxLen: 8 }).find((x) => !inStar(x));
          F.count('eps', back.length);
          F.add({ items: draw(A.states, A.trans.concat(back), W.accept, { start: A.start, g: { taken: back.map((e) => e.from + '>' + e.to), good: [A.start] } }), say: 'The tempting shortcut: make the start ' + A.start + ' accepting (for ε) and add ε-moves from ' + listOr(A.accept) + ' back to ' + A.start + '.', meta: { wrong: bad === undefined ? null : bad } });
          if (bad !== undefined) {
            const path = pathOf(W, bad);
            F.add({ items: draw(A.states, A.trans.concat(back), W.accept, { start: A.start, g: { taken: lit(path), bad: [path.length ? path[path.length - 1].to : A.start] } }), say: 'But now ' + R.w(bad) + ' is accepted, and it is not in A*: it is not made of words of A. Moves come back into ' + A.start + ' (its loop), so a run can stop there half-way through a word.', mark: 'wrong' });
          } else F.add({ items: draw(A.states, A.trans.concat(back), W.accept, { start: A.start }), say: 'Here nothing goes wrong, because no move enters ' + A.start + '. As soon as some move does, a run can stop at ' + A.start + ' in the middle of a word, so the safe way is a new start.' });
          F.set('eps', 0);
        }
        const link = [eps(newS, A.start)];
        F.set('states', A.states.length + 1).count('eps', 1);
        F.add({ items: draw([newS].concat(A.states), A.trans.concat(link), [newS].concat(A.accept), { start: newS, g: { taken: [newS + '>' + A.start], good: [newS], hot: [newS] } }), say: 'The right way: a new start ' + newS + ', accepting, so ε (zero words) is in A*, with an ε-move into ' + A.start + '. Nothing ever comes back into ' + newS + '.', meta: { glue: true } });
        F.count('eps', back.length);
        F.add({ items: draw([newS].concat(A.states), A.trans.concat(link, back), [newS].concat(A.accept), { start: newS, g: { taken: back.map((e) => e.from + '>' + e.to) } }), say: 'ε-moves from each accepting state (' + listOr(A.accept, 'none') + ') back to ' + A.start + ': after a whole word of A, start the next one.' });
        const w = sampleOf(S.fa, (x) => FA.accepts(A, x) || x === '');
        const path = w === undefined ? [] : pathOf(S.fa, w);
        F.add({ items: draw([newS].concat(A.states), A.trans.concat(link, back), [newS].concat(A.accept), { start: newS, g: { taken: lit(path) } }), say: finalSay(S.fa, w, ': it is not a word of A, but it splits into words of A, and the path loops back by ε between them'), mark: 'done' });
      }
      return { frames: F.list, def: { sections: [R.tuple(S.fa, 'The glued machine'), R.delta(S.fa).section] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && fr[1] && fr[1].meta && fr[1].meta.wrong, once: true, pick: 'option', options: ['Yes', 'No'], ask: (fr) => 'Suppose we just make the start accepting and add ε-moves back to it. Will ' + R.w(fr[1].meta.wrong) + ' (not a sequence of words of A) be accepted?', answer: () => 'Yes', explain: (fr) => fr[2].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.glue && !fr.some((x) => x.meta && x.meta.wrong), once: true, pick: 'option', options: ['ε-moves', 'moves on a symbol', 'merging states', 'deleting states'], ask: 'What will join the machines together?', answer: () => 'ε-moves', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'In the machine for A·B, which states accept?', options: ['A\'s accepting states', 'B\'s accepting states', 'Both', 'A new final state only'], answer: 1, why: 'A word must finish inside B; A\'s accepting states now only lead into B by ε.' },
      { q: 'Why does the star construction add a new start state instead of making the old start accepting?', options: ['To accept ε only', 'Because moves may come back into the old start, and a run could then stop half-way through a word', 'Because NFAs need two starts', 'It is only a convention'], answer: 1, why: 'If the old start has incoming moves, accepting there would accept strings that end in the middle of a word of A.' },
      { q: 'Is ε in A* for every A?', options: ['Yes: zero words joined together', 'Only if ε is in A', 'Only if A is finite', 'No'], answer: 0, why: 'The star allows any number of pieces, and zero pieces give ε.' },
      { q: 'How many ε-moves does the union construction add?', options: ['1', '2', 'one per accepting state', 'none'], answer: 1, why: 'From the new start to each of the two old starts.' },
      { q: 'Why are B\'s states renamed (with a ′) when they clash with A\'s?', options: ['For looks', 'So the two machines share no state: a shared state would let runs jump between them', 'To make the machine deterministic', 'They are never renamed'], answer: 1, why: 'Gluing must only connect the machines through the new ε-moves, so they must be disjoint.' },
    ],
  });

  // ---- reversal ----------------------------------------------------------------------------------------------------
  const ENDS_AB = 'start p\naccept r\np -a,b-> p\np -a-> q\nq -b-> r';
  const ENDS_AB_DFA = 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x';
  const TWO_ACC = 'start s\naccept a1 b1\ns -a-> a1\ns -b-> b1\na1 -a-> a1\nb1 -b-> b1';
  const NO_ACC = 'start s\ns -a-> t\nt -b-> s';
  T.topic({
    id: 'closure-reverse', family: 'closure', order: 30, title: 'Reversal: turn every arrow around',
    blurb: 'A path that spells w from the start to acceptance, walked backwards, spells w reversed. So turn every arrow around and swap the roles of start and accepting states.',
    inputs: [
      R.machineInput({ id: 'm', label: 'Machine', def: ENDS_AB_DFA, kind: 'nfa', max: 6 }),
      { id: 'w', kind: 'string', label: 'A string to reverse', def: 'aab', max: 7 },
    ],
    presets: [
      { label: 'Ends with ab: the reversal starts with ba', values: { m: ENDS_AB_DFA, w: 'aab' } },
      { label: 'An NFA for ends with ab', values: { m: ENDS_AB, w: 'bab' } },
      { label: 'Two accepting states: a new start', values: { m: TWO_ACC, w: 'aaa' } },
      { label: 'No accepting state: the reversal of ∅', values: { m: NO_ACC, w: 'ab' } },
    ],
    check: R.alphaCheck('m', 'w', 'String'),
    counters: [{ id: 'flipped', label: 'arrows turned' }, { id: 'read', label: 'symbols read' }],
    run(inp) {
      const fa = R.fa(inp.m), rev = FA.reverse(fa), rf = rev.fa;
      const d0 = R.dia(fa);
      const pos0 = K.graph.layout(d0).pos;
      const pos = rf.states.length > fa.states.length ? K.graph.layout(R.dia(rf), { fixed: pos0 }).pos : pos0;
      const F = new T.Frames(['flipped', 'read']);
      const w = inp.w, wr = [...w].reverse().join('');
      const okW = FA.accepts(fa, w), okR = FA.accepts(rf, wr);
      const flipKeys = (items) => items.map((it) => { if (it.kind !== 'edge' || !/^g:e:/.test(it.key)) return it; const [p, q] = it.key.slice(4).split('>'); return Object.assign({}, it, { key: 'g:e:' + q + '>' + p }); });
      const pathA = okW ? FA.paths(fa, w, 1).paths[0] : null;
      F.add({ items: K.graph.draw(d0, { pos, taken: pathA ? pathA.map((e) => e.from + '>' + e.to) : [] }).items, meta: { start: fa.start }, say: 'The machine ' + (okW ? 'accepts ' + R.w(w) + ' (its path is lit).' : 'does not accept ' + R.w(w) + '.') + ' Reversal must accept ' + R.w(wr) + ' exactly when this machine accepts ' + R.w(w) + '.' });
      // the arrows turn, still with the old start and accepting states
      const turned = { kind: 'nfa', states: fa.states, start: fa.start, accept: fa.accept, trans: R.dia(FA.make({ states: fa.states, start: fa.start, accept: fa.accept, trans: fa.trans.map((e) => ({ from: e.to, sym: e.sym, to: e.from })) })).trans, pos: {} };
      F.set('flipped', fa.trans.length);
      const g1 = K.graph.draw(turned, { pos, edgeCls: Object.fromEntries(turned.trans.map((t) => [t.from + '>' + t.to, 'hot'])) });
      F.add({ items: flipKeys(g1.items), say: 'Turn all ' + fa.trans.length + ' arrows around: p -a-> q becomes q -a-> p. ' + (FA.kind(FA.make({ states: fa.states, start: fa.start, accept: fa.accept, trans: fa.trans.map((e) => ({ from: e.to, sym: e.sym, to: e.from })) })) !== 'dfa' && FA.kind(fa) === 'dfa' ? 'Some state now has two arrows on the same symbol: the reversal of a DFA is usually an NFA.' : 'Labels stay as they were.') });
      const startStep = rev.trace.find((s) => s.kind === 'start');
      const drawRev = (o) => flipKeys(K.graph.draw(R.dia(rf), Object.assign({ pos }, o || {})).items);
      F.add({ items: drawRev({ startHot: true, good: rf.accept, hot: [rf.start], from: rf.states.length > fa.states.length ? { [rf.start]: fa.accept.map((q) => 'g:s:' + q) } : {} }), say: startStep.say + ' The old start ' + fa.start + ' becomes the only accepting state.', hl: { tuple: ['2', '3'] }, meta: { newStart: rf.states.length > fa.states.length } });
      // run w reversed on the reversed machine: a cloud of states
      const clouds = R.clouds(rf, wr);
      const sym = [...wr];
      const sx0 = R.bounds(drawRev()), cw = 46;
      const sx = sx0.x + sx0.w / 2 - Math.max(1, sym.length) * cw / 2, sy = sx0.y + sx0.h + 56;
      const scene = (i, o) => drawRev(o).concat(K.string.draw({ text: sym, pos: i, x: sx, y: sy, cw, label: 'reversed', headText: i >= sym.length ? 'end' : 'next' }).items);
      F.add({ items: scene(0, { active: clouds[0] || [] }), say: 'Now read ' + R.w(wr) + ', the reversal of ' + R.w(w) + '. The machine starts in ' + R.set(clouds[0] || []) + '.', meta: { run: 0 } });
      for (let i = 0; i < sym.length; i++) {
        F.count('read');
        const c = clouds[i + 1] || [];
        F.add({ items: scene(i + 1, { active: c, bad: c.length ? [] : [] }), say: c.length ? 'Read ' + sym[i] + ': the live states are ' + R.set(c) + '.' : 'Read ' + sym[i] + ': no state is left alive.', meta: { run: i + 1 } });
        if (!c.length) break;
      }
      const last = clouds[Math.min(sym.length, clouds.length - 1)] || [];
      F.add({ items: scene(sym.length, { active: last, good: last.filter((q) => rf.accept.includes(q)) }), say: (okR ? R.w(wr) + ' is accepted' : R.w(wr) + ' is rejected') + ', and the original machine ' + (okW ? 'accepts ' : 'rejects ') + R.w(w) + ': ' + (okR === okW ? 'they agree, as they must.' : 'they disagree!'), mark: okR ? 'accepted' : 'rejected', meta: { verdict: okR ? 'Accept' : 'Reject' } });
      return { frames: F.list, def: { sections: [R.tuple(rf, 'The reversed machine'), R.delta(rf).section] } };
    },
    predict: [
      { at: (f, i) => i === 1, once: true, pick: 'item', ask: 'The arrows are turned. Which state will be the only accepting state of the reversed machine? Click it.', answer: (fr) => 'g:s:' + fr[0].meta.start, explain: (fr) => fr[2].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the reversed machine accept the reversed string?', answer: (fr) => fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What happens to the start state in the reversal?', options: ['It stays the start', 'It becomes the only accepting state', 'It is deleted', 'It becomes a dead state'], answer: 1, why: 'A reversed path ends where the original began.' },
      { q: 'The machine has three accepting states. How does the reversal start?', options: ['In all three at once, through a new start with ε-moves', 'In one of them chosen at random', 'In the old start', 'It cannot be reversed'], answer: 0, why: 'A machine has one start, so a new one guesses by ε which old accepting state the reversed path begins at.' },
      { q: 'Is the reversal of a DFA always a DFA?', options: ['Yes', 'No: two arrows into one state on the same symbol become two arrows out of it', 'Only if it is complete', 'Only for finite languages'], answer: 1, why: 'Determinism limits arrows out of a state, not arrows into it; turning them around can break it.' },
      { q: 'The language has no accepting state. What is its reversal?', options: ['Σ*', '{ε}', '∅', 'Undefined'], answer: 2, why: 'The reversal of ∅ is ∅: the new start has no ε-moves to follow.' },
    ],
  });

  // ---- homomorphisms ----------------------------------------------------------------------------------------------------
  const parseH = (text) => {
    const h = {};
    for (const part of String(text).split(/[,;\n]+/)) {
      const p = part.trim();
      if (!p) continue;
      const m = /^(\S)\s*(?:=|→|->|:|↦)\s*(\S*)$/.exec(p);
      if (!m) throw new Error('Mapping: write each symbol as a = 01 (use ε for the empty string), separated by commas');
      h[m[1]] = m[2] === 'ε' || m[2] === 'eps' ? '' : m[2];
    }
    return h;
  };
  const showH = (h) => Object.keys(h).sort().map((a) => 'h(' + a + ') = ' + R.w(h[a])).join(', ');
  const AB_STAR = 'start p\naccept q\np -a-> p\np -b-> q';
  const HAS_00 = 'start z\naccept zz\nz -1-> z\nz -0-> o\no -1-> z\no -0-> zz\nzz -0,1-> zz';
  const EVEN_LEN = 'start e\naccept e\ne -0,1-> o\no -0,1-> e';
  T.topic({
    id: 'closure-hom', family: 'closure', order: 40, title: 'Homomorphisms and their inverses',
    blurb: 'A homomorphism replaces each symbol by a string: each arrow becomes a little chain spelling that string. Its inverse asks where h(a) leads, and draws one arrow there.',
    inputs: [
      { id: 'mode', kind: 'choice', label: 'Construction', def: 'hom', options: [{ value: 'hom', label: 'h(L): replace symbols' }, { value: 'inv', label: 'h⁻¹(L): pull back' }] },
      R.machineInput({ id: 'm', label: 'Machine for L', def: AB_STAR, kind: 'nfa', max: 4, eps: false }),
      { id: 'h', kind: 'text', label: 'Mapping h', def: 'a = 01, b = 1', check: (v, inp) => {
        let h; try { h = parseH(v); } catch (e) { return e.message; }
        const al = T.Machine.alphabet(T.Machine.parse(inp.m));
        if (!Object.keys(h).length) return 'Mapping: give at least one symbol, like a = 01';
        if (Object.values(h).some((s) => [...s].length > 3)) return 'Mapping: each image at most 3 symbols long, so the picture stays readable';
        if (inp.mode === 'hom') { const miss = al.find((a) => h[a] === undefined); if (miss) return 'Mapping: say what h(' + miss + ') is'; }
        else { if (Object.keys(h).length > 3) return 'Mapping: at most 3 source symbols'; const bad = Object.values(h).join('').split('').find((c) => !al.includes(c)); if (bad) return 'Mapping: "' + bad + '" is not a symbol of the machine, which reads {' + al.join(', ') + '}'; }
        return null;
      } },
    ],
    presets: [
      { label: 'h(a*b) with h(a) = 01, h(b) = 1', values: { mode: 'hom', m: AB_STAR, h: 'a = 01, b = 1' } },
      { label: 'An image that is ε: h(b) = ε', values: { mode: 'hom', m: AB_STAR, h: 'a = 10, b = ε' } },
      { label: 'h⁻¹(contains 00) with h(a) = 0, h(b) = 10', values: { mode: 'inv', m: HAS_00, h: 'a = 0, b = 10' } },
      { label: 'h⁻¹(even length) with h(a) = 01, h(b) = 1', values: { mode: 'inv', m: EVEN_LEN, h: 'a = 01, b = 1' } },
      { label: 'h⁻¹ when h(c) = ε: loops everywhere', values: { mode: 'inv', m: HAS_00, h: 'a = 0, c = ε' } },
    ],
    counters: [{ id: 'edges', label: 'arrows rebuilt' }, { id: 'states', label: 'states' }],
    run(inp) {
      const fa = R.fa(inp.m), h = parseH(inp.h);
      const F = new T.Frames(['edges', 'states']);
      const d0 = R.dia(fa);
      if (inp.mode === 'hom') {
        const res = FA.homomorphism(fa, h);
        const pos0 = K.graph.layout(d0, { gapX: 230, gapY: 150 }).pos;
        const pos = K.graph.layout(R.dia(res.fa), { fixed: pos0, gapX: 230 }).pos;
        let cur = fa.trans.slice(), states = fa.states.slice();
        const draw = (o) => K.graph.draw(R.dia(FA.make({ states, start: fa.start, accept: fa.accept, trans: cur })), Object.assign({ pos }, o || {})).items;
        F.set('states', states.length);
        F.add({ items: draw(), say: 'L is accepted by this machine over {' + fa.alphabet.join(', ') + '}. Apply ' + showH(h) + ': every arrow must read the image of its symbol instead.', hl: { h: ['0'] } });
        res.trace.forEach((s, k) => {
          const e = s.edge;
          cur = cur.filter((x) => !(x.from === e.from && x.sym === e.sym && x.to === e.to));
          const img = [...h[e.sym]];
          const chain = [e.from].concat(s.chain, [e.to]);
          states = states.concat(s.chain);
          const add = img.length ? img.map((c, i) => ({ from: chain[i], sym: c, to: chain[i + 1] })) : [{ from: e.from, sym: '', to: e.to }];
          cur = cur.concat(add);
          F.count('edges').set('states', states.length);
          F.add({ items: draw({ taken: add.map((x) => x.from + '>' + x.to), hot: s.chain, from: Object.fromEntries(s.chain.map((q) => [q, 'g:s:' + e.from])) }), say: s.say, meta: { k, step: e } });
        });
        const ws = FA.enumerate(fa, { max: 8, maxLen: 4 });
        const w = ws.find((x) => x.length >= 2) || ws.find((x) => x.length) || ws[0];
        if (w !== undefined) {
          const hw = [...w].map((c) => h[c]).join('');
          const path = FA.paths(res.fa, hw, 1).paths[0] || [];
          const g = R.bounds(draw());
          const syms = [...hw];
          let at = 0;
          const brackets = [...w].map((c, i) => { const b = { id: 'b' + i, from: at, to: at + [...h[c]].length, text: c, cls: i % 2 ? 'z' : 'x' }; at = b.to; return b; }).filter((b) => b.to > b.from);
          const cw = 46, sx = g.x + g.w / 2 - Math.max(1, syms.length) * cw / 2;
          F.add({ items: draw({ taken: path.map((x) => x.from + '>' + x.to) }).concat(K.string.draw({ text: syms, x: sx, y: g.y + g.h + 50, cw, label: 'h(' + R.w(w) + ')', brackets, head: false }).items), say: R.w(w) + ' is in L, so h(' + R.w(w) + ') = ' + R.w(hw) + ' must be in h(L): its path (lit) follows the chains, one bracket per original symbol.', mark: 'done' });
        }
        return { frames: F.list, def: { sections: [{ id: 'h', kind: 'math', title: 'The homomorphism', text: showH(h).split(', ').join('\n') }, R.tuple(res.fa, 'The machine for h(L)'), R.delta(res.fa).section] } };
      }
      // inverse: same states, one arrow per state and source symbol, to wherever h(a) leads
      const src = Object.keys(h).sort();
      const res = FA.inverseHomomorphism(fa, h, src);
      const posL = K.graph.layout(d0).pos;
      const bl = R.bounds(K.graph.draw(d0, { pos: posL }).items);
      const posR = movePos(posL, bl.w + 170, 0);
      const left = (taken) => K.graph.draw(d0, { prefix: 'gl', pos: posL, taken }).items;
      const rtrans = [];
      const right = (o) => K.graph.draw(R.dia(FA.make({ states: fa.states, alphabet: src, start: fa.start, accept: fa.accept, trans: rtrans.slice() })), Object.assign({ pos: posR }, o || {})).items;
      const fullR = R.bounds(K.graph.draw(R.dia(res.fa), { pos: posR }).items);
      const capY = Math.min(bl.y, fullR.y) - 18;
      const caps = (rb) => [R.caption('cap:l', bl.x, capY, 'L over {' + fa.alphabet.join(', ') + '}', 'title', 'start'), R.caption('cap:r', bl.x + bl.w + 170, capY, 'h⁻¹(L) over {' + src.join(', ') + '}', 'title', 'start')];
      void caps;
      const capItems = caps();
      F.set('states', fa.states.length);
      F.add({ items: left([]).concat(right(), capItems), say: 'h⁻¹(L) holds the strings w over {' + src.join(', ') + '} with h(w) in L. Keep the same states; from each state q and symbol a, follow h(a) in the old machine and draw one arrow q -a-> to where it ends. Here ' + showH(h) + '.', hl: { h: ['0'] } });
      // light the old arrows used while reading h(a) from q
      const used = (q, word) => { let cur = [q]; const keys = []; for (const c of word) { const nx = []; for (const p of cur) for (const e of fa.trans) if (e.from === p && e.sym === c) { keys.push(p + '>' + e.to); if (!nx.includes(e.to)) nx.push(e.to); } cur = nx; } return keys; };
      fa.states.forEach((q, k) => {
        const steps = res.trace.filter((s) => s.kind === 'edge' && s.from === q);
        for (const s of steps) for (const r of s.to) rtrans.push({ from: q, sym: s.sym, to: r });
        F.count('edges', steps.reduce((n, s) => n + s.to.length, 0));
        F.add({ items: left([].concat(...steps.map((s) => used(q, s.word)))).concat(right({ hot: [q], taken: [].concat(...steps.map((s) => s.to.map((r) => q + '>' + r))) }), capItems), say: steps.map((s) => s.say).join(' '), meta: { k, q, steps: steps.map((s) => ({ sym: s.sym, to: s.to })) } });
      });
      const ws = FA.enumerate(res.fa, { max: 10, maxLen: 4 });
      const w = ws.find((x) => x.length >= 2) || ws[0];
      F.add({ items: left(w === undefined ? [] : (FA.paths(fa, [...w].map((c) => h[c]).join(''), 1).paths[0] || []).map((e) => e.from + '>' + e.to)).concat(right({ taken: w === undefined ? [] : (FA.paths(res.fa, w, 1).paths[0] || []).map((e) => e.from + '>' + e.to) }), capItems), say: w === undefined ? 'No string over {' + src.join(', ') + '} maps into L: h⁻¹(L) is empty.' : 'For example ' + R.w(w) + ' is accepted on the right because h(' + R.w(w) + ') = ' + R.w([...w].map((c) => h[c]).join('')) + ' is accepted on the left: both paths are lit.', mark: 'done' });
      return { frames: F.list, def: { sections: [{ id: 'h', kind: 'math', title: 'The homomorphism', text: showH(h).split(', ').join('\n') }, R.tuple(res.fa, 'The machine for h⁻¹(L)'), R.delta(res.fa).section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 0 && fr[i + 1].meta.q !== undefined && fr[i + 1].meta.steps.length && fr[i + 1].meta.steps[0].to.length === 1, once: true, pick: 'item', ask: (fr, i) => 'From ' + fr[i + 1].meta.q + ', where does h(' + fr[i + 1].meta.steps[0].sym + ') lead in the old machine? Click that state on the right.', answer: (fr, i) => 'g:s:' + fr[i + 1].meta.steps[0].to[0], explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 0 && fr[i + 1].meta.step, once: true, pick: 'option', options: (fr) => { const s = fr.find((x) => x.meta && x.meta.step); return R.numberOptions(0, [1, 2]); }, ask: 'How many new states does the first arrow\'s chain need? (A chain spelling a string of length n has n − 1 states inside.)', answer: (fr, i) => String(fr[i + 1].items.filter((x) => x.kind === 'state').length - fr[i].items.filter((x) => x.kind === 'state').length), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'h(a) = 01. The arrow p -a-> q becomes…', options: ['p -0-> q and p -1-> q', 'p -0-> x -1-> q through a new state x', 'p -01-> q', 'an ε-move'], answer: 1, why: 'An arrow reads one symbol, so reading 01 takes a chain of two arrows through a new middle state.' },
      { q: 'h(b) = ε. What does p -b-> q become?', options: ['Nothing: it is deleted', 'An ε-move p → q', 'A loop on p', 'A dead state'], answer: 1, why: 'Reading b now reads nothing, which is exactly an ε-move.' },
      { q: 'In the machine for h⁻¹(L), how are the states related to the machine for L?', options: ['They are the same states', 'Pairs of states', 'Subsets of states', 'One extra start'], answer: 0, why: 'Only the arrows change: q -a-> r when reading h(a) from q can end in r.' },
      { q: 'h(c) = ε in an inverse homomorphism. Which arrows on c appear?', options: ['None', 'A loop c on every state', 'Arrows to the start', 'Arrows to the accepting states'], answer: 1, why: 'Reading h(c) = ε from q stays at q, so every state gets a loop on c.' },
      { q: 'Why are regular languages closed under homomorphism?', options: ['Because the machine for h(L) is built by replacing each arrow by a chain', 'Because h is invertible', 'Because DFAs are closed under subsets', 'They are not'], answer: 0, why: 'The construction gives a finite automaton for h(L) directly.' },
    ],
  });

  // ---- quotient -----------------------------------------------------------------------------------------------------
  const ABAB = 'start p\naccept p\np -a-> q\nq -b-> p';
  const ONE_B = 'start s\naccept t\ns -b-> t';
  const ENDS_ABB = 'start e\naccept abb\ne -a-> a\ne -b-> e\na -a-> a\na -b-> ab\nab -a-> a\nab -b-> abb\nabb -a-> a\nabb -b-> e';
  const B_STAR = 'start s\naccept s\ns -b-> s';
  const EMPTY_M = 'start s\ns -a-> s';
  const EPS_M = 'start s\naccept s\ns -a-> t';
  T.topic({
    id: 'closure-quotient', family: 'closure', order: 50, title: 'The right quotient L / M',
    blurb: 'L / M is the strings x that can be finished by some y in M to give a word of L. Keep L\'s machine; a state accepts when some word of M leads from it to acceptance.',
    inputs: [
      R.machineInput({ id: 'a', label: 'DFA for L', def: ABAB, kind: 'dfa', max: 5 }),
      R.machineInput({ id: 'b', label: 'Machine for M', def: ONE_B, kind: 'nfa', max: 4 }),
    ],
    presets: [
      { label: '(ab)* / b = (ab)*a', values: { a: ABAB, b: ONE_B } },
      { label: 'Ends in abb / b*: cut off any b\'s', values: { a: ENDS_ABB, b: B_STAR } },
      { label: 'M = {ε}: nothing changes', values: { a: ENDS_ABB, b: EPS_M } },
      { label: 'M = ∅: the quotient is empty', values: { a: ABAB, b: EMPTY_M } },
    ],
    counters: [{ id: 'tested', label: 'states tested' }, { id: 'acc', label: 'new accepting' }],
    run(inp) {
      const A = R.fa(inp.a), B = R.fa(inp.b);
      const res = FA.quotient(A, B);
      const da = R.dia(A), db = R.dia(B);
      const pa = K.graph.layout(da).pos;
      const ba = R.bounds(K.graph.draw(da, { pos: pa }).items);
      const lb = K.graph.layout(db).pos, bb0 = R.bounds(K.graph.draw(db, { pos: lb }).items);
      const pb = movePos(lb, ba.x + ba.w + 120 - bb0.x, ba.y + ba.h / 2 - bb0.h / 2 - bb0.y);
      const gB = K.graph.draw(db, { prefix: 'gm', pos: pb }).items;
      const bb = R.bounds(gB);
      const side = gB.concat(frameBox('rgM', bb, 'r2', 'M', 16));
      const del = FA._deltaMap(A);
      const walk = (q, y) => { const keys = []; let p = q; for (const c of y) { const r = del.get(p) && del.get(p).get(c); if (r === undefined) break; keys.push(p + '>' + r); p = r; } return { keys, end: p }; };
      const F = new T.Frames(['tested', 'acc']);
      const newAcc = [];
      const draw = (o, acc) => K.graph.draw(Object.assign({}, da, { accept: acc || A.accept }), Object.assign({ pos: pa }, o || {})).items.concat(side);
      const exM = sample(B, 3);
      F.add({ items: draw(), say: 'L is accepted by the machine on the left, M by the one in the box (' + (exM.length ? 'it accepts ' + exM.join(', ') + (exM.length >= 3 ? ', …' : '') : 'it accepts nothing') + '). x is in L / M when x·y is in L for some y in M. A run on x stops in some state q, so ask of every state: can a word of M lead from q to acceptance?' });
      const gm = R.bounds(draw());
      const capY = gm.y + gm.h + 36;
      res.trace.forEach((s, k) => {
        F.count('tested');
        if (s.accepting) { newAcc.push(s.state); F.count('acc'); }
        const wk = s.accepting ? walk(s.state, s.witness) : { keys: [], end: null };
        const pathM = s.accepting ? (FA.paths(B, s.witness, 1).paths[0] || []).map((e) => 'gm:e:' + e.from + '>' + e.to) : [];
        const items = draw({ hot: [s.state], taken: wk.keys, good: newAcc.filter((q) => q !== s.state).concat(s.accepting && wk.end ? [wk.end] : []), bad: s.accepting ? [] : [s.state] }).map((it) => (pathM.includes(it.key) ? Object.assign({}, it, { cls: (it.cls || '') + ' taken' }) : it));
        items.push(R.caption('verdict', gm.x + gm.w / 2, capY, s.accepting ? 'from ' + s.state + ': y = ' + R.w(s.witness) + ' is in M and reaches acceptance' : 'from ' + s.state + ': no word of M reaches acceptance', s.accepting ? 'good' : 'bad'));
        F.add({ items, say: s.say, meta: { k, state: s.state, yes: s.accepting } });
      });
      F.add({ items: draw({ good: newAcc }, newAcc), say: 'Same states and moves, new accepting states ' + R.set(newAcc) + '. ' + (newAcc.length ? 'For example ' + R.w(FA.enumerate(res.fa, { max: 1, maxLen: 6 })[0]) + ' is in L / M.' : 'No state qualifies, so L / M is empty.'), hl: { tuple: ['3'] }, mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(res.fa, 'The machine for L / M'), { id: 'rule', kind: 'math', title: 'The rule', text: 'q accepts when L(from q) ∩ M ≠ ∅\n(an emptiness test on a product)' }, R.delta(res.fa).section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 1, once: true, pick: 'option', options: ['Yes', 'No'], ask: (fr, i) => 'Will ' + fr[i + 1].meta.state + ' accept in L / M: does some word of M lead from it to acceptance?', answer: (fr, i) => (fr[i + 1].meta.yes ? 'Yes' : 'No'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'L = {abc} and M = {c}. What is L / M?', options: ['{ab}', '{c}', '{abc}', '∅'], answer: 0, why: 'ab·c = abc is in L, and nothing else can be finished by c.' },
      { q: 'Which part of L\'s machine changes to accept L / M?', options: ['The moves', 'The start', 'Only the accepting states', 'Everything'], answer: 2, why: 'A run on x ends in the same state as before; only whether that state counts as accepting changes.' },
      { q: 'What is L / {ε}?', options: ['∅', 'L', '{ε}', 'Σ*'], answer: 1, why: 'Finishing with the empty string changes nothing: x is in L / {ε} exactly when x is in L.' },
      { q: 'How does the construction decide whether state q accepts?', options: ['By trying every string', 'By testing whether the language from q meets M, an emptiness test on a product', 'By guessing', 'By minimising'], answer: 1, why: 'q accepts when some y in M leads from q to acceptance, that is, when L(from q) ∩ M is not empty, which is decidable.' },
    ],
  });
})();
