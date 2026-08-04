// From automata back to expressions, and comparing expressions: state elimination ripping states out of a
// generalised NFA whose edges carry expressions, the R table of paths through the first k states filled
// cell by cell from the table before it, and equivalence of two expressions through their minimal DFAs
// run side by side, ending in a counterexample or a proof that every pair agrees.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg, RE = T.RE, FA = T.FA;
  const X = (T.RegX = T.RegX || {});

  T.family({ id: 'regex', part: 'regular', order: 50, title: 'Regular expressions', blurb: 'Union, concatenation and star: expressions as trees, turned into automata (Thompson, positions, derivatives) and back again (state elimination, the R table), simplified and compared.' });
  const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
  const sup = (n) => String(n).split('').map((d) => SUP[d]).join('');

  // ---- state elimination -----------------------------------------------------------------------------------------
  const TWO = 'start p\naccept q\np -a-> q\nq -b-> p\nq -a-> q';
  const CHAIN = 'start x\naccept z\nx -a-> y\ny -b-> z\nz -a-> y\nx -b-> x';
  const EVEN_A = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const TWO_ACC = 'start s\naccept s t\ns -a-> t\nt -b-> s';
  T.topic({
    id: 'regex-eliminate', family: 'regex', order: 60, title: 'State elimination: automaton to expression',
    blurb: 'Give the machine one new start and one new end, let edges carry expressions, then rip out the old states one at a time. Every path through a removed state becomes an expression on a bypass edge.',
    inputs: [
      R.machineInput({ id: 'm', label: 'Machine', def: TWO, kind: 'any', max: 5 }),
      { id: 'order', kind: 'list', label: 'Order of removal (empty: fewest paths first)', def: [], max: 5, check: (v, inp) => { const st = T.Machine.parse(inp.m).states; const bad = v.find((q) => !st.includes(q)); return bad !== undefined ? 'Order: ' + bad + ' is not a state of the machine' : null; } },
    ],
    presets: [
      { label: 'Two states', values: { m: TWO, order: [] } },
      { label: 'Same machine, other order: q first', values: { m: TWO, order: ['q', 'p'] } },
      { label: 'A loop through two states', values: { m: CHAIN, order: [] } },
      { label: 'Even number of a\'s', values: { m: EVEN_A, order: [] } },
      { label: 'Two accepting states: ε-edges to F', values: { m: TWO_ACC, order: [] } },
    ],
    counters: [{ id: 'left', label: 'old states left' }, { id: 'edges', label: 'edges' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const res = RE.fromFA(fa, inp.order && inp.order.length ? { order: inp.order } : {});
      const tr = res.trace, g0 = tr[0];
      const S = g0.start, Fn = g0.final;
      const d = R.dia(fa);
      const pos0 = K.graph.layout(d, { gapX: 190, gapY: 150 }).pos;
      const xs = fa.states.map((q) => pos0[q].x), ys = fa.states.map((q) => pos0[q].y);
      const pos = Object.assign({}, pos0);
      pos[S] = { x: Math.min(...xs) - 170, y: pos0[fa.start].y };
      const accY = fa.accept.length ? fa.accept.reduce((a, q) => a + pos0[q].y, 0) / fa.accept.length : (Math.min(...ys) + Math.max(...ys)) / 2;
      pos[Fn] = { x: Math.max(...xs) + 170, y: accY };
      // a generalised NFA: one edge per pair of states, labelled with an expression
      const gn = (states, edges, o) => {
        o = o || {};
        const m = { kind: 'gnfa', states, start: S, accept: [Fn], trans: edges.map((e) => ({ from: e.from, to: e.to, label: e.regex })) };
        return X.edgeX(K.graph.draw(m, Object.assign({ pos }, o)).items);
      };
      const F = new T.Frames(['left', 'edges']);
      let left = fa.states.slice();
      F.set('left', left.length).set('edges', fa.trans.length);
      F.add({ items: K.graph.draw(d, { pos }).items, say: 'The machine to turn into an expression. Its edges carry single symbols; soon they will carry whole expressions.' });
      let edges = g0.edges;
      F.set('edges', edges.length);
      F.add({ items: gn([S].concat(left, [Fn]), edges, { hot: [S, Fn] }), say: g0.say + ' Now the start has no edge in and the end has no edge out.', meta: { first: tr[1] && tr[1].state } });
      const card = (lines, y) => R.note('card', { x: pos[S].x - 30, y, title: 'bypass edges', lines: lines.slice(0, 4).concat(lines.length > 4 ? ['…'] : []), mono: true, size: 15 }).items;
      const below = R.bounds(gn([S].concat(left, [Fn]), edges)).y + R.bounds(gn([S].concat(left, [Fn]), edges)).h + 24;
      const allBelow = Math.max(below, ...tr.filter((s) => s.kind === 'eliminate').map((s, k) => { void k; return below; }));
      const rows = (es) => es.map((e) => [e.from, e.to, e.regex]);
      tr.filter((s) => s.kind === 'eliminate').forEach((s) => {
        const q = s.state;
        const touching = edges.filter((e) => e.from === q || e.to === q).map((e) => e.from + '>' + e.to);
        const lines = s.updates.map((u) => u.from + '→' + u.to + ': ' + (u.old ? u.old + ' | ' : '') + u.through);
        F.add({ items: gn([S].concat(left, [Fn]), edges, { hot: [q], taken: touching }).concat(card(lines.length ? lines : ['no path passes through ' + q], allBelow)), say: 'Rip out ' + q + (s.loop ? ', whose loop ' + s.loop + ' may be taken any number of times: (' + s.loop + ')*' : '') + '. ' + (s.updates.length ? 'Every path p → ' + q + ' → r gets a bypass: R(p, ' + q + ')' + (s.loop ? ' (' + s.loop + ')*' : '') + ' R(' + q + ', r).' : 'No path passes through it, so nothing is lost.'), hl: { edges: edges.map((e, i) => (e.from === q || e.to === q ? String(i) : null)).filter((x) => x !== null) }, meta: { q, nUpd: s.updates.length } });
        left = left.filter((x) => x !== q);
        edges = s.edges;
        F.set('left', left.length).set('edges', edges.length);
        const changed = s.updates.map((u) => u.from + '>' + u.to);
        const fr = { items: gn([S].concat(left, [Fn]), edges, { taken: changed }).concat(card(s.updates.map((u) => u.from + '→' + u.to + ': ' + u.regex), allBelow)), say: (s.updates.length ? s.updates.map((u) => u.from + ' → ' + u.to + ' becomes ' + u.regex).join('; ') : q + ' is gone') + '. The language from ' + S + ' to ' + Fn + ' is the same as before.', hl: { edges: edges.map((e, i) => (changed.includes(e.from + '>' + e.to) ? String(i) : null)).filter((x) => x !== null) } };
        fr.exits = { ['g:s:' + q]: { exit: 'shrink' } };
        F.add(fr);
      });
      const last = tr[tr.length - 1];
      F.add({ items: gn([S, Fn], edges, { good: [S, Fn] }).concat([R.caption('result', (pos[S].x + pos[Fn].x) / 2, allBelow + 30, 'L = ' + last.regex, 'big good')]), say: last.say + (inp.order && inp.order.length ? ' Another order of removal can give a different, equivalent expression.' : ' States with the fewest paths through them went first, which keeps the expression short.'), mark: 'done' });
      return { frames: F.list, def: { sections: [{ id: 'rule', kind: 'math', title: 'Removing q', text: 'for every p → q → r:\nR(p,r) ← R(p,r) | R(p,q) R(q,q)* R(q,r)\nthen delete q and its edges' }, { id: 'edges', kind: 'table', title: 'Edges at the start', colHead: ['from', 'to', 'expression'], rows: rows(g0.edges) }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.first, once: true, pick: 'item', ask: (fr, i) => 'Which old state will be ripped out first? Click it.', answer: (fr, i) => 'g:s:' + fr[i].meta.first, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.q && f.meta.nUpd > 0, once: true, pick: 'option', options: (fr, i) => R.numberOptions(fr[i].meta.nUpd), ask: (fr, i) => 'How many bypass edges does removing ' + fr[i].meta.q + ' create or rewrite?', answer: (fr, i) => String(fr[i].meta.nUpd), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why add a new start S and a new end F first?', options: ['To make the machine deterministic', 'So that, at the end, a single edge S → F carries the whole answer', 'To remove ε-moves', 'To make it minimal'], answer: 1, why: 'With one start with no edges in and one end with no edges out, eliminating every old state leaves exactly S → F.' },
      { q: 'Removing q, with p → q labelled x, a loop y on q and q → r labelled z, adds what to R(p, r)?', options: ['xyz', 'x y* z', 'x | y | z', '(xyz)*'], answer: 1, why: 'A path enters q by x, loops any number of times by y, and leaves by z.' },
      { q: 'Does the order of removal change the language of the final expression?', options: ['Yes', 'No, only how the expression looks', 'Only if the machine is an NFA', 'Only for loops'], answer: 1, why: 'Each step keeps the language from S to F; different orders give different but equivalent expressions.' },
      { q: 'With no accepting state, what does S → F end up as?', options: ['ε', '∅', 'Σ*', 'There is no edge'], answer: 1, why: 'Nothing leads to F, and a missing edge stands for ∅.' },
    ],
  });

  // ---- the R table -----------------------------------------------------------------------------------------------
  // break a long expression into lines at its top-level unions
  const wrap = (s, n) => {
    if (s.length <= n) return s;
    const parts = [];
    let depth = 0, cur = '';
    for (const c of s) { if (c === '(') depth++; if (c === ')') depth--; if (c === '|' && depth === 0) { parts.push(cur); cur = ''; } else cur += c; }
    parts.push(cur);
    const lines = [];
    for (const p of parts) { if (lines.length && (lines[lines.length - 1] + '|' + p).length <= n) lines[lines.length - 1] += '|' + p; else lines.push((lines.length ? '|' : '') + p); }
    return lines.join('\n');
  };
  const KL2 = 'start p\naccept q\np -a-> q\nq -b-> p\nq -a-> q';
  const KL_LINE = 'start 1\naccept 3\n1 -a-> 2\n2 -b-> 3';
  const KL_LOOP = 'start x\naccept x\nx -a-> y\ny -b-> x';
  const KL_EVEN = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  T.topic({
    id: 'regex-kleene', family: 'regex', order: 70, title: 'The R table: paths through the first k states',
    blurb: 'R(i, j) with k on top is every word leading from i to j that passes only through the first k states on the way. Each new table comes from the one before: go round state k as often as you like.',
    inputs: [R.machineInput({ id: 'm', label: 'Machine', def: KL2, kind: 'any', max: 3 })],
    presets: [
      { label: 'Two states', values: { m: KL2 } },
      { label: 'A straight line: 1 → 2 → 3', values: { m: KL_LINE } },
      { label: 'A loop: x → y → x', values: { m: KL_LOOP } },
      { label: 'Even number of a\'s', values: { m: KL_EVEN } },
    ],
    check: (inp) => (T.Machine.parse(inp.m).states.length > 3 ? 'Machine: at most 3 states, so the table fits' : null),
    counters: [{ id: 'k', label: 'k' }, { id: 'cells', label: 'cells computed' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const kl = RE.kleene(fa);
      const Q = fa.states, n = Q.length;
      const tabs = kl.trace.filter((s) => s.kind === 'table');
      const F = new T.Frames(['k', 'cells']);
      const W = 22;
      const tbl = (cells, o) => K.table.draw({ rows: cells.map((r) => r.map((c) => (c === null ? '' : wrap(c, W)))), rowHead: Q, colHead: Q, corner: 'from \\ to', x: 0, y: o.y, mono: true, size: 14, prefix: o.prefix, title: o.title, hot: o.hot || [], act: o.act || [], cls: o.cls, minW: 70 });
      const t0 = tbl(tabs[0].cells, { y: 0, prefix: 'old', title: 'R' + sup(0) });
      const gapY = t0.box.h + 70;
      F.add({ items: tbl(tabs[0].cells, { y: 0, prefix: 'old', title: 'R' + sup(0) + ': no state in between' }).items, say: 'k = 0: R' + sup(0) + '(i, j) is the union of the symbols on edges from i to j, with ε added on the diagonal (staying put). No path may pass through any state yet.', hl: { f: ['0'] } });
      for (let k = 1; k <= n; k++) {
        const prev = tabs[k - 1].cells, next = tabs[k].cells, via = Q[k - 1], kk = k - 1;
        const cur = Q.map(() => Q.map(() => null));
        const pivot = [];
        for (let i = 0; i < n; i++) { pivot.push([i, kk]); pivot.push([kk, i]); }
        F.set('k', k);
        const scene = (o) => tbl(prev, { y: 0, prefix: 'old', title: 'R' + sup(k - 1) + ': through ' + (k - 1 ? R.set(Q.slice(0, k - 1)) : 'no state'), act: o.act || pivot, hot: o.src || [] }).items.concat(tbl(cur, { y: gapY, prefix: 'new', title: 'R' + sup(k) + ': through ' + R.set(Q.slice(0, k)), hot: o.hot || [], cls: (r, c) => (cur[r][c] !== null && !(o.hot && o.hot[0] && o.hot[0][0] === r && o.hot[0][1] === c) ? (cur[r][c] === prev[r][c] ? '' : 'good') : '') }).items, o.arrows || []);
        F.add({ items: scene({}), say: 'k = ' + k + ': now paths may also pass through ' + via + '. The row and column of ' + via + ' in the old table (lit) are all that is needed.', hl: { f: ['1'] } });
        for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
          cur[i][j] = next[i][j];
          F.count('cells');
          const srcs = [[i, j], [i, kk], [kk, kk], [kk, j]].filter((p, x, a) => a.findIndex((q) => q[0] === p[0] && q[1] === p[1]) === x);
          const arrows = srcs.map((p, x) => ({ key: 'ar:' + x, kind: 'edge', from: 'old:' + p[0] + ',' + p[1], to: 'new:' + i + ',' + j, cls: 'prov' + (x % 2 ? ' b' : ''), audit: 'ignore', layer: 'top', bend: 30 * (x % 2 ? -1 : 1) * (p[1] > j ? -1 : 1) }));
          const same = next[i][j] === prev[i][j];
          const formula = prev[i][j] + ' | ' + prev[i][kk] + ' (' + prev[kk][kk] + ')* ' + prev[kk][j];
          F.add({ items: scene({ hot: [[i, j]], src: srcs, arrows }), say: 'R' + sup(k) + '(' + Q[i] + ', ' + Q[j] + ') = ' + formula + (same ? ', which adds nothing new: it stays ' + next[i][j] + '.' : ', which simplifies to ' + next[i][j] + '.'), hl: { f: ['1'] }, meta: { cell: [i, j], same, srcKeys: srcs.map((p) => 'old:' + p[0] + ',' + p[1]) } });
        }
      }
      const s = Q.indexOf(fa.start);
      const lastT = tabs[n].cells;
      const accCells = fa.accept.map((f) => [s, Q.indexOf(f)]);
      F.add({ items: tbl(lastT, { y: 0, prefix: 'old', title: 'R' + sup(n) + ': through every state', hot: accCells }).items.concat([R.caption('result', t0.box.w / 2, t0.box.h + 40, 'L = ' + kl.regex, 'big good')]), say: 'With k = ' + n + ' every path is allowed. The language is the union of R' + sup(n) + '(' + fa.start + ', f) over the accepting states f ' + R.set(fa.accept) + ' (lit): ' + kl.regex + '.', mark: 'done', hl: { f: ['2'] } });
      return { frames: F.list, def: { sections: [{ id: 'f', kind: 'math', title: 'The recurrence', text: 'R⁰(i,j) = symbols on i → j (+ ε if i = j)\nRᵏ(i,j) = Rᵏ⁻¹(i,j) | Rᵏ⁻¹(i,k) (Rᵏ⁻¹(k,k))* Rᵏ⁻¹(k,j)\nL = union of Rⁿ(start, f), f accepting' }, R.delta(fa).section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.cell && !fr[i].meta, once: true, pick: 'item', ask: (fr, i) => { const c = fr[i + 1].meta.cell; return 'The next cell is row ' + (c[0] + 1) + ', column ' + (c[1] + 1) + '. Click a cell of the old table it is built from.'; }, answer: (fr, i) => fr[i + 1].meta.srcKeys, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => f.meta && f.meta.cell && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.cell && i > 4, once: true, pick: 'option', options: ['It changes', 'It stays the same'], ask: 'Will the next cell change from the old table, or stay the same?', answer: (fr, i) => (fr[i + 1].meta.same ? 'It stays the same' : 'It changes'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does R⁰(i, i) always contain?', options: ['∅', 'ε', 'Every symbol', 'Nothing'], answer: 1, why: 'Staying at i reads the empty string, which needs no intermediate state.' },
      { q: 'R¹(i, j) may pass through which states in between?', options: ['None', 'Only the first state', 'Any state', 'Only i and j'], answer: 1, why: 'The superscript counts how many of the states (in their order) may be visited between the ends.' },
      { q: 'For a machine with n states, how many tables are computed?', options: ['n', 'n + 1', '2ⁿ', 'n²'], answer: 1, why: 'Tables for k = 0, 1, …, n.' },
      { q: 'Why does the recurrence star R(k, k)?', options: ['To allow ε', 'A path may go round state k any number of times before going on', 'To make the expression regular', 'It does not'], answer: 1, why: 'Between arriving at k and finally leaving it, a path can loop back to k again and again.' },
    ],
  });

  // ---- equivalence ------------------------------------------------------------------------------------------------
  T.topic({
    id: 'regex-equiv', family: 'regex', order: 90, title: 'Are two expressions equal?',
    blurb: 'Build the minimal DFA of each and run them side by side on every reachable pair of states. A pair where one accepts and the other does not gives a counterexample; if none exists, the languages are equal.',
    inputs: [X.input('r', 'First expression', '(a|b)*b', 10), X.input('s', 'Second expression', 'a*b(a|b)*', 10)],
    presets: [
      { label: 'Ends with b vs contains b: a counterexample', values: { r: '(a|b)*b', s: 'a*b(a|b)*' } },
      { label: '(a|b)* vs (a*b*)*: equal', values: { r: '(a|b)*', s: '(a*b*)*' } },
      { label: '(ab)*a vs a(ba)*: equal', values: { r: '(ab)*a', s: 'a(ba)*' } },
      { label: 'Almost: a*b* vs (ab)*', values: { r: 'a*b*', s: '(ab)*' } },
      { label: 'ε matters: a* vs a+', values: { r: 'a*', s: 'a+' } },
    ],
    counters: [{ id: 'pairs', label: 'pairs visited' }],
    run(inp) {
      const ar = RE.parse(inp.r), as = RE.parse(inp.s);
      const sigma = [...new Set(RE.alphabet(ar).concat(RE.alphabet(as)))].sort();
      if (!sigma.length) sigma.push('a');
      const A = FA.canonical(RE.minimalDFA(ar, { alphabet: sigma }).fa, 'p');
      const B = FA.canonical(RE.minimalDFA(as, { alphabet: sigma }).fa, 'q');
      const dA = R.dia(A), dB = R.dia(B);
      const pA = K.graph.layout(dA).pos, gA = K.graph.draw(dA, { pos: pA, prefix: 'A' });
      const bA = R.bounds(gA.items);
      const pB0 = K.graph.layout(dB).pos, gB0 = K.graph.draw(dB, { pos: pB0, prefix: 'B' });
      const bB = R.bounds(gB0.items);
      const dx = bA.x + bA.w + 110 - bB.x;
      const pB = {};
      for (const q of B.states) pB[q] = { x: pB0[q].x + dx, y: pB0[q].y + (bA.y + bA.h / 2) - (bB.y + bB.h / 2) };
      const eq = FA.equivalent(A, B);
      const visits = eq.trace.filter((s) => s.kind === 'visit');
      const width = bA.w + 110 + bB.w;
      const cx = bA.x + width / 2;
      const bB2 = R.bounds(K.graph.draw(dB, { pos: pB, prefix: 'B' }).items);
      const yLow = Math.max(bA.y + bA.h, bB2.y + bB2.h) + 40;
      const capY = Math.min(bA.y, bB2.y) - 26;
      const caps = [R.caption('capA', bA.x + bA.w / 2, capY, 'r = ' + RE.show(ar), 'mono'), R.caption('capB', bB2.x + bB2.w / 2, capY, 's = ' + RE.show(as), 'mono')];
      const machines = (aOpts, bOpts) => K.graph.draw(dA, Object.assign({ pos: pA, prefix: 'A' }, aOpts || {})).items.concat(K.graph.draw(dB, Object.assign({ pos: pB, prefix: 'B' }, bOpts || {})).items, caps);
      const pairCells = (k, bad) => {
        const out = [];
        const cw = 74, per = Math.max(1, Math.min(visits.length, Math.floor(width / (cw + 6))));
        visits.slice(0, k).forEach((v, i) => {
          const r = Math.floor(i / per), c = i % per, nRow = Math.min(per, visits.length - r * per);
          const accA = A.accept.includes(v.pair[0]), accB = B.accept.includes(v.pair[1]);
          out.push({ key: 'pair:' + i, kind: 'cell', x: cx - (nRow * (cw + 6) - 6) / 2 + c * (cw + 6), y: yLow + 26 + r * 42, w: cw, h: 34, text: v.pair[0] + ',' + v.pair[1], cls: 'mono ' + (bad && i === k - 1 ? 'bad' : i === k - 1 ? 'hot' : accA ? 'good' : ''), size: 14 });
        });
        if (k) out.push({ key: 'pair:label', kind: 'text', x: cx, y: yLow + 12, text: 'pairs (state of r, state of s) reached together', anchor: 'middle', cls: 'title' });
        return out;
      };
      const F = new T.Frames(['pairs']);
      F.add({ items: machines(), say: 'Left: the minimal DFA of r = ' + RE.show(ar) + '. Right: the minimal DFA of s = ' + RE.show(as) + '. Do they accept the same strings?', meta: { equal: eq.equal } });
      visits.forEach((v, i) => {
        F.count('pairs');
        const accA = A.accept.includes(v.pair[0]), accB = B.accept.includes(v.pair[1]);
        const bad = accA !== accB;
        F.add({ items: machines({ active: [v.pair[0]] }, { active: [v.pair[1]] }).concat(pairCells(i + 1, bad)), say: 'Some string leads r\'s machine to ' + v.pair[0] + ' and s\'s machine to ' + v.pair[1] + ': ' + (bad ? 'one accepts and the other does not!' : accA ? 'both accept.' : 'neither accepts.') });
      });
      if (eq.equal) {
        const iso = FA.isomorphic(A, B);
        F.add({ items: machines({ good: A.accept }, { good: B.accept }).concat(pairCells(visits.length)), say: 'Every reachable pair agrees, so no string can tell the expressions apart: they are equal. ' + (iso.iso ? 'Indeed the two minimal DFAs are the same machine with the states renamed (' + Object.entries(iso.map).map(([a, b]) => a + ' ↔ ' + b).join(', ') + ').' : ''), mark: 'equal' });
      } else {
        const w = [...eq.counterexample];
        const runA = R.runDFA(A, eq.counterexample), runB = R.runDFA(B, eq.counterexample);
        const sx = cx - (Math.max(1, w.length) * 46) / 2;
        const sy = yLow + 26 + (Math.ceil(visits.length / Math.max(1, Math.floor(width / 80))) * 42) + 40;
        const str = (i) => K.string.draw({ text: w, pos: i, x: sx, y: sy, cw: 46, label: 'counterexample', headText: i >= w.length ? 'end' : 'next' }).items;
        F.add({ items: machines({ active: [A.start] }, { active: [B.start] }).concat(pairCells(visits.length, true), str(0)), say: 'The shortest string reaching that pair is ' + R.w(eq.counterexample) + '. Run it on both machines.', meta: { endB: runB.end } });
        for (let i = 0; i < w.length; i++) F.add({ items: machines({ active: [runA.path[i + 1]], taken: [runA.path[i] + '>' + runA.path[i + 1]] }, { active: [runB.path[i + 1]], taken: [runB.path[i] + '>' + runB.path[i + 1]] }).concat(pairCells(visits.length, true), str(i + 1)), say: 'Read ' + w[i] + ': r\'s machine goes to ' + runA.path[i + 1] + ', s\'s machine to ' + runB.path[i + 1] + '.' });
        const inR = runA.accept;
        F.add({ items: machines(inR ? { good: [runA.end] } : { bad: [runA.end] }, inR ? { bad: [runB.end] } : { good: [runB.end] }).concat(pairCells(visits.length, true), str(w.length)), say: R.w(eq.counterexample) + ' is matched by ' + (inR ? 'r' : 's') + ' but not by ' + (inR ? 's' : 'r') + ', so the expressions are not equal.', mark: 'different' });
      }
      return { frames: F.list, def: { sections: [R.tuple(A, 'r\'s minimal DFA', 'ta'), R.tuple(B, 's\'s minimal DFA', 'tb'), { id: 'how', kind: 'text', title: 'Why this works', text: 'Run both machines together breadth first. Every string leads to one pair of states; the strings agree exactly when every reachable pair agrees on accepting. The first disagreeing pair found gives a shortest counterexample.' }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['Equal', 'Not equal'], ask: 'Do r and s describe the same language?', answer: (fr) => (fr[0].meta.equal ? 'Equal' : 'Not equal'), explain: (fr) => fr[fr.length - 1].say },
      { at: (f) => f.meta && f.meta.endB, once: true, pick: 'item', ask: 'In which state of s\'s machine will the counterexample end? Click it.', answer: (fr, i) => 'B:s:' + fr[i].meta.endB, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Is equivalence of regular expressions decidable?', options: ['Yes', 'No', 'Only without star', 'Only for one symbol'], answer: 0, why: 'Turn both into DFAs and search the reachable pairs: finitely many.' },
      { q: 'Two expressions are equal. What can be said of their minimal DFAs?', options: ['Nothing', 'They are the same machine up to renaming states', 'They have the same number of edges only', 'One is bigger'], answer: 1, why: 'Each regular language has one minimal DFA, up to the names of its states.' },
      { q: 'Why do a* and a+ differ?', options: ['They do not', 'a* matches ε and a+ does not', 'a+ matches more', 'Different alphabets'], answer: 1, why: 'The empty string is the counterexample: zero copies are allowed only by star.' },
      { q: 'How many strings must the pair search look at?', options: ['All strings, for ever', 'At most one per reachable pair of states', 'Exactly 2ⁿ', 'Only the strings of the first expression'], answer: 1, why: 'It visits each reachable pair once, by a shortest string, so it stops after at most |A| × |B| pairs.' },
    ],
  });
})();
