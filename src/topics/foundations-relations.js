// Relations and functions: a relation drawn as a graph and as a matrix, with each property (reflexive,
// symmetric, antisymmetric, transitive) checked by lighting the arrows that make it or break it; and
// functions as arrows between two columns, tested for one-to-one and onto with the counterexample lit.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found;

  T.family({ id: 'found-relations', part: 'foundations', order: 20, title: 'Relations and functions', blurb: 'A relation is a set of ordered pairs: arrows in a graph, ones in a matrix. Its properties are about which arrows must be there, and a function is a relation with exactly one arrow out of every element.' });

  const H = K.rel;
  const yesNo = (b) => (b ? 'Yes' : 'No');

  // ---------------------------------------------------------------------------------------------------
  // Properties of a relation
  // ---------------------------------------------------------------------------------------------------
  const PROPS = [
    { id: 'reflexive', line: 'reflexive:      (x, x) ∈ R for every x in D' },
    { id: 'symmetric', line: 'symmetric:      (x, y) ∈ R ⇒ (y, x) ∈ R' },
    { id: 'antisymmetric', line: 'antisymmetric:  (x, y), (y, x) ∈ R ⇒ x = y' },
    { id: 'transitive', line: 'transitive:     (x, y), (y, z) ∈ R ⇒ (x, z) ∈ R' },
  ];

  T.topic({
    id: 'rel-props', family: 'found-relations', order: 10, title: 'Properties of a relation',
    blurb: 'Draw a relation as arrows and as a matrix, then test it: loops for reflexive, arrows that come back for symmetric, no two-way arrows for antisymmetric, and a shortcut for every two-step path for transitive.',
    inputs: [
      { id: 'D', kind: 'list', label: 'Set D', def: ['1', '2', '3', '4'], min: 1, max: 6, check: (v) => H.checkDomain(v, 'Set D') },
      { id: 'R', kind: 'text', label: 'Pairs of R (x-y)', def: '1-1, 2-2, 3-3, 4-4, 1-2, 2-1, 2-3, 3-2', check: (v, inp) => H.checkPairs(v, inp.D || [], 'Pairs of R') },
    ],
    presets: [
      { label: 'Close neighbours: not transitive', values: { D: ['1', '2', '3', '4'], R: '1-1, 2-2, 3-3, 4-4, 1-2, 2-1, 2-3, 3-2' } },
      { label: 'Same parity: an equivalence', values: { D: ['1', '2', '3', '4'], R: '1-1, 2-2, 3-3, 4-4, 1-3, 3-1, 2-4, 4-2' } },
      { label: 'Divides: a partial order', values: { D: ['1', '2', '3', '6'], R: '1-1, 2-2, 3-3, 6-6, 1-2, 1-3, 1-6, 2-6, 3-6' } },
      { label: 'Next one up: 1→2→3→4', values: { D: ['1', '2', '3', '4'], R: '1-2, 2-3, 3-4' } },
      { label: 'The empty relation', values: { D: ['a', 'b', 'c'], R: '' } },
      { label: 'Only loops: symmetric and antisymmetric', values: { D: ['a', 'b', 'c'], R: 'a-a, c-c' } },
      { label: 'Knows each other: symmetric, not transitive', values: { D: ['p', 'q', 'r', 's'], R: 'p-q, q-p, q-r, r-q, r-s, s-r' } },
    ],
    counters: [{ id: 'pairs', label: 'pairs in R' }, { id: 'checked', label: 'properties checked' }, { id: 'hold', label: 'properties that hold' }],
    run(inp) {
      const D = inp.D, R = H.parsePairs(inp.R);
      const has = (x, y) => R.some((p) => p[0] === x && p[1] === y);
      const narrow = H.narrow();
      const c = K.rel.circle(D);
      const mW = 40 + D.length * 40, mH = 34 + D.length * 38;
      const mx = narrow ? -mW / 2 : c.box.x + c.box.w - 30, my = narrow ? c.box.y + c.box.h - 20 : -mH / 2;
      const F2 = new T.Frames(['pairs', 'checked', 'hold']);
      const scene = (g, m, extra) => K.rel.graph(Object.assign({ D, pos: c.pos }, g)).items.concat(K.rel.matrix(Object.assign({ D, x: mx, y: my }, m)).items, extra || []);
      const defLines = [D.length ? 'D = {' + D.join(', ') + '}' : 'D = ∅'].concat(H.pairLines('R', R), PROPS.map((p) => p.line));
      const propLine = (id) => String(1 + H.pairLines('R', R).length + PROPS.findIndex((p) => p.id === id));
      const shown = [];
      F2.add({ items: scene({ R: [] }, { R: [] }), say: 'The set D = {' + D.join(', ') + '} has ' + D.length + ' element' + (D.length === 1 ? '' : 's') + '. A relation on D is a set of ordered pairs (x, y): each pair is an arrow from x to y, and a 1 in row x, column y of the matrix.', hl: { def: ['0'] } });
      if (!R.length) F2.add({ items: scene({ R: [] }, { R: [] }), say: 'Here R is empty: no arrows at all, and every entry of the matrix is 0. The empty set is a perfectly good relation.', hl: { def: ['1'] } });
      else if (R.length <= 8) {
        for (const [x, y] of R) {
          shown.push([x, y]);
          F2.count('pairs');
          F2.add({ items: scene({ R: shown.slice(), good: [[x, y]] }, { R: shown.slice(), good: [[x, y]] }), say: x === y ? '(' + x + ', ' + x + ') ∈ R: a loop at ' + x + ', and a 1 on the diagonal of the matrix.' : '(' + x + ', ' + y + ') ∈ R: an arrow from ' + x + ' to ' + y + ', and a 1 in row ' + x + ', column ' + y + '.', hl: { def: ['1'] } });
        }
      } else {
        F2.count('pairs', R.length);
        F2.add({ items: scene({ R, good: R }, { R, good: R }), say: 'All ' + R.length + ' pairs of R at once: an arrow for each, and a 1 in the matrix for each.', hl: { def: ['1'] } });
      }
      const verdict = {};
      // -- reflexive
      {
        const diag = D.map((x) => [x, x]);
        const missing = D.filter((x) => !has(x, x));
        F2.add({ items: scene({ R, hot: diag.filter(([x]) => has(x, x)) }, { R, act: diag }), say: 'Reflexive asks for a loop at every element: the whole diagonal of the matrix must be 1.', hl: { def: [propLine('reflexive')] }, meta: { ask: 'reflexive', yes: !missing.length } });
        verdict.reflexive = !missing.length;
        F2.count('checked').count('hold', verdict.reflexive ? 1 : 0);
        F2.add({ items: scene({ R, good: diag.filter(([x]) => has(x, x)), ghost: missing.map((x) => [x, x]) }, { R, good: diag.filter(([x]) => has(x, x)), bad: missing.map((x) => [x, x]) }), say: missing.length ? 'Not reflexive: ' + missing.map((x) => '(' + x + ', ' + x + ')').join(', ') + (missing.length === 1 ? ' is' : ' are') + ' missing. The dashed loop' + (missing.length === 1 ? ' shows' : 's show') + ' what would have to be added.' : 'Reflexive: every element has its loop, so the diagonal is all 1s.', hl: { def: [propLine('reflexive')] } });
      }
      // -- symmetric
      {
        const off = R.filter(([x, y]) => x !== y);
        const bad = off.filter(([x, y]) => !has(y, x));
        F2.add({ items: scene({ R, hot: off }, { R, act: off.map(([x, y]) => [y, x]) }), say: 'Symmetric asks that every arrow comes back: if (x, y) is in R then so is (y, x). In the matrix, each 1 must have a 1 at its mirror image across the diagonal.', hl: { def: [propLine('symmetric')] }, meta: { ask: 'symmetric', yes: !bad.length } });
        verdict.symmetric = !bad.length;
        F2.count('checked').count('hold', verdict.symmetric ? 1 : 0);
        F2.add({ items: scene({ R, bad, good: off.filter((p) => !bad.includes(p)), ghost: bad.map(([x, y]) => [y, x]) }, { R, bad: bad.map(([x, y]) => [y, x]), good: off.filter((p) => !bad.includes(p)) }), say: bad.length ? 'Not symmetric: ' + bad.slice(0, 3).map(([x, y]) => '(' + x + ', ' + y + ') is there but (' + y + ', ' + x + ') is not').join('; ') + '. The dashed arrows are the missing returns.' : off.length ? 'Symmetric: every arrow between two different elements has its partner going back. Loops are their own mirror image.' : 'Symmetric, with nothing to check: there is no arrow between two different elements, so no arrow lacks a partner.', hl: { def: [propLine('symmetric')] } });
      }
      // -- antisymmetric
      {
        const two = R.filter(([x, y]) => x !== y && has(y, x));
        F2.add({ items: scene({ R }, { R }), say: 'Antisymmetric is not the opposite of symmetric: it forbids two different elements pointing at each other. One-way arrows and loops are fine.', hl: { def: [propLine('antisymmetric')] }, meta: { ask: 'antisymmetric', yes: !two.length } });
        verdict.antisymmetric = !two.length;
        F2.count('checked').count('hold', verdict.antisymmetric ? 1 : 0);
        const off = R.filter(([x, y]) => x !== y);
        F2.add({ items: scene({ R, bad: two, good: off.filter((p) => !two.includes(p)) }, { R, bad: two }), say: two.length ? 'Not antisymmetric: ' + two.filter(([x, y]) => x < y).slice(0, 3).map(([x, y]) => x + ' and ' + y + ' point at each other').join('; ') + ', yet ' + (two.length > 2 ? 'they are' : 'the two are') + ' different elements.' : verdict.symmetric && off.length === 0 ? 'Antisymmetric as well: with only loops, nothing points both ways. A relation can be symmetric and antisymmetric at once.' : 'Antisymmetric: no two different elements point at each other.', hl: { def: [propLine('antisymmetric')] } });
      }
      // -- transitive
      {
        const paths = [], broken = [];
        for (const [x, y] of R) for (const [y2, z] of R) if (y2 === y && !(x === y && y === z)) { paths.push([x, y, z]); if (!has(x, z)) broken.push([x, y, z]); }
        verdict.transitive = !broken.length;
        F2.add({ items: scene({ R }, { R }), say: 'Transitive asks for a shortcut: whenever x → y → z, the arrow x → z must be there too (x and z may be the same element, needing a loop).', hl: { def: [propLine('transitive')] }, meta: { ask: 'transitive', yes: !broken.length } });
        if (broken.length) {
          const [x, y, z] = broken[0];
          F2.add({ items: scene({ R, hot: [[x, y], [y, z]] }, { R, hot: [[x, y], [y, z]] }), say: 'Follow ' + x + ' → ' + y + ' → ' + z + '. Is there an arrow straight from ' + x + ' to ' + z + '?', hl: { def: [propLine('transitive')] }, meta: { pickCell: broken.map(([a, , cc]) => K.rel.matrix({ D, x: mx, y: my, R }).cellKey(a, cc)) } });
          const show = broken.slice(0, 3);
          F2.count('checked');
          F2.add({ items: scene({ R, hot: show.flatMap(([a, b, cc]) => [[a, b], [b, cc]]), ghost: show.map(([a, , cc]) => [a, cc]) }, { R, hot: show.flatMap(([a, b, cc]) => [[a, b], [b, cc]]), bad: show.map(([a, , cc]) => [a, cc]) }), say: 'Not transitive: ' + show.map(([a, b, cc]) => a + ' → ' + b + ' → ' + cc + ' has no shortcut ' + a + ' → ' + cc).join('; ') + (broken.length > 3 ? ', and more' : '') + '. The dashed arrow' + (show.length === 1 ? ' is' : 's are') + ' missing.', hl: { def: [propLine('transitive')] } });
        } else {
          F2.count('checked').count('hold');
          const ex = paths.find(([a, b, cc]) => a !== b && b !== cc) || paths[0];
          F2.add({ items: scene(ex ? { R, hot: [[ex[0], ex[1]], [ex[1], ex[2]]], good: [[ex[0], ex[2]]] } : { R }, ex ? { R, hot: [[ex[0], ex[1]], [ex[1], ex[2]]], good: [[ex[0], ex[2]]] } : { R }), say: ex ? 'Transitive: every two-step path has its shortcut. For example ' + ex[0] + ' → ' + ex[1] + ' → ' + ex[2] + ' is matched by ' + ex[0] + ' → ' + ex[2] + '. All ' + paths.length + ' such paths were checked.' : 'Transitive, with nothing to check: no two arrows join end to start (apart from loops), so no shortcut is ever demanded.', hl: { def: [propLine('transitive')] } });
        }
      }
      // -- summary
      const eq = verdict.reflexive && verdict.symmetric && verdict.transitive, po = verdict.reflexive && verdict.antisymmetric && verdict.transitive;
      const name = eq && po ? 'an equivalence and a partial order (only the loops: equality)' : eq ? 'an equivalence relation' : po ? 'a partial order' : 'neither an equivalence nor a partial order';
      const bx = narrow ? -150 : -150, by = narrow ? my + mH + 30 : Math.max(c.box.y + c.box.h - 40, my + mH + 20);
      const badges = PROPS.map((p, i) => ({ key: 'badge:' + p.id, kind: 'cell', x: bx + (i % 2) * 154, y: by + Math.floor(i / 2) * 46, w: 146, h: 38, text: (verdict[p.id] ? '✓ ' : '✗ ') + p.id, cls: verdict[p.id] ? 'good' : 'bad', size: 15, enter: 'drop' }));
      badges.push({ key: 'badge:name', kind: 'text', x: bx + 150, y: by + 118, text: 'R is ' + name.replace(/ \(.*\)$/, ''), anchor: 'middle', cls: eq || po ? 'good' : 'strong', size: 16 });
      F2.add({ items: scene({ R }, { R }, badges), say: 'So R is ' + name + '. An equivalence needs reflexive, symmetric and transitive; a partial order needs reflexive, antisymmetric and transitive.', hl: { def: PROPS.map((p) => propLine(p.id)).filter((_, i) => verdict[PROPS[i].id]) }, mark: 'verdict' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The relation and the four properties', text: defLines.join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask === 'reflexive', pick: 'option', options: ['Yes', 'No'], ask: 'Is R reflexive? Look for a loop at every element.', answer: (fr, i) => yesNo(fr[i].meta.yes), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.ask === 'symmetric', pick: 'option', options: ['Yes', 'No'], ask: 'Is R symmetric? Does every arrow come back?', answer: (fr, i) => yesNo(fr[i].meta.yes), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.ask === 'antisymmetric', pick: 'option', options: ['Yes', 'No'], ask: 'Is R antisymmetric? Do any two different elements point at each other?', answer: (fr, i) => yesNo(fr[i].meta.yes), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.ask === 'transitive', pick: 'option', options: ['Yes', 'No'], ask: 'Is R transitive? Check every path of two arrows for a shortcut.', answer: (fr, i) => yesNo(fr[i].meta.yes), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.pickCell, pick: 'item', ask: 'Which entry of the matrix would have to be 1 for transitivity, but is 0? Click it.', answer: (fr, i) => fr[i].meta.pickCell, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'D = {1, 2, 3} and R = ∅. Which properties does R have?', options: ['None of them', 'Symmetric, antisymmetric and transitive, but not reflexive', 'All four', 'Only reflexive'], answer: 1, why: 'The last three only say "if these pairs are there, then...": with no pairs nothing can break them. Reflexive demands three loops, which are missing.' },
      { q: 'Which relation on {1, 2} is both symmetric and antisymmetric?', options: ['{(1, 2), (2, 1)}', '{(1, 1), (2, 2)}', '{(1, 2)}', 'None can be both'], answer: 1, why: 'Loops come back to themselves (symmetric) and never join two different elements (antisymmetric).' },
      { q: 'R = {(1, 2), (2, 1)} on {1, 2}. Is it transitive?', options: ['Yes', 'No: (1, 1) and (2, 2) are missing'], answer: 1, why: '1 → 2 → 1 needs the shortcut 1 → 1, a loop. Transitivity allows x = z.' },
      { q: 'In the matrix, what does symmetry look like?', options: ['The diagonal is all 1', 'The matrix equals its mirror image across the diagonal', 'Every row has a 1', 'There are no 1s below the diagonal'], answer: 1, why: 'Entry (x, y) must equal entry (y, x).' },
      { q: 'A relation is reflexive, antisymmetric and transitive. What is it called?', options: ['An equivalence relation', 'A partial order', 'A function', 'A partition'], answer: 1, why: 'Swap antisymmetric for symmetric and you get an equivalence instead.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Functions: one-to-one and onto
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'fn-kinds', family: 'found-relations', order: 20, title: 'One-to-one, onto and both',
    blurb: 'A function sends every element of A to exactly one element of B. One-to-one: no two arrows meet. Onto: every element of B is hit. Both: a bijection, and the arrows can be turned round.',
    inputs: [
      { id: 'A', kind: 'list', label: 'Domain A', def: ['1', '2', '3', '4'], min: 1, max: 6, check: (v) => H.checkDomain(v, 'Domain A') },
      { id: 'B', kind: 'list', label: 'Codomain B', def: ['a', 'b', 'c'], min: 1, max: 6, check: (v) => H.checkDomain(v, 'Codomain B') },
      { id: 'f', kind: 'text', label: 'Arrows of f (x-y)', def: '1-b, 2-a, 3-c, 4-b', check: (v, inp) => { let R; try { R = H.parsePairs(v); } catch (e) { return 'Arrows of f: ' + e.message; } for (const [x, y] of R) { if (!(inp.A || []).includes(x)) return 'Arrows of f: ' + x + ' is not in A'; if (!(inp.B || []).includes(y)) return 'Arrows of f: ' + y + ' is not in B'; } return null; } },
    ],
    presets: [
      { label: 'Two meet: onto, not one-to-one', values: { A: ['1', '2', '3', '4'], B: ['a', 'b', 'c'], f: '1-b, 2-a, 3-c, 4-b' } },
      { label: 'One missed: one-to-one, not onto', values: { A: ['1', '2', '3'], B: ['a', 'b', 'c', 'd'], f: '1-c, 2-a, 3-d' } },
      { label: 'A bijection, then turned round', values: { A: ['1', '2', '3', '4'], B: ['w', 'x', 'y', 'z'], f: '1-x, 2-z, 3-w, 4-y' } },
      { label: 'Neither', values: { A: ['1', '2', '3'], B: ['a', 'b', 'c'], f: '1-a, 2-a, 3-b' } },
      { label: 'Not a function at all', values: { A: ['1', '2', '3'], B: ['a', 'b'], f: '1-a, 1-b, 2-b' } },
    ],
    counters: [{ id: 'arrows', label: 'arrows' }, { id: 'hit', label: 'elements of B hit' }],
    run(inp) {
      const A = inp.A, B = inp.B, P = H.parsePairs(inp.f);
      const out = (a) => P.filter((p) => p[0] === a), into = (b) => P.filter((p) => p[1] === b);
      const F2 = new T.Frames(['arrows', 'hit']);
      const gap = H.narrow() ? 220 : 280;
      const draw = (o) => K.rel.columns(Object.assign({ A, B, gap, titles: ['A (domain)', 'B (codomain)'] }, o)).items;
      const hitN = (pairs) => new Set(pairs.map((p) => p[1])).size;
      const lines = ['A = {' + A.join(', ') + '}', 'B = {' + B.join(', ') + '}'].concat(H.pairLines('f', P, 3), ['function:    exactly one arrow out of each a ∈ A', 'one-to-one:  f(a) = f(a′) ⇒ a = a′', 'onto:        every b ∈ B is some f(a)', 'bijection:   one-to-one and onto']);
      const L0 = 2 + H.pairLines('f', P, 3).length;
      F2.add({ items: draw({ pairs: [] }), say: 'A has ' + A.length + ' element' + (A.length === 1 ? '' : 's') + ' and B has ' + B.length + '. Each arrow of f goes from an element of A to an element of B.', hl: { def: ['0', '1'] } });
      const shown = [];
      for (const a of A) {
        const os = out(a);
        if (!os.length) continue;
        shown.push(...os);
        F2.count('arrows', os.length).set('hit', hitN(shown));
        F2.add({ items: draw({ pairs: shown.slice(), good: os }), say: os.length === 1 ? 'f(' + a + ') = ' + os[0][1] + '.' : a + ' has ' + os.length + ' arrows, to ' + os.map((p) => p[1]).join(' and ') + '.', hl: { def: ['2'] } });
      }
      // a function?
      const none = A.filter((a) => !out(a).length), many = A.filter((a) => out(a).length > 1);
      const nodeCls = {};
      if (none.length || many.length) {
        none.forEach((a) => { nodeCls['A:' + a] = 'bad'; });
        many.forEach((a) => { nodeCls['A:' + a] = 'bad'; });
        F2.add({ items: draw({ pairs: P, bad: P.filter((p) => many.includes(p[0])), nodeCls }), say: 'This is not a function: ' + [many.length ? many.join(', ') + (many.length === 1 ? ' has' : ' have') + ' more than one arrow out' : '', none.length ? none.join(', ') + (none.length === 1 ? ' has' : ' have') + ' no arrow at all' : ''].filter(Boolean).join(', and ') + '. A function gives every element of A exactly one value.', hl: { def: [String(L0)] }, mark: 'not a function' });
        F2.add({ items: draw({ pairs: P, bad: P.filter((p) => many.includes(p[0])), nodeCls }), say: 'It is still a relation from A to B, any set of pairs is, but "one-to-one" and "onto" only make sense once it is a function.', hl: { def: [String(L0)] } });
        return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The function', text: lines.join('\n') }] } };
      }
      F2.add({ items: draw({ pairs: P }), say: 'Every element of A has exactly one arrow out, so f is a function from A to B.', hl: { def: [String(L0)] } });
      // one-to-one
      const meet = B.filter((b) => into(b).length > 1);
      F2.add({ items: draw({ pairs: P }), say: 'One-to-one (injective): no two elements of A share a value, so no two arrows end at the same place.', hl: { def: [String(L0 + 1)] }, meta: { ask: 'inj', yes: !meet.length } });
      meet.forEach((b) => { nodeCls['B:' + b] = 'bad'; });
      F2.add({ items: draw({ pairs: P, bad: P.filter((p) => meet.includes(p[1])), nodeCls: Object.assign({}, nodeCls) }), say: meet.length ? 'Not one-to-one: ' + meet.map((b) => into(b).map((p) => 'f(' + p[0] + ')').join(' = ') + ' = ' + b).join(', and ') + '. Knowing the value ' + meet[0] + ' does not tell you where it came from.' : 'One-to-one: every element of B has at most one arrow coming in.' + (A.length > B.length ? '' : ''), hl: { def: [String(L0 + 1)] } });
      // onto
      const missed = B.filter((b) => !into(b).length);
      F2.add({ items: draw({ pairs: P, nodeCls: Object.assign({}, nodeCls) }), say: 'Onto (surjective): every element of B must be hit by at least one arrow.', hl: { def: [String(L0 + 2)] }, meta: { ask: 'sur', yes: !missed.length, missed: missed.map((b) => 'fn:b:' + b) } });
      missed.forEach((b) => { nodeCls['B:' + b] = 'hot'; });
      F2.add({ items: draw({ pairs: P, nodeCls: Object.assign({}, nodeCls), good: missed.length ? [] : P }), say: missed.length ? 'Not onto: nothing maps to ' + missed.join(' or ') + '.' + (A.length < B.length ? ' With only ' + A.length + ' arrows for ' + B.length + ' targets, some target had to be missed.' : '') : 'Onto: every element of B is hit.' + (A.length > B.length && meet.length ? ' With ' + A.length + ' arrows landing on ' + B.length + ' targets, two had to meet: that is the pigeonhole principle.' : ''), hl: { def: [String(L0 + 2)] } });
      const bij = !meet.length && !missed.length;
      if (bij) {
        F2.add({ items: draw({ pairs: P, good: P }), say: 'One-to-one and onto: f is a bijection. Each element of A is paired with exactly one element of B, and the other way round, so |A| = |B| = ' + A.length + '.', hl: { def: [String(L0 + 3)] }, mark: 'bijection' });
        F2.add({ items: draw({ pairs: P, good: P, reverse: true, titles: ['A', 'B: f⁻¹ goes back'] }), say: 'Turn every arrow round and you get the inverse f⁻¹ from B to A, which is again a function: one arrow out of every element of B.', hl: { def: [String(L0 + 3)] } });
      } else F2.add({ items: draw({ pairs: P, nodeCls: Object.assign({}, nodeCls), bad: P.filter((p) => meet.includes(p[1])) }), say: 'So f is ' + (meet.length && missed.length ? 'neither one-to-one nor onto' : meet.length ? 'onto but not one-to-one' : 'one-to-one but not onto') + '. Turning its arrows round would not give a function: ' + (meet.length ? meet[0] + ' would have two arrows out' : missed[0] + ' would have none') + '.', hl: { def: [String(L0 + 3)] }, mark: 'verdict' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The function', text: lines.join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask === 'inj', pick: 'option', options: ['Yes', 'No'], ask: 'Is f one-to-one? Look for two arrows ending at the same place.', answer: (fr, i) => yesNo(fr[i].meta.yes), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.ask === 'sur' && f.meta.missed.length, pick: 'item', ask: 'Click an element of B that no arrow reaches.', answer: (fr, i) => fr[i].meta.missed, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.ask === 'sur' && !f.meta.missed.length, pick: 'option', options: ['Yes', 'No'], ask: 'Is f onto? Is every element of B hit?', answer: () => 'Yes', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'A has 5 elements and B has 3. Can a function from A to B be one-to-one?', options: ['Yes, if chosen carefully', 'No: two of the five arrows must end at the same element', 'Only if it is onto'], answer: 1, why: 'Five arrows, three targets: by the pigeonhole principle two arrows meet.' },
      { q: 'A has 3 elements and B has 5. Can a function from A to B be onto?', options: ['Yes', 'No: three arrows reach at most three elements'], answer: 1, why: 'Each element of A has one arrow, so at most 3 elements of B are hit.' },
      { q: 'When does turning the arrows of f round give a function?', options: ['Always', 'When f is one-to-one', 'When f is onto', 'Exactly when f is a bijection'], answer: 3, why: 'Turned round, every element of B needs exactly one arrow out: at least one (onto) and at most one (one-to-one).' },
      { q: 'Which of these is not a function from {1, 2} to {a, b}?', options: ['{(1, a), (2, a)}', '{(1, b), (2, a)}', '{(1, a), (1, b)}', '{(1, b), (2, b)}'], answer: 2, why: '1 has two values and 2 has none; a function gives every element exactly one.' },
    ],
  });
})();
