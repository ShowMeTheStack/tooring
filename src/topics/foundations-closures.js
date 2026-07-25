// Closures of a relation: the smallest relation containing R that has a property. Warshall's algorithm fills
// the transitive closure round by round, each new pair drawn with the two-step path through k that justifies
// it; and the equivalence closure adds loops, then mirrors, then shortcuts, and ends as a partition.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found;
  const H = K.rel;

  T.family({ id: 'found-closures', part: 'foundations', order: 30, title: 'Closures', blurb: 'Add as few pairs as possible to make a relation reflexive, symmetric or transitive. Warshall\'s algorithm finds the transitive closure in one pass per element.' });

  const pk = (x, y) => x + '\u0000' + y;
  const domainInput = (def) => ({ id: 'D', kind: 'list', label: 'Set D', def, min: 1, max: 6, check: (v) => H.checkDomain(v, 'Set D') });
  const pairsInput = (def) => ({ id: 'R', kind: 'text', label: 'Pairs of R (x-y)', def, check: (v, inp) => H.checkPairs(v, inp.D || [], 'Pairs of R') });
  /** The graph on its circle and the matrix beside it (below it on a phone) */
  function layout(D) {
    const c = H.circle(D);
    const narrow = H.narrow();
    const mW = 40 + D.length * 40, mH = 34 + D.length * 38;
    return { c, mx: narrow ? -mW / 2 : c.box.x + c.box.w - 30, my: narrow ? c.box.y + c.box.h - 20 : -mH / 2, mW, mH, narrow };
  }

  // ---------------------------------------------------------------------------------------------------
  // Warshall
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'closure-warshall', family: 'found-closures', order: 10, title: 'Transitive closure: Warshall\'s algorithm',
    blurb: 'In round k, a path may pass through k: wherever i → k and k → j, add i → j. After one round per element every path has its shortcut.',
    inputs: [domainInput(['1', '2', '3', '4']), pairsInput('1-2, 2-3, 3-4, 4-2')],
    presets: [
      { label: 'A chain: 1→2→3→4', values: { D: ['1', '2', '3', '4'], R: '1-2, 2-3, 3-4' } },
      { label: 'A cycle: loops appear', values: { D: ['a', 'b', 'c'], R: 'a-b, b-c, c-a' } },
      { label: 'Two islands', values: { D: ['1', '2', '3', '4', '5'], R: '1-2, 2-3, 4-5' } },
      { label: 'Already transitive', values: { D: ['1', '2', '3'], R: '1-2, 1-3, 2-3' } },
      { label: 'The empty relation', values: { D: ['x', 'y', 'z'], R: '' } },
    ],
    counters: [{ id: 'round', label: 'round' }, { id: 'added', label: 'pairs added' }, { id: 'pairs', label: 'pairs now' }],
    run(inp) {
      const D = inp.D, R = H.parsePairs(inp.R);
      const L = layout(D);
      const tc = F.transitiveClosure(D, R);
      const F2 = new T.Frames(['round', 'added', 'pairs']);
      const cur = R.slice(), added = [];
      const scene = (g, m) => H.graph(Object.assign({ D, pos: L.c.pos, R: cur.slice() }, g)).items.concat(H.matrix(Object.assign({ D, R: cur.slice(), x: L.mx, y: L.my }, m)).items);
      F2.set('pairs', R.length);
      F2.add({ items: scene({}, {}), say: 'R has ' + R.length + ' pair' + (R.length === 1 ? '' : 's') + '. Its transitive closure R⁺ is the smallest transitive relation containing R: x R⁺ y exactly when a path of arrows leads from x to y. Warshall finds it in ' + D.length + ' rounds, one per element.', hl: { def: ['0'] } });
      const steps = tc.trace.slice(1);
      let k;
      let idx = 0;
      for (k = 0; k < D.length; k++) {
        const v = D[k];
        const adds = [];
        while (idx < steps.length && steps[idx].kind === 'add') adds.push(steps[idx++]);
        idx++; // the round's summary
        F2.set('round', k + 1);
        // pairs that will be added this round, for the prediction
        const cellKeys = adds.map((a) => H.matrix({ D, R: [], x: L.mx, y: L.my }).cellKey(a.pair[0], a.pair[1]));
        const into = cur.filter(([a, b]) => b === v && a !== v).map(([a]) => a), outOf = cur.filter(([a, b]) => a === v && b !== v).map(([, b]) => b);
        F2.add({ items: scene({ nodeCls: { [v]: 'hot' }, hot: cur.filter(([a, b]) => a === v || b === v) }, { lit: { rows: [v], cols: [v] } }), say: 'Round ' + (k + 1) + ': paths may now pass through ' + v + '. Arrows into ' + v + ' come from ' + (into.length ? into.join(', ') : 'nowhere') + '; arrows out of ' + v + ' go to ' + (outOf.length ? outOf.join(', ') : 'nowhere') + '. In the matrix, column ' + v + ' meets row ' + v + '.', hl: { def: ['1', '2'] }, meta: { round: v, adds: cellKeys, any: adds.length > 0 } });
        for (const st of adds) {
          const [i, j] = st.pair;
          cur.push([i, j]); added.push([i, j]);
          F2.count('added').count('pairs');
          F2.add({ items: scene({ hot: st.via, good: [[i, j]], nodeCls: { [v]: 'hot' } }, { hot: st.via, good: [[i, j]], lit: { rows: [v], cols: [v] }, arrows: [{ from: st.via[0], to: [i, j] }, { from: st.via[1], to: [i, j], cls: 'b' }] }), say: st.say + (i === j ? ' It is a loop: ' + i + ' can come back to itself.' : ''), hl: { def: ['2'] } });
        }
        if (!adds.length) F2.add({ items: scene({ nodeCls: { [v]: 'hot' } }, { lit: { rows: [v], cols: [v] } }), say: 'Round ' + (k + 1) + ' adds nothing: ' + (!into.length || !outOf.length ? 'no path can pass through ' + v + ', since ' + (!into.length ? 'no arrow comes into it' : 'no arrow leaves it') + '.' : 'every path through ' + v + ' already has its shortcut.'), hl: { def: ['2'] } });
      }
      F2.add({ items: scene({ good: added }, { good: added }), say: added.length ? 'Done. R⁺ has ' + cur.length + ' pairs: the ' + R.length + ' of R and ' + added.length + ' shortcuts (lit). Any path, however long, now has a direct arrow, so R⁺ is transitive, and nothing was added that a transitive relation containing R could do without.' : 'Done, and nothing was added: R was already transitive, so R⁺ = R.', hl: { def: ['3'] }, mark: 'closure' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Warshall\'s algorithm', text: ['R⁽⁰⁾ = R', 'round k: paths may pass through the first k elements', 'add (i, j) when (i, k) and (k, j) are there', 'R⁺ = R⁽ⁿ⁾: every path has its shortcut'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.round !== undefined && f.meta.any, once: true, pick: 'item', ask: 'Which entry of the matrix will this round turn into 1? Click one.', answer: (fr, i) => fr[i].meta.adds, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.round !== undefined && !f.meta.any, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will this round add any pair?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'R = {(a, b), (b, a)}. Which pairs does its transitive closure add?', options: ['None', '(a, a) and (b, b)', '(a, b) only', 'All four pairs on {a, b} are already there'], answer: 1, why: 'a → b → a needs the shortcut a → a, and b → a → b needs b → b.' },
      { q: 'How many rounds does Warshall\'s algorithm take on a set of n elements?', options: ['log n', 'n', 'n²', 'Until nothing changes, which can be more than n'], answer: 1, why: 'One round per element that a path may pass through; after round n every element is allowed.' },
      { q: 'In round k, when is (i, j) added?', options: ['When (i, k) and (k, j) are both 1', 'When (i, j) and (j, k) are both 1', 'When row i equals row k', 'When (k, k) is 1'], answer: 0, why: 'A path i → … → k → … → j through k gives i a way to reach j.' },
      { q: 'What does (x, y) ∈ R⁺ mean in the picture?', options: ['There is an arrow x → y in R', 'There is a path of one or more arrows from x to y in R', 'x and y are in the same row', 'y can reach x'], answer: 1, why: 'The closure adds exactly the pairs joined by a path.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Equivalence closure: loops, then mirrors, then shortcuts, then the classes
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'closure-equivalence', family: 'found-closures', order: 20, title: 'The smallest equivalence containing R',
    blurb: 'Add loops (reflexive), then the arrow back for every arrow (symmetric), then shortcuts (transitive). What comes out is an equivalence, and its classes are the connected pieces of the picture.',
    inputs: [domainInput(['1', '2', '3', '4', '5']), pairsInput('1-2, 3-2, 4-5')],
    presets: [
      { label: 'Two pieces', values: { D: ['1', '2', '3', '4', '5'], R: '1-2, 3-2, 4-5' } },
      { label: 'One long chain: one class', values: { D: ['a', 'b', 'c', 'd'], R: 'a-b, b-c, c-d' } },
      { label: 'Nothing related: singletons', values: { D: ['p', 'q', 'r'], R: '' } },
      { label: 'Already an equivalence', values: { D: ['1', '2', '3'], R: '1-1, 2-2, 3-3, 1-2, 2-1' } },
    ],
    counters: [{ id: 'pairs', label: 'pairs' }, { id: 'added', label: 'pairs added' }, { id: 'classes', label: 'classes' }],
    run(inp) {
      const D = inp.D, R = H.parsePairs(inp.R);
      const L = layout(D);
      const F2 = new T.Frames(['pairs', 'added', 'classes']);
      const cur = R.slice();
      const scene = (g, m) => H.graph(Object.assign({ D, pos: L.c.pos, R: cur.slice() }, g)).items.concat(H.matrix(Object.assign({ D, R: cur.slice(), x: L.mx, y: L.my }, m)).items);
      F2.set('pairs', R.length);
      F2.add({ items: scene({}, {}), say: 'R has ' + R.length + ' pair' + (R.length === 1 ? '' : 's') + '. To make an equivalence, add what each property demands, and nothing more: loops, then return arrows, then shortcuts.', hl: { def: ['0'] } });
      const refl = F.reflexiveClosure(D, cur);
      const loops = refl.trace.map((s) => s.pair);
      F2.add({ items: scene({ ghost: loops, ghostCls: 'good' }, { act: loops }), say: loops.length ? 'Reflexive: ' + loops.map(([x]) => x).join(', ') + (loops.length === 1 ? ' needs a loop' : ' need loops') + '.' : 'Reflexive: every element already has its loop.', hl: { def: ['1'] }, meta: { ask: 'loops', n: loops.length } });
      cur.push(...loops); F2.count('added', loops.length).set('pairs', cur.length);
      F2.add({ items: scene({ good: loops }, { good: loops }), say: loops.length ? 'Added ' + loops.length + ' loop' + (loops.length === 1 ? '' : 's') + '. The diagonal of the matrix is now all 1s.' : 'Nothing to add for reflexivity.', hl: { def: ['1'] } });
      const sym = F.symmetricClosure(D, cur);
      const mirrors = sym.trace.map((s) => s.pair);
      F2.add({ items: scene({ hot: sym.trace.map((s) => s.because), ghost: mirrors, ghostCls: 'good' }, { hot: sym.trace.map((s) => s.because), act: mirrors }), say: mirrors.length ? 'Symmetric: every one-way arrow needs its return, ' + mirrors.map(([y, x]) => y + ' → ' + x).join(', ') + '.' : 'Symmetric: every arrow already comes back.', hl: { def: ['2'] } });
      cur.push(...mirrors); F2.count('added', mirrors.length).set('pairs', cur.length);
      F2.add({ items: scene({ good: mirrors }, { good: mirrors }), say: mirrors.length ? 'Added ' + mirrors.length + ' return arrow' + (mirrors.length === 1 ? '' : 's') + '. The matrix is its own mirror image now.' : 'Nothing to add for symmetry.', hl: { def: ['2'] } });
      const tc = F.transitiveClosure(D, cur);
      const short = tc.trace.filter((s) => s.kind === 'add');
      F2.add({ items: scene({ hot: short.flatMap((s) => s.via).filter((p) => cur.some((q) => q[0] === p[0] && q[1] === p[1])), ghost: short.map((s) => s.pair), ghostCls: 'good' }, { act: short.map((s) => s.pair) }), say: short.length ? 'Transitive: Warshall finds ' + short.length + ' missing shortcut' + (short.length === 1 ? '' : 's') + ', ' + short.slice(0, 4).map((s) => s.pair.join(' → ')).join(', ') + (short.length > 4 ? ', …' : '') + '. Doing symmetry first matters: shortcuts of a symmetric relation come in pairs, so it stays symmetric.' : 'Transitive: every path already has its shortcut.', hl: { def: ['3'] } });
      cur.push(...short.map((s) => s.pair)); F2.count('added', short.length).set('pairs', cur.length);
      F2.add({ items: scene({ good: short.map((s) => s.pair) }, { good: short.map((s) => s.pair) }), say: 'Now R is reflexive, symmetric and transitive: an equivalence with ' + cur.length + ' pairs, ' + (cur.length - R.length) + ' more than we started with.', hl: { def: ['3'] } });
      // the classes: colour the nodes, then gather each class into a block
      const cl = F.classes(D, cur).result;
      const cOf = {};
      cl.forEach((c, i) => c.forEach((x) => { cOf[x] = 'kc' + (i % 6); }));
      F2.set('classes', cl.length);
      F2.add({ items: scene({ nodeCls: cOf }, {}), say: 'Elements joined by arrows are equivalent. Colour each class: ' + cl.map((c) => '{' + c.join(', ') + '}').join(', ') + '. These are the connected pieces of the original picture.', hl: { def: ['4'] }, meta: { classes: cl.length } });
      // blocks: one region per class, its elements in a row inside
      const items = [];
      const BW = (c) => c.length * 56 + 24;
      const total = cl.reduce((a, c) => a + BW(c), 0) + (cl.length - 1) * 18;
      let x = L.narrow ? -total / 2 : Math.min(-total / 2, L.mx - 30 - total);
      const by = -48;
      const blockPos = {};
      cl.forEach((c, i) => {
        items.push({ key: 'blk:' + i, kind: 'region', x, y: by, w: BW(c), h: 96, cls: 'r' + (i % 6), text: '[' + c[0] + ']', enter: 'fade' });
        c.forEach((e, j) => { blockPos[e] = { x: x + 40 + j * 56, y: by + 62 }; });
        x += BW(c) + 18;
      });
      const nodes = D.map((e) => ({ key: 'rl:n:' + e, kind: 'state', x: blockPos[e].x, y: blockPos[e].y, r: H.nodeR(e), w: 2 * H.nodeR(e), h: 2 * H.nodeR(e), rx: H.nodeR(e), text: e, cls: 'state ' + cOf[e] }));
      F2.add({ items: items.concat(nodes, H.matrix({ D, R: cur, x: L.mx, y: L.my }).items), say: 'The classes are disjoint and together they cover D: a partition into ' + cl.length + ' block' + (cl.length === 1 ? '' : 's') + '. Inside a block every element is related to every other, so the arrows are no longer needed.', hl: { def: ['4'] }, mark: 'partition' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Closing under each property', text: [H.pairLines('R', R)[0] + (R.length > 4 ? ' …' : ''), '1. add (x, x) for every x', '2. add (y, x) for every (x, y)', '3. add (x, z) for every path x → y → z', '4. classes: [x] = {y : x ~ y}'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask === 'loops', pick: 'option', options: (fr, i, inp) => [...new Set([0, 1, 2, 3, 4, 5, 6].slice(0, inp.D.length + 1).map(String))], ask: 'How many loops must be added to make R reflexive?', answer: (fr, i) => String(fr[i].meta.n), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].mark === 'partition', pick: 'option', options: ['1', '2', '3', '4', '5', '6'], ask: 'How many classes will the partition have?', answer: (fr, i) => String(fr[i].meta.classes), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why add the return arrows before the shortcuts?', options: ['It is faster', 'Shortcuts of a symmetric relation are symmetric too, so the result stays symmetric; the other order could need another round', 'Symmetry removes pairs', 'It makes no difference to anything'], answer: 1, why: 'Symmetric then transitive gives an equivalence in one pass. Transitive first can leave paths that only appear after mirroring.' },
      { q: 'D = {a, b, c} and R = ∅. What is the smallest equivalence containing R?', options: ['∅', 'Only the three loops: equality', 'All nine pairs', 'It does not exist'], answer: 1, why: 'Reflexivity forces the loops; with no other arrows nothing more is needed. Every class is a single element.' },
      { q: 'In the picture of R, what are the classes of its equivalence closure?', options: ['The cycles', 'The pieces connected by arrows, ignoring their direction', 'The elements with loops', 'The rows of the matrix'], answer: 1, why: 'Two elements end up related exactly when a chain of arrows, in either direction, joins them.' },
    ],
  });
})();
