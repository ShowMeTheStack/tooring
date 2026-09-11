// Reductions as gadgets, second half: 3SAT to VERTEX COVER, to SUBSET SUM (a table of digits), to 3-COLOUR
// (a palette triangle and OR gadgets) and to HAM-PATH (rows crossed left or right, clause detours). Each one
// is assembled gadget by gadget from the core's builder, then a satisfying assignment is carried forward to a
// certificate of the target, checked by the target's verifier, and carried back again. An unsatisfiable
// formula shows the certificate that cannot exist and the one gadget that breaks when you try.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'cx-red', part: 'complexity', order: 50, title: 'Reductions as gadgets', blurb: 'Turn one problem into another in polynomial time, piece by piece, and carry every certificate across in both directions.' });

  // ---- shared pieces -----------------------------------------------------------------------------------------
  /** A check for a formula input: clauses of one to three literals, and the size limits that keep it readable */
  const fcheck = (maxN, maxM) => (v) => {
    let f;
    try { f = T.sat.parse(v); } catch (e) { return 'Formula: ' + e.message + '. Write clauses like (x ∨ ¬y ∨ z) ∧ (¬x ∨ y).'; }
    if (!f.clauses.length) return 'Formula: give at least one clause';
    if (f.clauses.some((c) => !c.length || c.length > 3)) return 'Formula: every clause needs one to three literals, like (x ∨ ¬y ∨ z)';
    if (f.n > maxN) return 'Formula: at most ' + maxN + ' variables here, so the picture stays readable';
    if (f.clauses.length > maxM) return 'Formula: at most ' + maxM + ' clauses here, so the picture stays readable';
    return null;
  };
  const isTrue = (a, l) => (l > 0 ? !!a[l] : !a[-l]);
  /** A satisfying assignment, trying "true" first for each variable (more interesting than all-false), or null */
  function satisfying(f) {
    const a = new Array(f.n + 1).fill(false);
    for (let m = 2 ** f.n - 1; m >= 0; m--) {
      for (let v = 1; v <= f.n; v++) a[v] = !!(m & (1 << (f.n - v)));
      if (T.sat.evaluate(f, a)) return a.slice();
    }
    return null;
  }
  /** The assignment that leaves fewest clauses false (for showing where an unsatisfiable formula breaks) */
  function nearest(f) {
    let best = null, bad = Infinity;
    const a = new Array(f.n + 1).fill(false);
    for (let m = 2 ** f.n - 1; m >= 0; m--) {
      for (let v = 1; v <= f.n; v++) a[v] = !!(m & (1 << (f.n - v)));
      const k = f.clauses.filter((c) => !c.some((l) => isTrue(a, l))).length;
      if (k < bad) { bad = k; best = a.slice(); }
    }
    return best;
  }
  const ftext = (f) => T.sat.toText(f);
  const lit = (f, l) => T.sat.litText(f, l);
  const asText = (f, a) => Array.from({ length: f.n }, (_, i) => lit(f, i + 1) + ' = ' + (a[i + 1] ? 1 : 0)).join(', ');
  const plural = (k, w) => k + ' ' + w + (k === 1 ? '' : 's');
  /** The formula, centred over a picture whose middle is at cx and whose top is at top */
  function formulaAbove(f, a, cx, top, opts) {
    const probe = K.cx.formula(Object.assign({ f, a, labels: true, maxW: 640 }, opts || {}));
    return K.cx.formula(Object.assign({ f, a, labels: true, maxW: 640, x: cx - probe.box.w / 2, y: top - probe.box.h }, opts || {}));
  }
  function chips(f, a, cx, y, opts) {
    const probe = K.cx.assignment(Object.assign({ f, a, label: 'assignment' }, opts || {}));
    return K.cx.assignment(Object.assign({ f, a, label: 'assignment', x: cx - probe.box.w / 2 + 50, y }, opts || {}));
  }
  const COL = ['colT', 'colF', 'colB'], CNAME = ['T', 'F', 'B'];
  /** The box around some points, padded */
  const ptsBox = (pts, px, py) => { const xs = pts.map((p) => p.x), ys = pts.map((p) => p.y); return { x: Math.min(...xs) - px, y: Math.min(...ys) - py, w: Math.max(...xs) - Math.min(...xs) + 2 * px, h: Math.max(...ys) - Math.min(...ys) + 2 * py }; };
  // the clause switcher: look at one clause's gadget at a time, and optionally dim every other edge
  const focusInput = (max) => ({ id: 'focus', kind: 'choice', label: 'Clause in focus', def: 'all', options: [{ value: 'all', label: 'all' }].concat(Array.from({ length: max }, (_, i) => ({ value: String(i + 1), label: 'clause ' + (i + 1) }))) });
  const EDGES_INPUT = { id: 'edges', kind: 'choice', label: 'Edges', def: 'all', options: [{ value: 'all', label: 'all' }, { value: 'clause', label: 'only this clause\'s' }] };
  const focusCheck = (inp) => { const m = T.sat.parse(inp.f).clauses.length; return inp.focus && inp.focus !== 'all' && +inp.focus > m ? 'Clause in focus: the formula has only ' + plural(m, 'clause') : null; };
  /** With a clause in focus, keep the frames about it (and the general ones), aim the camera at its band, and say "clause k of m" */
  function focusFrames(list, inp, m, boxOf) {
    if (!inp.focus || inp.focus === 'all') return list;
    const k = +inp.focus - 1, box = boxOf(k);
    return list.filter((fr) => !fr.meta || fr.meta.clause === undefined || fr.meta.clause === k).map((fr) => {
      // frames about the clause look at its band; the general ones (palette, variables, checks) at what they are about
      if (fr.meta && fr.meta.clause === k) { fr.view = box; fr.narrowView = box; const lead = 'Clause ' + (k + 1); fr.say = fr.say.startsWith(lead) ? lead + ' of ' + m + fr.say.slice(lead.length) : lead + ' of ' + m + '. ' + fr.say; }
      else if (fr.narrowView) fr.view = fr.narrowView;
      else fr.view = box;
      return fr;
    });
  }
  /**
   * The gadget kit's drawing of the finished graph, remembered: routing the edges is the slow part, and a
   * graph being assembled is drawn as the finished one with the parts not yet built left out, so edges keep
   * their bends from frame to frame and nothing jumps. opts.full = {nodes, edges, groups} of the whole
   * graph; opts.nodes and opts.edges say what is drawn now and carry each frame's classes.
   */
  const drawCache = new Map();
  function gdraw(opts) {
    const full = opts.full;
    const sig = opts.prefix + '|' + full.nodes.map((x) => x.id + ':' + x.label + '@' + x.x + ',' + x.y).join(';') + '|' + full.edges.map((e) => e.a + '>' + e.b).join(';') + '|' + (full.groups || []).map((g) => g.id).join(';');
    let base = drawCache.get(sig);
    if (!base) { base = K.gadget.draw({ nodes: full.nodes, edges: full.edges, groups: full.groups, directed: opts.directed, prefix: opts.prefix }).items; if (drawCache.size > 60) drawCache.clear(); drawCache.set(sig, base); }
    const P = opts.prefix;
    const cert = new Set(opts.cert || []);
    const nById = new Map(opts.nodes.map((x) => [P + ':v:' + x.id, x]));
    const eByKey = new Map(opts.edges.map((e) => [P + ':e:' + e.a + '>' + e.b, e]));
    const groups = new Set((opts.groups || []).filter((g) => opts.nodes.some((x) => x.group === g.id)).map((g) => P + ':g:' + g.id));
    const out = [];
    for (const it of base) {
      const nd = nById.get(it.key), e = eByKey.get(it.key);
      if (it.kind === 'state') { if (nd) out.push(Object.assign({}, it, opts.size ? { size: opts.size } : {}, { cls: ['gnode', nd.role === 'var' ? 'var' : nd.role === 'clause' ? 'clause' : '', cert.has(nd.id) ? 'cert' : '', nd.cls || ''].filter(Boolean).join(' ') })); }
      else if (it.kind === 'edge') { if (e) out.push(Object.assign({}, it, opts.straight ? { bend: 0 } : {}, { cls: ['gedge', e.cls || ''].filter(Boolean).join(' ') })); }
      else if (it.kind === 'region') { if (groups.has(it.key)) out.push(Object.assign({}, it)); }
      else out.push(Object.assign({}, it));
    }
    return { items: out };
  }

  const quizCommon = {
    poly: { q: 'Why must a reduction run in polynomial time?', options: ['So the target instance is small enough to print', 'So that a fast algorithm for the target would give a fast algorithm for 3SAT', 'Because gadgets must be planar', 'It need not: any computable map will do'], answer: 1, why: 'If building the target took exponential time, solving it quickly would not solve 3SAT quickly; the reduction would prove nothing about NP-hardness.' },
    both: { q: 'Why does a correct reduction need both directions, satisfiable ⇒ yes and yes ⇒ satisfiable?', options: ['One direction is enough', 'Without the backward direction a yes for the target could come from an unsatisfiable formula', 'Both directions make it faster', 'The backward direction is only needed for 2SAT'], answer: 1, why: 'The forward map shows satisfiable formulas land on yes instances; the backward map shows nothing else does, so the answers match exactly.' },
  };

  // ============================================================================================================
  // 3SAT → VERTEX COVER
  // ============================================================================================================
  const VC_DEF = '(x ∨ y ∨ ¬z) ∧ (¬x ∨ ¬y ∨ z)';
  T.topic({
    id: 'cx-red-vc', family: 'cx-red', order: 55, title: '3SAT → VERTEX COVER',
    blurb: 'Each variable becomes an edge and each clause a triangle, joined by links to the literals. A cover of size k exists exactly when the formula can be satisfied.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (3-CNF)', def: VC_DEF, check: fcheck(4, 4) }, focusInput(4), EDGES_INPUT],
    check: focusCheck,
    presets: [
      { label: 'Two clauses, three variables', values: { f: VC_DEF } },
      { label: 'Three clauses', values: { f: '(a ∨ b ∨ c) ∧ (¬a ∨ ¬b ∨ c) ∧ (a ∨ ¬c)' } },
      { label: 'A one-literal clause', values: { f: '(¬p) ∧ (p ∨ q ∨ r) ∧ (¬q ∨ ¬r)' } },
      { label: 'Unsatisfiable: x and ¬x', values: { f: '(x ∨ x) ∧ (¬x ∨ ¬x)' } },
      { label: 'Unsatisfiable: all four sign pairs', values: { f: '(x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y)' } },
    ],
    counters: [{ id: 'v', label: 'vertices' }, { id: 'e', label: 'edges' }, { id: 'k', label: 'k' }, { id: 'c', label: 'in the cover' }],
    run(inp) {
      const f = T.sat.parse(inp.f);
      const R = T.red.sat3ToVC(f);
      const n = f.n, m = f.clauses.length;
      const litNode = (l) => 2 * (Math.abs(l) - 1) + (l < 0 ? 1 : 0);
      // positions: variable edges along the top, clause triangles below, each triangle's corners ordered
      // like the literals they link to so the links fan out instead of crossing the triangle
      const Wd = Math.max(n, m, 2) * 170;
      const pos = {};
      for (let v = 1; v <= n; v++) { const cx = (v - 0.5) * Wd / n; pos[2 * (v - 1)] = { x: cx - 40, y: 0 }; pos[2 * (v - 1) + 1] = { x: cx + 40, y: 0 }; }
      const occOf = [], clauseOfNode = {};
      f.clauses.forEach((c, j) => {
        const ids = R.draw.nodes.filter((x) => x.group === 'clause ' + (j + 1)).map((x) => x.id);
        occOf.push(ids);
        ids.forEach((id) => { clauseOfNode[id] = j; });
        const cx = (j + 0.5) * Wd / m;
        const order = ids.map((id, p) => ({ id, tx: pos[litNode(c[p])].x })).sort((a, b) => a.tx - b.tx);
        if (order.length === 3) { pos[order[0].id] = { x: cx - 52, y: 235 }; pos[order[1].id] = { x: cx, y: 168 }; pos[order[2].id] = { x: cx + 52, y: 235 }; }
        else if (order.length === 2) { pos[order[0].id] = { x: cx - 42, y: 210 }; pos[order[1].id] = { x: cx + 42, y: 210 }; }
        else pos[order[0].id] = { x: cx, y: 210 };
      });
      const node = (x) => ({ id: x.id, label: x.label, role: x.role === 'variable' ? 'var' : 'clause', group: x.group, x: pos[x.id].x, y: pos[x.id].y });
      const allE = R.draw.edges;
      const ek = (e) => e.a + '>' + e.b;
      const edgeClause = (e) => (e.role === 'variable' ? undefined : clauseOfNode[e.a]);
      const groups = [];
      for (let v = 1; v <= n; v++) groups.push({ id: 'x' + v, label: 'variable ' + lit(f, v) });
      // clause groups are named underneath (links come in from above and would cross a name at the top)
      for (let j = 1; j <= m; j++) groups.push({ id: 'clause ' + j, label: ' ' });
      // the boxes a phone (or the clause switcher) shows: one variable, or one clause with the literals it links to
      const varBox = (v) => ptsBox([pos[2 * (v - 1)], pos[2 * (v - 1) + 1]], 56, 70);
      const clauseBox = (j) => ptsBox(occOf[j].map((id) => pos[id]).concat(f.clauses[j].map((l) => pos[litNode(l)])), 50, 70);
      const rowBox = ptsBox(Object.keys(pos).filter((id) => +id < 2 * n).map((id) => pos[id]), 50, 70);
      const F = new T.Frames(['v', 'e', 'k', 'c']);
      const st = { nodes: new Set(), edges: new Set(), cover: new Set(), out: new Set(), a: null, chips: false, bad: new Set(), hotE: new Set() };
      const fy = -56 - 22;
      const scene = (opts) => {
        opts = opts || {};
        const only = inp.edges === 'clause' && opts.clause !== undefined;
        const nodes = R.draw.nodes.filter((x) => st.nodes.has(x.id)).map((x) => Object.assign(node(x), { cls: st.out.has(x.id) ? 'hot' : st.bad.has(x.id) ? 'bad' : '' }));
        const edges = allE.filter((e) => st.edges.has(ek(e))).map((e) => ({ a: e.a, b: e.b, cls: st.hotE.has(ek(e)) ? 'hot' : only && edgeClause(e) !== opts.clause ? 'faded' : '' }));
        let items = gdraw({ nodes, edges, groups, cert: [...st.cover], prefix: 'vc', size: 17, straight: true, full: { nodes: R.draw.nodes.map(node), edges: allE, groups } }).items;
        for (let j = 0; j < m; j++) if (st.nodes.has(occOf[j][0])) items.push({ key: 'vc:cn:' + j, kind: 'text', x: (j + 0.5) * Wd / m, y: 290, text: 'C' + (j + 1), anchor: 'middle', cls: 'title' });
        items = items.concat(formulaAbove(f, opts.fa || null, Wd / 2, fy).items);
        if (st.chips) items = items.concat(chips(f, st.a, Wd / 2, 306).items);
        return items;
      };
      const add = (fr, about) => { fr.narrowView = about === undefined ? rowBox : about; return F.add(fr); };
      const count = () => { F.set('v', st.nodes.size).set('e', st.edges.size).set('c', st.cover.size); };
      add({ items: scene(), say: 'The formula ' + ftext(f) + ' has ' + plural(n, 'variable') + ' and ' + plural(m, 'clause') + '. We build a graph and a number k so that a cover of k vertices exists exactly when the formula can be satisfied.' });
      for (let v = 1; v <= n; v++) {
        st.nodes.add(2 * (v - 1)); st.nodes.add(2 * (v - 1) + 1); st.edges.add(2 * (v - 1) + '>' + (2 * (v - 1) + 1)); count();
        add({ items: scene(), say: 'Variable ' + lit(f, v) + ' becomes the edge ' + lit(f, v) + ' — ' + lit(f, -v) + ': every cover must take at least one end, and taking exactly one end will say which value ' + lit(f, v) + ' has.', hl: { def: [0] } }, varBox(v));
      }
      f.clauses.forEach((c, j) => {
        for (const id of occOf[j]) st.nodes.add(id);
        for (const e of allE) if (e.role === 'clause' && occOf[j].includes(e.a)) st.edges.add(ek(e));
        count();
        const shape = c.length === 3 ? 'a triangle' : c.length === 2 ? 'a single edge' : 'a lone vertex';
        add({ items: scene({ clause: j }), say: 'Clause ' + (j + 1) + ', (' + c.map((l) => lit(f, l)).join(' ∨ ') + '), becomes ' + shape + ' of its ' + plural(c.length, 'occurrence') + ': a cover must take all of them but at most one.', meta: { clause: j }, hl: { def: [1] } }, clauseBox(j));
      });
      f.clauses.forEach((c, j) => {
        for (const e of allE) if (e.role === 'link' && occOf[j].includes(e.a)) st.edges.add(ek(e));
        count();
        add({ items: scene({ clause: j }), say: 'Link each occurrence in clause ' + (j + 1) + ' to the vertex of its literal: ' + c.map((l) => lit(f, l) + ' — ' + lit(f, l)).join(', ') + '. An occurrence left out of the cover needs its literal covered instead.', meta: { clause: j }, hl: { def: [2] } }, clauseBox(j));
      });
      F.set('k', R.k);
      add({ items: scene(), say: 'Ask for a cover of size k = n + Σ(|clause| − 1) = ' + n + ' + ' + f.clauses.map((c) => c.length - 1).join(' + ') + ' = ' + R.k + ': one end of every variable edge and all but one vertex of every clause gadget, with nothing to spare.', hl: { def: [3] } });
      const a = satisfying(f);
      if (a) {
        const C = R.forward(a);
        st.a = a; st.chips = true;
        add({ items: scene({ fa: a }), say: 'Forward: take the satisfying assignment ' + asText(f, a) + '.', hl: { def: [4] } });
        for (let v = 1; v <= n; v++) st.cover.add(litNode(a[v] ? v : -v));
        count();
        add({ items: scene({ fa: a }), say: 'For each variable cover the vertex of its true literal: ' + Array.from({ length: n }, (_, i) => lit(f, a[i + 1] ? i + 1 : -(i + 1))).join(', ') + ' (' + n + (n === 1 ? ' vertex' : ' vertices') + ').', hl: { def: [4] } });
        f.clauses.forEach((c, j) => {
          const keep = occOf[j].find((id, p) => isTrue(a, c[p]));
          const p = occOf[j].indexOf(keep);
          st.out.add(keep);
          for (const id of occOf[j]) if (id !== keep && C.includes(id)) st.cover.add(id);
          const link = allE.find((e) => e.role === 'link' && e.a === keep);
          st.hotE.add(ek(link));
          count();
          add({ items: scene({ fa: a, clause: j }), say: 'Clause ' + (j + 1) + ': leave out the occurrence of ' + lit(f, c[p]) + ', which is true, and cover the rest. Its link to ' + lit(f, c[p]) + ' is still covered from the top, because ' + lit(f, c[p]) + ' is in the cover.', meta: { clause: j, keepable: occOf[j].filter((id, q) => isTrue(a, c[q])).map((id) => 'vc:v:' + id) }, hl: { def: [4] } }, clauseBox(j));
        });
        const ok = T.cx.verifyVertexCover(R.graph, R.k, C);
        add({ items: scene({ fa: a }), say: 'The verifier checks the cover: ' + C.length + ' vertices, at most k = ' + R.k + ', and every one of the ' + R.graph.edges.length + ' edges has an end in it. ' + (ok.ok ? 'It is a vertex cover.' : ok.reason), mark: ok.ok ? 'accepted' : 'rejected', hl: { def: [4] } });
        st.a = new Array(n + 1).fill(null); st.out.clear(); st.hotE.clear();
        add({ items: scene(), say: 'Backward: forget the assignment and start from the cover alone.', hl: { def: [5] } });
        const b = R.backward(C);
        st.a = b;
        add({ items: scene({ fa: b }), say: 'A cover of size k takes exactly one end of each variable edge, so read the values off the top row: ' + asText(f, b) + '. ' + (T.sat.evaluate(f, b) ? 'Every clause is satisfied.' : 'Something is wrong.'), mark: 'accepted', hl: { def: [5] } });
      } else {
        const t = nearest(f);
        st.a = t; st.chips = true;
        for (let v = 1; v <= n; v++) st.cover.add(litNode(t[v] ? v : -v));
        const failing = [];
        f.clauses.forEach((c, j) => {
          const keep = occOf[j].find((id, p) => isTrue(t, c[p]));
          if (keep === undefined) { failing.push(j); for (const id of occOf[j]) { st.cover.add(id); st.bad.add(id); } }
          else for (const id of occOf[j]) if (id !== keep) st.cover.add(id); else st.out.add(id);
        });
        count();
        add({ items: scene({ fa: t }), say: 'No assignment satisfies this formula. Try the best one, ' + asText(f, t) + ': clause ' + failing.map((j) => j + 1).join(' and ') + ' has every literal false, so none of its occurrences may stay out (its links would be uncovered). The cover needs ' + st.cover.size + ' vertices, more than k = ' + R.k + '.', mark: 'rejected', hl: { def: [3] } }, clauseBox(failing[0]));
        const none = T.cx.findVertexCover(R.graph, R.k);
        add({ items: scene({ fa: t }), say: none ? 'A search found a cover anyway, which cannot happen.' : 'A search over every way to cover the edges confirms it: no vertex cover of size ' + R.k + ' exists, just as no assignment satisfies the formula. The reduction maps no to no.', mark: 'rejected' });
      }
      const k = R.k;
      return { frames: focusFrames(F.list, inp, m, clauseBox), def: { sections: [
        { id: 'def', kind: 'math', title: 'The construction', text: 'variable x: vertices x, ¬x and the edge x — ¬x\nclause: its occurrences joined in a triangle\nlink: each occurrence — the vertex of its literal\nk = n + Σ(|C| − 1) = ' + k + '\nforward: true literals, plus all but one true occurrence per clause\nbackward: x is true when vertex x is in the cover' },
        { id: 'size', kind: 'math', title: 'Size', text: R.graph.n + ' vertices, ' + R.graph.edges.length + ' edges: linear in the formula' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.clause === 0 && fr[i + 1].meta.keepable, once: true, pick: 'item', ask: 'Clause 1 may keep exactly one of its vertices out of the cover. Click a vertex that can stay out.', answer: (fr, i) => fr[i + 1].meta.keepable, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].mark === 'rejected' && /No assignment/.test(fr[i + 1].say), once: true, pick: 'option', options: ['Yes', 'No'], ask: 'This formula is unsatisfiable. Will the graph have a vertex cover of size k?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does each variable become an edge x — ¬x?', options: ['To make the graph connected', 'A cover must take an end of it, and with no budget to spare it takes exactly one: the true literal', 'Because x and ¬x are in the same clause', 'To count the variables'], answer: 1, why: 'The edge forces at least one end into the cover; k leaves room for only one, so the cover chooses a value.' },
      { q: 'A clause triangle has three vertices. How many of them must a cover take?', options: ['One', 'At least two', 'All three', 'None'], answer: 1, why: 'Each triangle edge needs an end in the cover, and one vertex cannot cover all three edges, so at least two are taken.' },
      { q: 'For 3 variables and 4 clauses of three literals, what is k?', options: ['7', '11', '15', '12'], answer: 1, why: 'k = n + 2m = 3 + 8 = 11: one per variable edge, two per clause triangle.' },
      { q: 'The occurrence of ¬y left out of a clause triangle: why must ¬y be true?', options: ['Its link edge must be covered by the other end, the vertex ¬y on top', 'Because it is the first literal', 'Triangles prefer negations', 'It need not be'], answer: 0, why: 'An occurrence outside the cover leaves its link uncovered unless the literal vertex above is in the cover, which means that literal is true.' },
      quizCommon.both,
    ],
  });

  // ============================================================================================================
  // 3SAT → SUBSET SUM
  // ============================================================================================================
  const SS_DEF = '(x ∨ y ∨ ¬z) ∧ (¬x ∨ ¬y ∨ z)';
  T.topic({
    id: 'cx-red-subsetsum', family: 'cx-red', order: 60, title: '3SAT → SUBSET SUM, digit by digit',
    blurb: 'Numbers written in decimal with one column per variable and one per clause. Picking the right rows makes every column add up to the target, and no column can ever carry.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (3-CNF)', def: SS_DEF, check: fcheck(4, 4) }],
    check: (inp) => { const f = T.sat.parse(inp.f); return f.n + f.clauses.length > 7 ? 'Formula: variables plus clauses at most 7, so the digits fit on the screen' : null; },
    presets: [
      { label: 'Two clauses, three variables', values: { f: SS_DEF } },
      { label: 'A literal twice: digit 2', values: { f: '(a ∨ a ∨ b) ∧ (¬a ∨ ¬b)' } },
      { label: 'A one-literal clause', values: { f: '(p) ∧ (¬p ∨ q ∨ r) ∧ (¬q ∨ ¬r)' } },
      { label: 'Unsatisfiable', values: { f: '(x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ y) ∧ (¬x ∨ ¬y)' } },
    ],
    counters: [{ id: 'rows', label: 'numbers' }, { id: 'digits', label: 'digits each' }, { id: 'chosen', label: 'chosen' }],
    run(inp) {
      const f = T.sat.parse(inp.f);
      const R = T.red.sat3ToSubsetSum(f);
      const n = f.n, m = f.clauses.length, D = n + m;
      const rows = R.table.rows;
      const head = (r) => r.role === 'true' ? r.label + ' (' + lit(f, r.var) + ' = 1)' : r.role === 'false' ? r.label + ' (' + lit(f, r.var) + ' = 0)' : r.label + ' (slack)';
      const F = new T.Frames(['rows', 'digits', 'chosen']);
      F.set('digits', D);
      // row heads grow leftwards, so the digit columns never move as rows are added
      const headW = (hs) => Math.max(40, ...hs.map((t) => T.geom.textWidth(t, 14, { bold: true }) + 22), T.geom.textWidth('number', 13, { bold: true }) + 18);
      const maxHead = headW(rows.map(head).concat(['target', 'sum']));
      const fBox = K.cx.formula({ f, labels: true, maxW: 330 }).box, labW = T.geom.textWidth('assignment', 13, { bold: true }) + 24;
      const tableView = { x: -maxHead - 16, y: -56, w: maxHead + D * 52 + 32, h: 34 + (rows.length + 2) * 33 + 76 };
      const colHead = R.table.columns.map((c, i) => (i < n ? c : 'C' + (i - n + 1)));
      const st = { shown: 0, target: false, chosen: new Set(), sum: new Array(D).fill(null), colHot: -1, a: null, faded: false, bad: new Set() };
      const scene = () => {
        const body = rows.slice(0, st.shown).map((r) => r.digits.map(String));
        const heads = rows.slice(0, st.shown).map(head);
        if (st.target) { body.push(R.table.targetDigits.map(String)); heads.push('target'); }
        if (st.sum.some((x) => x !== null)) { body.push(st.sum.map((x) => (x === null ? '' : String(x)))); heads.push('sum'); }
        const nT = st.shown + (st.target ? 1 : 0);
        const tb = K.table.draw({ rows: body, rowHead: heads, colHead, corner: 'number', mono: true, cw: 52, ch: 33, size: 16, x: -headW(heads), y: 0, prefix: 'ss',
          cls: (r, c, v) => {
            const out = [];
            if (r < st.shown) {
              if (st.chosen.has(r)) { if (v !== '0') out.push(c === st.colHot ? 'hot' : 'act'); }
              else if (st.faded) out.push('faded');
              if (v === '0') out.push('zero');
            } else if (r === st.shown && st.target) out.push('targetrow');
            else if (r === nT) { if (st.bad.has(c)) out.push('bad'); else if (st.sum[c] !== null) out.push(c === st.colHot ? 'hot' : 'good'); }
            if (c === st.colHot && r < st.shown && !st.chosen.has(r) && v !== '0') out.push('faded');
            return out.join(' ');
          } });
        let items = tb.items;
        const box = tb.box;
        // the column groups named above the header
        const hx = (c) => items.find((it) => it.key === 'ss:ch:' + c);
        items.push({ key: 'ss:gv', kind: 'bracket', x1: hx(0).x, x2: hx(n - 1).x + hx(n - 1).w, y: -6, side: 'above', text: 'variables' });
        items.push({ key: 'ss:gc', kind: 'bracket', x1: hx(n).x, x2: hx(D - 1).x + hx(D - 1).w, y: -6, side: 'above', text: 'clauses' });
        // the formula and the assignment stand to the right of the table, so the table can be drawn large
        const rx = D * 52 + 44;
        items = items.concat(K.cx.formula({ f, a: st.a, labels: true, maxW: 330, x: rx, y: -40 }).items);
        if (st.a) items = items.concat(K.cx.assignment({ f, a: st.a, label: 'assignment', x: rx + labW, y: fBox.h - 10 }).items);
        void box;
        return items;
      };
      // the header cells must exist before any row: build from a table with no rows yet
      F.add({ narrowView: tableView, items: scene(), say: 'Every number gets ' + D + ' decimal digits: one column for each of the ' + plural(n, 'variable') + ' and one for each of the ' + plural(m, 'clause') + '. A column never adds up to more than 5, so nothing ever carries into the next.', hl: { def: [0] } });
      for (let v = 1; v <= n; v++) {
        st.shown += 2; F.set('rows', st.shown);
        const y = rows[st.shown - 2], z = rows[st.shown - 1];
        const where = (r) => r.digits.slice(n).map((d, j) => (d ? 'C' + (j + 1) + (d > 1 ? ' (twice)' : '') : null)).filter(Boolean);
        const wy = where(y), wz = where(z);
        F.add({ narrowView: tableView, items: scene(), say: 'Variable ' + lit(f, v) + ': ' + y.label + ' (true) and ' + z.label + ' (false) both have 1 in column ' + lit(f, v) + '. In the clause columns ' + y.label + ' has a digit for each clause containing ' + lit(f, v) + (wy.length ? ' (' + wy.join(', ') + ')' : ' (none)') + ', and ' + z.label + ' for each containing ' + lit(f, -v) + (wz.length ? ' (' + wz.join(', ') + ')' : ' (none)') + '.' + (y.digits.concat(z.digits).some((d) => d > 1) ? ' A literal repeated in a clause gives the digit 2.' : ''), hl: { def: [1] } });
      }
      for (let j = 0; j < m; j++) {
        st.shown += 2; F.set('rows', st.shown);
        F.add({ narrowView: tableView, items: scene(), say: 'Clause ' + (j + 1) + ' gets two slack numbers g' + (j + 1) + ' and h' + (j + 1) + ', each with a single 1 in column C' + (j + 1) + '. Together they can add at most 2 there.', hl: { def: [2] } });
      }
      st.target = true;
      F.add({ narrowView: tableView, items: scene(), say: 'The target ' + R.target + ' has 1 in every variable column (pick exactly one of y and z) and 3 in every clause column. Slack gives at most 2, so each clause column needs at least one true literal.', hl: { def: [3] } });
      const a = satisfying(f);
      if (a) {
        const pick = R.forward(a);
        st.a = a; st.faded = true;
        for (const i of pick) if (rows[i].role !== 'slack') st.chosen.add(i);
        F.set('chosen', st.chosen.size);
        const trueCount = f.clauses.map((c) => c.filter((l) => isTrue(a, l)).length);
        const needTwo = trueCount.map((t, j) => (t === 1 ? 'ss:ch:' + (n + j) : null)).filter(Boolean);
        F.add({ narrowView: tableView, items: scene(), say: 'Forward: the assignment ' + asText(f, a) + ' picks y for each true variable and z for each false one: ' + [...st.chosen].map((i) => rows[i].label).join(', ') + '. In the clause columns they give ' + trueCount.map((t, j) => 'C' + (j + 1) + ': ' + t).join(', ') + '.', meta: { needTwo }, hl: { def: [4] } });
        for (const i of pick) st.chosen.add(i);
        F.set('chosen', st.chosen.size);
        F.add({ narrowView: tableView, items: scene(), say: 'Top every clause column up to 3 with slack: ' + trueCount.map((t, j) => 'C' + (j + 1) + ' takes ' + (3 - t) + ' slack').join(', ') + '. A clause with three true literals needs none.', hl: { def: [4] } });
        for (let c = D - 1; c >= 0; c--) {
          st.colHot = c;
          const parts = [...st.chosen].sort((x, y) => x - y).map((i) => rows[i].digits[c]).filter((d) => d > 0);
          st.sum[c] = parts.reduce((s, d) => s + d, 0);
          F.add({ narrowView: tableView, items: scene(), say: 'Column ' + colHead[c] + ': ' + (parts.length ? parts.join(' + ') : 'nothing') + ' = ' + st.sum[c] + ', and the target digit is ' + R.table.targetDigits[c] + '. No carry, so the next column starts fresh.', hl: { def: [c < n ? 1 : 3] } });
        }
        st.colHot = -1;
        const idx = [...st.chosen].sort((x, y) => x - y);
        const ok = T.cx.verifySubsetSum(R.nums, R.target, idx);
        F.add({ narrowView: tableView, items: scene(), say: 'The verifier adds the chosen numbers: ' + idx.map((i) => R.nums[i]).join(' + ') + ' = ' + idx.reduce((s, i) => s + R.nums[i], 0) + '. ' + (ok.ok ? 'That is the target.' : ok.reason), mark: ok.ok ? 'accepted' : 'rejected', hl: { def: [4] } });
        st.a = new Array(n + 1).fill(null);
        const b = R.backward(idx);
        F.add({ narrowView: tableView, items: scene(), say: 'Backward: from the chosen numbers alone, each variable column holds 1, so exactly one of its y and z was picked. Read the values off them.', hl: { def: [5] } });
        st.a = b;
        F.add({ narrowView: tableView, items: scene(), say: 'y picked means true: ' + asText(f, b) + '. And since slack gives at most 2 per clause column, every clause has a true literal: ' + (T.sat.evaluate(f, b) ? 'the formula is satisfied.' : 'something is wrong.'), mark: 'accepted', hl: { def: [5] } });
      } else {
        const t = nearest(f);
        st.a = t; st.faded = true;
        for (let i = 0; i < 2 * n; i++) if ((rows[i].role === 'true') === !!t[rows[i].var]) st.chosen.add(i);
        const trueCount = f.clauses.map((c) => c.filter((l) => isTrue(t, l)).length);
        f.clauses.forEach((c, j) => { const sl = rows.map((r, i) => (r.role === 'slack' && r.clause === j ? i : -1)).filter((i) => i >= 0); sl.slice(0, Math.max(0, 3 - trueCount[j])).forEach((i) => st.chosen.add(i)); });
        F.set('chosen', st.chosen.size);
        const failing = trueCount.map((x, j) => (x ? -1 : n + j)).filter((x) => x >= 0);
        F.add({ narrowView: tableView, items: scene(), say: 'No assignment satisfies this formula. Take the closest, ' + asText(f, t) + ', and both slack numbers in every clause column.', meta: { failing: failing.map((c) => 'ss:ch:' + c) }, hl: { def: [4] } });
        for (let c = 0; c < D; c++) st.sum[c] = [...st.chosen].reduce((s, i) => s + rows[i].digits[c], 0);
        for (const c of failing) st.bad.add(c);
        F.add({ narrowView: tableView, items: scene(), say: 'Column ' + failing.map((c) => colHead[c]).join(' and ') + ' adds up to only 2: no true literal, and the slack is used up. Since no column carries, no other column can make up the missing 1.', mark: 'rejected', hl: { def: [3] } });
        const none = T.cx.findSubsetSum(R.nums, R.target);
        F.add({ narrowView: tableView, items: scene(), say: none ? 'A search found a subset anyway, which cannot happen.' : 'A search over all sums of these ' + R.nums.length + ' numbers confirms that none reaches ' + R.target + '. Unsatisfiable maps to no.', mark: 'rejected' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'def', kind: 'math', title: 'The construction', text: 'columns: one per variable, one per clause, in base 10\ny_i, z_i: 1 in column x_i; in column C_j how often x_i (¬x_i) occurs in C_j\ng_j, h_j: a single 1 in column C_j\ntarget: 1 in each variable column, 3 in each clause column\nforward: y or z by value, then slack up to 3\nbackward: x_i is true when y_i is chosen' },
        { id: 'nums', kind: 'table', title: 'The numbers', colHead: ['value'], rowHead: rows.map((r) => r.label).concat(['target']), rows: R.nums.map((x) => [String(x)]).concat([[String(R.target)]]) },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.needTwo && fr[i + 1].meta.needTwo.length, once: true, pick: 'item', ask: 'Under the chosen rows, which clause column has only one true literal, and so needs both of its slack numbers? Click its header.', answer: (fr, i) => fr[i + 1].meta.needTwo, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.failing, once: true, pick: 'item', ask: 'With this assignment and all the slack, which column will fall short of the target? Click its header.', answer: (fr, i) => fr[i + 1].meta.failing, explain: (fr, i) => fr[i + 2] ? fr[i + 2].say : fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && /Top every clause column/.test(fr[i + 1].say || ''), once: true, pick: 'option', options: ['Yes, a column can reach 10', 'No, a column holds at most 5'], ask: 'Can adding these numbers ever carry from one column into the next?', answer: () => 'No, a column holds at most 5', explain: 'A clause column holds at most 3 literal digits plus 2 slack; a variable column at most 2. Nothing reaches 10.' },
    ],
    quiz: [
      { q: 'Why is base 10 safe here?', options: ['Base 10 is the usual base', 'No column can sum past 5, so there are no carries and each column is checked on its own', 'The numbers are small', 'Base 2 would also have no carries'], answer: 1, why: 'At most three literal digits and two slack digits meet in a clause column, at most two in a variable column; base 10 leaves room. In base 2 columns would carry and mix.' },
      { q: 'What does the 1 in a variable column of the target force?', options: ['Exactly one of y_i and z_i is chosen', 'Both are chosen', 'Neither', 'The slack'], answer: 0, why: 'Only y_i and z_i have a digit in that column, both 1, and the target is 1: exactly one is picked, which gives x_i a value.' },
      { q: 'Why does each clause have exactly two slack numbers, not three?', options: ['To save digits', 'With three, a clause with no true literal could still reach 3', 'Two is the clause length', 'It is arbitrary'], answer: 1, why: 'Slack makes up a shortfall of at most 2, so at least one of the 3 must come from a true literal.' },
      { q: 'The numbers have n + m digits. Is that polynomial in the size of the formula?', options: ['Yes: the number of digits is what counts, not the value', 'No: the values are exponential', 'Only for small n', 'Only in base 2'], answer: 0, why: 'Writing a number of n + m digits takes n + m symbols. Its value is exponential, which is why SUBSET SUM with numbers written in unary is easy.' },
      quizCommon.poly,
    ],
  });

  // ============================================================================================================
  // 3SAT → 3-COLOUR
  // ============================================================================================================
  const C3_DEF = '(x ∨ ¬y ∨ z) ∧ (¬x ∨ y)';
  /** Colourings of the OR gadget alone: inputs fixed to T or F, u, v, o free. Returns every valid (u, v, o) */
  function orColourings(cx, cy) {
    const out = [];
    for (let u = 0; u < 3; u++) for (let v = 0; v < 3; v++) for (let o = 0; o < 3; o++) if (u !== cx && v !== cy && u !== v && o !== u && o !== v) out.push([u, v, o]);
    return out;
  }
  T.topic({
    id: 'cx-red-3col', family: 'cx-red', order: 65, title: '3SAT → 3-COLOUR',
    blurb: 'A triangle fixes what the three colours mean, each variable is a pair of literals coloured true and false, and OR gadgets force each clause to contain a literal coloured true.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (3-CNF)', def: C3_DEF, check: fcheck(3, 2) }, focusInput(2), EDGES_INPUT],
    check: focusCheck,
    presets: [
      { label: 'Two clauses', values: { f: C3_DEF } },
      { label: 'One clause of three', values: { f: '(a ∨ b ∨ c)' } },
      { label: 'A repeated literal', values: { f: '(p ∨ p ∨ ¬q) ∧ (q)' } },
      { label: 'Unsatisfiable: (x) and (¬x)', values: { f: '(x) ∧ (¬x)' } },
    ],
    counters: [{ id: 'v', label: 'vertices' }, { id: 'e', label: 'edges' }, { id: 'col', label: 'coloured' }],
    run(inp) {
      const f = T.sat.parse(inp.f);
      const R = T.red.sat3To3Colour(f);
      const n = f.n, m = f.clauses.length;
      const N = R.draw.nodes, E = R.draw.edges;
      // Hand-placed on channels: the palette at the top right, the literal pairs in one row, each clause's two
      // OR gadgets in its own column band below the row, and the out — F and out — B edges run as straight
      // segments down, right along the bottom and up a lane on the right, so they never cross the gadgets.
      const BW = 300, Y1 = 150, Y2 = 228, GAP = 84;
      const Wb = (m - 1) * BW + 260, litW = (2 * n - 1) * GAP;
      const Wtot = Math.max(Wb, litW + 60, 300), lx0 = (Wtot - litW) / 2;
      const pos = {};
      pos[0] = { x: Wtot - 200, y: -228 }; pos[1] = { x: Wtot - 20, y: -228 }; pos[2] = { x: Wtot - 110, y: -148 };
      const posL = [], negL = [];
      for (let v = 1; v <= n; v++) { posL[v] = 3 + 2 * (v - 1); negL[v] = 4 + 2 * (v - 1); pos[posL[v]] = { x: lx0 + (2 * v - 2) * GAP, y: 0 }; pos[negL[v]] = { x: lx0 + (2 * v - 1) * GAP, y: 0 }; }
      const litNode = (l) => (l > 0 ? posL[l] : negL[-l]);
      const gad = [], inputs = [];
      f.clauses.forEach((c, j) => {
        const g = N.filter((x) => x.group === 'clause ' + (j + 1)).map((x) => x.id); // u1 v1 o1 u2 v2 out
        gad.push(g);
        const L = c.length === 3 ? c : c.length === 2 ? [c[0], c[1], c[1]] : [c[0], c[0], c[0]];
        inputs.push(L);
        const x0 = j * BW;
        // the first gadget's two middle vertices take their inputs in left-to-right order, so those two links do not cross
        const swap = pos[litNode(L[0])].x > pos[litNode(L[1])].x;
        pos[g[0]] = { x: x0 + (swap ? 100 : 20), y: Y1 }; pos[g[1]] = { x: x0 + (swap ? 20 : 100), y: Y1 };
        pos[g[2]] = { x: x0 + 60, y: Y2 }; pos[g[3]] = { x: x0 + 150, y: Y2 }; pos[g[4]] = { x: x0 + 200, y: Y1 }; pos[g[5]] = { x: x0 + 250, y: Y2 };
      });
      const label = (x) => (x.role === 'gadget-out' ? (gad.some((g) => g[5] === x.id) ? 'out' : 'o') : x.label);
      // the side channel: lane index 0 is the shallowest and nearest; the rightmost band takes the shallow lanes
      const lanes = [];
      f.clauses.forEach((c, j) => [1, 0].forEach((tgt) => {
        // tgt 1 = F, 2 = B; the left drop (to F) goes deeper and further out so the pair never cross
        const k = tgt === 1 ? 1 : 0;
        lanes.push({ j, tgt: tgt === 1 ? 1 : 2, L: 2 * (m - 1 - j) + k, dx: tgt === 1 ? -8 : 8 });
      }));
      const yBottom = Y2 + 48 + (2 * m - 1) * 15;
      const laneX = (L) => Wtot + 40 + L * 16;
      const into = { 1: lanes.filter((l) => l.tgt === 1).map((l) => l.L).sort((a, b) => a - b), 2: lanes.filter((l) => l.tgt === 2).map((l) => l.L).sort((a, b) => a - b) };
      const laneItems = (cls) => {
        const out = [];
        for (const l of lanes) {
          const o = pos[gad[l.j][5]], t = pos[l.tgt];
          const yb = Y2 + 48 + l.L * 15, xl = laneX(l.L);
          const idx = into[l.tgt].indexOf(l.L), dy = (idx - (into[l.tgt].length - 1) / 2) * 9;
          const ty = t.y + dy, tx = t.x + Math.sqrt(Math.max(0, 22 * 22 - dy * dy)) + 1;
          const x1 = o.x + l.dx, y1 = o.y + Math.sqrt(22 * 22 - l.dx * l.dx) + 1;
          const c = 'lane ' + (cls(l) || '');
          const K0 = 'c3:ln:' + l.j + ':' + l.tgt + ':';
          out.push({ key: K0 + 0, kind: 'line', x1, y1, x2: x1, y2: yb, cls: c, audit: 'edge-x' });
          out.push({ key: K0 + 1, kind: 'line', x1, y1: yb, x2: xl, y2: yb, cls: c, audit: 'edge-x' });
          out.push({ key: K0 + 2, kind: 'line', x1: xl, y1: yb, x2: xl, y2: ty, cls: c, audit: 'edge-x' });
          out.push({ key: K0 + 3, kind: 'line', x1: xl, y1: ty, x2: tx, y2: ty, cls: c, audit: 'edge-x' });
        }
        return out;
      };
      const ek = (e) => e.a + '>' + e.b;
      const edgeClause = (e) => { const j = gad.findIndex((g) => g.includes(e.b) || g.includes(e.a)); return j < 0 ? undefined : j; };
      const mainFull = { nodes: N.map((x) => ({ id: x.id, label: label(x), role: x.role === 'literal' ? 'var' : 'plain', x: pos[x.id].x, y: pos[x.id].y })), edges: E.filter((e) => e.role !== 'force') };
      // the formula and the assignment sit at the top left, beside the palette, when there is room
      const room = pos[0].x - 22 - 30;
      const fProbe = K.cx.formula({ f, maxW: Math.max(room, 200) });
      const fLeft = fProbe.box.w <= room;
      const fTop = fLeft ? -292 : -300 - fProbe.box.h;
      const cW = K.cx.assignment({ f }).box.w;
      const cLeft = fLeft && fProbe.box.h <= 60 && 100 + cW <= room;
      const MINI = { mx: { x: 40, y: 0 }, my: { x: 220, y: 0 }, mu: { x: 40, y: Y1 }, mv: { x: 220, y: Y1 }, mo: { x: 130, y: Y2 } };
      const bandBox = (j) => ({ x: j * BW - 40, y: -40, w: 340, h: yBottom + 80 });
      const paletteBox = ptsBox([pos[0], pos[1], pos[2]].concat(posL.slice(1).map((id) => pos[id]), negL.slice(1).map((id) => pos[id])), 40, 50);
      const miniBox = ptsBox(Object.values(MINI).concat([pos[2], { x: MINI.mo.x, y: Y2 + 70 }]), 50, 40);
      const F = new T.Frames(['v', 'e', 'col']);
      const st = { nodes: new Set(), edges: new Set(), col: {}, a: null, badE: new Set(), mini: null, lanes: new Set() };
      const scene = (opts) => {
        opts = opts || {};
        const only = inp.edges === 'clause' && opts.clause !== undefined;
        const fade = (j) => (only && j !== opts.clause ? 'faded' : '');
        let nodes = N.filter((x) => st.nodes.has(x.id)).map((x) => ({ id: x.id, label: label(x), role: x.role === 'literal' ? 'var' : 'plain', x: pos[x.id].x, y: pos[x.id].y, cls: st.col[x.id] !== undefined ? COL[st.col[x.id]] : '' }));
        let edges = E.filter((e) => e.role !== 'force' && st.edges.has(ek(e))).map((e) => ({ a: e.a, b: e.b, cls: fade(edgeClause(e)) }));
        let full = mainFull;
        if (st.mini) {
          const M = st.mini;
          const lab = { mx: 'in₁', my: 'in₂', mu: 'u', mv: 'v', mo: 'o' };
          for (const id of Object.keys(MINI)) nodes.push({ id, label: lab[id], role: id === 'mx' || id === 'my' ? 'var' : 'plain', x: MINI[id].x, y: MINI[id].y, cls: M.col[id] !== undefined ? COL[M.col[id]] : '' });
          edges = edges.concat([['mx', 2], ['my', 2], ['mx', 'mu'], ['my', 'mv'], ['mu', 'mv'], ['mu', 'mo'], ['mv', 'mo']].map(([a, b]) => ({ a, b })));
          full = { nodes, edges };
        }
        let items = gdraw({ nodes, edges, prefix: 'c3', size: 18, full, straight: true }).items;
        if (!st.mini) {
          items = items.concat(laneItems((l) => (st.badE.has(gad[l.j][5] + '>' + l.tgt) ? 'bad' : fade(l.j))).filter((it) => st.lanes.has(+it.key.split(':')[2])));
          for (const [j] of gad.entries()) if (st.nodes.has(gad[j][0])) items.push({ key: 'c3:cl:' + j, kind: 'text', x: j * BW + 130, y: yBottom + 30, text: 'clause ' + (j + 1) + ': (' + f.clauses[j].map((l) => lit(f, l)).join(' ∨ ') + ')', anchor: 'middle', cls: 'title' });
        }
        if (st.mini && st.mini.note) items.push({ key: 'c3:mn', kind: 'text', x: MINI.mo.x, y: Y2 + 56, text: st.mini.note, anchor: 'middle', cls: st.mini.noteCls || 'strong', size: 16 });
        items = items.concat(K.cx.formula({ f, a: opts.fa || null, maxW: fLeft ? room : 640, x: fLeft ? 0 : Wtot / 2 - fProbe.box.w / 2, y: fTop }).items);
        if (st.a) items = items.concat(K.cx.assignment({ f, a: st.a, label: 'assignment', x: cLeft ? 100 : Wtot / 2 - cW / 2, y: cLeft ? -212 : yBottom + 52 }).items);
        return items;
      };
      const add = (fr, about) => { fr.narrowView = about || paletteBox; return F.add(fr); };
      const count = () => { F.set('v', st.nodes.size + (st.mini ? 5 : 0)).set('e', st.edges.size + 2 * st.lanes.size + (st.mini ? 7 : 0)).set('col', Object.keys(st.col).length); };
      add({ items: scene(), say: 'The formula ' + ftext(f) + '. We build a graph that can be coloured with three colours exactly when the formula can be satisfied.' });
      [0, 1, 2].forEach((id) => st.nodes.add(id));
      for (const e of E) if (e.role === 'palette') st.edges.add(ek(e));
      st.col = { 0: 0, 1: 1, 2: 2 };
      count();
      add({ items: scene(), say: 'The palette: a triangle T, F, B. Its three corners need three different colours, so we simply call the colours by their names: true, false and base.', hl: { def: [0] } });
      for (let v = 1; v <= n; v++) {
        st.nodes.add(posL[v]); st.nodes.add(negL[v]);
        for (const e of E) if (e.role === 'variable' && (e.a === posL[v] || e.a === negL[v])) st.edges.add(ek(e));
        count();
        add({ items: scene(), say: 'Variable ' + lit(f, v) + ': the literals ' + lit(f, v) + ' and ' + lit(f, -v) + ' are joined to each other and to B, so one is coloured T and the other F: a value.', hl: { def: [1] } });
      }
      // the OR gadget on its own, for all four inputs
      const savedNodes = new Set(st.nodes), savedEdges = new Set(st.edges);
      st.nodes = new Set([0, 1, 2]); st.edges = new Set(E.filter((e) => e.role === 'palette').map(ek));
      const combos = [[1, 1], [0, 1], [1, 0], [0, 0]];
      st.mini = { col: { mx: 1, my: 1 }, note: 'an OR gadget on its own' };
      count();
      add({ items: scene(), say: 'Before the clauses, one OR gadget on its own: inputs in₁ and in₂ (each T or F, being joined to B), two middle vertices u and v joined to each other, and an output o joined to both.', hl: { def: [2] }, meta: { orFF: true } }, miniBox);
      combos.forEach(([x, y]) => {
        const all = orColourings(x, y);
        const outs = [...new Set(all.map((c) => c[2]))].sort();
        const show = all.find((c) => c[2] === 0) || all[0];
        st.mini = { col: { mx: x, my: y, mu: show[0], mv: show[1], mo: show[2] }, note: 'o can be ' + outs.map((c) => CNAME[c]).join(' or '), noteCls: outs.includes(0) ? 'good' : 'bad' };
        add({ items: scene(), say: x === 1 && y === 1 ? 'Inputs F and F: u and v must avoid F and each other, so they are T and B, and o, beside both, can only be F. False or false is false.' : 'Inputs ' + CNAME[x] + ' and ' + CNAME[y] + ': u and v can be chosen so that o is T (o can be ' + outs.map((c) => CNAME[c]).join(' or ') + '). A true input lets the output be true.', meta: { mini: true }, hl: { def: [2] } }, miniBox);
      });
      st.mini = null; st.nodes = savedNodes; st.edges = savedEdges; st.col = { 0: 0, 1: 1, 2: 2 };
      f.clauses.forEach((c, j) => {
        const g = gad[j], L = inputs[j];
        [g[0], g[1], g[2]].forEach((id) => st.nodes.add(id));
        for (const e of E) if (e.role === 'gadget' && [g[0], g[1], g[2]].includes(e.b)) st.edges.add(ek(e));
        count();
        add({ items: scene({ clause: j }), say: 'Clause ' + (j + 1) + ': a first OR gadget takes ' + lit(f, L[0]) + ' and ' + lit(f, L[1]) + '; its output o can be T only if one of them is T.' + (c.length < 3 ? ' The clause is short, so a literal is fed in twice.' : ''), meta: { clause: j }, hl: { def: [3] } }, bandBox(j));
        [g[3], g[4], g[5]].forEach((id) => st.nodes.add(id));
        for (const e of E) if (e.role === 'gadget' && g.slice(3).includes(e.b)) st.edges.add(ek(e));
        st.lanes.add(j);
        count();
        add({ items: scene({ clause: j }), say: 'A second OR gadget takes that o and ' + lit(f, L[2]) + '. Its output, out, is joined to F and B (the two edges run round the side), so it must be T: possible only if some literal of the clause is T.', meta: { clause: j }, hl: { def: [3, 4] } }, bandBox(j));
      });
      const a = satisfying(f);
      if (a) {
        st.a = a;
        const col = R.forward(a);
        for (let v = 1; v <= n; v++) { st.col[posL[v]] = col[posL[v]]; st.col[negL[v]] = col[negL[v]]; }
        count();
        add({ items: scene({ fa: a }), say: 'Forward: take ' + asText(f, a) + '. Colour each true literal T and each false one F.', hl: { def: [5] } });
        f.clauses.forEach((c, j) => {
          for (const id of gad[j]) st.col[id] = col[id];
          count();
          add({ items: scene({ fa: a, clause: j }), say: 'Clause ' + (j + 1) + ' has a true literal, so its gadgets can be coloured with out = T: u, v and o get ' + gad[j].slice(0, 5).map((id) => CNAME[col[id]]).join(', ') + '.', meta: { clause: j }, hl: { def: [5] } }, bandBox(j));
        });
        const ok = T.cx.verifyColouring(R.graph, 3, col);
        add({ items: scene({ fa: a }), say: 'The verifier checks all ' + R.graph.edges.length + ' edges: ' + (ok.ok ? 'the two ends of every edge differ. A proper 3-colouring.' : ok.reason), mark: ok.ok ? 'accepted' : 'rejected', hl: { def: [5] } });
        st.a = new Array(n + 1).fill(null);
        add({ items: scene(), say: 'Backward: given only a 3-colouring, call the colour of corner T "true".', hl: { def: [6] } });
        const b = R.backward(col);
        st.a = b;
        add({ items: scene({ fa: b }), say: 'A literal is true when it has the colour of T: ' + asText(f, b) + '. Every out vertex is T, so every clause has a T literal: ' + (T.sat.evaluate(f, b) ? 'the formula is satisfied.' : 'something is wrong.'), mark: 'accepted', hl: { def: [6] } });
      } else {
        const t = nearest(f);
        st.a = t;
        for (let v = 1; v <= n; v++) { st.col[posL[v]] = t[v] ? 0 : 1; st.col[negL[v]] = t[v] ? 1 : 0; }
        count();
        add({ items: scene({ fa: t }), say: 'No assignment satisfies this formula. Try ' + asText(f, t) + ' and colour the literals.', hl: { def: [5] } });
        // colour each gadget, ignoring the out vertex's edges to F and B, and look at what out is forced to
        const adj = new Map();
        for (const e of E) if (e.role !== 'force') { for (const [x, y] of [[e.a, e.b], [e.b, e.a]]) { if (!adj.has(x)) adj.set(x, []); adj.get(x).push(y); } }
        const failing = [];
        f.clauses.forEach((c, j) => {
          const g = gad[j];
          const search = (list, extra) => { const gi = (i) => { if (i === list.length) return extra(); for (let k = 0; k < 3; k++) { if ((adj.get(list[i]) || []).some((u) => st.col[u] === k)) continue; st.col[list[i]] = k; if (gi(i + 1)) return true; } delete st.col[list[i]]; return false; }; return gi(0); };
          // prefer out = T when it can be had
          const saved = Object.assign({}, st.col);
          st.col[g[5]] = 0;
          if (!search(g.slice(0, 5), () => !(adj.get(g[5]) || []).some((u) => st.col[u] === 0))) {
            st.col = saved;
            search(g, () => true);
            failing.push(j);
            for (const tgt of [1, 2]) if (st.col[tgt] === st.col[g[5]]) st.badE.add(g[5] + '>' + tgt);
          }
        });
        count();
        add({ items: scene({ fa: t, clause: failing[0] }), say: 'Clause ' + failing.map((j) => j + 1).join(' and ') + ' has only F inputs, so its gadgets force out to be F, but out is joined to F: the edge in red clashes. Changing the assignment only moves the clash to the other clause.', meta: { clause: failing[0] }, mark: 'rejected', hl: { def: [4] } }, bandBox(failing[0]));
        const none = T.cx.findColouring(R.graph, 3);
        add({ items: scene({ fa: t }), say: none ? 'A search found a colouring anyway, which cannot happen.' : 'A search through every colouring of the ' + R.graph.n + ' vertices confirms: no proper 3-colouring exists. Unsatisfiable maps to no.', mark: 'rejected' });
      }
      return { frames: focusFrames(F.list, inp, m, bandBox), def: { sections: [
        { id: 'def', kind: 'math', title: 'The construction', text: 'palette: a triangle T — F — B\nvariable: x — ¬x, both joined to B (one T, one F)\nOR gadget: inputs a, b; a — u, b — v, u — v, u — o, v — o\nclause (a ∨ b ∨ c): OR(OR(a, b), c) = out\nout — F and out — B: out must be T\nforward: literals by value, gadgets by search\nbackward: x is true when x has T\'s colour' },
        { id: 'size', kind: 'math', title: 'Size', text: '3 + 2n + 6m = ' + R.graph.n + ' vertices, ' + R.graph.edges.length + ' edges' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i] && fr[i].meta && fr[i].meta.orFF, once: true, pick: 'item', ask: 'Both inputs will be F. Which colour is the output o then forced to take? Click that corner of the palette.', answer: () => 'c3:v:1', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && /forced|force out/.test(fr[i + 1].say || '') && fr[i + 1].mark === 'rejected', once: true, pick: 'option', options: ['T', 'F', 'B'], ask: 'This clause has only false literals. What colour must its out vertex take?', answer: () => 'F', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does the palette triangle T, F, B do?', options: ['Nothing: it is decoration', 'It forces three different colours, giving them fixed meanings to compare against', 'It counts the variables', 'It is the first clause'], answer: 1, why: 'Colours have no names; the triangle uses all three and every other vertex is read relative to it.' },
      { q: 'Why is each literal joined to B?', options: ['So a literal is coloured T or F, never B', 'To make the graph connected', 'Because B means both', 'So x and ¬x share a colour'], answer: 0, why: 'A literal next to B cannot be B; with x — ¬x as well, one is T and the other F.' },
      { q: 'In an OR gadget with both inputs F, what colour must o take?', options: ['T', 'F', 'B', 'Any'], answer: 1, why: 'u and v avoid F and each other, so they are T and B; o touches both and must be F.' },
      { q: 'Why is out joined to both F and B?', options: ['To force out to be T', 'To force out to be F', 'To join clauses', 'It is a mistake'], answer: 0, why: 'A vertex next to F and B can only be T, which an OR chain allows only when some input is T.' },
      quizCommon.both,
    ],
  });

  // ============================================================================================================
  // 3SAT → HAM-PATH
  // ============================================================================================================
  const HP_DEF = '(x ∨ ¬y) ∧ (¬x ∨ y)';
  T.topic({
    id: 'cx-red-hampath', family: 'cx-red', order: 70, title: '3SAT → HAM-PATH',
    blurb: 'Each variable is a row the path must cross, left to right for true or right to left for false. A clause is a vertex reached by a short detour, open only to a crossing in a direction that makes one of its literals true.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (tiny)', def: HP_DEF, check: fcheck(2, 2) }],
    presets: [
      { label: 'Two variables, two clauses', values: { f: HP_DEF } },
      { label: 'One clause, both true', values: { f: '(x ∨ y)' } },
      { label: 'A clause on one variable', values: { f: '(¬p) ∧ (p ∨ q)' } },
      { label: 'Unsatisfiable: (x) and (¬x)', values: { f: '(x) ∧ (¬x)' } },
    ],
    counters: [{ id: 'v', label: 'vertices' }, { id: 'e', label: 'edges' }, { id: 'p', label: 'path length' }],
    run(inp) {
      const f = T.sat.parse(inp.f);
      const R = T.red.sat3ToHamPath(f);
      const n = f.n, m = f.clauses.length;
      const N = R.draw.nodes, E = R.draw.edges;
      const GX = 82, rowLen = 3 * m + 1, Wd = (rowLen - 1) * GX, cx = Wd / 2, RY = 250;
      const pos = {}, vars = [];
      for (let i = 0; i < n; i++) {
        const g = N.filter((x) => x.group === 'x' + (i + 1));
        const t = g[0], b = g[g.length - 1], row = g.slice(1, -1);
        vars.push({ t: t.id, b: b.id, row: row.map((x) => x.id) });
        pos[t.id] = { x: cx, y: i * RY - 76 };
        row.forEach((x, k) => { pos[x.id] = { x: k * GX, y: i * RY }; });
        pos[b.id] = { x: cx, y: i * RY + 76 };
      }
      const clauseIds = N.filter((x) => x.role === 'clause').map((x) => x.id);
      clauseIds.forEach((id, j) => {
        let x = (1.5 + 3 * j) * GX;
        if (Math.abs(x - cx) < 60) x += 110;
        pos[id] = { x, y: n > 1 ? RY / 2 : 150 };
      });
      const label = (x) => (x.role === 'separator' || x.role === 'left' || x.role === 'right' ? x.label.replace(/\d+\./, '') : x.label);
      const F = new T.Frames(['v', 'e', 'p']);
      const st = { nodes: new Set(), edges: new Set(), path: [], a: null, bad: new Set() };
      const ek = (e) => e.a + '>' + e.b;
      const scene = (opts) => {
        opts = opts || {};
        const on = new Set();
        for (let i = 0; i + 1 < st.path.length; i++) on.add(st.path[i] + '>' + st.path[i + 1]);
        const inPath = new Set(st.path);
        const nodes = N.filter((x) => st.nodes.has(x.id)).map((x) => ({ id: x.id, label: label(x), role: x.role === 'clause' ? 'clause' : x.role === 'top' || x.role === 'bottom' ? 'var' : 'plain', group: x.role === 'clause' ? undefined : x.group, x: pos[x.id].x, y: pos[x.id].y, cls: st.bad.has(x.id) ? 'bad' : x.id === st.path[st.path.length - 1] && opts.head ? 'hot' : '' }));
        const edges = E.filter((e) => st.edges.has(ek(e))).map((e) => ({ a: e.a, b: e.b, cls: on.has(ek(e)) ? 'cert' : st.path.length ? 'faded' : '' }));
        const groups = vars.map((v, i) => ({ id: 'x' + (i + 1), label: 'row of ' + lit(f, i + 1) }));
        const full = { nodes: N.map((x) => ({ id: x.id, label: label(x), role: 'plain', group: x.role === 'clause' ? undefined : x.group, x: pos[x.id].x, y: pos[x.id].y })), edges: E, groups };
        let items = gdraw({ nodes, edges, groups, directed: true, cert: [...inPath], prefix: 'hp', size: 17, full }).items;
        // the formula and the assignment side by side in one band over the rows
        items = items.concat(K.cx.formula({ f, a: opts.fa || null, labels: true, maxW: 520, x: topX, y: -146 - fB.h }).items);
        if (st.a) items = items.concat(K.cx.assignment({ f, a: st.a, label: 'assignment', x: topX + fB.w + 40 + labW, y: -146 - 60 }).items);
        return items;
      };
      const fB = K.cx.formula({ f, labels: true, maxW: 520 }).box, cW = K.cx.assignment({ f }).box.w, labW = T.geom.textWidth('assignment', 13, { bold: true }) + 24;
      const topX = cx - (fB.w + 40 + labW + cW) / 2;
      const rowBox = (i) => ptsBox([vars[i].t, vars[i].b].concat(vars[i].row).map((id) => pos[id]), 40, 60);
      const allBox = ptsBox(Object.values(pos), 40, 60);
      const clauseBox = (j) => ptsBox([pos[clauseIds[j]]].concat(E.filter((e) => e.role === 'detour' && (e.a === clauseIds[j] || e.b === clauseIds[j])).map((e) => pos[e.a === clauseIds[j] ? e.b : e.a])), 60, 60);
      let about = allBox;
      const add = (fr) => { fr.narrowView = about; return F.add(fr); };
      const count = () => { F.set('v', st.nodes.size).set('e', st.edges.size).set('p', st.path.length); };
      add({ items: scene(), say: 'The formula ' + ftext(f) + '. We build a directed graph with a path through every vertex exactly when the formula can be satisfied.' });
      vars.forEach((v, i) => {
        [v.t, v.b, ...v.row].forEach((id) => st.nodes.add(id));
        for (const e of E) if ((e.role === 'enter' || e.role === 'exit' || e.role === 'row') && st.nodes.has(e.a) && st.nodes.has(e.b)) st.edges.add(ek(e));
        count();
        about = rowBox(i);
        add({ items: scene(), say: 'Variable ' + lit(f, i + 1) + ': a row of ' + v.row.length + ' vertices with arrows both ways, a top t' + (i + 1) + ' leading into either end and a bottom b' + (i + 1) + ' reached from either end. Left to right will mean true, right to left false.', hl: { def: [0] } });
      });
      if (n > 1) {
        for (const e of E) if (e.role === 'link') st.edges.add(ek(e));
        count();
        about = allBox;
        add({ items: scene(), say: 'Chain the rows: b1 → t2. A path from t1 to b' + n + ' must go down through every row in turn, crossing each one exactly once.', hl: { def: [1] } });
      }
      f.clauses.forEach((c, j) => {
        st.nodes.add(clauseIds[j]);
        for (const e of E) if (e.role === 'detour' && (e.a === clauseIds[j] || e.b === clauseIds[j])) st.edges.add(ek(e));
        count();
        about = clauseBox(j);
        add({ items: scene(), say: 'Clause ' + (j + 1) + ', (' + c.map((l) => lit(f, l)).join(' ∨ ') + '), is the vertex c' + (j + 1) + '. ' + c.map((l) => (l > 0 ? 'From row ' + lit(f, l) + ' the detour p → c' + (j + 1) + ' → q points right: a left-to-right (true) crossing can take it.' : 'From row ' + lit(f, -l) + ' the detour q → c' + (j + 1) + ' → p points left: a right-to-left (false) crossing can take it.')).filter((s, k, arr) => arr.indexOf(s) === k).join(' '), hl: { def: [2] } });
      });
      about = allBox;
      add({ items: scene(), say: 'Ask for a Hamiltonian path from t1 to b' + n + ' through all ' + R.graph.n + ' vertices. Every clause vertex must be picked up by some detour.', hl: { def: [3] } });
      const a = satisfying(f);
      const owner = (asg) => f.clauses.map((c) => { const l = c.find((x) => isTrue(asg, x)); return l === undefined ? null : Math.abs(l); });
      if (a) {
        st.a = a;
        const path = R.forward(a);
        const first = vars[0].row[a[1] ? 0 : vars[0].row.length - 1];
        add({ items: scene({ fa: a }), say: 'Forward: take ' + asText(f, a) + '. Each clause is visited from the row of its first true literal: ' + owner(a).map((v, j) => 'c' + (j + 1) + ' from row ' + lit(f, v)).join(', ') + '.', meta: { first: 'hp:v:' + first }, hl: { def: [4] } });
        // add the path in pieces that end at a clause visit or at a bottom vertex
        let k = 1;
        st.path = [path[0]];
        while (k < path.length) {
          const startK = k;
          while (k < path.length && N[path[k]].role !== 'clause' && N[path[k]].role !== 'bottom') k++;
          if (k < path.length) k++;
          st.path = path.slice(0, k);
          count();
          const end = N[path[k - 1]];
          const vi = vars.findIndex((v) => v.t === path[startK] || v.row.includes(path[startK]));
          let say;
          if (end.role === 'clause') say = 'Detour: from ' + label(N[path[k - 2]]) + ' in row ' + lit(f, vi + 1) + ' to ' + end.label + ' and straight back to the next vertex of the row, picking up clause ' + end.label.slice(1) + '.';
          else say = 'Row ' + lit(f, vi + 1) + ' is crossed ' + (a[vi + 1] ? 'left to right (' + lit(f, vi + 1) + ' = 1)' : 'right to left (' + lit(f, vi + 1) + ' = 0)') + ', every vertex of it taken, and the path drops to ' + end.label + (vi + 1 < n ? ', then on to t' + (vi + 2) + '.' : ', the end.');
          about = end.role === 'clause' ? clauseBox(clauseIds.indexOf(end.id)) : rowBox(vi);
          add({ items: scene({ fa: a, head: true }), say, hl: { def: [4] } });
        }
        about = allBox;
        const ok = T.cx.verifyHamPath(R.graph, path, R.s, R.t);
        add({ items: scene({ fa: a }), say: 'The verifier checks the path: ' + path.length + ' vertices, each once, from t1 to b' + n + ', every step an edge. ' + (ok.ok ? 'A Hamiltonian path.' : ok.reason), mark: ok.ok ? 'accepted' : 'rejected', hl: { def: [4] } });
        st.a = new Array(n + 1).fill(null);
        add({ items: scene(), say: 'Backward: start from the path alone and look at how it enters each row.', hl: { def: [5] } });
        const b = R.backward(path);
        st.a = b;
        add({ items: scene({ fa: b }), say: 'Entering at the left end means true: ' + asText(f, b) + '. Each clause vertex was reached by a detour that only a true literal\'s crossing can make, so ' + (T.sat.evaluate(f, b) ? 'the formula is satisfied.' : 'something is wrong.'), mark: 'accepted', hl: { def: [5] } });
      } else {
        const t = nearest(f);
        st.a = t;
        const path = R.forward(t);
        st.path = path;
        const missed = clauseIds.filter((id) => !path.includes(id));
        missed.forEach((id) => st.bad.add(id));
        count();
        add({ items: scene({ fa: t }), say: 'No assignment satisfies this formula. Try ' + asText(f, t) + ': crossing the rows that way picks up ' + (clauseIds.length - missed.length ? 'some clauses' : 'no clause') + ', but ' + missed.map((id) => N[id].label).join(' and ') + ' can only be reached by a crossing in the other direction.', meta: { missed: missed.map((id) => 'hp:v:' + id) }, mark: 'rejected', hl: { def: [3] } });
        let none = null;
        try { none = T.cx.findHamPath(R.graph, R.s, R.t, { maxNodes: 2e5 }); } catch (e) { none = null; }
        add({ items: scene({ fa: t }), say: none ? 'A search found a path anyway, which cannot happen.' : 'A search through every path from t1 confirms: no Hamiltonian path exists. Unsatisfiable maps to no.', mark: 'rejected' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'def', kind: 'math', title: 'The construction', text: 'variable x_i: t_i, a two-way row s0 p1 q1 s1 … pm qm sm, b_i\nrows chained: b_i → t_(i+1)\nclause C_j: vertex c_j; x_i in C_j: p_ij → c_j → q_ij; ¬x_i: q_ij → c_j → p_ij\npath from t1 to b_n through all vertices\nforward: cross rows by value, detour at the first true literal\nbackward: entering a row at the left means true' },
        { id: 'size', kind: 'math', title: 'Size', text: R.graph.n + ' vertices, ' + R.graph.edges.length + ' arrows' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i] && fr[i].meta && fr[i].meta.first, once: true, pick: 'item', ask: 'Which vertex of the first row does the path enter first? Click it.', answer: (fr, i) => fr[i].meta.first, explain: 'The row is entered at its left end when the variable is true, at its right end when false.' },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.missed, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'This formula is unsatisfiable. Can some cleverer path still visit every vertex?', answer: () => 'No', explain: (fr, i) => fr[i + 2] ? fr[i + 2].say : fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does crossing a row from left to right mean?', options: ['The variable is true', 'The variable is false', 'The clause is satisfied', 'Nothing'], answer: 0, why: 'By construction left to right is true; the clause detours are oriented to match.' },
      { q: 'Why is there a separator vertex between the pairs of a row?', options: ['Decoration', 'So detours of different clauses cannot be combined into a path that jumps between them illegally', 'To make the row longer', 'To count steps'], answer: 1, why: 'Without separators a path could leave a row by one detour and come back through another clause, skipping vertices in a way no crossing direction explains.' },
      { q: 'A clause vertex c_j has no detour to the row of x in the right direction. When is it unreachable?', options: ['When every literal of the clause is false under the crossing directions', 'Always', 'Never', 'When x is true'], answer: 0, why: 'Each detour fits only a crossing that makes its literal true; with all literals false, no crossing can visit c_j.' },
      { q: 'How big is the graph for n variables and m clauses?', options: ['Exponential in n', 'n(3m + 3) + m vertices: polynomial', 'm² vertices', 'n + m vertices'], answer: 1, why: 'Each row has 3m + 1 vertices plus a top and a bottom, and there is one vertex per clause.' },
      quizCommon.poly,
    ],
  });
})();
