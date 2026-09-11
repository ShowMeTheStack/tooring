// Reductions as gadgets, part one: SAT → 3SAT (long clauses become chains, short ones are padded),
// 3SAT → CLIQUE and 3SAT → INDEPENDENT SET (a vertex per literal, grown out of the formula clause by
// clause), and the triangle INDEPENDENT SET ↔ VERTEX COVER ↔ CLIQUE by complements. Each picture builds
// the target instance piece by piece, then carries a certificate forward (assignment → vertices) and back.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'cx-red', part: 'complexity', order: 50, title: 'Reductions as gadgets', blurb: 'Turn one problem into another in polynomial time, piece by piece, and carry every certificate across in both directions.' });

  // ---- shared helpers ---------------------------------------------------------------------------------------
  const lt = (f, l) => T.sat.litText(f, l);
  const isTrue = (a, l) => (l > 0 ? !!a[l] : !a[-l]);
  const bit = (b) => (b ? '1' : '0');
  const plural = (n, w, ws) => n + ' ' + (n === 1 ? w : ws || w + 's');
  const clauseText = (f, c) => '(' + c.map((l) => lt(f, l)).join(' ∨ ') + ')';
  const listVals = (f, a, n) => { const out = []; for (let v = 1; v <= (n || f.n); v++) if (a[v] !== null && a[v] !== undefined) out.push(lt(f, v) + ' = ' + bit(a[v])); return out.join(', '); };

  /** Read a formula for a topic, or say kindly what is wrong with it */
  function readFormula(v, lim) {
    let f;
    try { f = T.sat.parse(v); } catch (e) { return { err: 'Formula: ' + e.message + '. Write clauses like (a ∨ ¬b) ∧ (b ∨ c); ¬, ~ or ! negate.' }; }
    if (!f.clauses.length) return { err: 'Formula: write at least one clause, like (a ∨ b)' };
    const long = f.clauses.findIndex((c) => c.length > lim.len);
    if (long >= 0) return { err: 'Formula: clause ' + (long + 1) + ' has ' + f.clauses[long].length + ' literals; here a clause has at most ' + lim.len };
    if (f.clauses.length > lim.clauses) return { err: 'Formula: at most ' + lim.clauses + ' clauses, so the picture stays readable' };
    if (f.n > lim.vars) return { err: 'Formula: at most ' + lim.vars + ' variables, so the picture stays readable' };
    return { f };
  }
  /** Every satisfying assignment would be too many; the first and the last in counting order are enough */
  function lastSat(f) {
    const a = new Array(f.n + 1).fill(false);
    for (let m = 2 ** f.n - 1; m >= 0; m--) { for (let v = 1; v <= f.n; v++) a[v] = !!(m & (1 << (v - 1))); if (T.sat.evaluate(f, a)) return a.slice(); }
    return null;
  }
  /** The assignment satisfying the most clauses (the closest miss of an unsatisfiable formula) */
  function bestMiss(f) {
    let best = null, bs = -1;
    const a = new Array(f.n + 1).fill(false);
    for (let m = 0; m < 2 ** f.n; m++) { for (let v = 1; v <= f.n; v++) a[v] = !!(m & (1 << (v - 1))); const s = f.clauses.filter((c) => T.sat.evalClause(c, a)).length; if (s > bs) { bs = s; best = a.slice(); } }
    return best;
  }

  // =========================================================================================================
  // SAT → 3SAT
  // =========================================================================================================
  const RULES3 = [
    '(ℓ₁ ∨ ℓ₂ ∨ ℓ₃) stays as it is',
    '(ℓ₁ ∨ ℓ₂) → (ℓ₁ ∨ ℓ₂ ∨ y) ∧ (ℓ₁ ∨ ℓ₂ ∨ ¬y)',
    '(ℓ) → (ℓ ∨ y ∨ y′), (ℓ ∨ y ∨ ¬y′), (ℓ ∨ ¬y ∨ y′), (ℓ ∨ ¬y ∨ ¬y′)',
    '(ℓ₁ ∨ … ∨ ℓₖ) → (ℓ₁ ∨ ℓ₂ ∨ z₁) ∧ (¬z₁ ∨ ℓ₃ ∨ z₂) ∧ … ∧ (¬zₖ₋₃ ∨ ℓₖ₋₁ ∨ ℓₖ)',
    'forward: zᵢ = 1 exactly when no literal before the chain\'s i-th link is true',
    'backward: forget the fresh variables',
  ];
  const ruleOf = { kept: 0, padded: 1, chain: 3 };

  T.topic({
    id: 'cx-red-sat3', family: 'cx-red', order: 10, title: 'SAT → 3SAT: chains and padding',
    blurb: 'Every clause is rewritten into clauses of exactly three literals: long ones become chains linked by fresh variables, short ones are padded. Satisfiability survives both ways.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (CNF, any clause length)', def: '(a ∨ b ∨ ¬c ∨ d ∨ e) ∧ (¬a ∨ c) ∧ (¬b ∨ ¬d ∨ c)',
      check: (v) => { const r = readFormula(v, { len: 6, clauses: 4, vars: 6 }); if (r.err) return r.err; if (T.sat.to3Sat(r.f).formula.n > 12) return 'Formula: that needs more than 12 variables in all with the fresh ones; shorten a clause'; return null; } }],
    presets: [
      { label: 'A chain and a pair', values: { f: '(a ∨ b ∨ ¬c ∨ d ∨ e) ∧ (¬a ∨ c) ∧ (¬b ∨ ¬d ∨ c)' } },
      { label: 'Only the last literal is true: every z is 1', values: { f: '(a ∨ b ∨ c ∨ d ∨ e) ∧ (¬a) ∧ (¬b ∨ ¬c)' } },
      { label: 'Already 3-CNF: nothing to do', values: { f: '(p ∨ ¬q ∨ r) ∧ (¬p ∨ q ∨ r) ∧ (¬r ∨ q ∨ p)' } },
      { label: 'Unsatisfiable, with unit clauses', values: { f: '(a) ∧ (¬a ∨ b) ∧ (¬b)' } },
      { label: 'One clause of six', values: { f: '(p ∨ q ∨ r ∨ s ∨ t ∨ u) ∧ (¬p ∨ ¬u)' } },
    ],
    counters: [{ id: 'clauses', label: '3-clauses made' }, { id: 'fresh', label: 'fresh variables' }],
    run(inp) {
      const f = T.sat.parse(inp.f);
      const r = T.sat.to3Sat(f), g = r.formula;
      const m = f.clauses.length;
      // which new clauses come from each old one, and the fresh variables each brings
      const rows = f.clauses.map((c, i) => {
        const idx = r.roles.map((x, k) => (x.from === i ? k : -1)).filter((k) => k >= 0);
        const vars = [...new Set(idx.flatMap((k) => g.clauses[k].map(Math.abs)).filter((v) => v > f.n))].sort((x, y) => x - y);
        return { i, idx, role: r.roles[idx[0]].role, vars };
      });
      // layout: the old clause on the left (right-aligned), an arrow, the new clauses on the right
      const ow = rows.map((rw) => K.cx.formula({ f, only: [rw.i] }).box.w);
      const OW = Math.max(...ow), X1 = OW + 110, NW = 360;
      let yy = 0;
      for (const rw of rows) { rw.y = yy; const nb = K.cx.formula({ f: g, only: rw.idx, x: X1, maxW: NW }).box; rw.h = Math.max(54, nb.h); rw.nw = nb.w; yy += rw.h + 22; }
      const chipY = yy + 14;
      const tag = { kept: 'kept', padded: 'padded', chain: 'chain' };
      // the close-up a narrow screen shows: the row a frame is about, and the values when they are in play
      const nchips = K.cx.assignment({ f: g, n: g.n, a: [] }).box.w;
      const rowBox = (i) => { const rw = rows[i]; return { x: OW - ow[i] - 10, y: rw.y - 10, w: X1 + rw.nw - (OW - ow[i]) + 20, h: rw.h + 20 }; };
      const chipBox = { x: 0, y: chipY - 6, w: 100 + nchips, h: 88 };
      let nvNext = null;
      // the scene: rows built so far (up to row `upto`, of which `part` new clauses), colourings a (old) and b (new)
      const scene = (o) => {
        o = o || {};
        const parts = [];
        if (o.hotOld !== undefined && o.hotOld >= 0) parts.push(rowBox(o.hotOld));
        if (o.chips) parts.push(chipBox);
        if (!parts.length) parts.push(...rows.map((rw) => rowBox(rw.i)));
        nvNext = unionBox(parts, 6);
        const items = [];
        const upto = o.upto === undefined ? m - 1 : o.upto;
        for (const rw of rows) {
          const fx = OW - ow[rw.i];
          items.push(...K.cx.formula({ f, a: o.a, only: [rw.i], prefix: 'o', x: fx, y: rw.y, hot: o.hotOld === rw.i ? [rw.i] : [] }).items);
          if (rw.i > upto) continue;
          const shown = rw.i === upto && o.part !== undefined ? rw.idx.slice(0, o.part) : rw.idx;
          const midY = rw.y + 27;
          // the arrow joins the last old literal to the first new one, so it hides with them on a close-up
          items.push({ key: 'ar:' + rw.i, kind: 'edge', from: 'o:l:' + rw.i + ':' + (f.clauses[rw.i].length - 1), to: 'n:l:' + rw.idx[0] + ':0', gapA: 9, gapB: 10, label: tag[rw.role] || rw.role, lx: (OW + X1) / 2, ly: midY - 15, size: 13, cls: rw.i === upto && o.building ? 'hot' : '' });
          const nf = K.cx.formula({ f: g, a: o.b, only: shown, prefix: 'n', x: X1, y: rw.y, maxW: NW, hot: o.hotNew || [] }).items;
          // freshly made clauses grow out of the clause they came from; a literal out of its old copy
          if (o.fresh) for (const it of nf) {
            const mm = /^n:(c|l):(\d+)/.exec(it.key);
            if (!mm || !o.fresh.includes(+mm[2])) continue;
            it.enter = 'from';
            if (mm[1] === 'c') it.src = 'o:c:' + rw.i;
            else { const lit = g.clauses[+mm[2]][+it.key.split(':')[3]]; const at = f.clauses[rw.i].indexOf(lit); it.src = at >= 0 ? 'o:l:' + rw.i + ':' + at : 'o:c:' + rw.i; }
          }
          items.push(...nf);
        }
        if (o.chips) {
          const n = o.chips === 'old' ? f.n : g.n;
          const why = {};
          for (let v = f.n + 1; v <= n; v++) why[v] = 'fresh';
          items.push(...K.cx.assignment({ f: g, n, a: o.chipA, x: 90, y: chipY, prefix: 'ch', label: 'values', hot: o.hotVars, why }).items);
        }
        return items;
      };
      const F = new T.Frames(['clauses', 'fresh']);
      const add0 = F.add.bind(F);
      F.add = (fr) => { fr.narrowView = nvNext; return add0(fr); };
      F.add({ items: scene({ upto: -1 }), say: 'The formula has ' + plural(m, 'clause') + ' of lengths ' + f.clauses.map((c) => c.length).join(', ') + '. 3SAT wants every clause to have exactly three literals, so each clause is rewritten on its own.', hl: { rules: [] }, meta: { freshTotal: g.n - f.n, newCount: g.clauses.length } });
      for (const rw of rows) {
        const c = f.clauses[rw.i], ct = clauseText(f, c);
        if (rw.role === 'kept') {
          F.count('clauses');
          F.add({ items: scene({ upto: rw.i, building: true, fresh: rw.idx, hotOld: rw.i }), say: ct + ' already has three literals: it is copied as it is.', hl: { rules: [0] } });
        } else if (rw.role === 'padded') {
          F.count('clauses', rw.idx.length).count('fresh', rw.vars.length);
          const names = rw.vars.map((v) => g.names[v]);
          F.add({ items: scene({ upto: rw.i, building: true, fresh: rw.idx, hotOld: rw.i }), say: c.length === 1
            ? ct + ' is a unit clause, too short: with fresh ' + names.join(' and ') + ' in all four sign patterns, the four new clauses can all be true only when ' + lt(f, c[0]) + ' is, since one of them has both fresh literals false.'
            : ct + ' has two literals: adding ' + names[0] + ' to one copy and ¬' + names[0] + ' to the other means one copy always rests on the old literals, so the pair is equivalent to the old clause.', hl: { rules: [c.length === 1 ? 2 : 1] }, meta: { built: rw.i } });
        } else {
          rw.idx.forEach((k, j) => {
            F.count('clauses');
            if (j === 0) F.count('fresh', rw.vars.length);
            const nc = g.clauses[k];
            const say = j === 0
              ? ct + ' has ' + c.length + ' literals, too many. Start a chain: ' + clauseText(g, nc) + ' takes the first two and hands the rest on through the fresh ' + lt(g, nc[2]) + '.'
              : j === rw.idx.length - 1
                ? 'The chain ends with ' + clauseText(g, nc) + ': the last two literals, guarded by ¬' + lt(g, -nc[0]) + '. In all ' + plural(rw.idx.length, 'clause') + ' for ' + c.length + ' literals, always k − 2.'
                : 'The next link ' + clauseText(g, nc) + ': if the clause was handed on (' + lt(g, -nc[0]) + ' = 1), the literal ' + lt(g, nc[1]) + ' or the next link ' + lt(g, nc[2]) + ' must take it.';
            F.add({ items: scene({ upto: rw.i, part: j + 1, building: true, fresh: [k], hotOld: rw.i, hotNew: [k] }), say, hl: { rules: [3] }, meta: j === 0 ? { chainStart: true, chainLen: rw.idx.length, len: c.length } : {} });
          });
        }
      }
      F.add({ items: scene({}), say: m + ' clauses became ' + g.clauses.length + ' clauses of exactly three literals, with ' + plural(g.n - f.n, 'fresh variable') + '. The new formula is at most a constant times longer: a polynomial-time rewrite.', hl: { rules: [] }, meta: { built: 'all' } });
      const a = T.sat.brute(f).assignment;
      if (a) {
        // forward: the old values, then each fresh variable worked out
        const b = new Array(g.n + 1).fill(null);
        for (let v = 1; v <= f.n; v++) b[v] = a[v];
        const full = r.forward(a);
        F.add({ items: scene({ a, b, chips: 'all', chipA: b }), say: 'Forward: take a satisfying assignment of the old formula, ' + listVals(f, a) + '. The old literals keep their values in the new clauses; the fresh variables still need values.', hl: { rules: [4] }, meta: { fwd: true } });
        for (const rw of rows) {
          if (rw.role === 'chain') {
            const c = f.clauses[rw.i];
            let first = c.findIndex((l) => isTrue(a, l));
            rw.vars.forEach((z, j) => {
              b[z] = full[z];
              const before = c.slice(0, j + 2).map((l) => lt(f, l)).join(', ');
              F.add({ items: scene({ a, b, chips: 'all', chipA: b.slice(), hotVars: [z], hotOld: rw.i }), say: g.names[z] + ' = ' + bit(full[z]) + (full[z] ? ': none of ' + before + ' is true, so the chain must carry the clause further and ' + g.names[z] + ' does it.' : ': ' + lt(f, c[first]) + ' is already true, so the links after it are satisfied by ¬' + g.names[z] + ' and ' + g.names[z] + ' can be 0.'), hl: { rules: [4] }, meta: { z, zval: bit(full[z]), name: g.names[z] } });
            });
          } else if (rw.role === 'padded') {
            for (const v of rw.vars) b[v] = full[v];
            F.add({ items: scene({ a, b, chips: 'all', chipA: b.slice(), hotVars: rw.vars, hotOld: rw.i }), say: 'The padding ' + rw.vars.map((v) => g.names[v]).join(', ') + ' can take any value, since the old literal ' + (f.clauses[rw.i].length === 1 ? lt(f, f.clauses[rw.i][0]) : 'pair') + ' already makes every padded copy true; take 0.', hl: { rules: [rw.role === 'padded' && f.clauses[rw.i].length === 1 ? 2 : 1] } });
          }
        }
        const okF = T.sat.evaluate(g, full);
        F.add({ items: scene({ a, b: full, chips: 'all', chipA: full }), say: okF ? 'Every one of the ' + g.clauses.length + ' new clauses is true: a satisfying assignment of the old formula became one of the new.' : 'Something went wrong: a new clause is false.', hl: { rules: [4] }, mark: okF ? 'forward' : undefined });
        // backward: any satisfying assignment of the new formula, restricted
        const b2 = lastSat(g);
        F.add({ items: scene({ b: b2, chips: 'all', chipA: b2 }), say: 'Backward: take any satisfying assignment of the 3-CNF, here ' + listVals(g, b2) + '.', hl: { rules: [5] }, meta: { back: true, fresh: Array.from({ length: g.n - f.n }, (_, k) => 'ch:v:' + (f.n + 1 + k)) } });
        const a2 = b2.slice(0, f.n + 1);
        const okB = T.sat.evaluate(f, a2);
        F.add({ items: scene({ a: a2, b: b2, chips: 'old', chipA: a2 }), say: 'Forget the fresh variables: ' + listVals(f, a2) + ' satisfies the old formula' + (okB ? '. If a chain\'s old literals were all false, its fresh z\'s alone could not make every link true, so some old literal must be true.' : '?'), hl: { rules: [5] }, mark: okB ? 'backward' : undefined });
      } else {
        const miss = bestMiss(f);
        const bad = f.clauses.findIndex((c) => !T.sat.evalClause(c, miss));
        F.add({ items: scene({ a: miss, chips: 'old', chipA: miss, hotOld: bad }), say: 'This formula is unsatisfiable: all ' + 2 ** f.n + ' assignments fail. Even the best, ' + listVals(f, miss) + ', leaves ' + clauseText(f, f.clauses[bad]) + ' false.', hl: { rules: [] }, meta: { unsat: true } });
        F.add({ items: scene({}), say: 'So the 3-CNF is unsatisfiable too: any assignment satisfying it would, with its fresh variables forgotten, satisfy the old formula. A reduction must keep the no-instances no.', hl: { rules: [5] }, mark: 'rejected' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'f', kind: 'math', title: 'The formula', text: f.clauses.map((c, i) => 'C' + (i + 1) + ' = ' + clauseText(f, c)).join('\n') },
        { id: 'rules', kind: 'math', title: 'The rewriting rules', text: RULES3.join('\n') },
      ] } };
    },
    predict: [
      { at: (fr) => fr.meta && fr.meta.freshTotal !== undefined, once: true, pick: 'option', options: (all, i) => { const t = all[i].meta.freshTotal; return [...new Set([0, 1, 2, 3, 4, 6, t])].sort((x, y) => x - y).map(String); },
        ask: 'Before we start: how many fresh variables will the whole rewrite need?', answer: (all, i) => String(all[i].meta.freshTotal), explain: 'A 3-literal clause needs none, a pair needs one, a unit clause two, and a clause of k > 3 literals needs k − 3.' },
      { at: (fr, i, all) => all[i + 1] && all[i + 1].meta && all[i + 1].meta.chainStart, once: true, pick: 'option', options: (all, i) => { const L = all[i + 1].meta.len; return [...new Set([L - 2, L - 1, L, 2 * L])].map(String); },
        ask: (all, i) => 'The next clause has ' + all[i + 1].meta.len + ' literals. How many three-literal clauses will its chain have?', answer: (all, i) => String(all[i + 1].meta.chainLen), explain: 'Each link uses one new literal except the first and the last, which use two: k literals make k − 2 clauses.' },
      { at: (fr, i, all) => all[i + 1] && all[i + 1].meta && all[i + 1].meta.z !== undefined, once: true, pick: 'option', options: ['0', '1'],
        ask: (all, i) => 'What value will ' + all[i + 1].meta.name + ' get?', answer: (all, i) => all[i + 1].meta.zval, explain: (all, i) => all[i + 1].say },
      { at: (fr, i, all) => fr.meta && fr.meta.back && fr.meta.fresh.length > 0, once: true, pick: 'item',
        ask: 'Going back, some of these values are thrown away. Click one of them.', answer: (all, i) => all[i].meta.fresh, explain: 'The fresh variables exist only in the new formula; the old one never mentions them.' },
    ],
    quiz: [
      { q: 'A clause with 7 literals becomes how many 3-literal clauses?', options: ['3', '5', '7', '21'], answer: 1, why: 'A chain of k − 2 = 5 links, joined by 4 fresh variables.' },
      { q: 'Why can the chain\'s clauses not all be satisfied by the fresh z variables alone?', options: ['The z\'s are always false', 'The first link has no ¬z, the last has no z, and each z only passes the burden one link on', 'Fresh variables cannot appear twice', 'Because the formula is in 3-CNF'], answer: 1, why: 'The first link needs z₁ = 1, which forces the next link to need z₂ = 1, and so on, until the last link has no fresh variable left: some original literal must be true.' },
      { q: 'Why is a unit clause (a) padded into four clauses and not just (a ∨ y ∨ y′)?', options: ['To make the formula longer', '(a ∨ y ∨ y′) could be made true by y alone, losing the meaning of (a)', 'Unit clauses are not allowed in CNF', 'Four is the number of variables'], answer: 1, why: 'With all four sign patterns of y and y′, one copy has both fresh literals false and so needs a itself.' },
      { q: 'Going backward from a satisfying assignment of the 3-CNF, what do we do with the fresh variables?', options: ['Keep them as new variables of the old formula', 'Forget them: the old variables alone already satisfy the old formula', 'Set them all to 1', 'Solve the formula again'], answer: 1, why: 'The restriction to the old variables works: each old clause is implied by its group of new clauses.' },
      { q: 'How big is the new formula?', options: ['Exponential in the old one', 'At most a constant times the old length', 'Exactly the same length', 'Quadratic in the number of variables'], answer: 1, why: 'Each clause of k literals becomes at most max(4, k − 2) clauses of three literals: linear growth, so the reduction runs in polynomial time.' },
    ],
  });

  // =========================================================================================================
  // 3SAT → CLIQUE and 3SAT → INDEPENDENT SET: a vertex per literal occurrence
  // =========================================================================================================
  /**
   * Clause groups round an ellipse wider than tall (the stage's own shape). A row group lies along the
   * tangent there, so an edge reaches each of its vertices from the inside without running through the
   * others; a triangle group points at the middle. Within each group the literals take the order that gives
   * the fewest crossings, then the shortest edges, over every ordering of every group.
   */
  const VR = 24;
  function occLayout(f, shape, edges) {
    const occ = T.red.occurrences(f), m = f.clauses.length;
    const Dx = m === 1 ? 0 : m === 2 ? 185 : shape === 'tri' ? 232 : 255, Dy = m <= 2 ? 0 : m === 4 ? 110 : 132;
    const deg = m === 1 ? [-90] : m === 2 ? [180, 0] : m === 3 ? [-90, 150, 30] : [-90, 0, 90, 180];
    const C = deg.map((d) => {
      const th = (d * Math.PI) / 180, c = Math.cos(th), s = Math.sin(th);
      let ux = m <= 2 ? c : c / Dx, uy = m <= 2 ? s : s / Dy;
      const nn = Math.hypot(ux, uy) || 1; ux /= nn; uy /= nn;
      let tx = -uy, ty = ux;
      if (tx < -0.01 || (Math.abs(tx) <= 0.01 && ty < 0)) { tx = -tx; ty = -ty; }
      return { x: Dx * c, y: Dy * s, ux, uy, tx, ty };
    });
    // the places a clause's vertices can take
    const slots = f.clauses.map((cl, j) => cl.map((_, p) => {
      const c = C[j], len = cl.length;
      if (shape === 'tri' && len === 3) { const th = (m === 1 ? -Math.PI / 2 : Math.atan2(-c.uy, -c.ux)) + (p * 2 * Math.PI) / 3; return { x: c.x + 54 * Math.cos(th), y: c.y + 54 * Math.sin(th) }; }
      const d = (p - (len - 1) / 2) * (shape === 'tri' ? 88 : 80);
      return { x: c.x + d * c.tx, y: c.y + d * c.ty };
    }));
    const groups = f.clauses.map((_, j) => occ.filter((o) => o.clause === j).map((o) => o.id));
    const permsOf = (n) => (n === 1 ? [[0]] : n === 2 ? [[0, 1], [1, 0]] : [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]);
    const P = groups.map((g) => permsOf(g.length));
    const orient = (a, b, c) => (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
    const crosses = (p1, p2, p3, p4) => { const d1 = orient(p3, p4, p1), d2 = orient(p3, p4, p2), d3 = orient(p1, p2, p3), d4 = orient(p1, p2, p4); return ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)); };
    const near = (p, a, b) => { const dx = b.x - a.x, dy = b.y - a.y, L = dx * dx + dy * dy || 1, t = Math.max(0, Math.min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / L)); return Math.hypot(a.x + t * dx - p.x, a.y + t * dy - p.y); };
    const pos = {};
    const place = (choice) => groups.forEach((g, j) => g.forEach((id, k) => { pos[id] = slots[j][P[j][choice[j]][k]]; }));
    const score = () => {
      let s = 0;
      for (let i = 0; i < edges.length; i++) {
        const [a, b] = edges[i], A = pos[a], B = pos[b];
        s += Math.hypot(A.x - B.x, A.y - B.y);
        for (const o of occ) if (o.id !== a && o.id !== b && near(pos[o.id], A, B) < VR + 4) s += 4000;
        for (let k = i + 1; k < edges.length; k++) { const [c, d] = edges[k]; if (c === a || c === b || d === a || d === b) continue; if (crosses(A, B, pos[c], pos[d])) s += 1000; }
      }
      return s;
    };
    const choice = new Array(m).fill(0);
    let best = null, bs = Infinity;
    for (;;) {
      place(choice);
      const s = score();
      if (s < bs) { bs = s; best = choice.slice(); }
      let j = m - 1;
      while (j >= 0 && choice[j] === P[j].length - 1) { choice[j] = 0; j--; }
      if (j < 0) break;
      choice[j]++;
    }
    place(best);
    // clause names sit outside their group, on the side away from the middle, where no edge goes
    const labels = C.map((c) => {
      const diag = Math.abs(c.ux) > 0.3 && Math.abs(c.uy) > 0.3;
      const len = shape === 'tri' ? 90 : 56 + 16 * Math.abs(c.uy) + (diag ? 40 : 0);
      return { x: c.x + c.ux * len, y: c.y + c.uy * len + 5, anchor: c.ux < -0.3 ? 'end' : c.ux > 0.3 ? 'start' : 'middle' };
    });
    // a box per clause group (its vertices, the shaded region and its name), for close-up views
    const boxes = groups.map((g, j) => {
      const xs = g.map((id) => pos[id].x), ys = g.map((id) => pos[id].y);
      const lb = labels[j], lw = 30, lx0 = lb.anchor === 'end' ? lb.x - lw : lb.anchor === 'start' ? lb.x : lb.x - lw / 2;
      const x0 = Math.min(Math.min(...xs) - VR - 16, lx0 - 4), x1 = Math.max(Math.max(...xs) + VR + 16, lx0 + lw + 4);
      const y0 = Math.min(Math.min(...ys) - VR - 36, lb.y - 20), y1 = Math.max(Math.max(...ys) + VR + 16, lb.y + 8);
      return { x: x0, y: y0, w: x1 - x0, h: y1 - y0 };
    });
    return { occ, pos, labels, boxes };
  }
  const unionBox = (bs, pad) => { const x0 = Math.min(...bs.map((b) => b.x)), y0 = Math.min(...bs.map((b) => b.y)), x1 = Math.max(...bs.map((b) => b.x + b.w)), y1 = Math.max(...bs.map((b) => b.y + b.h)); pad = pad || 0; return { x: x0 - pad, y: y0 - pad, w: x1 - x0 + 2 * pad, h: y1 - y0 + 2 * pad }; };

  /** One choice per clause, every way: the selections a k-set must be one of */
  function* picks(f) {
    const m = f.clauses.length, idx = new Array(m).fill(0);
    const base = []; let s = 0;
    f.clauses.forEach((c) => { base.push(s); s += c.length; });
    while (true) {
      yield idx.map((p, j) => base[j] + p);
      let j = m - 1;
      while (j >= 0 && idx[j] === f.clauses[j].length - 1) { idx[j] = 0; j--; }
      if (j < 0) return;
      idx[j]++;
    }
  }

  function occTopic(kind) {
    const isC = kind === 'clique';
    const NAME = isC ? 'clique' : 'independent set';
    return function (inp) {
      const f = T.sat.parse(inp.f);
      const R = isC ? T.red.sat3ToClique(f) : T.red.sat3ToIS(f);
      const G = R.graph, k = R.k, m = f.clauses.length;
      const occ0 = T.red.occurrences(f);
      const { occ, pos, labels, boxes } = occLayout(f, isC ? 'row' : 'tri', G.edges.filter(([a, b]) => isC || occ0[a].clause !== occ0[b].clause));
      const allIdx = f.clauses.map((_, j) => j);
      const mode = inp.edges || 'all';
      const sel = inp.focus && inp.focus !== 'all' ? Math.min(m, +inp.focus) - 1 : null;
      const verify = (S) => (isC ? T.cx.verifyClique(G, k, S) : T.cx.verifyIndependentSet(G, k, S));
      const L = (id) => lt(f, occ[id].lit);
      const where = (id) => L(id) + ' in C' + (occ[id].clause + 1);
      const nodesAll = occ.map((o) => ({ id: o.id, label: lt(f, o.lit), role: 'clause', group: 'c' + o.clause, x: pos[o.id].x, y: pos[o.id].y }));
      const groupsAll = f.clauses.map((c, j) => ({ id: 'c' + j, label: ' ' }));
      const edgeKind = (a, b) => (occ[a].clause === occ[b].clause ? 'clause' : isC ? 'compat' : 'conflict');
      const edgesAll = G.edges.map(([a, b]) => ({ a: Math.min(a, b), b: Math.max(a, b), kind: edgeKind(a, b) }));
      // the formula just above the graph with the values beside it, so the camera box stays tight
      const FW = m >= 4 ? 760 : 560;
      const fb = K.cx.formula({ f, labels: true, maxW: FW }).box;
      const cb = K.cx.assignment({ f, a: [] }).box;
      const graphBox = unionBox(boxes, 0);
      const GAP = 84, rowW = fb.w + GAP + cb.w;
      // with four clauses the formula fills its row, so the values go in the bottom corner the groups leave empty;
      // edges round the top group bow upwards, so the formula keeps a little distance
      const corner = m >= 4;
      const FX = corner ? -fb.w / 2 : -rowW / 2, FY = graphBox.y - fb.h - 34;
      const CXX = corner ? graphBox.x + graphBox.w - cb.w : FX + fb.w + GAP;
      const CY = corner ? graphBox.y + graphBox.h - 62 : FY + fb.h / 2 - 34;
      const chipBox = { x: CXX - 76, y: CY - 6, w: cb.w + 80, h: 70 };
      const focusView = sel === null ? null : unionBox([boxes[sel], boxes[(sel + 1) % m], boxes[(sel + m - 1) % m]], 24);
      const touches = (e, fc) => fc.includes(occ[e.a].clause) || fc.includes(occ[e.b].clause);
      const scene = (o) => {
        const vis = o.clauses || new Set(allIdx);
        const items = K.cx.formula({ f, a: o.a, x: FX, y: FY, maxW: FW, labels: true, prefix: 'cnf', hot: o.hotC || [] }).items;
        f.clauses.forEach((c, j) => { if (vis.has(j)) items.push({ key: 'cl:' + j, kind: 'text', x: labels[j].x, y: labels[j].y, text: 'C' + (j + 1), anchor: labels[j].anchor, size: 17, cls: 'strong' }); });
        const nodes = nodesAll.filter((n) => vis.has(occ[n.id].clause)).map((n) => Object.assign({}, n, { cls: 'rbig ' + ((o.ncls && o.ncls(n.id)) || '') }));
        const certSet = new Set(o.cert || []);
        const edges = edgesAll.filter((e) => vis.has(occ[e.a].clause) && vis.has(occ[e.b].clause) && (!o.edge || o.edge(e))).map((e) => {
          let cls = (o.ecls && o.ecls(e)) || '';
          if (o.fadeOthers && !(certSet.has(e.a) && certSet.has(e.b))) cls += ' faded';
          else if (mode === 'mine' && o.focus && !touches(e, o.focus) && !/faded/.test(cls)) cls += ' faded';
          return { a: e.a, b: e.b, cls };
        });
        for (const [a, b] of o.ghost || []) edges.push({ a, b, cls: 'bad dim' });
        const gd = K.gadget.draw({ nodes, edges, groups: groupsAll.filter((g) => vis.has(+g.id.slice(1))), cert: o.cert, certEdges: o.certEdges, prefix: 'g', r: VR });
        for (const it of gd.items) {
          if (it.kind === 'state' && o.grow) { const id = +it.key.slice(4); if (o.grow.includes(id)) { it.enter = 'from'; it.src = 'cnf:l:' + occ[id].clause + ':' + occ[id].pos; } }
          if (it.kind === 'edge' && /\bbad\b/.test(it.cls)) it.key += ':ghost';
        }
        items.push(...gd.items);
        if (o.chips) items.push(...K.cx.assignment({ f, a: o.chips, x: CXX, y: CY, prefix: 'ch', label: 'values', hot: o.hotVars }).items);
        return items;
      };
      const F = new T.Frames(['v', 'e']);
      // every frame: its items, a close-up for narrow screens, and the clause-in-focus camera
      const add = (o, fr) => {
        fr.items = scene(o);
        const fc = o.focus && o.focus.length ? o.focus : allIdx;
        fr.narrowView = unionBox(fc.map((j) => boxes[j]).concat(o.chips ? [chipBox] : []), 10);
        if (sel !== null) {
          fr.view = focusView;
          if (o.focus && o.focus.includes(sel)) fr.say = 'Clause ' + (sel + 1) + ' of ' + m + ': ' + fr.say;
        }
        F.add(fr);
      };
      const vkey = (id) => 'g:v:' + id;
      const RULE = isC
        ? ['one vertex per literal occurrence, grouped by clause', 'join u and v when they are in different clauses', '… and are not a literal and its negation', 'k = the number of clauses = ' + m, 'forward: pick a true literal in each clause', 'backward: make every picked literal true']
        : ['one vertex per literal occurrence, grouped by clause', 'join the literals of one clause (a triangle)', 'join every literal to each copy of its negation', 'k = the number of clauses = ' + m, 'forward: pick a true literal in each clause', 'backward: make every picked literal true'];
      add({ clauses: new Set() }, { say: 'The formula has ' + plural(m, 'clause') + '. We build a graph whose ' + NAME + 's of size ' + m + ' match its satisfying assignments, one clause at a time.' + (sel !== null ? ' The camera stays on clause ' + (sel + 1) + ' of ' + m + ' and its neighbours.' : ''), hl: { rule: [] } });
      const built = new Set();
      f.clauses.forEach((c, j) => {
        built.add(j);
        const ids = occ.filter((o) => o.clause === j).map((o) => o.id);
        F.count('v', ids.length);
        if (!isC) F.count('e', (ids.length * (ids.length - 1)) / 2);
        const shape = c.length === 3 ? 'a triangle' : c.length === 2 ? 'a single edge' : 'a lone vertex';
        add({ clauses: new Set(built), grow: ids, edge: (e) => e.kind === 'clause', ecls: (e) => (occ[e.a].clause === j ? 'hot' : ''), focus: [j] }, { say: isC
          ? 'C' + (j + 1) + ' = ' + clauseText(f, c) + ' gives ' + plural(c.length, 'vertex', 'vertices') + ', one per literal. Vertices of one clause are never joined: a clique takes at most one of them.' + (c.length < 3 ? ' This clause is short, so its group is smaller.' : '')
          : 'C' + (j + 1) + ' = ' + clauseText(f, c) + ' gives ' + plural(c.length, 'vertex', 'vertices') + ', joined into ' + shape + ': an independent set can take at most one of them.', hl: { rule: isC ? [0] : [0, 1] }, meta: { stage: 'clause' } });
      });
      const all = new Set(allIdx);
      if (isC) {
        // edges pair of clauses by pair of clauses: the new ones lit, the earlier ones faint, and the pairs
        // left out shown as red dashes once
        const pairs = [];
        for (let x = 0; x < m; x++) for (let y = x + 1; y < m; y++) pairs.push([x, y]);
        const done = new Set();
        pairs.forEach(([x, y], pi) => {
          done.add(x + ',' + y);
          const inPair = (e) => (occ[e.a].clause === x && occ[e.b].clause === y) || (occ[e.a].clause === y && occ[e.b].clause === x);
          const added = edgesAll.filter(inPair);
          F.count('e', added.length);
          const miss = [];
          for (const u of occ) for (const v of occ) if (u.clause === x && v.clause === y && u.lit === -v.lit) miss.push([u.id, v.id]);
          const left = miss.map(([u, v]) => where(u) + ' and ' + where(v));
          add({ clauses: all, edge: (e) => done.has(Math.min(occ[e.a].clause, occ[e.b].clause) + ',' + Math.max(occ[e.a].clause, occ[e.b].clause)), ecls: (e) => (inPair(e) ? 'hot' : 'faded'), ghost: miss, focus: [x, y] }, { say: 'Between C' + (x + 1) + ' and C' + (y + 1) + ': ' + plural(added.length, 'edge') + ' join literals that can be true together. ' + (miss.length ? 'Left apart (red dashes): ' + left.join('; ') + ', since a literal and its negation can never both be true.' : 'No literal here meets its negation, so every pair is joined.'), hl: { rule: [1, 2] }, meta: { stage: 'pair', pair: pi, miss: miss.map(([u, v]) => [vkey(u), vkey(v)]) } });
        });
      } else {
        // conflict edges variable by variable
        for (let v = 1; v <= f.n; v++) {
          const es = edgesAll.filter((e) => e.kind === 'conflict' && Math.abs(occ[e.a].lit) === v);
          if (!es.length) continue;
          F.count('e', es.length);
          const upTo = v;
          const fc = [...new Set(es.flatMap((e) => [occ[e.a].clause, occ[e.b].clause]))];
          add({ clauses: all, edge: (e) => e.kind === 'clause' || Math.abs(occ[e.a].lit) <= upTo, ecls: (e) => (e.kind === 'conflict' && Math.abs(occ[e.a].lit) === v ? 'hot' : ''), focus: fc }, { say: 'Variable ' + lt(f, v) + ': join every ' + lt(f, v) + ' to every ' + lt(f, -v) + ' (' + plural(es.length, 'edge') + '), so an independent set never picks both: the picks stay consistent.', hl: { rule: [2] }, meta: { stage: 'conflict' } });
        }
      }
      const sol = T.sat.brute(f);
      add({ clauses: all }, { say: 'The graph is built: ' + plural(G.n, 'vertex', 'vertices') + ', ' + plural(G.edges.length, 'edge') + '. Ask for ' + (isC ? 'a clique' : 'an independent set') + ' of size k = ' + k + ', one vertex for each clause.', hl: { rule: [3] }, meta: { target: true, yes: sol.sat } });
      if (sol.sat) {
        const a = sol.assignment, S = R.forward(a);
        add({ clauses: all, a, chips: a, fadeOthers: isC }, { say: 'Forward: take a satisfying assignment, ' + listVals(f, a) + '. Green literals are true; every clause has at least one.', hl: { rule: [4] } });
        S.forEach((id, j) => {
          add({ clauses: all, a, chips: a, cert: S.slice(0, j + 1), hotC: [j], fadeOthers: isC, focus: [j] }, { say: 'In C' + (j + 1) + ' the first true literal is ' + L(id) + ': its vertex goes into the set.', hl: { rule: [4] }, meta: { pickedNow: vkey(id), clause: j } });
        });
        const v = verify(S);
        const ce = [];
        if (isC) for (let x = 0; x < S.length; x++) for (let y = x + 1; y < S.length; y++) ce.push([S[x], S[y]]);
        add({ clauses: all, a, chips: a, cert: S, certEdges: ce, fadeOthers: isC }, { say: v.ok ? (isC
          ? 'All ' + ce.length + ' pairs of picked vertices are joined: they lie in different clauses, and two true literals are never x and ¬x. A clique of size ' + k + '.'
          : 'No two picked vertices are joined: one per clause, so no triangle edge, and two true literals are never x and ¬x. An independent set of size ' + k + '.') : 'The check failed: ' + v.reason, hl: { rule: [4] }, mark: 'forward' });
        // backward from some other k-set, the last one in counting order
        let S2 = null;
        for (const p of picks(f)) if (verify(p).ok) S2 = p;
        const ce2 = [];
        if (isC) for (let x = 0; x < S2.length; x++) for (let y = x + 1; y < S2.length; y++) ce2.push([S2[x], S2[y]]);
        add({ clauses: all, cert: S2, certEdges: ce2, chips: [], fadeOthers: isC }, { say: 'Backward: suppose we are handed any ' + NAME + ' of size ' + k + ', like {' + S2.map(L).join(', ') + '}. It has exactly one vertex in each clause' + (isC ? ', because vertices of one clause are never joined.' : ', because each clause is a clique of its own.'), hl: { rule: [5] }, meta: { back: true } });
        const a2 = new Array(f.n + 1).fill(null);
        S2.forEach((id, j) => {
          const l = occ[id].lit, was = a2[Math.abs(l)];
          a2[Math.abs(l)] = l > 0;
          add({ clauses: all, cert: S2, certEdges: ce2, chips: a2.slice(), hotVars: [Math.abs(l)], hotC: [j], fadeOthers: isC, focus: [j] }, { say: 'The vertex ' + where(id) + ' is picked, so make ' + L(id) + ' true: ' + lt(f, Math.abs(l)) + ' = ' + bit(l > 0) + (was !== null ? ' (already set, and no clash: ' + lt(f, l) + ' and ' + lt(f, -l) + ' are never both in the set).' : '.'), hl: { rule: [5] } });
        });
        const a3 = a2.map((x, i) => (i === 0 ? null : x === null ? false : x));
        const unset = a2.slice(1).map((x, i) => (x === null ? lt(f, i + 1) : null)).filter(Boolean);
        add({ clauses: all, cert: S2, certEdges: ce2, chips: a3, a: a3, fadeOthers: isC }, { say: (unset.length ? 'Nothing picked mentions ' + unset.join(', ') + ', so any value will do; take 0. ' : '') + 'Every clause holds a picked vertex, now a true literal: the formula is satisfied.', hl: { rule: [5] }, mark: T.sat.evaluate(f, a3) ? 'accepted' : undefined });
      } else {
        // no k-set: every way to pick one per clause has a clash
        let total = 1; for (const c of f.clauses) total *= c.length;
        let shown = 0;
        for (const p of picks(f)) {
          if (shown >= 2) break;
          let clash = null;
          for (let x = 0; x < p.length && !clash; x++) for (let y = x + 1; y < p.length; y++) if (occ[p[x]].lit === -occ[p[y]].lit) { clash = [p[x], p[y]]; break; }
          if (!clash) continue;
          shown++;
          add({ clauses: all, ncls: (id) => (clash.includes(id) ? 'bad' : p.includes(id) ? 'hot' : ''), focus: [occ[clash[0]].clause, occ[clash[1]].clause] }, { say: 'Try one vertex per clause: {' + p.map(L).join(', ') + '}. It fails: ' + where(clash[0]) + ' and ' + where(clash[1]) + (isC ? ' are not joined.' : ' are joined.'), hl: { rule: [2] } });
        }
        add({ clauses: all }, { say: 'All ' + total + ' ways to pick one vertex per clause meet some literal and its negation, so there is no ' + NAME + ' of size ' + k + '. That matches the formula: it is unsatisfiable.', hl: { rule: [3] }, mark: 'rejected' });
      }
      return { frames: F.list, def: { sections: [
        { id: 'f', kind: 'math', title: 'The formula', text: f.clauses.map((c, i) => 'C' + (i + 1) + ' = ' + clauseText(f, c)).join('\n') },
        { id: 'rule', kind: 'math', title: '3SAT → ' + (isC ? 'CLIQUE' : 'INDEPENDENT SET'), text: RULE.join('\n') },
      ] } };
    };
  }
  const occPredict = (isC) => [
    { at: (fr) => fr.meta && fr.meta.target, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will this graph have ' + (isC ? 'a clique' : 'an independent set') + ' of size k?', answer: (all, i) => (all[i].meta.yes ? 'Yes' : 'No'), explain: 'Exactly when the formula is satisfiable: that is what the reduction promises.' },
    { at: (fr, i, all) => all[i + 1] && all[i + 1].meta && all[i + 1].meta.pickedNow && all[i + 1].meta.clause === 1, once: true, pick: 'item', ask: 'Click the vertex the assignment picks in C2 (the first true literal there).', answer: (all, i) => all[i + 1].meta.pickedNow, explain: (all, i) => all[i + 1].say },
  ];
  const FORM_LIM = { len: 3, clauses: 4, vars: 4 };
  const checkF = (v) => readFormula(v, FORM_LIM).err || null;
  // the clause-in-focus switcher and the edge filter, shared by both pictures
  const VIEW_INPUTS = [
    { id: 'focus', kind: 'choice', label: 'Clause in focus', def: 'all', options: [{ value: 'all', label: 'all' }, { value: '1', label: 'clause 1' }, { value: '2', label: 'clause 2' }, { value: '3', label: 'clause 3' }, { value: '4', label: 'clause 4' }],
      check: (v, inp) => { if (v === 'all') return null; const r = readFormula(inp.f, FORM_LIM); if (r.f && +v > r.f.clauses.length) return 'Clause in focus: the formula has only ' + r.f.clauses.length + ' clauses'; return null; } },
    { id: 'edges', kind: 'choice', label: 'Edges', def: 'all', options: [{ value: 'all', label: 'all' }, { value: 'mine', label: 'only this clause\'s' }] },
  ];

  T.topic({
    id: 'cx-red-clique', family: 'cx-red', order: 20, title: '3SAT → CLIQUE',
    blurb: 'A vertex for every literal of every clause, edges between literals that can be true together: the formula is satisfiable exactly when the graph has a clique with one vertex per clause.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (3-CNF)', def: '(p ∨ q ∨ ¬r) ∧ (¬p ∨ r) ∧ (¬q ∨ ¬r ∨ p)', check: checkF }].concat(VIEW_INPUTS),
    presets: [
      { label: 'Three clauses, one short', values: { f: '(p ∨ q ∨ ¬r) ∧ (¬p ∨ r) ∧ (¬q ∨ ¬r ∨ p)' } },
      { label: 'A literal repeated in every clause', values: { f: '(a ∨ b) ∧ (a ∨ ¬b ∨ c) ∧ (a ∨ ¬c)' } },
      { label: 'Unsatisfiable: no clique of size 4', values: { f: '(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)' } },
      { label: 'A unit clause decides it', values: { f: '(¬s) ∧ (s ∨ t ∨ u) ∧ (¬t ∨ s)' } },
    ],
    counters: [{ id: 'v', label: 'vertices' }, { id: 'e', label: 'edges' }],
    run: occTopic('clique'),
    predict: occPredict(true).concat([
      { at: (fr, i, all) => all[i + 1] && all[i + 1].meta && all[i + 1].meta.stage === 'pair' && all[i + 1].meta.miss.length > 0, once: true, pick: 'item',
        ask: (all, i) => 'The edges between two clause groups come next. Click a vertex that will be left unjoined to some vertex of the other group.', answer: (all, i) => [...new Set(all[i + 1].meta.miss.flat())], explain: (all, i) => all[i + 1].say },
    ]),
    quiz: [
      { q: 'Why are two vertices of the same clause never joined?', options: ['To keep the graph small', 'So a clique takes at most one vertex per clause, and size k forces exactly one', 'Because they are the same literal', 'Because they are always contradictory'], answer: 1, why: 'With no edges inside a group, k = m vertices must come from m different clauses.' },
      { q: 'Why are x in one clause and ¬x in another not joined?', options: ['They are in the same clause', 'They cannot both be true, so a clique, read as true literals, must not hold both', 'Edges only join equal literals', 'To make the clique bigger'], answer: 1, why: 'Leaving them apart is what makes every clique a consistent choice of true literals.' },
      { q: 'For m clauses of three literals, the graph has how many vertices?', options: ['m', '3m', 'm²', '2ᵐ'], answer: 1, why: 'One per literal occurrence: 3m. The edges are at most (3m)², so the graph is built in polynomial time.' },
      { q: 'A clique of size k picks ¬q in C2. Going back, what value does q get?', options: ['1', '0', 'Either', 'It depends on C1'], answer: 1, why: 'A picked vertex becomes a true literal; ¬q true means q = 0.' },
      { q: 'If the formula is unsatisfiable, what happens to the graph?', options: ['It has no edges', 'It has no clique of size k', 'It is disconnected', 'It has a clique of size k anyway'], answer: 1, why: 'A k-clique would give a satisfying assignment, so there can be none: no-instances map to no-instances.' },
    ],
  });

  T.topic({
    id: 'cx-red-is', family: 'cx-red', order: 30, title: '3SAT → INDEPENDENT SET',
    blurb: 'Each clause becomes a triangle of its literals, and every literal is joined to its negations: an independent set with one vertex per triangle is a satisfying assignment.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (3-CNF)', def: '(a ∨ ¬b ∨ c) ∧ (¬a ∨ b ∨ ¬c) ∧ (b ∨ c)', check: checkF }].concat(VIEW_INPUTS),
    presets: [
      { label: 'Two triangles and an edge', values: { f: '(a ∨ ¬b ∨ c) ∧ (¬a ∨ b ∨ ¬c) ∧ (b ∨ c)' } },
      { label: 'Unsatisfiable: no independent set of size 4', values: { f: '(p ∨ q) ∧ (¬p ∨ q) ∧ (p ∨ ¬q) ∧ (¬p ∨ ¬q)' } },
      { label: 'The same literal everywhere: no conflicts', values: { f: '(x ∨ y ∨ z) ∧ (x ∨ y) ∧ (x ∨ z ∨ y)' } },
      { label: 'A lone vertex for a unit clause', values: { f: '(¬u) ∧ (u ∨ v ∨ ¬w) ∧ (w ∨ ¬v)' } },
    ],
    counters: [{ id: 'v', label: 'vertices' }, { id: 'e', label: 'edges' }],
    run: occTopic('is'),
    predict: occPredict(false),
    quiz: [
      { q: 'What do the triangle edges inside a clause do?', options: ['Make the set consistent', 'Allow at most one vertex per clause, so size k means exactly one', 'Join a literal to its negation', 'Nothing'], answer: 1, why: 'An independent set takes at most one corner of a triangle; with k = m it takes one from each.' },
      { q: 'What do the edges between x and ¬x do?', options: ['Count the clauses', 'Stop the set from making x and ¬x both true', 'Connect the triangles into a cycle', 'Force x to be true'], answer: 1, why: 'Joined vertices cannot both be in an independent set, so the picked literals never contradict each other.' },
      { q: 'This picture differs from 3SAT → CLIQUE by…', options: ['Nothing at all', 'Taking the complement of the clique graph', 'Using one vertex per variable', 'Asking for size 2k'], answer: 1, why: 'The clique graph joins exactly the pairs that are left apart here: an independent set in one is a clique in the other.' },
      { q: 'A formula with 4 clauses has no independent set of size 4 in its graph. What do we learn?', options: ['The formula is satisfiable', 'The formula is unsatisfiable', 'The reduction is wrong', 'Nothing'], answer: 1, why: 'A satisfying assignment would give an independent set of size 4 by the forward map.' },
    ],
  });

  // =========================================================================================================
  // INDEPENDENT SET ↔ VERTEX COVER ↔ CLIQUE
  // =========================================================================================================
  function readGraph(text) {
    const names = [], edges = [];
    const id = (s) => { let i = names.indexOf(s); if (i < 0) { names.push(s); i = names.length - 1; } return i; };
    for (const tok of String(text).split(/[\s,;]+/).filter(Boolean)) {
      const p = tok.split(/-+|—|–/);
      if (p.some((x) => !/^[A-Za-z0-9]{1,2}$/.test(x))) throw new Error('"' + tok + '" is not an edge like a-b or a vertex name of one or two letters');
      if (p.length === 1) { id(p[0]); continue; }
      if (p.length !== 2) throw new Error('"' + tok + '" should join two vertices, like a-b');
      if (p[0] === p[1]) throw new Error('"' + tok + '" joins a vertex to itself; leave loops out');
      const a = id(p[0]), b = id(p[1]);
      if (!edges.some(([x, y]) => (x === a && y === b) || (x === b && y === a))) edges.push([Math.min(a, b), Math.max(a, b)]);
    }
    return { n: names.length, edges, names };
  }

  T.topic({
    id: 'cx-red-complement', family: 'cx-red', order: 40, title: 'INDEPENDENT SET ↔ VERTEX COVER ↔ CLIQUE',
    blurb: 'Three problems, one picture: the vertices outside an independent set cover every edge, and in the complement graph the same set is a clique.',
    inputs: [
      { id: 'g', kind: 'text', label: 'Graph (edges like a-b, lone vertices by name)', def: 'a-b, b-c, c-d, d-e, e-a, a-f, c-f', check: (v) => { let G; try { G = readGraph(v); } catch (e) { return 'Graph: ' + e.message; } if (G.n < 2) return 'Graph: at least two vertices'; if (G.n > 8) return 'Graph: at most 8 vertices, so the picture stays readable'; return null; } },
      { id: 'k', kind: 'number', label: 'k (independent set size)', def: 3, min: 1, max: 8 },
    ],
    check: (inp) => { try { const G = readGraph(inp.g); if (inp.k > G.n) return 'k: at most the number of vertices, ' + G.n; } catch (e) { return null; } return null; },
    presets: [
      { label: 'A pentagon with a hub, k = 3', values: { g: 'a-b, b-c, c-d, d-e, e-a, a-f, c-f', k: 3 } },
      { label: 'A star: one vertex covers all', values: { g: 'h-a, h-b, h-c, h-d, h-e', k: 5 } },
      { label: 'Complete K4: the complement is empty', values: { g: 'a-b, a-c, a-d, b-c, b-d, c-d', k: 1 } },
      { label: 'Asking too much: no independent set of size 4', values: { g: 'p-q, q-r, r-s, s-t, t-p', k: 4 } },
      { label: 'No edges at all', values: { g: 'u, v, w, x', k: 4 } },
    ],
    counters: [{ id: 'n', label: 'vertices' }, { id: 'e', label: 'edges drawn' }, { id: 's', label: 'set size' }],
    run(inp) {
      const G = readGraph(inp.g), n = G.n, H = T.cx.complement(G), nm = (i) => G.names[i];
      const set = (S) => '{' + S.map(nm).join(', ') + '}';
      // an ellipse about as wide as the stage, so the graph fills it
      const R0 = 60 + 15 * n, RX = R0 * 1.45;
      const pos = G.names.map((_, i) => { const t = -Math.PI / 2 + (2 * Math.PI * i) / n; return { x: RX * Math.cos(t), y: R0 * Math.sin(t) }; });
      const whole = { x: -RX - 40, y: -R0 - 40, w: 2 * RX + 80, h: 2 * R0 + 80 };
      let k = inp.k, S = T.cx.findIndependentSet(G, k);
      const asked = k;
      let kk = k;
      while (!S && kk > 1) { kk--; S = T.cx.findIndependentSet(G, kk); }
      const inS = (i) => S.includes(i);
      const C = Array.from({ length: n }, (_, i) => i).filter((i) => !inS(i));
      const scene = (o) => {
        const nodes = G.names.map((s, i) => ({ id: i, label: s, x: pos[i].x, y: pos[i].y, cls: 'rbig ' + (o.ncls ? o.ncls(i) || '' : '') }));
        const edges = [];
        if (o.g) for (const [a, b] of G.edges) edges.push({ a, b, cls: o.gcls ? o.gcls(a, b) || '' : '' });
        if (o.h) for (const [a, b] of H.edges) edges.push({ a, b, cls: 'alt ' + (o.hcls ? o.hcls(a, b) || '' : '') });
        const items = K.gadget.draw({ nodes, edges, prefix: 'g', cert: o.cert, certEdges: o.certEdges, r: 24 }).items;
        return items;
      };
      const F = new T.Frames(['n', 'e', 's']);
      const add0 = F.add.bind(F);
      F.add = (fr) => { fr.narrowView = whole; return add0(fr); };
      F.set('n', n).set('e', G.edges.length);
      F.add({ items: scene({ g: true }), say: 'The graph G has ' + plural(n, 'vertex', 'vertices') + ' and ' + plural(G.edges.length, 'edge') + (G.edges.length ? '' : ': every set of vertices is independent here') + '. Three questions about it are really one.', hl: { rule: [] } });
      const v1 = T.cx.verifyIndependentSet(G, kk, S);
      F.set('s', S.length);
      if (kk === asked) F.add({ items: scene({ g: true, cert: S }), say: 'An independent set of size ' + k + ': S = ' + set(S) + '. No edge has both ends in S' + (v1.ok ? '.' : ' (check failed).'), hl: { rule: [0] }, meta: { isFound: true } });
      else {
        F.add({ items: scene({ g: true, cert: S }), say: 'There is no independent set of size ' + asked + ': every ' + asked + ' vertices include the two ends of some edge. The largest has size ' + kk + ', S = ' + set(S) + '; we follow that one, so k becomes ' + kk + '.', hl: { rule: [0] }, meta: { isFound: false } });
        k = kk;
      }
      F.add({ items: scene({ g: true, cert: S, ncls: (i) => (inS(i) ? '' : 'hot') }), say: 'Now look at the other ' + plural(C.length, 'vertex', 'vertices') + ', V − S = ' + set(C) + '. Every edge of G has at most one end in S, so at least one end in V − S.', hl: { rule: [1] }, meta: { cover: C.map((i) => 'g:v:' + i) } });
      const v2 = T.cx.verifyVertexCover(G, n - k, C);
      F.set('s', C.length);
      F.add({ items: scene({ g: true, ncls: (i) => (inS(i) ? 'faded' : 'colB'), gcls: () => 'good' }), say: 'Swap the colours: V − S is a vertex cover of size n − k = ' + (n - k) + '. ' + (G.edges.length ? 'Every one of the ' + G.edges.length + ' edges touches it' : 'With no edges, even the empty set covers') + (v2.ok ? '.' : ' (check failed).') + ' Backwards works the same way: the vertices outside a cover touch no edge among themselves.', hl: { rule: [1, 3] }, mark: 'cover' });
      F.set('s', S.length);
      F.add({ items: scene({ g: true, cert: S }), say: 'Back to S. Now the complement graph Ḡ: same vertices, and an edge exactly where G has none. It will have ' + n * (n - 1) / 2 + ' − ' + G.edges.length + ' = ' + H.edges.length + ' edges.', hl: { rule: [2] }, meta: { compCount: H.edges.length, total: n * (n - 1) / 2, ge: G.edges.length } });
      F.set('e', G.edges.length + H.edges.length);
      F.add({ items: scene({ g: true, h: true, cert: S, gcls: () => 'dim faded' }), say: 'The missing pairs grow in as the edges of Ḡ (purple), while the old edges of G fade away.', hl: { rule: [2] } });
      F.set('e', H.edges.length);
      const ce = [];
      for (let x = 0; x < S.length; x++) for (let y = x + 1; y < S.length; y++) ce.push([S[x], S[y]]);
      const v3 = T.cx.verifyClique(H, k, S);
      F.add({ items: scene({ h: true, cert: S, certEdges: ce }), say: 'In Ḡ, S = ' + set(S) + ' is a clique of size ' + k + ': each pair was left apart in G, so it is joined in Ḡ' + (v3.ok ? '.' : ' (check failed).') + (H.edges.length ? '' : ' Ḡ has no edges, so only single vertices are cliques.'), hl: { rule: [2, 4] }, mark: 'clique' });
      F.add({ items: scene({ h: true, cert: S, certEdges: ce }), say: 'So INDEPENDENT SET, VERTEX COVER and CLIQUE reduce to each other: keep the graph and use n − k, or complement the graph and keep k. Certificates map by taking V − S or by doing nothing.', hl: { rule: [0, 1, 2, 3, 4] } });
      return { frames: F.list, def: { sections: [
        { id: 'g', kind: 'math', title: 'The instance', text: 'V = {' + G.names.join(', ') + '}, n = ' + n + '\nE = {' + G.edges.map(([a, b]) => nm(a) + nm(b)).join(', ') + '}\nk = ' + asked },
        { id: 'rule', kind: 'math', title: 'The three reductions', text: ['(G, k) ∈ IS  ⇔  …', '… (G, n − k) ∈ VERTEX COVER, certificate S ↦ V − S', '… (Ḡ, k) ∈ CLIQUE, certificate S ↦ S', 'C covers G ⇔ no edge inside V − C', 'Ḡ joins exactly the pairs G leaves apart'].join('\n') },
      ] } };
    },
    predict: [
      { at: (fr) => fr.meta && fr.meta.cover && fr.meta.cover.length > 0, once: true, pick: 'item', ask: 'Which vertices will form the vertex cover? Click one of them.', answer: (all, i) => all[i].meta.cover, explain: 'The cover is everything outside S: V − S.' },
      { at: (fr) => fr.meta && fr.meta.compCount !== undefined, once: true, pick: 'option', options: (all, i) => { const m = all[i].meta; return [...new Set([m.compCount, m.ge, m.total, m.compCount + 1])].sort((a, b) => a - b).map(String); },
        ask: 'How many edges will the complement graph have?', answer: (all, i) => String(all[i].meta.compCount), explain: (all, i) => 'n(n − 1)/2 pairs in all, minus the ' + all[i].meta.ge + ' edges of G.' },
    ],
    quiz: [
      { q: 'S is an independent set of G. Which set is a vertex cover of G?', options: ['S', 'V − S', 'The neighbours of S', 'The edges of S'], answer: 1, why: 'No edge lies inside S, so each edge has an end in V − S.' },
      { q: 'The reduction INDEPENDENT SET → VERTEX COVER maps (G, k) to…', options: ['(G, k)', '(G, n − k)', '(Ḡ, k)', '(Ḡ, n − k)'], answer: 1, why: 'Same graph; an independent set of size k exists exactly when a cover of size n − k does.' },
      { q: 'In the complement graph, an independent set of G becomes…', options: ['A vertex cover', 'A clique', 'An independent set', 'A path'], answer: 1, why: 'Every pair not joined in G is joined in Ḡ.' },
      { q: 'G is the complete graph K₄. What is its largest independent set, and its complement?', options: ['Size 4; Ḡ = K₄', 'Size 1; Ḡ has no edges', 'Size 2; Ḡ is a square', 'Size 0; Ḡ = K₄'], answer: 1, why: 'Every pair is joined, so only single vertices are independent, and the complement keeps no edge at all.' },
      { q: 'Why does it matter that these reductions run in polynomial time?', options: ['It does not matter', 'So a fast algorithm for one problem would give a fast algorithm for the others', 'So the graphs stay small', 'To make the certificates shorter'], answer: 1, why: 'Polynomial-time reductions transfer membership in P (and NP-hardness) between problems.' },
    ],
  });
})();
