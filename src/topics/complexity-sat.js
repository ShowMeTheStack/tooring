// SAT: formulas lit clause by clause as variables are set, and every assignment counted; the DPLL search
// tree beside the formula, with unit propagation and pure literals as forced moves and conflicts that send
// the search back; 2-SAT as an implication graph whose strongly connected components decide everything;
// and random 3-SAT, easy when short or long and hard in between, near four clauses per variable.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'cx-sat', part: 'complexity', order: 40, title: 'Satisfiability', blurb: 'Boolean formulas in clause form: what an assignment does to them, how a solver searches, why two literals per clause is easy and three is not, and where random formulas are hardest.' });

  // ---------------------------------------------------------------------------------------------------------
  // shared: a formula from text, allowing the empty clause (written () or □) and the empty formula (⊤ or nothing)
  function parseF(text) {
    let src = String(text === undefined || text === null ? '' : text).trim();
    if (src === '' || src === '⊤') return { n: 0, clauses: [], names: [null] };
    src = src.replace(/\)\s*\(/g, ') ∧ (');
    const parts = src.split(/∧|&|\band\b|\n/).map((p) => p.trim()).filter((p) => p !== '');
    const isEmpty = (p) => { const q = p.replace(/[()\s]/g, ''); return q === '' || q === '□'; };
    const rest = parts.filter((p) => !isEmpty(p));
    const g = rest.length ? T.sat.parse(rest.join(' ∧ ')) : { n: 0, clauses: [], names: [null] };
    if (g.clauses.length !== rest.length) return g;
    const clauses = [];
    let k = 0;
    for (const p of parts) clauses.push(isEmpty(p) ? [] : g.clauses[k++]);
    return { n: g.n, clauses, names: g.names };
  }
  const clauseText = (f, c) => (c.length ? '(' + c.map((l) => T.sat.litText(f, l)).join(' ∨ ') + ')' : '□');
  const defLines = (f) => (f.clauses.length ? f.clauses.map((c, i) => 'C' + (i + 1) + ' = ' + clauseText(f, c)).join('\n') : 'no clauses: φ = ⊤');
  const checkF = (v, maxN, maxM) => { let f; try { f = parseF(v); } catch (e) { return 'Formula: ' + e.message + '; write clauses like (x ∨ ¬y) ∧ (y ∨ z)'; } if (f.n > maxN) return 'Formula: at most ' + maxN + ' variables, so the picture stays readable'; if (f.clauses.length > maxM) return 'Formula: at most ' + maxM + ' clauses'; if (f.clauses.some((c) => c.length > 4)) return 'Formula: at most 4 literals in a clause'; return null; };
  const bitsOf = (a, n) => { let s = ''; for (let v = 1; v <= n; v++) s += a[v] ? '1' : '0'; return s || 'ε'; };
  const rowA = (r, n) => { const a = [null]; for (let v = 1; v <= n; v++) a.push(!!(r & (1 << (n - v)))); return a; };

  // ---------------------------------------------------------------------------------------------------------
  // 5. formulas and assignments
  T.topic({
    id: 'cx-sat-assign', family: 'cx-sat', order: 10, title: 'Formulas and assignments',
    blurb: 'A formula in clause form is true when every clause has a true literal. Set the variables one by one and watch clauses turn green or red, then run through every assignment and count the ones that work.',
    inputs: [
      { id: 'f', kind: 'text', label: 'Formula φ', def: '(x ∨ ¬y ∨ z) ∧ (¬x ∨ y) ∧ (y ∨ ¬z) ∧ (¬x ∨ ¬z)' },
      { id: 'v', kind: 'text', label: 'Values, in order', def: 'y=0 x=1 z=0' },
    ],
    check: (inp) => {
      const e = checkF(inp.f, 4, 6); if (e) return e;
      const f = parseF(inp.f);
      for (const tok of String(inp.v || '').split(/[\s,;]+/).filter(Boolean)) {
        const m = /^([A-Za-z_][\w']*)\s*=\s*([01])$/.exec(tok);
        if (!m) return 'Values: write them like x=1 y=0, not "' + tok + '"';
        if (f.names.indexOf(m[1]) < 1) return 'Values: φ has no variable ' + m[1];
      }
      return null;
    },
    presets: [
      { label: 'Set y, then x, then z', values: { f: '(x ∨ ¬y ∨ z) ∧ (¬x ∨ y) ∧ (y ∨ ¬z) ∧ (¬x ∨ ¬z)', v: 'y=0 x=1 z=0' } },
      { label: 'One value sinks a clause early', values: { f: '(x ∨ y) ∧ (¬x) ∧ (¬y ∨ z)', v: 'x=1 y=1 z=1' } },
      { label: 'The empty clause: never true', values: { f: '(x ∨ y) ∧ () ∧ (¬x)', v: 'x=0' } },
      { label: 'The empty formula: always true', values: { f: '⊤', v: '' } },
      { label: 'Every assignment works', values: { f: '(x ∨ ¬x) ∧ (y ∨ ¬y ∨ z)', v: 'x=0 y=1' } },
    ],
    counters: [{ id: 'set', label: 'variables set' }, { id: 'rows', label: 'assignments tried' }, { id: 'models', label: 'satisfying ones' }],
    run(inp) {
      const f = parseF(inp.f), n = f.n, N = 2 ** n;
      const order = String(inp.v || '').split(/[\s,;]+/).filter(Boolean).map((t) => { const m = /^([A-Za-z_][\w']*)\s*=\s*([01])$/.exec(t); return { v: f.names.indexOf(m[1]), b: m[2] === '1' }; });
      const F = new T.Frames(['set', 'rows', 'models']);
      const fx = -360, fy = 0;
      const fm = (a, hot) => (f.clauses.length ? K.cx.formula({ f, a, x: fx, y: fy, maxW: 720, labels: true, hot: hot || [], prefix: 'fm' }) : K.cx.note({ x: fx + 200, y: fy, lines: ['φ = ⊤', 'no clauses, nothing to satisfy'], prefix: 'fm' }));
      const fb = fm([]).box;
      const chipY = fb.y + fb.h + 24;
      const chips = (a, hot) => (n ? K.cx.assignment({ f, a, x: fx + 110, y: chipY, hot, label: 'values', prefix: 'as' }).items : []);
      const status = (a) => f.clauses.map((c) => { if (c.some((l) => { const x = a[Math.abs(l)]; return x !== null && x !== undefined && (l > 0 ? x : !x); })) return 'sat'; if (c.every((l) => { const x = a[Math.abs(l)]; return x !== null && x !== undefined; })) return 'false'; return 'open'; });
      const keysOf = (i) => ['fm:c:' + i].concat(f.clauses[i].map((_, j) => 'fm:l:' + i + ':' + j));
      // phase 1: set the given values one at a time
      let a = new Array(n + 1).fill(null);
      F.add({ items: fm(a).items.concat(chips(a)), say: f.clauses.length ? 'φ has ' + f.clauses.length + ' clause' + (f.clauses.length === 1 ? '' : 's') + ' over ' + n + ' variable' + (n === 1 ? '' : 's') + '. It is true when every clause has at least one true literal.' + (f.clauses.some((c) => !c.length) ? ' One clause, □, is empty: it has no literal that could ever be true.' : '') : 'φ has no clauses at all. "Every clause is satisfied" is then true with nothing to check: the empty formula is always true.', hl: { f: [] } });
      order.forEach(({ v, b }, k) => {
        const before = status(a);
        a = a.slice(); a[v] = b;
        const after = status(a);
        F.count('set');
        const won = after.map((s, i) => (s === 'sat' && before[i] !== 'sat' ? i : -1)).filter((i) => i >= 0);
        const lost = after.map((s, i) => (s === 'false' && before[i] !== 'false' ? i : -1)).filter((i) => i >= 0);
        const name = f.names[v], tl = T.sat.litText(f, b ? v : -v);
        let say = 'Set ' + name + ' = ' + (b ? 1 : 0) + ': the literal ' + tl + ' is now true and ' + T.sat.litText(f, b ? -v : v) + ' false.';
        if (won.length) say += ' ' + won.map((i) => 'C' + (i + 1)).join(', ') + (won.length === 1 ? ' is' : ' are') + ' satisfied.';
        if (lost.length) say += ' ' + lost.map((i) => 'C' + (i + 1)).join(', ') + ' now ha' + (lost.length === 1 ? 's' : 've') + ' every literal false, so φ is false whatever comes next.';
        if (!won.length && !lost.length) say += ' No clause is decided by this.';
        F.add({ items: fm(a, won.concat(lost)).items.concat(chips(a, [v])), say, hl: { f: won.concat(lost) }, meta: { k } });
        F.list[F.list.length - 2].meta = Object.assign({}, F.list[F.list.length - 2].meta, { nextName: name + ' = ' + (b ? 1 : 0), nextWon: [].concat(...won.map(keysOf)) });
      });
      if (order.length) {
        const st = status(a);
        const unset = f.names.slice(1).filter((_, i) => a[i + 1] === null);
        const sayEnd = st.includes('false') ? 'Under these values φ is false: one false clause is enough.' : st.every((s) => s === 'sat') ? 'Every clause has a true literal: these values satisfy φ' + (unset.length ? ', whatever ' + unset.join(', ') + ' turn' + (unset.length === 1 ? 's' : '') + ' out to be.' : '.') : 'Some clause still depends on ' + unset.join(', ') + ': φ is not decided yet.';
        F.add({ items: fm(a).items.concat(chips(a)), say: sayEnd });
      }
      // phase 2: every assignment, as a truth table
      const perRow = n >= 3 ? 8 : 4, CW = Math.max(52, 34 + 15 * n);
      const gw = Math.min(N, perRow) * (CW + 8) - 8;
      const gx = fx + 360 - gw / 2, gy = chipY + (n ? 100 : 20);
      const grid = (done, hot) => {
        const items = [];
        if (n) items.push({ key: 'gr:label', kind: 'text', x: gx - 10, y: gy + 25, text: f.names.slice(1).join(' '), anchor: 'end', cls: 'mono' });
        for (let r = 0; r < N; r++) {
          const ok = T.sat.evaluate(f, rowA(r, n)), d = done > r;
          items.push({ key: 'gr:' + r, kind: 'cell', x: gx + (r % perRow) * (CW + 8), y: gy + Math.floor(r / perRow) * 50, w: CW, h: 40, rx: 6, text: bitsOf(rowA(r, n), n) + (d ? (ok ? ' ✓' : ' ✗') : ''), cls: 'mono ' + (d ? (ok ? 'good' : 'bad') : '') + (hot === r ? ' hot' : '') });
        }
        return items;
      };
      const count = Array.from({ length: N }, (_, r) => T.sat.evaluate(f, rowA(r, n))).filter(Boolean).length;
      F.add({ items: fm([]).items.concat(chips(new Array(n + 1).fill(null)), grid(0)), say: 'Now try every assignment: ' + n + ' variable' + (n === 1 ? '' : 's') + ' give 2' + K.cx.sup(n) + ' = ' + N + ' of them' + (n ? '' : ', the single empty assignment') + '. Each is checked clause by clause.', meta: { countStart: true, count, N } });
      const step = N > 8 ? 2 : 1;
      let models = 0;
      for (let r = 0; r < N; r += step) {
        const rows = [];
        for (let q = r; q < Math.min(N, r + step); q++) { rows.push(q); F.count('rows'); if (T.sat.evaluate(f, rowA(q, n))) { models++; F.count('models'); } }
        const q = rows[rows.length - 1], aq = rowA(q, n);
        const bad = f.clauses.findIndex((c) => !T.sat.evalClause(c, aq));
        F.add({ items: fm(aq, bad >= 0 ? [bad] : []).items.concat(chips(aq), grid(q + 1, q)), say: rows.map((x) => { const ax = rowA(x, n), b2 = f.clauses.findIndex((c) => !T.sat.evalClause(c, ax)); return (n ? bitsOf(ax, n) : 'The empty assignment') + (b2 < 0 ? ' satisfies φ' : ' fails at C' + (b2 + 1)); }).join('; ') + '.' });
      }
      F.add({ items: fm([]).items.concat(chips(new Array(n + 1).fill(null)), grid(N)), say: models + ' of the ' + N + ' assignments satisfy φ. ' + (models === 0 ? 'None does: φ is unsatisfiable.' : models === N ? 'All do: φ is valid, a tautology.' : 'φ is satisfiable but not valid.') + ' Counting this way takes 2ⁿ checks, which is hopeless once n is large.', mark: models ? 'satisfiable' : 'unsatisfiable' });
      return { frames: F.list, def: { sections: [
        { id: 'f', kind: 'math', title: 'φ in clause form', text: defLines(f) },
        { id: 'r', kind: 'text', title: 'Truth', text: 'A literal is a variable or its negation. A clause is true when one of its literals is; φ is true when all its clauses are. The empty clause □ is always false, the empty formula ⊤ always true.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.nextWon && f.meta.nextWon.length, once: true, ask: (fr, i) => 'Next: ' + fr[i].meta.nextName + '. Click a clause it will satisfy.', answer: (fr, i) => fr[i].meta.nextWon, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.countStart, once: true, pick: 'option', options: (fr, i) => { const { count, N } = fr[i].meta; return [...new Set([count, N - count, Math.floor(N / 2), 0, N])].slice(0, 4).sort((x, y) => x - y).map(String); }, ask: (fr, i) => 'How many of the ' + fr[i].meta.N + ' assignments will satisfy φ?', answer: (fr, i) => String(fr[i].meta.count), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'When is a clause (x ∨ ¬y ∨ z) false?', options: ['When x is false', 'When x = 0, y = 1 and z = 0', 'When y is true', 'Never'], answer: 1, why: 'A clause is false only when every one of its literals is false: x false, ¬y false (so y true), z false.' },
      { q: 'What is the truth value of the empty clause □?', options: ['Always true', 'Always false', 'It depends on the assignment', 'Undefined'], answer: 1, why: 'A clause needs some true literal; the empty clause has none to offer, under any assignment.' },
      { q: 'What is the truth value of a formula with no clauses?', options: ['Always true', 'Always false', 'It depends', 'Undefined'], answer: 0, why: 'All of its clauses are satisfied, vacuously: there are none.' },
      { q: 'A formula has 20 variables. How many assignments would a truth table list?', options: ['20', '400', 'about a million', 'about 20!'], answer: 2, why: '2²⁰ = 1 048 576, and every extra variable doubles it.' },
      { q: 'After setting some variables, one clause has every literal false. What can the remaining variables do?', options: ['Fix it', 'Nothing: φ is false under any completion', 'Make φ unsatisfiable', 'Make that clause a unit'], answer: 1, why: 'The clause does not mention them, or it would not be fully false; φ stays false.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // 6. DPLL
  T.topic({
    id: 'cx-dpll', family: 'cx-sat', order: 20, title: 'DPLL: search with forced moves',
    blurb: 'A SAT solver guesses a value, then lets the formula force what it can: a clause with one literal left must make it true (a unit), and a literal that appears with one sign only can safely be made true (pure). A conflict sends it back up the tree.',
    inputs: [
      { id: 'f', kind: 'text', label: 'Formula φ', def: '(x ∨ y ∨ z) ∧ (¬x ∨ y) ∧ (¬y ∨ z) ∧ (¬z ∨ ¬x) ∧ (x ∨ ¬y ∨ ¬z)' },
      { id: 'pure', kind: 'choice', label: 'Pure literal rule', def: 'on', options: [{ value: 'on', label: 'on' }, { value: 'off', label: 'off' }] },
    ],
    check: (inp) => { const e = checkF(inp.f, 5, 9); if (e) return e; if (!parseF(inp.f).clauses.length) return 'Formula: give at least one clause'; return null; },
    presets: [
      { label: 'Two conflicts, then a model', values: { f: '(x ∨ y ∨ z) ∧ (¬x ∨ y) ∧ (¬y ∨ z) ∧ (¬z ∨ ¬x) ∧ (x ∨ ¬y ∨ ¬z)', pure: 'on' } },
      { label: 'Unsatisfiable: every branch fails', values: { f: '(x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ z) ∧ (¬x ∨ ¬z)', pure: 'on' } },
      { label: 'Solved by units alone, no guess', values: { f: '(a) ∧ (¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ ¬a ∨ d)', pure: 'on' } },
      { label: 'Pure literals do the work', values: { f: '(p ∨ q) ∧ (p ∨ ¬r) ∧ (¬q ∨ ¬r) ∧ (q ∨ s)', pure: 'on' } },
      { label: 'The same without pure literals', values: { f: '(p ∨ q) ∧ (p ∨ ¬r) ∧ (¬q ∨ ¬r) ∧ (q ∨ s)', pure: 'off' } },
    ],
    counters: [{ id: 'decide', label: 'guesses' }, { id: 'unit', label: 'unit moves' }, { id: 'pure', label: 'pure moves' }, { id: 'conflict', label: 'conflicts' }],
    run(inp) {
      const f = parseF(inp.f), n = f.n;
      const r = T.sat.dpll(f, { pure: inp.pure !== 'off', traceLimit: 400, maxNodes: 300 });
      const F = new T.Frames(['decide', 'unit', 'pure', 'conflict']);
      const tree = r.tree;
      const asgOf = new Map([[0, new Array(n + 1).fill(null)]]);
      const whyOf = new Map([[0, {}]]);
      const seen = new Set([0]);
      const status = new Map();       // node -> 'conflict' | 'sat' | 'failed'
      const fx = -380;
      const fb = K.cx.formula({ f, x: fx, y: 0, maxW: 760, labels: true }).box;
      const chipY = fb.y + fb.h + 22, treeY = chipY + 110;
      const val = (a, l) => { const x = a[Math.abs(l)]; return x === null || x === undefined ? null : l > 0 ? x : !x; };
      const units = (a) => { const out = []; f.clauses.forEach((c, i) => { if (c.some((l) => val(a, l) === true)) return; const open = c.map((l, j) => [l, j]).filter(([l]) => val(a, l) === null); if (open.length === 1) out.push({ i, j: open[0][1], lit: open[0][0] }); }); return out; };
      const labelOf = (id) => (id === 0 ? 'φ' : T.sat.litText(f, Math.abs(tree[id].decision)) + ' = ' + (tree[id].decision > 0 ? 1 : 0));
      const drawTree = (cur) => {
        const mk = (id) => ({ id: 'n' + id, label: labelOf(id), cls: [status.get(id) === 'conflict' ? 'bad' : status.get(id) === 'sat' ? 'good' : status.get(id) === 'failed' ? 'pruned' : '', id === cur && !status.has(id) ? 'hot' : ''].filter(Boolean).join(' '), children: tree.filter((t) => t.parent === id && seen.has(t.id)).map((t) => mk(t.id)) });
        const path = [];
        if (r.sat && status.get(cur) === 'sat') for (let k = cur; k >= 0; k = tree[k].parent) path.unshift('n' + k);
        return K.tree.draw(mk(0), { x: 0, y: treeY, gapY: 74, path, prefix: 'tr' }).items;
      };
      const scene = (cur, hot) => {
        const a = asgOf.get(cur);
        const why = {};
        for (const [v, w] of Object.entries(whyOf.get(cur))) why[v] = w;
        const us = units(a);
        return { items: K.cx.formula({ f, a, x: fx, y: 0, maxW: 760, labels: true, hot }).items.concat(K.cx.assignment({ f, a, x: fx + 110, y: chipY, why, label: 'values', prefix: 'as', hot: [] }).items, drawTree(cur)), units: [].concat(...us.map((u) => ['cnf:l:' + u.i + ':' + u.j])) };
      };
      let cur = 0;
      const s0 = scene(0, []);
      F.add({ items: s0.items, say: 'DPLL starts at the root φ with nothing assigned. It first does every forced move, and guesses only when nothing is forced.', meta: { units: s0.units } });
      for (const st of r.trace) {
        let hot = [], say = st.say;
        if (st.kind === 'decide') {
          const p = tree[st.node].parent;
          seen.add(st.node);
          const a = asgOf.get(p).slice(); a[Math.abs(st.lit)] = st.lit > 0;
          asgOf.set(st.node, a);
          whyOf.set(st.node, Object.assign({}, whyOf.get(p), { [Math.abs(st.lit)]: 'guess' }));
          cur = st.node;
          F.count('decide');
          say = 'Nothing is forced, so guess: ' + T.sat.litText(f, Math.abs(st.lit)) + ' = ' + (st.lit > 0 ? 1 : 0) + (tree.some((t) => t.parent === p && t.id < st.node) ? ', the other value, since the first one failed.' : '.');
        } else if (st.kind === 'unit' || st.kind === 'pure') {
          const before = asgOf.get(st.node);
          if (st.kind === 'unit') { const u = units(before).find((x) => x.lit === st.lit); if (u) hot = [u.i]; }
          else hot = f.clauses.map((c, i) => (c.includes(st.lit) && !c.some((l) => val(before, l) === true) ? i : -1)).filter((i) => i >= 0);
          const a = before.slice(); a[Math.abs(st.lit)] = st.lit > 0;
          asgOf.set(st.node, a);
          whyOf.set(st.node, Object.assign({}, whyOf.get(st.node), { [Math.abs(st.lit)]: st.kind }));
          cur = st.node;
          F.count(st.kind);
          const nm = T.sat.litText(f, st.lit);
          say = st.kind === 'unit' ? (hot.length ? 'C' + (hot[0] + 1) + ' has only ' + nm + ' left: ' : 'A clause has only ' + nm + ' left: ') + nm + ' must be true, no guess needed.' : nm + ' appears only with this sign in the clauses still open' + (hot.length ? ' (' + hot.map((i) => 'C' + (i + 1)).join(', ') + ')' : '') + ': making it true can only help.';
        } else if (st.kind === 'conflict') {
          status.set(st.node, 'conflict');
          cur = st.node;
          const a = asgOf.get(st.node);
          const bad = f.clauses.findIndex((c) => c.every((l) => val(a, l) === false));
          if (bad >= 0) hot = [bad];
          F.count('conflict');
          say = (bad >= 0 ? 'Conflict: C' + (bad + 1) + ' has every literal false.' : 'Conflict: some clause has every literal false.') + ' This branch is dead; back up.';
        } else if (st.kind === 'backtrack') {
          status.set(st.node, 'failed');
          cur = st.node;
          say = 'Both values of ' + T.sat.litText(f, st.var) + ' failed below this node, so it fails too.';
        } else if (st.kind === 'sat') {
          status.set(st.node, 'sat');
          cur = st.node;
          say = 'Every clause has a true literal: a satisfying assignment, found after ' + F.counts.decide + ' guess' + (F.counts.decide === 1 ? '' : 'es') + '.';
        } else if (st.kind === 'unsatisfiable') {
          status.set(0, status.get(0) || 'failed');
          cur = 0;
          say = 'Every branch ended in a conflict, so φ is unsatisfiable. The whole tree is the proof, and it can be exponentially large.';
        } else if (st.kind === 'satisfiable') say = 'φ is satisfiable; the green path in the tree is the assignment, and the dead branches are the price of the guesses.';
        else if (st.kind === 'limit') say = 'The search tree grew past the limit of this picture, so it stops here.';
        const sc = scene(cur, hot);
        const end = ['satisfiable', 'unsatisfiable', 'limit'].includes(st.kind);
        F.add({ items: sc.items, say, hl: { f: hot }, mark: end ? (r.sat ? 'satisfiable' : 'unsatisfiable') : undefined, meta: { kind: st.kind, units: sc.units, sat: r.sat } });
      }
      return { frames: F.list, result: r.sat, def: { sections: [
        { id: 'f', kind: 'math', title: 'φ', text: defLines(f) },
        { id: 'rules', kind: 'math', title: 'The moves, in this order', text: 'unit: a clause with one open literal → make it true' + (inp.pure !== 'off' ? '\npure: a literal with one sign only → make it true' : '') + '\nconflict: a clause all false → back up\nguess: otherwise, try x = 1, then x = 0' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'unit' && f.meta && f.meta.units && f.meta.units.length, once: true, ask: 'A clause is down to one literal. Click the literal that unit propagation will make true.', answer: (fr, i) => fr[i].meta.units, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 3, once: true, pick: 'option', options: ['Satisfiable', 'Unsatisfiable'], ask: 'Will this search end with a satisfying assignment?', answer: (fr) => (fr[fr.length - 1].meta.sat ? 'Satisfiable' : 'Unsatisfiable'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why is unit propagation safe?', options: ['It is a guess that is usually right', 'A clause with one open literal can only be satisfied by making it true', 'It removes clauses', 'It is not safe'], answer: 1, why: 'Every other literal of the clause is already false; if this one were false too, the clause would be false.' },
      { q: 'Why is setting a pure literal true safe?', options: ['It satisfies clauses and falsifies none', 'It always leads to a conflict', 'It is the last variable', 'Pure literals are units'], answer: 0, why: 'Its negation appears nowhere in the open clauses, so making it true cannot hurt any clause.' },
      { q: 'What does DPLL do after a conflict?', options: ['Stops: unsatisfiable', 'Backs up to the latest guess and tries the other value', 'Restarts from scratch', 'Removes a clause'], answer: 1, why: 'The conflict shows this branch has no model; the search returns to the most recent guess not yet tried both ways.' },
      { q: 'For an unsatisfiable formula, what is DPLL\'s proof?', options: ['One assignment', 'The whole search tree, every branch closed by a conflict', 'The number of clauses', 'Nothing'], answer: 1, why: 'Unsatisfiability has no short certificate known in general; the closed tree covers every assignment.' },
      { q: 'Can a formula be solved without any guess?', options: ['Never', 'Yes, when forced moves alone satisfy it or produce a conflict at the root', 'Only if it has one variable', 'Only if it is unsatisfiable'], answer: 1, why: 'A chain of units can settle every variable, as in the preset solved by units alone.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // 7. 2-SAT by implications
  T.topic({
    id: 'cx-2sat', family: 'cx-sat', order: 30, title: '2-SAT: implications and components',
    blurb: 'With two literals per clause, (a ∨ b) says: if a is false then b is true, and if b is false then a is true. Draw these implications as arrows; the formula is unsatisfiable exactly when some x and ¬x can reach each other.',
    inputs: [{ id: 'f', kind: 'text', label: 'Formula (clauses of one or two literals)', def: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z) ∧ (y ∨ w)' }],
    check: (inp) => { const e = checkF(inp.f, 4, 7); if (e) return e; const f = parseF(inp.f); if (!f.clauses.length) return 'Formula: give at least one clause'; if (f.clauses.some((c) => c.length > 2 || !c.length)) return 'Formula: 2-SAT needs clauses of one or two literals'; return null; },
    presets: [
      { label: 'Satisfiable, four variables', values: { f: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z) ∧ (y ∨ w)' } },
      { label: 'Unsatisfiable: x and ¬x on one cycle', values: { f: '(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)' } },
      { label: 'A one-literal clause (p) is p ∨ p', values: { f: '(p) ∧ (¬p ∨ q) ∧ (¬q ∨ r)' } },
      { label: 'A long chain of implications', values: { f: '(¬a ∨ b) ∧ (¬b ∨ c) ∧ (¬c ∨ d) ∧ (¬d ∨ ¬a)' } },
    ],
    counters: [{ id: 'edges', label: 'implication arrows' }, { id: 'sccs', label: 'components' }],
    run(inp) {
      const f = parseF(inp.f), n = f.n;
      const r = T.sat.twoSat(f);
      const L = (l) => T.sat.litText(f, l);
      const lits = []; for (let v = 1; v <= n; v++) lits.push(v, -v);
      const imp = [];
      f.clauses.forEach((c, i) => { const [a, b] = c.length === 1 ? [c[0], c[0]] : c; imp.push({ from: -a, to: b, clause: i }); if (a !== b) imp.push({ from: -b, to: a, clause: i }); });
      const full = { kind: 'pda', states: lits.map(L), start: null, accept: [], trans: imp.map((e) => ({ from: L(e.from), to: L(e.to), label: '' })) };
      // x above ¬x, variables side by side: implications mostly run between the rows
      const pos = {};
      for (let v = 1; v <= n; v++) { pos[L(v)] = { x: (v - 1) * 150 + (v % 2 ? 0 : 40), y: 0 }; pos[L(-v)] = { x: (v - 1) * 150 + (v % 2 ? 40 : 0), y: 190 }; }
      const lay = K.graph.layout(full, { fixed: pos }).pos;
      const comp = new Map();
      r.components.forEach((members, k) => members.forEach((m) => comp.set(m, k)));
      const big = r.components.map((m, k) => (m.length > 1 ? k : -1)).filter((k) => k >= 0);
      const F = new T.Frames(['edges', 'sccs']);
      const fy = -150;
      const fm = (hot, a) => K.cx.formula({ f, a: a || [], x: -30, y: fy, maxW: Math.max(560, n * 150), labels: true, hot: hot || [], prefix: 'fm' }).items;
      const graph = (upto, opts) => {
        opts = opts || {};
        const m = { kind: 'pda', states: full.states, start: null, accept: [], trans: imp.slice(0, upto).map((e) => ({ from: L(e.from), to: L(e.to), label: '' })) };
        const cls = {};
        if (opts.scc) for (const s of full.states) { const k = comp.get(s); if (opts.scc.includes(k)) cls[s] = 'scc' + (big.indexOf(k) % 6); }
        if (opts.val) for (const l of lits) cls[L(l)] = (opts.val[Math.abs(l)] === (l > 0)) ? 'good' : 'faded';
        const edgeCls = {};
        for (const e of imp.slice(Math.max(0, upto - (opts.fresh || 0)), upto)) edgeCls[L(e.from) + '>' + L(e.to)] = 'hot';
        for (const k of opts.cycle || []) edgeCls[k] = 'bad thick';
        // implication graphs are dense: arrows may cross one another (never states or labels)
        return K.graph.draw(m, { pos: lay, cls, edgeCls, hot: opts.hot || [], bad: opts.bad || [] }).items.map((it) => (it.kind === 'edge' ? Object.assign(it, { audit: 'edge-x' }) : it));
      };
      F.add({ items: fm().concat(graph(0)), say: 'One node per literal: ' + lits.map(L).join(', ') + '. Each clause will add two arrows of the form "if this literal is false, that one must be true".', hl: { f: [] } });
      let upto = 0;
      f.clauses.forEach((c, i) => {
        const mine = imp.filter((e) => e.clause === i);
        upto += mine.length;
        F.set('edges', upto);
        const say = c.length === 1 ? clauseText(f, c) + ' is ' + L(c[0]) + ' ∨ ' + L(c[0]) + ': one arrow ' + L(-c[0]) + ' → ' + L(c[0]) + ', so if ' + L(c[0]) + ' were false it would have to be true.' : clauseText(f, c) + ': if ' + L(c[0]) + ' is false then ' + L(c[1]) + ' is true, and if ' + L(c[1]) + ' is false then ' + L(c[0]) + ' is true. Arrows ' + mine.map((e) => L(e.from) + ' → ' + L(e.to)).join(' and ') + '.';
        F.add({ items: fm([i]).concat(graph(upto, { fresh: mine.length })), say, hl: { f: [i] } });
      });
      // what x implies: everything reachable from it
      const reach = (s) => { const seen = new Set([s]), q = [s]; while (q.length) { const u = q.shift(); for (const e of imp) if (L(e.from) === u && !seen.has(L(e.to))) { seen.add(L(e.to)); q.push(L(e.to)); } } return seen; };
      const x1 = L(1), fromX = [...reach(x1)].filter((s) => s !== x1);
      F.list[F.list.length - 1].meta = { reachAsk: fromX.map((s) => 'g:s:' + s), x1 };
      F.add({ items: fm().concat(graph(upto, { hot: [x1].concat(fromX) })), say: 'Follow the arrows from ' + x1 + ': setting it true forces ' + (fromX.length ? fromX.join(', ') : 'nothing at all') + '. No branching: one choice sets off a chain of forced values, which is why 2-SAT is easy.' });
      const shown = [];
      big.forEach((k) => {
        shown.push(k);
        F.set('sccs', shown.length);
        F.add({ items: fm().concat(graph(upto, { scc: shown })), say: 'A strongly connected component: ' + r.components[k].join(', ') + ' all reach each other along arrows, so they must all be true together or all false together.' });
      });
      F.set('sccs', r.components.length);
      if (!big.length) F.add({ items: fm().concat(graph(upto)), say: 'No two literals reach each other both ways: every component is a single literal, ' + r.components.length + ' in all.' });
      const bad = r.trace.find((t) => t.kind === 'conflict');
      if (bad) {
        const v = bad.var, a = L(v), b = L(-v);
        // a cycle a → … → b → … → a, by breadth-first paths
        const pathTo = (s, t) => { const prev = new Map([[s, null]]), q = [s]; while (q.length) { const u = q.shift(); if (u === t) break; for (const e of imp) { const x = L(e.from), y = L(e.to); if (x === u && !prev.has(y)) { prev.set(y, u); q.push(y); } } } const out = []; for (let u = t; prev.get(u) !== null && prev.get(u) !== undefined; u = prev.get(u)) out.unshift(prev.get(u) + '>' + u); return out; };
        const cyc = pathTo(a, b).concat(pathTo(b, a));
        F.add({ items: fm().concat(graph(upto, { scc: big, cycle: cyc, bad: [a, b] })), say: a + ' and ' + b + ' sit in the same component: ' + a + ' forces ' + b + ' and ' + b + ' forces ' + a + '. Whatever value ' + a + ' takes, it would have to take the other one too, so φ is unsatisfiable.', mark: 'unsatisfiable', meta: { sat: false } });
      } else {
        const asg = r.assignment;
        F.add({ items: fm([], asg).concat(graph(upto, { val: asg })), say: 'No variable shares a component with its negation, so φ is satisfiable. Taking components from the end of the arrows backwards, each gets true unless its negation already did: ' + f.names.slice(1).map((nm, i) => nm + ' = ' + (asg[i + 1] ? 1 : 0)).join(', ') + '. Every clause is green.', mark: 'satisfiable', meta: { sat: true } });
      }
      return { frames: F.list, result: r.sat, def: { sections: [
        { id: 'f', kind: 'math', title: 'φ', text: defLines(f) },
        { id: 'imp', kind: 'math', title: 'Implications', text: imp.map((e) => L(e.from) + ' → ' + L(e.to) + '   from C' + (e.clause + 1)).join('\n') },
        { id: 'thm', kind: 'text', title: 'The test', text: 'φ is satisfiable exactly when no variable x has x and ¬x in the same strongly connected component. Components are found in linear time, so 2-SAT is in P.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.reachAsk && f.meta.reachAsk.length, once: true, ask: (fr, i) => 'Suppose ' + fr[i].meta.x1 + ' is true. Click a literal that this forces to be true.', answer: (fr, i) => fr[i].meta.reachAsk, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Satisfiable', 'Unsatisfiable'], ask: 'Is φ satisfiable?', answer: (fr) => (fr[fr.length - 1].meta.sat ? 'Satisfiable' : 'Unsatisfiable'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Which arrows does the clause (a ∨ ¬b) add?', options: ['a → ¬b and b → ¬a', '¬a → ¬b and b → a', 'a → b and ¬b → ¬a', 'only ¬a → ¬b'], answer: 1, why: 'If a is false then ¬b must be true; if ¬b is false (b true) then a must be true.' },
      { q: 'When is a 2-SAT formula unsatisfiable?', options: ['When it has a cycle', 'When some x and ¬x are in the same strongly connected component', 'When it has more clauses than variables', 'When some literal has no arrows'], answer: 1, why: 'Then x forces ¬x and ¬x forces x, so neither value is possible.' },
      { q: 'Why is 2-SAT easy while 3-SAT is NP-complete?', options: ['3-SAT has more variables', 'With two literals, a false literal forces the other one; with three, it leaves a choice', '2-SAT formulas are shorter', 'Nobody knows'], answer: 1, why: 'A two-literal clause turns into implications, and following implications needs no search. A three-literal clause with one literal false still leaves two options.' },
      { q: 'How is a one-literal clause (p) handled?', options: ['It is ignored', 'As (p ∨ p): one arrow ¬p → p', 'As two arrows p → ¬p', 'It makes the formula unsatisfiable'], answer: 1, why: 'If p were false, p would have to be true: the arrow ¬p → p rules p = false out.' },
      { q: 'How long does the component test take on a formula with n variables and m clauses?', options: ['O(n + m)', 'O(2ⁿ)', 'O(n!)', 'O(m²ⁿ)'], answer: 0, why: 'The graph has 2n nodes and 2m arrows, and strongly connected components are found in one pass.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // 8. the phase transition in random 3-SAT
  // a small DPLL that counts the nodes of its search tree (unit propagation, branching on a shortest clause)
  function searchNodes(f) {
    const n = f.n, cl = f.clauses, val = new Int8Array(n + 1);
    let nodes = 0;
    const go = () => {
      nodes++;
      const trail = [];
      const undo = () => { for (const v of trail) val[v] = 0; };
      for (;;) {
        let changed = false, best = null, bestLen = 9, open = false;
        for (let i = 0; i < cl.length; i++) {
          const c = cl[i];
          let free = 0, last = 0, sat = false;
          for (let j = 0; j < c.length; j++) { const l = c[j], x = l > 0 ? val[l] : -val[-l]; if (x === 1) { sat = true; break; } if (x === 0) { free++; last = l; } }
          if (sat) continue;
          if (!free) { undo(); return false; }
          if (free === 1) { const v = last > 0 ? last : -last; val[v] = last > 0 ? 1 : -1; trail.push(v); changed = true; continue; }
          open = true;
          if (free < bestLen) { bestLen = free; best = c; }
        }
        if (changed) continue;
        if (!open) return true;
        let v = n + 1;
        for (const l of best) { const a = l > 0 ? l : -l; if (!val[a] && a < v) v = a; }
        for (const s of [1, -1]) { val[v] = s; if (go()) return true; val[v] = 0; }
        undo(); return false;
      }
    };
    const sat = go();
    return { sat, nodes };
  }
  const RATIOS = [1.5, 2, 2.5, 3, 3.5, 4, 4.5, 5, 5.5, 6, 6.5, 7];
  T.topic({
    id: 'cx-phase', family: 'cx-sat', order: 40, title: 'Random 3-SAT: where the hard formulas live',
    blurb: 'Make random 3-clause formulas with n variables and m clauses. With few clauses almost all are satisfiable and easy; with many, almost none are, and that is easy to see too. In between, near m/n ≈ 4.3, the answer flips and the solver works hardest.',
    inputs: [
      { id: 'n', kind: 'number', label: 'Variables n', def: 20, min: 6, max: 30 },
      { id: 'samples', kind: 'number', label: 'Formulas per ratio', def: 16, min: 6, max: 24 },
      { id: 'seed', kind: 'number', label: 'Seed', def: 7, min: 1, max: 9999 },
    ],
    presets: [
      { label: '20 variables', values: { n: 20, samples: 16, seed: 7 } },
      { label: '30 variables: a sharper edge', values: { n: 30, samples: 16, seed: 3 } },
      { label: '8 variables: blurry and easy', values: { n: 8, samples: 20, seed: 11 } },
      { label: '20 variables, other formulas', values: { n: 20, samples: 16, seed: 42 } },
    ],
    counters: [{ id: 'formulas', label: 'formulas solved' }, { id: 'nodes', label: 'search nodes in all' }],
    run(inp) {
      const n = inp.n, S = inp.samples;
      const R = T.sat.rng(inp.seed * 7919 + n);
      const data = RATIOS.map((ratio) => {
        const m = Math.round(ratio * n), runs = [];
        for (let s = 0; s < S; s++) {
          const clauses = [];
          for (let i = 0; i < m; i++) {
            const vs = [];
            while (vs.length < 3) { const v = 1 + R.int(n); if (!vs.includes(v)) vs.push(v); }
            clauses.push(vs.map((v) => (R() < 0.5 ? -v : v)));
          }
          runs.push(searchNodes({ n, clauses }));
        }
        const sorted = runs.map((x) => x.nodes).sort((a, b) => a - b);
        return { ratio, m, runs, pct: (100 * runs.filter((x) => x.sat).length) / S, median: sorted[Math.floor(S / 2)], total: sorted.reduce((a, b) => a + b, 0) };
      });
      const maxMed = Math.max(...data.map((d) => d.median));
      const peak = data.find((d) => d.median === maxMed);
      const F = new T.Frames(['formulas', 'nodes']);
      const W = 470, H = 150;
      const ymax = Math.max(10, Math.ceil(maxMed / 10) * 10);
      const scene = (k) => {
        const shown = data.slice(0, k + 1);
        const mark = k >= 0 ? [{ id: 'm', x: data[k].ratio, text: 'm/n = ' + data[k].ratio }] : [];
        const top = K.cx.plot({ x: 0, y: 0, w: W, h: H, xs: [1, 7.5], ys: [0, 100], xTicks: [], yTicks: [0, 50, 100], yTickText: (t) => t + '%', yLabel: 'satisfiable', marks: mark, series: [{ id: 'p', label: 'satisfiable', pts: shown.map((d) => [d.ratio, d.pct]), cls: 's1' }], prefix: 'pa' });
        const bot = K.cx.plot({ x: 0, y: H + 70, w: W, h: H, xs: [1, 7.5], ys: [0, ymax], xTicks: [2, 3, 4, 5, 6, 7], yTicks: [0, Math.round(ymax / 2), ymax], xLabel: 'clauses per variable, m/n', yLabel: 'search nodes (median)', marks: k >= 0 ? [{ id: 'm', x: data[k].ratio }] : [], series: [{ id: 'e', label: 'effort', pts: shown.map((d) => [d.ratio, d.median]), cls: 's4' }], prefix: 'pb' });
        const jar = [];
        if (k >= 0) {
          const d = data[k];
          jar.push({ key: 'jar:label', kind: 'text', x: W + 120, y: 14, text: 'm = ' + d.m + ' clauses', anchor: 'start', cls: 'strong' });
          d.runs.forEach((x, i) => jar.push({ key: 'jar:' + i, kind: 'cell', x: W + 120 + (i % 4) * 34, y: 28 + Math.floor(i / 4) * 34, w: 28, h: 28, rx: 5, text: '', cls: x.sat ? 'good' : 'bad', title: (x.sat ? 'satisfiable' : 'unsatisfiable') + ', ' + x.nodes + ' search nodes' }));
          jar.push({ key: 'jar:legend', kind: 'text', x: W + 120, y: 28 + Math.ceil(S / 4) * 34 + 16, text: d.runs.filter((x) => x.sat).length + ' sat, ' + d.runs.filter((x) => !x.sat).length + ' unsat', anchor: 'start', cls: 'strong', size: 14 });
        }
        return top.items.concat(bot.items, jar);
      };
      F.add({ items: scene(-1), say: 'Each formula has ' + n + ' variables and m clauses of 3 distinct variables with random signs. For each ratio m/n, ' + S + ' formulas are made and solved by DPLL, counting the nodes of its search tree.' });
      data.forEach((d, k) => {
        F.count('formulas', S).count('nodes', d.total);
        const sat = d.runs.filter((x) => x.sat).length;
        let say = 'm/n = ' + d.ratio + ' (' + d.m + ' clauses): ' + sat + ' of ' + S + ' satisfiable, median ' + d.median + ' search nodes. ';
        if (d.pct === 100 && d.ratio < 4) say += 'Few constraints: a model is found almost straight away.';
        else if (d.pct === 0) say += 'Overconstrained: conflicts appear after a few guesses, so unsatisfiability is quick to see.';
        else say += 'Near the edge: some formulas are satisfiable and some not, and telling which takes the most search.';
        F.add({ items: scene(k), say, meta: { k } });
      });
      const cross = data.find((d) => d.pct <= 50);
      F.add({ items: scene(data.length - 1), say: 'The satisfiable fraction falls from 100% to 0% around m/n ≈ ' + (cross ? cross.ratio : '4.3') + ', and the effort peaks at m/n = ' + peak.ratio + '. For large n the drop sharpens near 4.27 and the peak grows exponentially: hard instances sit at the threshold.', mark: 'peak at ' + peak.ratio, meta: { peak: peak.ratio } });
      return { frames: F.list, def: { sections: [
        { id: 'gen', kind: 'math', title: 'The experiment', text: 'n = ' + n + ' variables, ' + S + ' formulas per ratio\nclause: 3 distinct variables, random signs\nm = round(ratio × n), ratio from 1.5 to 7\neffort: nodes of the DPLL search tree' },
        { id: 'pt', kind: 'text', title: 'Phase transition', text: 'For random 3-SAT the chance of satisfiability drops from near 1 to near 0 in a narrow window around m/n ≈ 4.27, narrower as n grows. Worst-case hardness is a separate matter: NP-completeness is about every instance, not random ones.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.k === 2, once: true, pick: 'option', options: ['Below m/n = 3', 'Between 3.5 and 5.5', 'Above 6'], ask: 'Where will the solver work hardest?', answer: (fr) => { const p = fr[fr.length - 1].meta.peak; return p < 3 ? 'Below m/n = 3' : p <= 5.5 ? 'Between 3.5 and 5.5' : 'Above 6'; }, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why are random formulas with very many clauses easy?', options: ['They are always satisfiable', 'They are so constrained that conflicts show up after a few guesses', 'They have fewer variables', 'DPLL skips them'], answer: 1, why: 'With many clauses, unit propagation quickly reaches a false clause on every branch, so the refutation is small.' },
      { q: 'Around which ratio of clauses to variables does random 3-SAT switch from mostly satisfiable to mostly unsatisfiable?', options: ['1', '2', 'about 4.27', '10'], answer: 2, why: 'Experiments put the threshold near 4.27 for large n.' },
      { q: 'Does the easy behaviour away from the threshold contradict NP-completeness?', options: ['Yes', 'No: NP-completeness is about the worst case, not typical random instances', 'Only for small n', 'It proves P = NP'], answer: 1, why: 'Hard instances may be rare under a particular random model; NP-hardness says some instances are hard if P ≠ NP.' },
      { q: 'What happens to the transition as n grows?', options: ['It moves to 0', 'It gets sharper', 'It disappears', 'It moves to 10'], answer: 1, why: 'The window where both answers are common narrows, and the effort at the peak grows quickly.' },
    ],
  });
})();
