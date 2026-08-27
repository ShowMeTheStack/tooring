// Functions without machines: primitive recursive functions as expression trees evaluated node by node,
// the μ operator searching for a zero, Ackermann's function outgrowing them all, and the lambda calculus
// reducing terms with Church numerals.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'rec-functions', part: 'turing', order: 50, title: 'Recursive functions and λ', blurb: 'Build functions from zero, successor and projections with composition and recursion, add an unbounded search, or just substitute terms into terms: each way reaches exactly the computable functions.' });

  const argsOf = (s) => String(s).split(/[\s,]+/).filter(Boolean).map(Number);
  const argsCheck = (n, max) => (v) => { const a = argsOf(v); if (a.some((x) => !Number.isInteger(x) || x < 0)) return 'Arguments: whole numbers, like 2, 3'; if (a.length !== n) return 'Arguments: this function takes ' + n; if (a.some((x) => x > max)) return 'Arguments: at most ' + max + ' each, so the picture stays readable'; return null; };
  const badge = (key, x, y, text, cls) => ({ key, kind: 'token', x, y, r: 12, text: String(text), cls: 'tu-choice' + (cls ? ' ' + cls : ''), audit: 'ignore', layer: 'top' });

  // ======================================================================================================
  // Primitive recursion: the definition as a tree, each node lighting up as it is evaluated
  // ======================================================================================================
  const PR = {
    add: { n: 2, args: '2, 3', max: 4, say: 'add(x, y) = x + y: recursion on y, adding one each time' },
    mult: { n: 2, args: '2, 2', max: 3, say: 'mult(x, y) = x · y: recursion on y, adding x each time' },
    pred: { n: 1, args: '3', max: 5, say: 'pred(x) = x − 1 (0 stays 0): recursion that keeps the previous count' },
    monus: { n: 2, args: '4, 1', max: 4, say: 'monus(x, y) = x − y, not below 0: pred applied y times' },
    double: { n: 1, args: '3', max: 4, say: 'double(x) = add(x, x): composition only, no recursion' },
    sg: { n: 1, args: '0', max: 5, say: 'sg(x) = 1 if x > 0, else 0' },
  };
  /** The expression of a library function as a tree for the tree kit; named functions inside are leaves */
  function exprTree(e, path) {
    const id = 'e' + path;
    switch (e.t) {
      case 'Z': return { id, label: 'Z', cls: 'leaf', e };
      case 'S': return { id, label: 'S', cls: 'leaf', e };
      case 'P': return { id, label: 'P' + e.i + ',' + e.n, cls: 'leaf', e };
      case 'N': return { id, label: e.name, cls: 'leaf', e };
      case 'C': return { id, label: 'C', e, children: [exprTree(e.f, path + 'f')].concat(e.gs.map((g, i) => exprTree(g, path + 'g' + i))) };
      case 'R': return { id, label: 'R', e, children: [exprTree(e.f, path + 'f'), exprTree(e.g, path + 'g')] };
      case 'M': return { id, label: 'μ', e, children: [exprTree(e.f, path + 'f')] };
    }
    return { id, label: '?', e };
  }
  T.topic({
    id: 'primrec-tree', family: 'rec-functions', order: 10, title: 'Primitive recursive functions',
    blurb: 'Start with zero Z, successor S and projections P; build with composition C and primitive recursion R. A definition is a tree, and evaluating it walks the tree, R going round once for each step down to 0.',
    inputs: [
      { id: 'f', kind: 'choice', label: 'Function', def: 'add', options: Object.keys(PR).map((k) => ({ value: k, label: PR[k].say.split(':')[0] })) },
      { id: 'a', kind: 'text', label: 'Arguments', def: '2, 3', check: (v, inp) => argsCheck(PR[inp.f].n, PR[inp.f].max)(v) },
    ],
    presets: [
      { label: 'add(2, 3)', values: { f: 'add', a: '2, 3' } },
      { label: 'add(2, 0): no rounds at all', values: { f: 'add', a: '2, 0' } },
      { label: 'mult(2, 2)', values: { f: 'mult', a: '2, 2' } },
      { label: 'pred(3)', values: { f: 'pred', a: '3' } },
      { label: 'double(3)', values: { f: 'double', a: '3' } },
      { label: 'sg(0)', values: { f: 'sg', a: '0' } },
    ],
    counters: [{ id: 'calls', label: 'calls' }, { id: 'rounds', label: 'rounds of R' }],
    run(inp) {
      const env = T.rec.library();
      const def = env[inp.f];
      const args = argsOf(inp.a);
      const root = exprTree(def.expr, '');
      const value = new Map();
      const events = [];
      // evaluate, noting each call and each value against the node of the tree
      const ev = (node, a, depth) => {
        const e = node.e;
        let v;
        events.push({ kind: 'call', node, args: a.slice() });
        switch (e.t) {
          case 'Z': v = 0; break;
          case 'S': v = a[0] + 1; break;
          case 'P': v = a[e.i - 1]; break;
          case 'N': v = T.rec.evaluate(e.name, a, env, { trace: false }).value; break;
          case 'C': { const inner = node.children.slice(1).map((g) => ev(g, a, depth + 1)); v = ev(node.children[0], inner, depth + 1); break; }
          case 'R': {
            const xs = a.slice(0, -1), y = a[a.length - 1];
            v = ev(node.children[0], xs, depth + 1);
            events.push({ kind: 'round', node, k: 0, v, xs, y });
            for (let k = 0; k < y; k++) { v = ev(node.children[1], xs.concat([k, v]), depth + 1); events.push({ kind: 'round', node, k: k + 1, v, xs, y }); }
            break;
          }
        }
        events.push({ kind: 'ret', node, args: a.slice(), v });
        return v;
      };
      const result = ev(root, args, 0);
      const name = (n) => (n.e.t === 'P' ? 'P(' + n.e.i + ',' + n.e.n + ')' : n.e.t === 'N' ? n.e.name : n.e.t === 'C' || n.e.t === 'R' ? T.rec.toText(n.e) : n.label);
      const F = new T.Frames(['calls', 'rounds']);
      let hot = null;
      const scene = (top, cls) => {
        const mark = (n) => Object.assign({}, n, { cls: [n.cls || '', n.id === hot ? 'hot' : value.has(n.id) ? 'tu-k2' : ''].join(' ').trim(), children: n.children ? n.children.map(mark) : undefined });
        const d = K.tree.draw(mark(root), { gapY: 84, gapX: 30, grow: false });
        const items = d.items;
        for (const [id, v] of value) { const p = d.pos.get(id); if (p) items.push(badge('v' + id, p.x + 24, p.y - 22, v, id === hot ? 'hot' : '')); }
        items.push({ key: 'top', kind: 'text', x: d.box.x + d.box.w / 2, y: d.box.y - 34, text: top, anchor: 'middle', cls: 'mono' + (cls ? ' ' + cls : ''), mono: true, size: 16 });
        return items;
      };
      F.add({ items: scene(inp.f + '(' + args.join(', ') + ') = ?'), say: inp.f + ' = ' + def.text + '. As a tree: ' + PR[inp.f].say + '. Each node will show its last value in a badge.' });
      let shown = 0;
      for (const x of events) {
        if (shown > 70) break;
        if (x.kind === 'call') { F.count('calls'); if (x.node.e.t !== 'R' && x.node.e.t !== 'C') continue; hot = x.node.id; shown++; F.add({ items: scene(name(x.node) + '(' + x.args.join(', ') + ')'), say: x.node.e.t === 'R' ? 'R on (' + x.args.join(', ') + '): recursion on the last argument, ' + x.args[x.args.length - 1] + '. First the base case, then the step function ' + x.args[x.args.length - 1] + ' time' + (x.args[x.args.length - 1] === 1 ? '' : 's') + '.' : 'C on (' + x.args.join(', ') + '): first the inner functions on these arguments, then the outer one on their results.' }); continue; }
        if (x.kind === 'round') { hot = x.node.id; value.set(x.node.id, x.v); if (x.k) F.count('rounds'); shown++; F.add({ items: scene('h(' + x.xs.concat([x.k]).join(', ') + ') = ' + x.v), say: x.k === 0 ? 'Base case: h(' + x.xs.concat([0]).join(', ') + ') = f(' + (x.xs.join(', ') || '') + ') = ' + x.v + '.' : 'Round ' + x.k + ': h(' + x.xs.concat([x.k]).join(', ') + ') = g(' + x.xs.concat([x.k - 1, '…']).join(', ') + ') = ' + x.v + (x.k === x.y ? '. That was the last round.' : '.'), meta: { round: x.k, v: x.v, y: x.y } }); continue; }
        hot = x.node.id; value.set(x.node.id, x.v); shown++;
        F.add({ items: scene(name(x.node) + '(' + x.args.join(', ') + ') = ' + x.v), say: name(x.node) + '(' + x.args.join(', ') + ') = ' + x.v + ({ Z: ': zero, whatever the arguments.', S: ': one more than its argument.', P: ': it picks argument ' + x.node.e.i + ' of ' + x.node.e.n + '.', N: ', using ' + x.node.e.name + ' as an already built function.' }[x.node.e.t] || '.') });
      }
      hot = root.id;
      F.add({ items: scene(inp.f + '(' + args.join(', ') + ') = ' + result, 'good'), say: inp.f + '(' + args.join(', ') + ') = ' + result + '. Every primitive recursive function is total: each R runs a number of rounds fixed before it starts, so evaluation always ends.', mark: 'value' });
      const fr = F.list;
      const r = fr.findIndex((f) => f.meta && f.meta.round === f.meta.y && f.meta.y > 0);
      if (r > 1) fr[r - 1].predict = { ask: 'What will the last round of R give?', options: [...new Set([fr[r].meta.v, fr[r].meta.v + 1, Math.max(0, fr[r].meta.v - 1), fr[r].meta.v * 2])].map(String).sort((a, b) => a - b), answer: String(fr[r].meta.v), explain: fr[r].say, pick: 'option' };
      else fr[0].predict = { ask: 'What is ' + inp.f + '(' + args.join(', ') + ')?', options: [...new Set([result, result + 1, Math.max(0, result - 1), result + 2])].map(String).sort((a, b) => a - b), answer: String(result), explain: 'The tree evaluates to ' + result + '.', pick: 'option' };
      return { frames: fr, def: { sections: [
        { id: 'base', kind: 'math', title: 'Building blocks', text: 'Z(x̄) = 0\nS(x) = x + 1\nP(i,n)(x₁, …, xₙ) = xᵢ\nC(f; g₁, …, gₘ)(x̄) = f(g₁(x̄), …, gₘ(x̄))\nR(f, g)(x̄, 0) = f(x̄)\nR(f, g)(x̄, y + 1) = g(x̄, y, R(f, g)(x̄, y))' },
        { id: 'lib', kind: 'math', title: 'Definitions used', text: T.rec.LIBRARY.trim().split('\n').filter((l) => /^(add|mult|pred|monus|double|sg) /.test(l)).join('\n') },
      ] } };
    },
    quiz: [
      { q: 'In add = R(P(1,1), C(S; P(3,3))), what does the step function receive?', options: ['x only', 'x, the counter y, and the previous value', 'Only the previous value', 'Nothing'], answer: 1, why: 'R passes (x̄, y, h(x̄, y)) to g; here P(3,3) picks the previous value and S adds one.' },
      { q: 'Why does evaluating a primitive recursive function always halt?', options: ['It uses no loops', 'Each recursion runs exactly as many rounds as its last argument says, known before it starts', 'The values are small', 'It does not always halt'], answer: 1, why: 'Primitive recursion is a bounded loop: a for loop, never a while loop.' },
      { q: 'Are all total computable functions primitive recursive?', options: ['Yes', 'No: Ackermann\'s function grows faster than any of them', 'Only for one argument', 'Only the increasing ones'], answer: 1, why: 'Ackermann\'s function is total and computable but eventually beats every primitive recursive function.' },
      { q: 'How is pred(x) = x − 1 built?', options: ['From a minus sign', 'R(Z, P(1,2)): at each round keep the counter y, the value one below y + 1', 'With μ', 'It cannot be'], answer: 1, why: 'pred(0) = 0, and pred(y + 1) = y, which is the counter the step function is handed.' },
    ],
  });

  // ======================================================================================================
  // The μ operator: search 0, 1, 2, … for the first zero
  // ======================================================================================================
  const MU = {
    div: { n: 2, args: '7, 2', show: 'div(x, y) = least z with (z + 1)·y > x', inner: 'nsg(lt(x, (z + 1)·y))', meaning: (a, z) => '(' + (z + 1) + ')·' + a[1] + ' = ' + (z + 1) * a[1] + (((z + 1) * a[1] > a[0]) ? ' > ' : ' ≤ ') + a[0] },
    isqrt: { n: 1, args: '10', show: 'isqrt(x) = least z with (z + 1)² > x', inner: 'nsg(lt(x, (z + 1)²))', meaning: (a, z) => (z + 1) + '² = ' + (z + 1) * (z + 1) + ((z + 1) * (z + 1) > a[0] ? ' > ' : ' ≤ ') + a[0] },
    log2: { n: 1, args: '9', show: 'log2(x) = least z with 2^(z + 1) > x', inner: 'nsg(lt(x, 2^(z + 1)))', meaning: (a, z) => '2^' + (z + 1) + ' = ' + 2 ** (z + 1) + (2 ** (z + 1) > a[0] ? ' > ' : ' ≤ ') + a[0] },
  };
  const LIMIT = 12;
  T.topic({
    id: 'mu-search', family: 'rec-functions', order: 20, title: 'The μ operator: unbounded search',
    blurb: 'μ looks for the least z with f(x̄, z) = 0, trying 0, 1, 2, … in turn. If there is none it searches for ever, and the function is undefined there: the price of computing everything computable.',
    inputs: [
      { id: 'f', kind: 'choice', label: 'Function', def: 'div', options: Object.keys(MU).map((k) => ({ value: k, label: MU[k].show })) },
      { id: 'a', kind: 'text', label: 'Arguments', def: '7, 2', check: (v, inp) => argsCheck(MU[inp.f].n, 40)(v) },
    ],
    presets: [
      { label: 'div(7, 2)', values: { f: 'div', a: '7, 2' } },
      { label: 'isqrt(10)', values: { f: 'isqrt', a: '10' } },
      { label: 'log2(9)', values: { f: 'log2', a: '9' } },
      { label: 'isqrt(0): found at once', values: { f: 'isqrt', a: '0' } },
      { label: 'div(5, 0): the search never ends', values: { f: 'div', a: '5, 0' } },
    ],
    counters: [{ id: 'tries', label: 'values of z tried' }, { id: 'calls', label: 'calls of f' }],
    run(inp) {
      const env = T.rec.library();
      const M = env[inp.f].expr, f = M.f;
      const a = argsOf(inp.a);
      const X = MU[inp.f];
      const CW = 52, F = new T.Frames(['tries', 'calls']);
      const probes = [];
      let calls = 0, found = null;
      for (let z = 0; z < LIMIT; z++) { const r = T.rec.evaluate(f, a.concat([z]), env, { trace: false }); calls += r.calls; probes.push({ z, v: r.value, calls }); if (r.value === 0) { found = z; break; } }
      const scene = (k, end) => {
        const items = [{ key: 'title', kind: 'text', x: 0, y: -70, text: X.show, cls: 'mono', mono: true, size: 16 }, { key: 'inner', kind: 'text', x: 0, y: -44, text: 'f(' + a.join(', ') + ', z) = ' + X.inner, cls: 'tu-small' }];
        for (let z = 0; z < LIMIT; z++) {
          const p = z < k ? probes[z] : null;
          items.push({ key: 'z' + z, kind: 'cell', x: z * CW, y: 0, w: CW, h: CW, text: p ? String(p.v) : '', cls: 'mono' + (p ? (p.v === 0 ? ' good' : ' read') : '') + (z === k - 1 && !end ? ' hot' : ''), rx: 4, sub: z });
        }
        items.push({ key: 'zl', kind: 'text', x: -14, y: CW / 2 + 5, text: 'f =', anchor: 'end', cls: 'strong' });
        items.push({ key: 'zz', kind: 'text', x: -14, y: CW + 18, text: 'z =', anchor: 'end', cls: 'tu-num', size: 12 });
        if (k > 0) items.push({ key: 'mu', kind: 'head', x: Math.min(k - 1, LIMIT - 1) * CW + CW / 2, y: CW + 24, text: 'μ', side: 'below', cls: end ? (found !== null ? 'good' : 'bad') : 'hot' });
        items.push({ key: 'more', kind: 'text', x: LIMIT * CW + 10, y: CW / 2 + 5, text: '⋯', cls: 'strong' });
        return items;
      };
      F.add({ items: scene(0), say: inp.f + '(' + a.join(', ') + ') = μz[f(' + a.join(', ') + ', z) = 0]: try z = 0, 1, 2, … and stop at the first z where f gives 0. f is 1 while the answer is still too small.' });
      probes.forEach((p, i) => { F.count('tries').set('calls', p.calls); F.add({ items: scene(i + 1), say: 'z = ' + p.z + ': ' + X.meaning(a, p.z) + ', so f = ' + p.v + (p.v === 0 ? '. The first zero: stop.' : '. Not zero: try z = ' + (p.z + 1) + '.'), meta: { v: p.v, z: p.z } }); });
      F.add({ items: scene(probes.length, true), say: found !== null ? inp.f + '(' + a.join(', ') + ') = ' + found + ', found after ' + (found + 1) + ' tr' + (found ? 'ies' : 'y') + '.' : 'f is 1 for every z: ' + X.meaning(a, LIMIT - 1).replace(/^.*?=/, '(z + 1)·0 =') + ' for all z. The search goes on for ever, so ' + inp.f + '(' + a.join(', ') + ') has no value at all. μ makes partial functions.', mark: found !== null ? 'found' : 'undefined' });
      const fr = F.list;
      if (fr.length > 3) fr[1].predict = { ask: 'At which z will the search stop?', options: found !== null ? [...new Set([found, found + 1, Math.max(0, found - 1), found + 2])].map(String).sort((x, y) => x - y) : ['0', '2', '5', 'never'], answer: found !== null ? String(found) : 'never', explain: found !== null ? 'The first z with ' + X.show.split(' with ')[1] + ' is ' + found + '.' : 'With y = 0, (z + 1)·0 = 0 is never more than x: no z works.', pick: 'option' };
      if (fr[1] && fr[1].predict && found !== null && !fr[1].predict.options.includes(String(found))) delete fr[1].predict;
      if (!fr.some((f) => f.predict)) fr[0].predict = { ask: 'Will the search find a zero?', options: ['Yes', 'No'], answer: found !== null ? 'Yes' : 'No', explain: fr[fr.length - 1].say, pick: 'option' };
      return { frames: fr, def: { sections: [{ id: 'mu', kind: 'math', title: 'Minimisation', text: 'μf(x̄) = the least z with f(x̄, z) = 0,\n  provided f(x̄, z′) is defined for all z′ < z;\nundefined if there is no such z.\n' + inp.f + ' = ' + env[inp.f].text }, { id: 'why', kind: 'text', title: 'Why it matters', text: 'Primitive recursion plus μ gives the μ-recursive (partial recursive) functions, exactly the functions Turing machines compute. Every one can even be written with a single μ, at the outside (Kleene\'s normal form).' }] } };
    },
    quiz: [
      { q: 'What does μ add that primitive recursion lacks?', options: ['Composition', 'An unbounded search, a while loop', 'Projections', 'Multiplication'], answer: 1, why: 'Primitive recursion only has loops whose length is known in advance.' },
      { q: 'div(5, 0) is undefined because…', options: ['dividing by 0 is an error message', 'the search for z never finds a zero, so it never halts', 'μ refuses 0', 'it is 0'], answer: 1, why: 'f stays 1 for every z, so μ keeps searching.' },
      { q: 'Which functions do μ-recursive functions compute?', options: ['Only total ones', 'Exactly the Turing-computable partial functions', 'Only primitive recursive ones', 'All functions'], answer: 1, why: 'Each model simulates the other: one more face of the Church–Turing thesis.' },
      { q: 'If f is primitive recursive and the search always succeeds, is μf total?', options: ['Yes', 'No', 'Only for one argument', 'Only if f is increasing'], answer: 0, why: 'f is total, and a zero always exists, so the search always ends. (Whether a zero always exists is the hard part to know.)' },
    ],
  });

  // ======================================================================================================
  // Ackermann's function: its call tree, then a table that explodes
  // ======================================================================================================
  const ackCalls = (m, n) => T.rec.ackermann(m, n, { trace: false, maxCalls: 1000 }).calls;
  const ackShort = (m, n) => {
    const f = T.rec.ackFormula(m, n);
    if (f.value !== null && f.value < 1e7) return String(f.value);
    if (m === 3) return '2^' + (n + 3) + '−3';
    if (m === 4 && n === 2) return '2^65536−3';
    if (m === 4) return '2↑↑' + (n + 3) + '−3';
    return '…';
  };
  T.topic({
    id: 'ackermann', family: 'rec-functions', order: 30, title: 'Ackermann\'s function',
    blurb: 'A(0, n) = n + 1, A(m + 1, 0) = A(m, 1), A(m + 1, n + 1) = A(m, A(m + 1, n)). Total and computable, yet it grows faster than any primitive recursive function: watch the call tree, then the table explode.',
    inputs: [{ id: 'm', kind: 'number', label: 'm', def: 1, min: 0, max: 2 }, { id: 'n', kind: 'number', label: 'n', def: 2, min: 0, max: 3 }],
    check: (inp) => (ackCalls(inp.m, inp.n) > 30 ? 'A(' + inp.m + ', ' + inp.n + ') makes ' + ackCalls(inp.m, inp.n) + ' calls; pick smaller numbers (at most 30 calls), the table will show the rest' : null),
    presets: [
      { label: 'A(1, 2)', values: { m: 1, n: 2 } },
      { label: 'A(2, 1)', values: { m: 2, n: 1 } },
      { label: 'A(0, 3): one call', values: { m: 0, n: 3 } },
      { label: 'A(1, 0)', values: { m: 1, n: 0 } },
    ],
    counters: [{ id: 'calls', label: 'calls' }, { id: 'depth', label: 'deepest' }],
    run(inp) {
      // the call tree, built in the order the calls happen
      let nid = 0;
      const events = [];
      const call = (m, n, parent, depth) => {
        const node = { id: 'a' + nid++, m, n, children: [], depth };
        if (parent) parent.children.push(node);
        events.push({ kind: 'call', node });
        let v;
        if (m === 0) v = n + 1;
        else if (n === 0) v = call(m - 1, 1, node, depth + 1);
        else { const inner = call(m, n - 1, node, depth + 1); v = call(m - 1, inner, node, depth + 1); }
        node.v = v;
        events.push({ kind: 'ret', node });
        return v;
      };
      const rootNode = { children: [] };
      const result = call(inp.m, inp.n, rootNode, 0);
      const root = rootNode.children[0];
      const born = new Set(), val = new Map();
      let hot = null;
      const view = (n) => ({ id: n.id, label: 'A(' + n.m + ',' + n.n + ')', cls: n.id === hot ? 'hot' : val.has(n.id) ? 'tu-k2' : '', children: n.children.filter((c) => born.has(c.id)).map(view) });
      const scene = () => {
        const d = K.tree.draw(view(root), { gapY: 76, gapX: 14 });
        const items = d.items;
        for (const [id, v] of val) { const p = d.pos.get(id); if (p) items.push(badge('v' + id, p.x + 34, p.y - 20, v, id === hot ? 'hot' : '')); }
        return { items, box: d.box };
      };
      const F = new T.Frames(['calls', 'depth']);
      for (const e of events) {
        if (e.kind === 'call') {
          born.add(e.node.id); hot = e.node.id;
          F.count('calls').set('depth', Math.max(F.counts.depth, e.node.depth + 1));
          const { m, n } = e.node;
          F.add({ items: scene().items, say: 'Call A(' + m + ', ' + n + '): ' + (m === 0 ? 'm = 0, so the answer is n + 1 = ' + (n + 1) + '.' : n === 0 ? 'n = 0, so it is A(' + (m - 1) + ', 1).' : 'it needs A(' + m + ', ' + (n - 1) + ') first, then A(' + (m - 1) + ', that).') });
        } else {
          val.set(e.node.id, e.node.v); hot = e.node.id;
          if (e.node.m === 0) continue;
          F.add({ items: scene().items, say: 'A(' + e.node.m + ', ' + e.node.n + ') = ' + e.node.v + '.', meta: { node: e.node } });
        }
      }
      hot = root.id;
      const final = scene();
      F.add({ items: final.items, say: 'A(' + inp.m + ', ' + inp.n + ') = ' + result + ' after ' + F.counts.calls + ' calls. Small numbers, but look what happens as m grows.', mark: 'value' });
      // the growth table, row by row
      const tb = (rowsDone) => {
        const rows = [];
        for (let m = 0; m <= 4; m++) { const r = []; for (let n = 0; n <= 5; n++) r.push(m < rowsDone ? ackShort(m, n) : ''); rows.push(r); }
        return K.table.draw({ rows, rowHead: ['m = 0', 'm = 1', 'm = 2', 'm = 3', 'm = 4'], colHead: ['n = 0', '1', '2', '3', '4', '5'], corner: 'A', x: final.box.x + final.box.w / 2 - 345, y: final.box.y, cw: 100, mono: true, size: 14, prefix: 'ack', hot: rowsDone ? Array.from({ length: 6 }, (_, n) => [rowsDone - 1, n]) : [], cls: (m, n) => (m < rowsDone && m === 4 && n >= 2 ? 'bad' : '') }).items;
      };
      const rowSay = ['Row 0: A(0, n) = n + 1. Just counting.', 'Row 1: A(1, n) = n + 2.', 'Row 2: A(2, n) = 2n + 3. Each row repeats the row above.', 'Row 3: A(3, n) = 2^(n+3) − 3: exponential.', 'Row 4: A(4, n) = 2↑↑(n + 3) − 3, a tower of twos. A(4, 2) = 2^65536 − 3 has 19,729 digits; A(4, 3) could not be written down in the universe.'];
      for (let m = 0; m <= 4; m++) F.add({ items: tb(m + 1), say: rowSay[m], mark: m === 4 ? 'explodes' : undefined });
      const fr = F.list;
      const ask = fr.findIndex((f) => f.meta && f.meta.node === root);
      if (ask > 1) fr[ask - 1].predict = { ask: 'What is A(' + inp.m + ', ' + inp.n + ')?', options: [...new Set([result, result + 1, Math.max(1, result - 1), result * 2])].map(String).sort((x, y) => x - y), answer: String(result), explain: fr[ask].say, pick: 'option' };
      else fr[fr.length - 3].predict = { ask: 'Row 3 is next. How fast does A(3, n) grow?', options: ['like n', 'like 2n', 'like 2ⁿ', 'like n²'], answer: 'like 2ⁿ', explain: rowSay[3], pick: 'option' };
      return { frames: fr, def: { sections: [
        { id: 'def', kind: 'math', title: 'The definition', text: 'A(0, n) = n + 1\nA(m + 1, 0) = A(m, 1)\nA(m + 1, n + 1) = A(m, A(m + 1, n))' },
        { id: 'why', kind: 'text', title: 'Why it is not primitive recursive', text: 'Every primitive recursive function f has some m with f(x) < A(m, x) for all x: a bounded loop nesting can only climb so many rows. So A(x, x) beats every one of them, yet it is computable, and the recursion always ends since (m, n) goes down in the lexicographic order.' },
      ] } };
    },
    quiz: [
      { q: 'Why does the computation of A(m, n) always end?', options: ['It is primitive recursive', 'Each call goes to a pair that is smaller in the lexicographic order (m first, then n)', 'The numbers stay small', 'It does not always end'], answer: 1, why: 'Either m goes down, or m stays and n goes down; such a sequence cannot go on for ever.' },
      { q: 'What is A(1, n)?', options: ['n + 1', 'n + 2', '2n', '2ⁿ'], answer: 1, why: 'A(1, n) = A(0, A(1, n − 1)) = A(1, n − 1) + 1, starting from A(1, 0) = 2.' },
      { q: 'Is Ackermann\'s function computable?', options: ['No, it grows too fast', 'Yes: a program with a stack computes it', 'Only for m ≤ 3', 'Only with μ'], answer: 1, why: 'It is total and computable, just not primitive recursive.' },
      { q: 'What does Ackermann\'s function show?', options: ['Some total computable functions are not primitive recursive', 'Recursion is unnecessary', 'All functions are computable', 'Towers of twos are finite'], answer: 0, why: 'It outgrows every primitive recursive function, so bounded loops are not enough for all total computable functions.' },
    ],
  });

  // ======================================================================================================
  // The lambda calculus: β-reduction, leftmost outermost, with Church numerals
  // ======================================================================================================
  /** Print a term as the core does, also returning where the subterms at two paths sit */
  function pp(e, want) {
    const spans = {};
    const go = (x, path) => {
      let s;
      const start = out.length;
      if (x.t === 'var') out += x.n;
      else if (x.t === 'lam') {
        const vs = []; let b = x, p = path;
        while (b.t === 'lam') { vs.push(b.v); b = b.b; p = p + 'b'; }
        out += 'λ' + vs.join(' ') + '. ';
        go(b, p);
      } else {
        if (x.f.t === 'lam') { out += '('; go(x.f, path + 'f'); out += ')'; } else go(x.f, path + 'f');
        out += ' ';
        if (x.a.t === 'var') go(x.a, path + 'a'); else { out += '('; go(x.a, path + 'a'); out += ')'; }
      }
      if (want.includes(path)) spans[path] = [start, out.length];
      void s;
    };
    let out = '';
    go(e, '');
    return { text: out, spans };
  }
  T.topic({
    id: 'lambda-reduce', family: 'rec-functions', order: 40, title: 'The lambda calculus',
    blurb: 'Terms are variables, functions λx. M and applications M N; the only rule is to put an argument in for the variable. Numbers are Church numerals, λf x. f (f x) being 2, and that is enough to compute anything.',
    inputs: [{ id: 't', kind: 'text', label: 'Term (λ or \\, numbers are Church numerals, names like SUCC, PLUS)', def: 'SUCC 2', check: (v) => { try { const e = T.lambda.parse(v); if (T.lambda.size(e) > 80) return 'Term: too big for the picture'; return null; } catch (e) { return 'Term: ' + e.message; } } }],
    presets: [
      { label: 'SUCC 2', values: { t: 'SUCC 2' } },
      { label: 'PLUS 2 1', values: { t: 'PLUS 2 1' } },
      { label: 'MULT 2 2', values: { t: 'MULT 2 2' } },
      { label: 'NOT TRUE', values: { t: 'NOT TRUE' } },
      { label: 'Ω: no normal form', values: { t: '(λx. x x) (λx. x x)' } },
      { label: 'K I Ω: outermost first escapes the loop', values: { t: '(λx y. x) (λz. z) ((λx. x x) (λx. x x))' } },
    ],
    counters: [{ id: 'steps', label: 'β-steps' }, { id: 'size', label: 'term size' }],
    run(inp) {
      const L = T.lambda;
      let e = L.parse(inp.t);
      const rows = [];
      let steps = 0, verdict = 'normal';
      rows.push({ e, r: null });
      while (true) {
        const r = L.step(e);
        if (!r) break;
        if (steps >= 14) { verdict = 'limit'; break; }
        rows[rows.length - 1].r = r;
        e = r.term; steps++;
        rows.push({ e, r: null });
      }
      const VIS = 6, RH = 50;
      const F = new T.Frames(['steps', 'size']);
      const rowItems = (i, y, lit) => {
        const x = rows[i];
        const want = x.r ? [x.r.path.join(''), x.r.path.join('') + 'f', x.r.path.join('') + 'a'] : [];
        const p = pp(x.e, want);
        const size = Math.max(10, Math.min(17, 640 / (Math.max(1, p.text.length) * 0.61)));
        const cw = size * 0.602;
        const items = [];
        if (lit && x.r) {
          const pf = p.spans[x.r.path.join('') + 'f'], pa = p.spans[x.r.path.join('') + 'a'];
          if (pf) items.push({ key: 'hf' + i, kind: 'region', x: pf[0] * cw - 2, y: y - size - 2, w: (pf[1] - pf[0]) * cw + 4, h: size + 12, rx: 5, text: '', cls: 'tu-line' });
          if (pa) items.push({ key: 'ha' + i, kind: 'region', x: pa[0] * cw - 2, y: y - size - 2, w: (pa[1] - pa[0]) * cw + 4, h: size + 12, rx: 5, text: '', cls: 'tu-box' });
        }
        items.push({ key: 'r' + i, kind: 'text', x: 0, y, text: p.text, cls: 'mono', mono: true, size, enter: 'drop', exit: 'rise' });
        items.push({ key: 'n' + i, kind: 'text', x: -16, y, text: i ? '→β' : '', anchor: 'end', cls: 'tu-num', size: 12, exit: 'rise' });
        return items;
      };
      const scene = (i, extra) => {
        const first = Math.max(0, i - VIS + 1);
        const items = [{ key: 'legend', kind: 'text', x: 0, y: -40, text: 'FUNCTION λx. M (YELLOW) APPLIED TO ITS ARGUMENT (BLUE)', cls: 'title' }];
        for (let k = first; k <= i; k++) items.push(...rowItems(k, (k - first) * RH, k === i));
        if (extra) items.push(...extra);
        return items;
      };
      const say = (i) => { const r = rows[i].r; return r ? 'The leftmost outermost redex applies ' + L.show(r.redex.f) + ' to ' + L.show(r.redex.a) + ': put ' + L.show(r.redex.a) + ' in for ' + r.redex.f.v + ' in the body.' : ''; };
      F.set('size', L.size(rows[0].e));
      F.add({ items: scene(0), say: 'Names are expanded: ' + inp.t + ' is ' + L.show(rows[0].e) + '. ' + (rows[0].r ? say(0) : 'There is no redex: it is already in normal form.'), meta: { r: !!rows[0].r } });
      for (let i = 1; i < rows.length; i++) { F.count('steps').set('size', L.size(rows[i].e)); F.add({ items: scene(i), say: (rows[i].r ? say(i) : 'No redex is left: ' + L.show(rows[i].e) + ' is the normal form.'), meta: { r: !!rows[i].r } }); }
      const nf = rows[rows.length - 1].e;
      const k = verdict === 'normal' ? L.unchurch(nf) : null, b = verdict === 'normal' ? L.unbool(nf) : null;
      const last = rows.length - 1, first = Math.max(0, last - VIS + 1), y = (last - first + 1) * RH + 20;
      const extra = [];
      if (k !== null) {
        for (let j = 0; j < k; j++) extra.push({ key: 'cf' + j, kind: 'cell', x: j * 46, y, w: 40, h: 40, text: 'f', cls: 'mono tu-k1', rx: 6 });
        extra.push({ key: 'cx', kind: 'cell', x: k * 46, y, w: 40, h: 40, text: 'x', cls: 'mono', rx: 6 });
        if (k) extra.push({ key: 'cb', kind: 'bracket', x1: 0, x2: k * 46 - 6, y: y + 46, side: 'below', text: 'f applied ' + k + ' time' + (k === 1 ? '' : 's') + ': the numeral ' + k, cls: 'y' });
      }
      const end = verdict === 'limit' ? 'After ' + steps + ' steps the term is ' + L.show(nf) + ' again, or still growing: there is no normal form, and reduction goes on for ever.' : k !== null ? 'The normal form ' + L.show(nf) + ' is the Church numeral ' + k + ': it applies f ' + k + ' time' + (k === 1 ? '' : 's') + ' to x.' : b !== null ? 'The normal form ' + L.show(nf) + ' is ' + (b ? 'TRUE: it picks the first of two arguments.' : 'FALSE: it picks the second of two arguments.') : 'The normal form is ' + L.show(nf) + '.';
      F.add({ items: scene(last, extra), say: end, mark: verdict === 'limit' ? 'no normal form' : 'normal form' });
      const fr = F.list;
      if (k !== null && fr.length > 3) fr[fr.length - 2].predict = { ask: 'Which Church numeral is the answer?', options: [...new Set([k, k + 1, Math.max(0, k - 1), k + 2])].map(String).sort((x, y2) => x - y2), answer: String(k), explain: end, pick: 'option' };
      else if (verdict === 'limit') fr[1].predict = { ask: 'Will this term ever reach a normal form?', options: ['Yes', 'No'], answer: 'No', explain: 'Ω reduces to itself: (λx. x x) (λx. x x) → (λx. x x) (λx. x x) → …', pick: 'option' };
      else if (b !== null && fr.length > 2) fr[0].predict = { ask: 'Will the result be TRUE or FALSE?', options: ['TRUE', 'FALSE'], answer: b ? 'TRUE' : 'FALSE', explain: end, pick: 'option' };
      else if (fr.length > 2) fr[0].predict = { ask: 'How many β-steps will normal order take?', options: [...new Set([steps, steps + 1, Math.max(1, steps - 1), steps + 3])].map(String).sort((x, y2) => x - y2), answer: String(steps), explain: end, pick: 'option' };
      return { frames: fr, def: { sections: [
        { id: 'rule', kind: 'math', title: 'β-reduction', text: '(λx. M) N  →β  M[x := N]\n(renaming bound variables so nothing free in N is captured)\nnormal order: always the leftmost outermost redex' },
        { id: 'defs', kind: 'math', title: 'Names', text: ['SUCC', 'PLUS', 'MULT', 'TRUE', 'FALSE', 'NOT'].map((n) => n + ' = ' + L.DEFS[n]).join('\n') + '\nn = λf x. f (f … (f x)), n times' },
      ] } };
    },
    quiz: [
      { q: 'What is the Church numeral 3?', options: ['λx. 3', 'λf x. f (f (f x))', 'λf x. f x x x', '(λx. x) 3'], answer: 1, why: 'n is the function that applies f n times.' },
      { q: 'Why does SUCC = λn f x. f (n f x) add one?', options: ['It counts', 'n f x applies f n times; one more f around it makes n + 1', 'It doubles', 'It is a primitive'], answer: 1, why: 'The result applies f once more than n does.' },
      { q: 'K I Ω reaches a normal form under normal order but not if Ω is reduced first. Why?', options: ['Ω is not a term', 'K throws its second argument away, so reducing outermost first never touches Ω', 'Normal order is faster', 'It does not reach one'], answer: 1, why: 'Leftmost outermost first finds a normal form whenever one exists.' },
      { q: 'What does the lambda calculus compute?', options: ['Only arithmetic', 'Exactly the functions Turing machines compute', 'More than Turing machines', 'Only total functions'], answer: 1, why: 'Each can simulate the other, which is part of the evidence for the Church–Turing thesis.' },
    ],
  });
})();
