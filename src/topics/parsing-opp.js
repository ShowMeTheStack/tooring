// Operator-precedence parsing: relations <· ≐ ·> between terminals worked out from LEADING and TRAILING of
// an operator grammar, the shift-reduce parse they drive (a handle sits between a <· and a ·>), and
// precedence functions f and g, found as longest paths in a graph, that replace the whole table.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'opp', part: 'parsing', order: 58, title: 'Operator precedence', blurb: 'For grammars where no two nonterminals stand side by side: three relations between terminals decide when to shift and where a handle begins and ends.' });

  const ARITH = 'E → E + T | T\nT → T * P | P\nP → ( E ) | n';
  const POW = 'E → E - T | T\nT → F ^ T | F\nF → ( E ) | n';
  const AMB = 'E → E + E | n';
  const LISTS = 'S → S ; a | a';
  const N = { '<': '<·', '=': '≐', '>': '·>' };
  const checkOp = (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 4, operator: true })(v);

  /** The relation table as a stage table: row = terminal on the stack, column = next input symbol */
  function relTable(R, opts) {
    const ts = R.terminals;
    return K.table.draw({ prefix: opts.prefix || 'or', rows: ts.map((a) => ts.map((b) => (R.rel[a] && R.rel[a][b] ? N[R.rel[a][b]] : ''))), rowHead: ts, colHead: ts, corner: 'stack \\ next', x: opts.x || 0, y: opts.y || 0, mono: true, size: 16, minW: 50, hot: opts.hot ? [opts.hot] : [], cls: (r, c) => (opts.bad && opts.bad.some((p) => p[0] === r && p[1] === c) ? 'bad' : '') });
  }

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'opp-relations', family: 'opp', order: 10, title: 'Precedence relations from LEADING and TRAILING',
    blurb: 'a ≐ b when they sit together in a rule; a <· b when b can begin something that follows a; a ·> b when a can end something that b follows. LEADING and TRAILING say which terminals can begin and end what a nonterminal derives.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Operator grammar', def: ARITH, check: checkOp }],
    presets: [
      { label: 'Sums and products', values: { g: ARITH } },
      { label: 'A right-associative power', values: { g: POW } },
      { label: 'A list: S → S ; a | a', values: { g: LISTS } },
      { label: 'Ambiguous: a clash', values: { g: AMB } },
    ],
    counters: [{ id: 'rel', label: 'relations' }, { id: 'conflicts', label: 'clashes' }],
    run(inp) {
      const G = T.PX.G(inp.g), R0 = T.opp.relationsFromGrammar(G), F = new T.Frames(['rel', 'conflicts']);
      const lead = new Map(G.nonterminals.map((A) => [A, []])), trail = new Map(G.nonterminals.map((A) => [A, []]));
      const R = { terminals: R0.terminals, rel: Object.fromEntries(R0.terminals.map((a) => [a, {}])) };
      const bad = [];
      const pw = T.PX.panel({ rows: T.PX.ruleRows(G) }).w;
      const maxM = Math.max(1, ...G.nonterminals.map((A) => Math.max(R0.leading[A].length, R0.trailing[A].length)));
      const rowsW = 150 + maxM * 48;
      const tx = pw + 40, ty = Math.max(G.nonterminals.length * 54 + 30, G.productions.length * 38 + 50);
      const scene = (o) => {
        o = o || {};
        const items = T.PX.panel({ prefix: 'gr', x: 0, y: 0, title: 'Rules', rows: T.PX.ruleRows(G, o.prod === undefined || o.prod === null ? null : [o.prod]), rowH: 34, size: 16 }).items;
        items.push(...T.PX.setRows(G.nonterminals.map((A) => ({ id: 'L' + A, label: 'LEADING(' + A + ')', members: lead.get(A) })), { prefix: 'ld', x: pw + 40, y: 0, labelW: 150, hot: o.hot ? [o.hot] : [] }));
        items.push(...T.PX.setRows(G.nonterminals.map((A) => ({ id: 'T' + A, label: 'TRAILING(' + A + ')', members: trail.get(A) })), { prefix: 'tr', x: pw + 40 + rowsW + 20, y: 0, labelW: 150, hot: o.hot ? [o.hot] : [] }));
        items.push(...relTable(R, { x: tx, y: ty, hot: o.cell, bad }).items);
        return items;
      };
      F.add({ items: scene({}), say: 'An operator grammar: no ε-rules and never two nonterminals side by side, so between any two nonterminals in a sentential form there is a terminal. The relations will be between terminals only, with $ at both ends.' });
      for (const st of R0.trace) {
        const ri = (a) => R0.terminals.indexOf(a);
        if (st.kind === 'leading' || st.kind === 'trailing') {
          (st.kind === 'leading' ? lead : trail).get(st.A).push(...st.add);
          F.add({ items: scene({ prod: st.prod, hot: (st.kind === 'leading' ? 'L' : 'T') + st.A }), say: st.say, hl: { g: [st.prod] } });
        } else if (st.kind === 'conflict') {
          F.count('conflicts'); bad.push([ri(st.a), ri(st.b)]);
          F.add({ items: scene({ cell: [ri(st.a), ri(st.b)] }), say: st.say, mark: 'clash', meta: { kind: 'conflict' } });
        } else {
          R.rel[st.a][st.b] = st.kind === 'less' ? '<' : st.kind === 'equal' ? '=' : '>';
          F.count('rel');
          const m = /in (.*?) → (.*)$/.exec(st.say);
          void m;
          F.add({ items: scene({ cell: [ri(st.a), ri(st.b)] }), say: st.say, meta: { kind: st.kind, cell: 'or:' + ri(st.a) + ',' + ri(st.b), rel: N[R.rel[st.a][st.b]] } });
        }
      }
      F.add({ items: scene({}), say: R0.conflicts.length ? 'Some pair of terminals got two relations, so this grammar is not an operator-precedence grammar: the table cannot tell the parser what to do there. (The grammar is ambiguous; an unambiguous one with one level per operator would do.)' : 'Every pair has at most one relation: the grammar is an operator-precedence grammar. An empty cell means the two terminals can never meet: a syntax error.', mark: R0.conflicts.length ? 'not operator-precedence' : 'done' });
      return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'rel', kind: 'text', title: 'The relations', text: 'a ≐ b: a and b appear side by side in a rule, or with one nonterminal between them. a <· b: a is followed by a nonterminal B in a rule, and b is in LEADING(B). a ·> b: a nonterminal A is followed by b in a rule, and a is in TRAILING(A). $ <· everything in LEADING(start); everything in TRAILING(start) ·> $.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.rel && fr[i + 1].meta.kind === 'greater', once: true, pick: 'option', options: ['<·', '≐', '·>'], ask: 'The next relation filled in: which one will it be?', answer: (fr, i) => fr[i + 1].meta.rel, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'less' && i > 2, once: true, pick: 'item', ask: 'A <· relation is next. Click the cell it goes into.', answer: (fr, i) => fr[i + 1].meta.cell, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'With E → E + T | T and T → T * P | P, what is the relation between + and *?', options: ['+ ≐ *', '+ <· *', '+ ·> *', 'None'], answer: 1, why: 'In E → E + T, + is followed by T, and * is in LEADING(T): the * phrase is reduced first, inside the +.' },
      { q: 'And between * and +?', options: ['* <· +', '* ≐ +', '* ·> +', 'None'], answer: 2, why: 'E is followed by + in E → E + T and * is in TRAILING(E): the * phrase ends before the +.' },
      { q: 'Which pair is related by ≐ in P → ( E ) | n?', options: ['( and )', '( and n', 'n and )', 'none'], answer: 0, why: '( and ) appear in the same rule with only a nonterminal between them.' },
      { q: 'Why must an operator grammar never put two nonterminals side by side?', options: ['To keep it unambiguous', 'So relations between neighbouring terminals are enough to find handles', 'For speed', 'Because of ε'], answer: 1, why: 'The parser only looks at terminals; two adjacent nonterminals would hide a boundary it cannot see.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'opp-parse', family: 'opp', order: 20, title: 'The operator-precedence parse',
    blurb: 'Compare the topmost terminal on the stack with the next input symbol: <· or ≐ means shift, ·> means the handle is complete. It starts just after the nearest <· below it. Nonterminals are carried along but never looked at.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Operator grammar', def: ARITH, check: checkOp },
      { id: 'w', kind: 'string', label: 'Input', def: 'n+n*n', max: 9 },
    ],
    presets: [
      { label: 'Products first: n+n*n', values: { g: ARITH, w: 'n+n*n' } },
      { label: 'Brackets: (n+n)*n', values: { g: ARITH, w: '(n+n)*n' } },
      { label: 'Right to left: n^n^n', values: { g: POW, w: 'n^n^n' } },
      { label: 'An error: n+*n', values: { g: ARITH, w: 'n+*n' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 9)(inp),
    counters: [{ id: 'shifts', label: 'shifts' }, { id: 'reduces', label: 'reductions' }],
    run(inp) {
      const G = T.PX.G(inp.g), R = T.opp.relationsFromGrammar(G), w = T.PX.word(G, inp.w), r = T.opp.parse(R, w), F = new T.Frames(['shifts', 'reduces']);
      let nodes = [{ id: 'bot', label: '$' }], seq = 0;
      const snaps = [];
      for (const st of r.trace) {
        snaps.push({ st, roots: nodes.slice(1).filter((n) => n.children) .concat([]), stackNodes: nodes.slice() });
        const shifted = w.length - (st.input.length - 1);
        if (st.kind === 'shift') nodes.push({ id: 't' + shifted, label: st.b, at: shifted, cls: 'term' });
        else if (st.kind === 'reduce') {
          const kids = nodes.splice(st.handle.start, st.handle.end - st.handle.start);
          nodes.push({ id: 'n' + seq++, label: st.prod !== null ? G.productions[st.prod].A : 'N', cls: 'nt', children: kids });
        }
      }
      const depth = (n) => (n.children ? 1 + Math.max(...n.children.map(depth)) : 0);
      const H = Math.max(2, ...nodes.slice(1).map(depth)) * 60;
      const ts = R.terminals, cw = 46, sy = 60;
      const tx = -cw / 2 + 60;
      const scene = (s, o) => {
        o = o || {};
        const st = s.st, shifted = w.length - (st.input.length - 1);
        const placed = s.stackNodes.slice(1);
        const pending = w.map((a, i) => ({ id: 't' + i, label: a, at: i, cls: 'term pending' })).slice(shifted);
        const items = T.PX.forest({ prefix: 'of', roots: placed.concat(pending), x: 0, y: 0, gap: 70, gy: 56, hot: o.hot || [] }).items;
        // the stack row with the relation between its top terminal and the next symbol
        const cells = st.stack.map((x, i) => ({ t: x, k: 'k' + i + x })), x0 = -cw / 2;
        cells.forEach((c, i) => items.push({ key: 'os:' + c.k, kind: 'cell', x: x0 + i * cw, y: sy, w: cw - 4, h: 40, text: c.t, cls: 'mono stack' + (c.t === 'N' ? ' act' : '') + (o.handle && i >= o.handle.start ? ' hot' : '') }));
        const rx = x0 + cells.length * cw + 6;
        items.push({ key: 'os:rel', kind: 'cell', x: rx, y: sy, w: 48, h: 40, text: st.relation ? N[st.relation] : '', cls: 'mono ' + (st.kind === 'error' ? 'bad' : 'mark'), size: 18 });
        st.input.forEach((x, i) => items.push({ key: 'oi:' + (w.length + 1 - st.input.length + i), kind: 'cell', x: rx + 56 + i * cw, y: sy, w: cw - 4, h: 40, text: x, cls: 'mono' + (i === 0 ? ' act' : '') + (x === '$' && i === st.input.length - 1 ? ' endmark' : '') }));
        items.push({ key: 'os:lab', kind: 'text', x: x0 - 14, y: sy + 25, text: 'stack', anchor: 'end', cls: 'title' });
        if (o.handle) items.push({ key: 'os:hb', kind: 'bracket', x1: x0 + o.handle.start * cw, x2: x0 + o.handle.end * cw - 4, y: sy + 46, side: 'below', text: 'handle', cls: 'y' });
        const a = st.a, b = st.b;
        items.push(...relTable(R, { x: tx, y: sy + 80, hot: a !== undefined && b !== undefined ? [ts.indexOf(a), ts.indexOf(b)] : null }).items);
        return items;
      };
      for (const s of snaps) {
        const st = s.st;
        if (st.kind === 'start') { F.add({ items: scene(s), say: st.say + ' Only terminals are compared; a reduced phrase shows on the stack as N.' }); continue; }
        if (st.kind === 'shift') { F.count('shifts'); F.add({ items: scene(s), say: st.say + (st.relation === '=' ? ' (≐: they belong to the same handle)' : ''), meta: { kind: 'shift', rel: N[st.relation] } }); continue; }
        if (st.kind === 'reduce') { F.count('reduces'); F.add({ items: scene(s, { handle: st.handle }), say: st.say + ' The handle runs from just after the nearest <· down the stack up to the top.', hl: { g: st.prod === null ? [] : [st.prod] }, meta: { kind: 'reduce', rel: '·>' } }); continue; }
        if (st.kind === 'accept') { F.add({ items: scene(s, { hot: s.stackNodes.slice(1).map((n) => n.id) }), say: st.say + ' The tree is skeletal: chains of unit rules such as E → T → P leave no handle of their own, so they do not appear.', mark: 'accepted', meta: { yes: true } }); continue; }
        if (st.kind === 'error') F.add({ items: scene(s), say: st.say + ' An empty table cell means these two terminals can never meet in a sentence.', mark: 'rejected', meta: { yes: false } });
      }
      return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'tb', kind: 'table', title: 'Relations', corner: 'stack \\ next', colHead: ts, rowHead: ts, rows: ts.map((a) => ts.map((b) => (R.rel[a][b] ? N[R.rel[a][b]] : ''))) }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.rel && i > 1, once: true, pick: 'option', options: ['Shift', 'Reduce'], ask: 'Compare the top terminal with the next symbol in the table. Shift or reduce?', answer: (fr, i) => (fr[i + 1].meta.kind === 'reduce' ? 'Reduce' : 'Shift'), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the input be accepted?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'The top terminal is + and the next symbol is *, with + <· *. What happens?', options: ['Reduce', 'Shift *', 'Error', 'Accept'], answer: 1, why: '<· means a new handle starts at *: shift it.' },
      { q: 'Where does a handle begin?', options: ['At the bottom of the stack', 'Just after the nearest terminal below it related by <·', 'At the top terminal', 'At the first N'], answer: 1, why: 'Walk down through ≐ relations until a <· is found; the handle starts just above it.' },
      { q: 'Why is the parse tree called skeletal?', options: ['It has no leaves', 'Unit rules like E → T never form a handle, so those nodes are missing', 'It is drawn faintly', 'It has no root'], answer: 1, why: 'The parser cannot see nonterminals, so a phrase that is only renamed is never reduced on its own.' },
      { q: 'How does n ^ n ^ n group when ^ is right-associative in the grammar?', options: ['(n ^ n) ^ n', 'n ^ (n ^ n)', 'It is an error', 'Either way'], answer: 1, why: '^ <· ^ makes the parser shift the second ^ before reducing the first.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  const CYCLE = 'a b $\na < > >\nb > < >\n$ < < .';
  T.topic({
    id: 'opp-functions', family: 'opp', order: 30, title: 'Precedence functions',
    blurb: 'Replace the table by two numbers per terminal: f for it on the stack and g for it as input, with f(a) < g(b) exactly when a <· b. Build a graph (≐ glues nodes, the other relations become edges); the longest path out of each node is its value. A cycle means no functions exist.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Operator grammar', def: ARITH, check: checkOp },
      { id: 't', kind: 'text', label: 'Or a relation table (header line of terminals, then one row each; leave empty to use the grammar)', def: '' },
    ],
    presets: [
      { label: 'Sums and products', values: { g: ARITH, t: '' } },
      { label: 'A list: S → S ; a | a', values: { g: LISTS, t: '' } },
      { label: 'A table with a cycle', values: { g: ARITH, t: CYCLE } },
    ],
    check: (inp) => { if (!inp.t || !inp.t.trim()) return null; try { T.opp.fromTable(inp.t); return null; } catch (e) { return 'Table: ' + e.message; } },
    counters: [{ id: 'nodes', label: 'nodes' }, { id: 'edges', label: 'edges' }],
    run(inp) {
      const useT = inp.t && inp.t.trim();
      const G = T.PX.G(inp.g), R = useT ? T.opp.fromTable(inp.t) : T.opp.relationsFromGrammar(G), fn = T.opp.functions(R), ts = R.terminals;
      const F = new T.Frames(['nodes', 'edges']);
      const parent = new Map();
      for (const a of ts) { parent.set('f' + a, 'f' + a); parent.set('g' + a, 'g' + a); }
      const find = (x) => { while (parent.get(x) !== x) x = parent.get(x); return x; };
      const label = (root) => { const ms = [...parent.keys()].filter((k) => find(k) === root); return ms.map((k) => k[0] + '(' + k.slice(1) + ')').join(' ≐ '); };
      const edges = [];
      // final nodes and their places, so nothing moves while the graph is built
      for (const st of fn.trace) if (st.kind === 'merge') parent.set(find('g' + st.b), find('f' + st.a));
      const finalRoots = [...new Set([...parent.keys()].map(find))];
      const finalOf = new Map([...parent.keys()].map((k) => [k, find(k)]));
      for (const k of parent.keys()) parent.set(k, k);
      const names = {};
      // f nodes on a top row, g nodes on a bottom row, glued pairs between; at the end every node slides to
      // its value on a number line, so a <· b reads as f(a) left of g(b)
      const rowOf = (rt) => { const ms = [...parent.keys()].filter((k) => find(k) === rt); return ms.some((k) => k[0] === 'f') && ms.some((k) => k[0] === 'g') ? 1 : ms[0][0] === 'f' ? 0 : 2; };
      const valueOf = (rt) => (rt[0] === 'f' ? fn.f[rt.slice(1)] : fn.g[rt.slice(1)]);
      const place = (roots, byValue) => {
        const at = {}, used = {};
        for (const rt of roots) {
          const row = rowOf(rt);
          let x;
          let dy = 0;
          if (byValue) { const v = valueOf(rt); const key = row + ':' + v; used[key] = (used[key] || 0) + 1; x = v * 130; dy = (used[key] - 1) * 52 * (row === 2 ? 1 : -1); }
          else x = ts.indexOf(rt.slice(1)) * 96;
          at[rt] = { x, y: row * 170 + dy };
        }
        return at;
      };
      const scene = (o) => {
        o = o || {};
        const roots = [...new Set([...parent.keys()].map(find))];
        const at = place(roots, !!o.values), items = [];
        const hot = new Set(o.hot || []), bad = new Set(o.bad || []);
        for (const rt of roots) {
          const text = names[rt] || label(rt), w = Math.max(54, T.geom.textWidth(text, 16, { bold: true }) + 22);
          items.push({ key: 'pf:s:' + rt, kind: 'state', x: at[rt].x, y: at[rt].y, w, h: 44, rx: 22, text, cls: 'state' + (hot.has(rt) ? ' hot' : '') + (bad.has(rt) ? ' bad' : ''), sub: o.values ? String(valueOf(rt)) : undefined, pick: true });
        }
        const seenE = new Set();
        for (const e of edges) {
          const a = find(e.from), b = find(e.to), k = a + '>' + b;
          if (seenE.has(k)) continue; seenE.add(k);
          items.push({ key: 'pf:e:' + k, kind: 'edge', from: 'pf:s:' + a, to: 'pf:s:' + b, bend: rowOf(a) === rowOf(b) ? 40 : 0, cls: (o.edgeCls && o.edgeCls[k]) || (hot.has(a) && hot.has(b) ? 'hot' : 'soft'), audit: 'edge-x' });
        }
        T.PX.unblock(items);
        if (o.values) {
          const maxV = Math.max(0, ...roots.map(valueOf));
          for (let v = 0; v <= maxV; v++) items.push({ key: 'pf:tick' + v, kind: 'text', x: v * 130, y: 2 * 170 + 150, text: String(v), anchor: 'middle', cls: 'strong', size: 16 });
          items.push({ key: 'pf:axis', kind: 'line', x1: -30, y1: 2 * 170 + 126, x2: maxV * 130 + 60, y2: 2 * 170 + 126, cls: 'dash' });
        }
        ['f(a): on the stack', 'f ≐ g', 'g(b): next input'].forEach((t, r) => items.push({ key: 'pf:row' + r, kind: 'text', x: -70, y: r * 170 + 5, text: t, anchor: 'end', cls: 'title' }));
        return items;
      };
      for (const rt of [...parent.keys()]) names[rt] = label(rt);
      F.set('nodes', parent.size);
      F.add({ items: scene({}), say: 'One node for f(a) and one for g(a), for every terminal a among ' + ts.join(' ') + '. f is a terminal\'s strength on the stack, g its strength as the next input.' });
      for (const st of fn.trace) {
        if (st.kind === 'merge') {
          const a = find('f' + st.a), b = find('g' + st.b);
          parent.set(b, a); names[a] = label(a);
          F.set('nodes', new Set([...parent.keys()].map(find)).size);
          F.add({ items: scene({ hot: [a] }), say: st.say, meta: { kind: 'merge' } });
        } else if (st.kind === 'edge') {
          edges.push({ from: st.from, to: st.to }); F.count('edges');
          F.add({ items: scene({ hot: [st.from, st.to] }), say: st.say + ' An edge ' + names[st.from] + ' → ' + names[st.to] + '.', meta: { kind: 'edge' } });
        } else if (st.kind === 'cycle') {
          const cyc = st.cycle, ec = {};
          for (let i = 0; i + 1 < cyc.length; i++) ec[cyc[i] + '>' + cyc[i + 1]] = 'bad';
          F.add({ items: scene({ bad: cyc, edgeCls: ec }), say: st.say + ' Each node on it would have to be bigger than itself.', mark: 'no functions', meta: { ok: false } });
        }
      }
      if (fn.ok) {
        F.add({ items: scene({ values: true }), say: 'Every node gets the length of the longest path out of it: ' + ts.map((a) => 'f(' + a + ') = ' + fn.f[a] + ', g(' + a + ') = ' + fn.g[a]).join('; ') + '. Now a <· b exactly when f(a) < g(b), and so on, with 2n numbers instead of n² cells.', mark: 'functions found', meta: { ok: true } });
        F.add({ items: scene({ values: true }), say: 'The price: an empty cell (an error) is lost, since any two numbers compare. A parser using f and g notices some errors later, when it tries to reduce a handle that matches no rule.' });
      }
      return { frames: F.list, def: { sections: [{ id: 'tb', kind: 'table', title: 'Relations', corner: 'stack \\ next', colHead: ts, rowHead: ts, rows: ts.map((a) => ts.map((b) => (R.rel[a][b] ? N[R.rel[a][b]] : ''))) }].concat(fn.ok ? [{ id: 'fg', kind: 'table', title: 'f and g', colHead: ts, rowHead: ['f', 'g'], rows: [ts.map((a) => String(fn.f[a])), ts.map((a) => String(fn.g[a]))] }] : []) } };
    },
    predict: [
      { at: (f, i, fr) => i === 0, once: true, pick: 'option', options: ['Yes', 'No: there is a cycle'], ask: 'Will precedence functions exist for this table?', answer: (fr) => (fr.some((x) => x.meta && x.meta.ok === false) ? 'No: there is a cycle' : 'Yes'), explain: (fr) => fr.find((x) => x.meta && x.meta.ok !== undefined).say },
    ],
    quiz: [
      { q: 'a ·> b. Which edge does the graph get?', options: ['g(b) → f(a)', 'f(a) → g(b)', 'f(a) ≐ g(b)', 'None'], answer: 1, why: 'f(a) must be bigger than g(b); an edge points from the bigger to the smaller.' },
      { q: 'Why does a cycle mean no functions exist?', options: ['The graph is too large', 'Every node on it would have to be bigger than itself', 'The grammar is ambiguous', 'It does not'], answer: 1, why: 'Following edges always goes to a strictly smaller value.' },
      { q: 'What is lost by using f and g instead of the table?', options: ['Nothing', 'The empty cells: errors are detected later', 'The ≐ relations', 'Associativity'], answer: 1, why: 'Two numbers always compare, so blank cells become some relation.' },
      { q: 'How much space do the functions need for n terminals?', options: ['n²', '2n numbers', 'n³', 'One number'], answer: 1, why: 'One f and one g per terminal.' },
    ],
  });
})();
