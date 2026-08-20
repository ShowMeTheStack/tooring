// The LR family, part two: parsing with it. Shift-reduce with handles (the stack, the rest of the input and
// the rightmost derivation read backwards), the LR driver with its states, the automaton lit and the tree
// growing bottom up over the tokens, precedence and associativity settling the conflicts of an ambiguous
// expression grammar, and a map of the grammar classes with examples placed in it.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const LR = () => T.PX.LR;

  T.family({ id: 'shift-reduce', part: 'parsing', order: 40, title: 'Shift-reduce parsing', blurb: 'Bottom up: shift input symbols onto a stack and, when the top of the stack is a handle, reduce it to a nonterminal. The tree grows from the leaves to the root.' });
  T.family({ id: 'lr-power', part: 'parsing', order: 50, title: 'The power of LR', blurb: 'Precedence declarations that settle conflicts, and which grammars each method can take.' });

  const SUMS = 'E → E + T | T\nT → x | ( E )';
  const LISTS = 'L → L ; x | x';
  const OPTL = 'L → x L | ε';
  const checkGL = (v) => T.PX.LR.checkG(v);

  /** Replay an LR parse into a forest over the tokens: shifted leaves, reduced nodes, pending tokens dim */
  function replay(G, r, w) {
    const out = [];
    let nodes = [], seq = 0;
    for (const st of r.trace) {
      const shifted = w.length - (st.input.length - 1);
      out.push({ st, roots: nodes.slice(), shifted });
      if (st.kind === 'shift') nodes.push({ id: 't' + shifted, label: st.symbol, at: shifted, cls: 'term' });
      else if (st.kind === 'reduce') {
        const q = T.lr.augment(G).productions[st.prod], k = q.rhs.length;
        const kids = k ? nodes.splice(nodes.length - k, k) : [{ id: 'e' + seq, label: 'ε', at: shifted - 0.5, cls: 'eps' }];
        nodes.push({ id: 'n' + seq++, label: q.A, cls: 'nt', children: kids });
      }
    }
    return out;
  }
  const forestItems = (s, w, opts) => {
    const pending = w.map((a, i) => ({ id: 't' + i, label: a, at: i, cls: 'term pending' })).slice(s.shifted);
    return T.PX.forest(Object.assign({ prefix: 'sf', roots: s.roots.concat(pending), x: 0, y: 0, gap: 70, gy: 56 }, opts));
  };
  const tableFor = (G) => T.lr.buildTable(G, 'lalr', { precedence: true });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'shift-reduce', family: 'shift-reduce', order: 10, title: 'Shift, reduce, and the handle',
    blurb: 'Read symbols onto a stack; whenever the top of the stack is a handle (a right side whose reduction leads back to the start), replace it by its left side. Read the reductions upwards and you have a rightmost derivation.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: SUMS, check: checkGL },
      { id: 'w', kind: 'string', label: 'Input', def: 'x+(x+x)', max: 8 },
    ],
    presets: [
      { label: 'Sums: x+(x+x)', values: { g: SUMS, w: 'x+(x+x)' } },
      { label: 'A list: x;x;x', values: { g: LISTS, w: 'x;x;x' } },
      { label: 'ε at the end: x x', values: { g: OPTL, w: 'xx' } },
      { label: 'Rejected: x+)', values: { g: SUMS, w: 'x+)' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 8)(inp),
    counters: [{ id: 'shifts', label: 'shifts' }, { id: 'reduces', label: 'reductions' }],
    run(inp) {
      const G = T.PX.G(inp.g), t = tableFor(G), w = T.PX.word(G, inp.w), r = T.lr.parse(t, w), aug = t.aug;
      const snaps = replay(G, r, w), F = new T.Frames(['shifts', 'reduces']);
      const forms = [];
      const lastRoots = snaps[snaps.length - 1].roots;
      const depth = (n) => (n.children ? 1 + Math.max(...n.children.map(depth)) : 0);
      const H = Math.max(2, ...lastRoots.map(depth), r.accepted ? 0 : 2) * 60;
      const rowY = 60, cw = 44;
      const formText = (st) => (st.symbols.concat(st.input.slice(0, -1)).join(' ') || 'ε');
      const panelX = w.length * 70 + 20;
      const scene = (s, o) => {
        o = o || {};
        const fo = forestItems(s, w, { hot: o.hot || [] });
        const items = fo.items;
        // the configuration: stack | rest of the input, with the handle bracketed
        const st = s.st, cells = st.symbols.map((x, i) => ({ t: x, k: 's' + i + x })).concat([{ t: '|', k: 'bar' }], st.input.map((x, i) => ({ t: x, k: 'i' + (w.length + 1 - st.input.length + i) })));
        cells.forEach((c, i) => items.push({ key: 'cf:' + c.k, kind: 'cell', x: -cw / 2 + i * cw, y: rowY, w: c.t === '|' ? 14 : cw - 4, h: 40, text: c.t === '|' ? '' : c.t, cls: c.t === '|' ? 'mark' : i < st.symbols.length ? 'mono act' : 'mono' + (c.t === '$' ? ' endmark' : '') }));
        if (o.handle) items.push({ key: 'cf:hb', kind: 'bracket', x1: -cw / 2 + o.handle.start * cw, x2: -cw / 2 + Math.max(o.handle.end, o.handle.start + 0.3) * cw - 4, y: rowY + 46, side: 'below', text: 'handle', cls: 'y' });
        items.push({ key: 'cf:lab', kind: 'text', x: -cw / 2 - 14, y: rowY + 25, text: 'stack | input', anchor: 'end', cls: 'title' });
        items.push(...T.PX.panel({ prefix: 'dv', x: panelX, y: -H, title: 'Derivation, read upwards', rows: forms.slice().reverse().map((f, k) => ({ id: f.id, text: (k === 0 ? '' : '⇒ ') + f.text, cls: k === 0 ? 'hot' : '' })), rowH: 30, size: 15, w: Math.max(240, (w.length + 2) * 20 + 60), mono: true, minH: H + 40 }).items);
        return items;
      };
      for (const s of snaps) {
        const st = s.st;
        if (st.kind === 'start') { forms.push({ id: 'f0', text: formText(st) }); F.add({ items: scene(s), say: 'The stack is empty and the whole input ' + T.PX.show(w) + ' is waiting. The input itself is the last line of a rightmost derivation; each reduction will write the line before it.' }); continue; }
        if (st.kind === 'shift') { F.count('shifts'); F.add({ items: scene(s), say: 'No handle on top of the stack yet, so shift ' + st.symbol + '.', meta: { kind: 'shift' } }); continue; }
        if (st.kind === 'reduce') {
          F.count('reduces');
          const q = aug.productions[st.prod];
          const after = st.symbols.slice(0, st.handle.start).concat([q.A], st.symbols.slice(st.handle.end));
          F.add({ items: scene(s, { handle: st.handle }), say: 'The top of the stack, ' + (q.rhs.length ? T.grammar.showRhs(aug, q.rhs) : 'nothing (an empty handle)') + ', is a handle: reduce it by ' + T.grammar.showProd(aug, q) + '.', hl: { g: [st.prod - 1] }, meta: { kind: 'reduce', prod: st.prod } });
          forms.push({ id: 'f' + forms.length, text: after.concat(st.input.slice(0, -1)).join(' ') || 'ε' });
          continue;
        }
        if (st.kind === 'accept') { F.add({ items: scene(s, { hot: s.roots.map((n) => n.id) }), say: 'The stack holds just ' + G.start + ' and the input is used up: accept. Read the panel from the top down and it is a rightmost derivation of ' + T.PX.show(w) + '; the reductions found it backwards.', mark: 'accepted', meta: { yes: true } }); continue; }
        if (st.kind === 'error') F.add({ items: scene(s), say: st.say + ' No handle can ever form from this stack, so ' + T.PX.show(w) + ' is rejected.', mark: 'rejected', meta: { yes: false } });
      }
      return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'h', kind: 'text', title: 'Handles', text: 'A handle is a right side on top of the stack whose reduction is one step of the rightmost derivation, backwards. Reducing anything else, even a matching right side, leads to a dead end. An LR parser recognises handles with its automaton.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i].meta && fr[i].meta.kind === 'shift', once: true, pick: 'option', options: ['Shift', 'Reduce'], ask: 'Shift the next symbol, or reduce what is on top?', answer: (fr, i) => (fr[i + 1].meta.kind === 'reduce' ? 'Reduce' : 'Shift'), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the input be accepted?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Which derivation does a shift-reduce parser trace, read from its last reduction back?', options: ['Leftmost', 'Rightmost', 'Neither', 'Both'], answer: 1, why: 'Each reduction undoes the rightmost step: the handle is always at the right end of the part already read.' },
      { q: 'Stack: E + T, next symbol $, grammar E → E + T | T. What happens?', options: ['Reduce T to E', 'Reduce E + T to E', 'Shift $', 'Error'], answer: 1, why: 'E + T is the handle; reducing only T would leave E + E, which no rule can reduce.' },
      { q: 'Why is the handle always on top of the stack?', options: ['By luck', 'Because the parser reduces as soon as a handle appears, before shifting further', 'Because the stack is reversed', 'It is not'], answer: 1, why: 'Rightmost derivations in reverse expose handles at the right end of what has been read.' },
      { q: 'How many reductions does the parse of a string make?', options: ['One per input symbol', 'One per interior node of its parse tree', 'One per rule', 'Two per symbol'], answer: 1, why: 'Each reduction creates exactly one node above the leaves.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'lr-parse', family: 'shift-reduce', order: 20, title: 'The LR parser at work',
    blurb: 'States on the stack remember what has been seen. ACTION[state, next symbol] says shift or reduce; after a reduction, GOTO[exposed state, nonterminal] says where to go. The automaton lights up as the parser walks it.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: SUMS, check: checkGL },
      { id: 'w', kind: 'string', label: 'Input', def: 'x+(x)', max: 7 },
    ],
    presets: [
      { label: 'Sums: x+(x)', values: { g: SUMS, w: 'x+(x)' } },
      { label: 'A list: x;x;x', values: { g: LISTS, w: 'x;x;x' } },
      { label: 'Rejected early: x(', values: { g: SUMS, w: 'x(' } },
      { label: 'Products first: x+x*x', values: { g: 'E → E + T | T\nT → T * x | x', w: 'x+x*x' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 7)(inp),
    counters: [{ id: 'shifts', label: 'shifts' }, { id: 'reduces', label: 'reductions' }, { id: 'height', label: 'stack height' }],
    run(inp) {
      const G = T.PX.G(inp.g), t = tableFor(G), aug = t.aug, w = T.PX.word(G, inp.w), r = T.lr.parse(t, w);
      const coll = { states: t.states }, m = LR().machine(coll), pos = LR().layout(m), bx = LR().box(pos, m);
      const snaps = replay(G, r, w), F = new T.Frames(['shifts', 'reduces', 'height']);
      const fx = bx.x + bx.w + 70;
      const lastRoots = snaps[snaps.length - 1].roots;
      const depth = (n) => (n.children ? 1 + Math.max(...n.children.map(depth)) : 0);
      const fH = Math.max(2, ...lastRoots.map(depth)) * 60;
      const fy = Math.max(bx.y + fH + 30, bx.y + bx.h - 60);
      const sy = Math.max(bx.y + bx.h, fy + 40) + 50;
      const scene = (s, o) => {
        o = o || {};
        const st = s.st, cur = st.stack[st.stack.length - 1];
        const g = K.graph.draw(m, { pos, prefix: 'au', hot: [String(o.state === undefined ? cur : o.state)], taken: o.edge ? [o.edge] : [], bad: o.bad ? [String(cur)] : [] });
        const items = g.items;
        items.push(...forestItems(s, w, { x: fx, y: fy, hot: o.hotNodes || [] }).items);
        // the stack as a row: state, symbol, state, …
        let x = bx.x;
        items.push({ key: 'ls:lab', kind: 'text', x: x, y: sy - 12, text: 'stack (states and symbols)', cls: 'title' });
        st.stack.forEach((q, i) => {
          if (i) { const sym = st.symbols[i - 1]; items.push({ key: 'ls:y' + i + ':' + sym, kind: 'cell', x, y: sy, w: 44, h: 40, text: sym, cls: 'mono stack' + (o.handle && i - 1 >= o.handle.start ? ' hot' : ''), enter: 'drop', exit: 'rise' }); x += 48; }
          items.push({ key: 'ls:q' + i + ':' + q, kind: 'cell', x, y: sy, w: 40, h: 40, text: String(q), cls: 'mono stack act' + (i === st.stack.length - 1 ? ' hot' : ''), enter: 'drop', exit: 'rise', pick: true });
          x += 44;
        });
        items.push(...T.PX.panel({ prefix: 'ac', x: Math.max(x + 40, fx), y: sy - 30, w: 300, mono: false, rows: [{ id: 'a', text: o.action || ' ', cls: o.bad ? 'bad' : o.action ? 'act' : '' }], rowH: 34, size: 15 }).items);
        return items;
      };
      for (const s of snaps) {
        const st = s.st, cur = st.stack[st.stack.length - 1];
        F.set('height', st.stack.length);
        if (st.kind === 'start') { F.add({ items: scene(s, { action: 'start in state 0' }), say: 'The stack holds state 0, the automaton\'s start. Each step looks up ACTION[top state, next symbol].', meta: {} }); continue; }
        const a = st.input[0];
        if (st.kind === 'shift') { F.count('shifts'); F.add({ items: scene(s, { action: 'ACTION[' + cur + ', ' + a + '] = s' + st.to, edge: cur + '>' + st.to }), say: 'ACTION[' + cur + ', ' + a + '] = s' + st.to + ': push ' + a + ' and state ' + st.to + ', following the edge on ' + a + '.', meta: { kind: 'shift', to: st.to } }); continue; }
        if (st.kind === 'reduce') {
          F.count('reduces');
          const q = aug.productions[st.prod];
          F.add({ items: scene(s, { action: 'ACTION[' + cur + ', ' + a + '] = r' + st.prod, handle: st.handle }), say: 'ACTION[' + cur + ', ' + a + '] = r' + st.prod + ': reduce by ' + T.grammar.showProd(aug, q) + '. Pop ' + q.rhs.length + ' symbol' + (q.rhs.length === 1 ? '' : 's') + ' with their states, exposing state ' + st.exposed + '.', hl: { g: [st.prod] }, meta: { kind: 'reduce', exposed: st.exposed, goto: st.goto } });
          F.add({ items: scene(snaps[snaps.indexOf(s) + 1] || s, { action: 'GOTO[' + st.exposed + ', ' + q.A + '] = ' + st.goto, state: st.goto, edge: st.exposed + '>' + st.goto }), say: 'GOTO[' + st.exposed + ', ' + q.A + '] = ' + st.goto + ': push ' + q.A + ' and state ' + st.goto + '. In the tree, ' + q.A + ' becomes the parent of what was reduced.', meta: { kind: 'goto' } });
          continue;
        }
        if (st.kind === 'accept') { F.add({ items: scene(s, { action: 'ACTION[' + cur + ', $] = accept', hotNodes: s.roots.map((n) => n.id) }), say: 'ACTION[' + cur + ', $] = accept: the input reduced to ' + G.start + '. The tree is complete, built from the leaves up.', mark: 'accepted', meta: { yes: true } }); continue; }
        if (st.kind === 'error') F.add({ items: scene(s, { action: 'ACTION[' + cur + ', ' + a + '] is empty', bad: true }), say: st.say + ' The error is found at the first symbol that cannot continue any sentence: LR parsers detect errors as early as possible.', mark: 'rejected', meta: { yes: false } });
      }
      const rowsT = t.states.map((s) => t.terminals.concat(t.nonterminals).map((a) => { const x = t.action[s.id][a]; return x ? T.lr.actionText(x) : t.goto[s.id][a] !== undefined ? String(t.goto[s.id][a]) : ''; }));
      return { frames: F.list, def: { sections: [T.PX.gdef(aug, { title: 'Augmented grammar (rule numbers)', numbered: true }), { id: 'tb', kind: 'table', title: 'ACTION and GOTO (LALR(1))', corner: 'state', colHead: t.terminals.concat(t.nonterminals), rowHead: t.states.map((s) => String(s.id)), rows: rowsT }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'goto' && i > 3, once: true, pick: 'item', ask: 'After this reduction, which state will be exposed on top of the stack? Click it in the stack.', answer: (fr, i) => { const m = fr[i].meta; void m; return fr[i].items.filter((it) => /^ls:q/.test(it.key) && it.text === String(fr[i].meta.exposed)).map((it) => it.key); }, explain: (fr, i) => fr[i].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'shift' && i > 0, once: true, pick: 'item', ask: 'The next step is a shift. Click the state the automaton moves to.', answer: (fr, i) => 'au:s:' + fr[i + 1].meta.to, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does an LR parser keep states on its stack and not just symbols?', options: ['To save time: the top state sums up everything below it', 'For error messages only', 'Because symbols cannot be stored', 'To count the input'], answer: 0, why: 'The top state is where the automaton would be after reading the stack\'s symbols, so nothing below needs to be looked at.' },
      { q: 'After reducing by A → β with |β| = 3, how many stack entries are popped?', options: ['1', '3 symbols with their 3 states', '4', 'All of them'], answer: 1, why: 'Each symbol of the handle came with a state; both go.' },
      { q: 'What is GOTO used for?', options: ['Shifting', 'Choosing the state after pushing the nonterminal of a reduction', 'Accepting', 'Errors'], answer: 1, why: 'The exposed state and the new nonterminal give the next state.' },
      { q: 'How soon does an LR parser notice a syntax error?', options: ['At the end of the input', 'At the first symbol that cannot continue any valid prefix', 'After the next reduction', 'Never'], answer: 1, why: 'It has the viable-prefix property: it never shifts a symbol that cannot lead to a sentence.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  const EXPR = 'E → E + E | E * E | ( E ) | n';
  const withPrec = (decl) => (decl ? decl + '\n' : '') + EXPR;
  T.topic({
    id: 'lr-precedence', family: 'lr-power', order: 10, title: 'Precedence and associativity settle conflicts',
    blurb: 'An ambiguous expression grammar gives shift/reduce conflicts. Declaring which operator binds tighter, and whether equal ones group left or right, picks one action in every clashing cell, and so picks one tree.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar with %left / %right / %nonassoc lines', def: withPrec('%left +\n%left *'), check: (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 3 })(v) },
      { id: 'w', kind: 'string', label: 'Expression', def: 'n+n*n+n', max: 9 },
    ],
    presets: [
      { label: 'Usual: + below *, both left', values: { g: withPrec('%left +\n%left *'), w: 'n+n*n+n' } },
      { label: 'No declarations: shift wins', values: { g: withPrec(''), w: 'n+n*n+n' } },
      { label: 'Reversed: * below +', values: { g: withPrec('%left *\n%left +'), w: 'n+n*n+n' } },
      { label: 'Right-associative +', values: { g: withPrec('%right +\n%left *'), w: 'n+n+n' } },
      { label: 'Non-associative +: n+n+n is an error', values: { g: withPrec('%nonassoc +\n%left *'), w: 'n+n+n' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 9)(inp),
    counters: [{ id: 'cells', label: 'clashing cells' }, { id: 'settled', label: 'settled by declarations' }],
    run(inp) {
      const G = T.PX.G(inp.g), t = T.lr.buildTable(G, 'lalr', { precedence: true }), raw = T.lr.buildTable(G, 'lalr', { precedence: false });
      const w = T.PX.word(G, inp.w), r = T.lr.parse(t, w), aug = t.aug, F = new T.Frames(['cells', 'settled']);
      const decl = Object.entries(G.precedence || {}).sort((a, b) => a[1].level - b[1].level);
      const rows = [];
      const cardW = 430;
      const snaps = replay(G, r, w);
      const fin = snaps[snaps.length - 1];
      const scene = (o) => {
        o = o || {};
        const items = T.PX.panel({ prefix: 'pc', x: 0, y: 0, w: cardW, title: 'Clashing cells', rows: rows.map((x, k) => Object.assign({}, x, { cls: x.cls + (k === rows.length - 1 && o.lit ? ' hot' : '') })), rowH: 30, size: 14, mono: false, minH: 30 + Math.max(4, raw.conflicts.length) * 34 + 8 }).items;
        items.push(...T.PX.panel({ prefix: 'pd', x: 0, y: 30 + Math.max(4, raw.conflicts.length) * 34 + 30, w: cardW, title: 'Declarations (lowest first)', rows: decl.length ? decl.map(([a, v]) => ({ id: a, text: '%' + v.assoc + '  ' + a + '   (level ' + v.level + ')' })) : [{ id: 'none', text: 'none: every conflict falls back to shift', cls: 'faint' }], rowH: 30, size: 14, mono: false }).items);
        if (o.tree) items.push(...forestItems(o.tree, w, { x: cardW + 70, y: 300 }).items);
        return items;
      };
      F.add({ items: scene({}), say: 'E → E + E | E * E is ambiguous, so its LALR(1) table has ' + raw.conflicts.length + ' shift/reduce conflicts: with E + E on the stack and * next, should the parser reduce the + now, or shift the * first?', meta: { n: raw.conflicts.length } });
      for (const c of raw.conflicts) {
        F.count('cells');
        const res = t.resolutions.find((x) => x.state === c.state && x.symbol === c.symbol);
        const red = aug.productions[c.actions.find((x) => x.type === 'reduce').prod];
        const what = 'stack … ' + T.grammar.showRhs(aug, red.rhs) + ', next ' + c.symbol + ': ';
        if (res) { F.count('settled'); rows.push({ id: c.state + c.symbol, text: what + res.decided, cls: res.decided === 'error' ? 'bad' : 'good' }); F.add({ items: scene({ lit: true }), say: res.say, meta: { decided: res.decided } }); }
        else { rows.push({ id: c.state + c.symbol, text: what + 'shift (by default)', cls: 'bad' }); F.add({ items: scene({ lit: true }), say: c.say + ' No declaration covers it.', meta: { decided: 'shift' } }); }
      }
      const shape = r.accepted ? fin.roots[0] : null;
      const group = (n) => (!n.children ? n.label : n.children.length === 3 && n.children[0].children ? '(' + group(n.children[0]) + ' ' + n.children[1].label + ' ' + group(n.children[2]) + ')' : n.children.length === 1 ? group(n.children[0]) : n.children.map(group).join(' '));
      F.add({ items: scene({ tree: fin }), say: r.accepted ? 'With the table settled, ' + T.PX.show(w) + ' has exactly one parse: ' + group(shape).replace(/^\((.*)\)$/, '$1') + ', read off the tree.' : 'The parse of ' + T.PX.show(w) + ' fails: ' + r.error.message + '. A non-associative operator may not be chained without brackets.', mark: r.accepted ? 'one tree' : 'rejected' });
      return { frames: F.list, def: { sections: [T.PX.gdef(aug, { title: 'Augmented grammar (rule numbers)', numbered: true }), { id: 'rule', kind: 'text', title: 'How a clash is settled', text: 'Compare the precedence of the next symbol with that of the rule (its last operator). Higher symbol: shift. Higher rule: reduce. Equal: %left reduces, %right shifts, %nonassoc makes it an error. With no declaration, shift wins.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.decided && i === 0, once: true, pick: 'option', options: ['shift', 'reduce', 'error'], ask: 'The first clashing cell: what will the declarations choose?', answer: (fr, i) => fr[i + 1].meta.decided, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Stack E + E, next symbol *, with %left + then %left *. What does the parser do?', options: ['Reduce E + E', 'Shift *', 'Error', 'Accept'], answer: 1, why: '* is declared later, so it binds tighter: shift it and do the multiplication first.' },
      { q: 'Stack E + E, next symbol +, with %left +. What happens?', options: ['Shift', 'Reduce', 'Error', 'It depends on the input'], answer: 1, why: 'Equal precedence and left associativity: reduce, so n + n + n groups as (n + n) + n.' },
      { q: 'What does %right do for a ^ b ^ c?', options: ['Groups as (a ^ b) ^ c', 'Groups as a ^ (b ^ c)', 'Makes it an error', 'Nothing'], answer: 1, why: 'Right associativity shifts on equal precedence, so the right part is reduced first.' },
      { q: 'Why use precedence declarations instead of an unambiguous grammar?', options: ['They accept more strings', 'The grammar stays short and readable and the table smaller', 'They are required by LR', 'They remove the need for a lexer'], answer: 1, why: 'E → E op E with a few declarations replaces a ladder of nonterminals, one per level.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  const EXAMPLES = [
    { id: 'ex1', short: 'a A | b B', label: 'S → a A | b B; A → c; B → c', g: 'S → a A | b B\nA → c\nB → c' },
    { id: 'ex2', short: 'L → L ; x | x', label: 'L → L ; x | x', g: 'L → L ; x | x' },
    { id: 'ex3', short: 'L → x L | ε', label: 'L → x L | ε', g: 'L → x L | ε' },
    { id: 'ex4', short: 'sums, products', label: 'E → E + T | T; T → T * x | x', g: 'E → E + T | T\nT → T * x | x' },
    { id: 'ex5', short: 'S → c | A A', label: 'S → c | A A; A → B; B → c', g: 'S → c | A A\nA → B\nB → c' },
    { id: 'ex6', short: 'a X b | c Y b …', label: 'S → a X b | c Y b | a Y d | …', g: 'S → a X b | c Y b | a Y d | c X d\nX → e\nY → e' },
    { id: 'ex7', short: 'E → E + E | n', label: 'E → E + E | n', g: 'E → E + E | n' },
  ];
  const LEVELS = [['none', 'All context-free grammars'], ['lr1', 'LR(1)'], ['lalr', 'LALR(1)'], ['slr', 'SLR(1)'], ['lr0', 'LR(0)']];
  const levelOf = (v) => ({ 'LR(0)': 4, 'SLR(1)': 3, 'LALR(1)': 2, 'LR(1)': 1 })[v] || 0;
  T.topic({
    id: 'lr-classify', family: 'lr-power', order: 20, title: 'Which method takes which grammar',
    blurb: 'LR(0) ⊂ SLR(1) ⊂ LALR(1) ⊂ LR(1): each looks further or more precisely and takes more grammars. LL(1) cuts across: every LL(1) grammar is LR(1), but a left-recursive grammar is never LL(1).',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Your grammar', def: 'S → c | A A\nA → B\nB → c', check: checkGL }],
    presets: EXAMPLES.map((e) => ({ label: e.label.length > 30 ? e.label.slice(0, 28) + '…' : e.label, values: { g: e.g } })),
    counters: [{ id: 'tested', label: 'tables built' }],
    run(inp) {
      const G = T.PX.G(inp.g), c = T.lr.classify(G), ll = T.ll.ll1Table(G);
      const F = new T.Frames(['tested']);
      const boxes = LEVELS.map((_, i) => ({ x: i * 24, y: i * 46, w: 960 - i * 196, h: 470 - i * 64 }));
      const band = { x: boxes[4].x + 16, y: boxes[4].y + 110, w: boxes[1].x + boxes[1].w - 18 - (boxes[4].x + 16), h: 96 };
      const where = (lvl, isLL, k) => {
        const b = boxes[lvl], strip = lvl === 4 ? b.x + 16 : boxes[lvl + 1].x + boxes[lvl + 1].w + 14;
        return { x: strip + 10, y: isLL ? band.y + 48 + k * 26 : b.y + 44 + k * 26 };
      };
      const ex = EXAMPLES.map((e) => { const g = T.PX.G(e.g), cc = T.lr.classify(g); return Object.assign({}, e, { lvl: levelOf(cc.verdict), ll: T.ll.ll1Table(g).ll1 }); });
      const mine = { lvl: levelOf(c.verdict), ll: ll.ll1 };
      const same = ex.find((e) => e.g.replace(/\s+/g, '') === inp.g.replace(/\s+/g, ''));
      const slots = {};
      const place = (lvl, isLL) => { const k = (slots[lvl + ':' + isLL] = (slots[lvl + ':' + isLL] || 0) + 1) - 1; return where(lvl, isLL, k); };
      const exPos = ex.map((e) => place(e.lvl, e.ll));
      const myPos = same ? exPos[ex.indexOf(same)] : place(mine.lvl, mine.ll);
      const scene = (o) => {
        o = o || {};
        const items = [];
        LEVELS.forEach(([id, label], i) => items.push({ key: 'cl:' + id, kind: 'region', x: boxes[i].x, y: boxes[i].y, w: boxes[i].w, h: boxes[i].h, text: label, cls: 'r' + i + (o.hot === i ? (o.ok ? ' good' : ' bad') : ''), audit: 'group' }));
        items.push({ key: 'cl:ll', kind: 'region', x: band.x, y: band.y, w: band.w, h: band.h, text: 'LL(1)', cls: 'frame' + (o.llHot ? (ll.ll1 ? ' good' : ' bad') : ''), audit: 'group' });
        ex.forEach((e, k) => { const p = exPos[k]; items.push({ key: 'cl:p:' + e.id, kind: 'token', x: p.x, y: p.y - 4, r: 5, cls: same === e && o.mine ? 'good' : 'act', audit: 'overlap-ok' }); items.push({ key: 'cl:t:' + e.id, kind: 'text', x: p.x + 12, y: p.y + 1, text: e.short, cls: 'strong', size: 18 }); });
        if (o.mine && !same) { items.push({ key: 'cl:me', kind: 'token', x: myPos.x, y: myPos.y - 4, r: 8, cls: 'good', pulse: true, audit: 'overlap-ok' }); items.push({ key: 'cl:met', kind: 'text', x: myPos.x + 14, y: myPos.y + 1, text: 'yours', cls: 'strong', size: 18 }); }
        return items;
      };
      F.add({ items: scene({}), say: 'Each box holds the grammars its method can parse without conflicts, and each is inside the next: a stronger method takes everything a weaker one does. The dashed band is LL(1). The dots are example grammars.' });
      LEVELS.slice(1).reverse().forEach(([k, name]) => {
        const i = LEVELS.findIndex((x) => x[0] === k), lv = c.levels[k];
        F.count('tested');
        F.add({ items: scene({ hot: i, ok: lv.ok }), say: (lv.ok ? 'The ' + name + ' table has no conflicts (' + lv.states + ' states).' : 'Not ' + name + ': ' + lv.conflicts[0].say.replace(/; .* wins by default\./, '.')), meta: { level: name, ok: lv.ok } });
      });
      F.count('tested');
      F.add({ items: scene({ llHot: true }), say: ll.ll1 ? 'The LL(1) table has no conflicts either: the grammar is LL(1) too.' : 'Not LL(1): ' + ll.conflicts[0].say, meta: { ll: ll.ll1 } });
      F.add({ items: scene({ mine: true }), say: 'So the grammar sits in ' + (c.verdict ? c.verdict + (mine.lvl === 4 ? '' : ', but not in the classes inside it') : 'none of the LR classes: ' + (T.grammar.ambiguity(G, 6).trace.some((x) => x.kind === 'found') ? 'it is ambiguous, and no ambiguous grammar is LR(k)' : 'it needs more than one symbol of lookahead')) + (ll.ll1 ? ', and inside the LL(1) band.' : ', outside the LL(1) band.'), mark: c.verdict || 'not LR(1)' });
      return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'v', kind: 'table', title: 'The tests', colHead: ['conflicts', 'states'], rowHead: ['LR(0)', 'SLR(1)', 'LALR(1)', 'LR(1)', 'LL(1)'], rows: ['lr0', 'slr', 'lalr', 'lr1'].map((k) => [String(c.levels[k].conflicts.length), String(c.levels[k].states)]).concat([[String(ll.conflicts.length), '–']]) }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['LR(0)', 'SLR(1)', 'LALR(1)', 'LR(1)', 'None of them'], ask: 'What is the smallest class your grammar belongs to?', answer: (fr) => { const m = fr[fr.length - 1].mark; return m === 'not LR(1)' ? 'None of them' : m; }, explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.ll !== undefined, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Is the grammar LL(1)?', answer: (fr, i) => (fr[i + 1].meta.ll ? 'Yes' : 'No'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Is every LR(0) grammar LL(1)?', options: ['Yes', 'No: L → L ; x | x is LR(0) but left-recursive, so not LL(1)', 'Only without ε', 'Only if unambiguous'], answer: 1, why: 'The classes cross: LR methods are happy with left recursion, LL methods are not.' },
      { q: 'Is every LL(1) grammar LR(1)?', options: ['Yes', 'No', 'Only SLR(1) ones', 'Only without ε'], answer: 0, why: 'An LR(1) parser can postpone each decision that LL(1) makes, so it never has less information.' },
      { q: 'Can an ambiguous grammar be LR(1)?', options: ['Yes, with luck', 'No: two trees mean some table cell must hold two actions', 'Only LALR(1)', 'Only with ε'], answer: 1, why: 'A deterministic parser produces one tree; ambiguity always shows up as a conflict (unless precedence settles it by choice).' },
      { q: 'Why is LALR(1) the usual choice in parser generators?', options: ['It takes every grammar', 'Its tables are LR(0)-sized, and it takes nearly every grammar LR(1) takes', 'It is the simplest', 'It needs no lookahead'], answer: 1, why: 'The few LR(1)-but-not-LALR grammars rarely come up in practice.' },
    ],
  });
})();
