// Top-down predictive parsing, part two: running it. The table-driven parser with its stack, the input and
// the table cell it consults at each step while the parse tree grows from the root; the same parser with
// panic-mode error recovery; and the recursive-descent procedures the table turns into, running with a
// call stack.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const L = () => T.PX.LL;

  /** Replay the predictive parser's trace into tree snapshots (paths as ids, so the tree only grows) */
  function replay(G, r) {
    const nodes = new Map([['r', { sym: G.start, kids: null }]]);
    const stack = ['r'];
    const snap = () => { const build = (p) => { const n = nodes.get(p); return { sym: n.sym, prod: n.kids ? 0 : null, children: n.kids ? n.kids.map(build) : null, error: n.error, missing: n.missing, done: n.done, path: p }; }; return build('r'); };
    const out = [];
    for (const st of r.trace) {
      const top = stack[stack.length - 1];
      let focus = top;
      if (st.kind === 'expand') {
        stack.pop();
        const p = G.productions[st.prod], n = nodes.get(top);
        n.kids = p.rhs.map((s, k) => { nodes.set(top + '.' + k, { sym: s, kids: null }); return top + '.' + k; });
        for (let k = n.kids.length - 1; k >= 0; k--) stack.push(n.kids[k]);
      } else if (st.kind === 'match') { nodes.get(top).done = true; stack.pop(); }
      else if (st.kind === 'sync-pop') { const n = nodes.get(top); n.kids = []; n.error = true; stack.pop(); }
      else if (st.kind === 'pop-terminal') { nodes.get(top).missing = true; stack.pop(); }
      else focus = null;
      out.push({ st, tree: snap(), focus });
    }
    return out;
  }
  const treeCls = (G, focus) => (n, path) => [path === focus ? 'hot' : '', n.done ? 'good' : ''].filter(Boolean).join(' ');

  /** The scene for both the plain and the recovering parser */
  function runLL(inp, recover) {
    const G = T.PX.G(inp.g), t = T.ll.ll1Table(G);
    const r = T.ll.predictive(G, inp.w, { recover, table: t });
    const w = r.word, snaps = replay(G, r);
    const F = new T.Frames(recover ? ['steps', 'errors', 'skipped'] : ['steps', 'expanded', 'matched']);
    const final = snaps.length ? snaps[snaps.length - 1].tree : { sym: G.start, children: null };
    const pos = K.tree.layout(T.PX.kitTree(final, { G }), { gapY: 70, gapX: 18 });
    let minX = 0, maxX = 0, maxY = 0;
    for (const p of pos.values()) { minX = Math.min(minX, p.x); maxX = Math.max(maxX, p.x); maxY = Math.max(maxY, p.y); }
    const iy = maxY + 80, cw = 46;
    const toks = w.concat(['$']);
    const ix = -(toks.length * cw) / 2;
    const sx = Math.min(minX - 60, ix - 100) - 130;
    const tx = Math.max(maxX + 60, ix + toks.length * cw + 40);
    const skipped = new Set();
    const scene = (s, o) => {
      o = o || {};
      const items = [];
      if (s) items.push(...K.tree.draw(T.PX.kitTree(s.tree, { G, cls: treeCls(G, s.focus) }), { prefix: 'll', gapY: 70, gapX: 18 }).items);
      const stk = s ? s.st.stack : ['$', G.start];
      items.push(...K.stack.draw({ items: stk.map((x, k) => ({ text: x, cls: k === stk.length - 1 ? 'hot' : '' })), x: sx, y: iy + 44, label: 'stack', prefix: 'lst', max: 9 }).items);
      const at = s ? s.st.pos : 0;
      items.push(...K.string.draw({ text: toks, pos: o.end ? null : at, x: ix, y: iy, cw, prefix: 'lin', label: 'input', cls: (i) => [i === toks.length - 1 ? 'endmark' : '', skipped.has(i) ? 'gone' : ''].filter(Boolean).join(' ') }).items);
      const tb = T.PX.llTable(G, t, t.table, { x: tx, y: 0, hot: o.cell });
      items.push(...tb.items);
      if (o.sync) items.push(...T.PX.panel({ prefix: 'syn', x: tx, y: tb.box.h + 24, w: Math.max(260, tb.box.w), title: 'Synchronising set of ' + o.sync.A, rows: [{ id: 's', text: 'FOLLOW(' + o.sync.A + ') = ' + T.PX.set(T.PX.sortSet(t.follow.get(o.sync.A))), cls: o.sync.hit ? 'good' : 'bad' }], rowH: 32, size: 15 }).items);
      return items;
    };
    F.add({ items: scene(null), say: 'The stack starts as $ ' + G.start + ' (start symbol on top) and the input is ' + T.PX.show(w) + ' followed by $. At every step the top of the stack and the next input symbol decide what happens.' + (t.ll1 ? '' : ' The table has a conflict; the parser takes the first rule in a clashing cell.') });
    for (const s of snaps) {
      const st = s.st;
      if (st.kind === 'accept') continue;
      F.count('steps');
      const a = st.input[0], top = st.stack[st.stack.length - 1];
      let o = {};
      if (st.kind === 'expand') { o.cell = [G.nonterminals.indexOf(top), t.terminals.indexOf(a)]; if (!recover) F.count('expanded'); }
      if (st.kind === 'match' && !recover) F.count('matched');
      if (st.kind === 'skip') { skipped.add(st.pos); F.count('skipped'); F.count('errors'); if (T.grammar.isN(G, top)) o.sync = { A: top, hit: false }; }
      if (st.kind === 'sync-pop') { F.count('errors'); o.sync = { A: top, hit: true }; }
      if (st.kind === 'pop-terminal') F.count('errors');
      if (st.kind === 'error') { F.count('errors'); o.cell = T.grammar.isN(G, top) ? [G.nonterminals.indexOf(top), t.terminals.indexOf(a)] : undefined; }
      F.add({ items: scene(s, o), say: st.say, hl: { g: st.prod !== undefined ? [st.prod] : [] }, mark: st.kind === 'error' ? 'error' : undefined, meta: { kind: st.kind, cell: o.cell ? 'lt:' + o.cell[0] + ',' + o.cell[1] : null, err: /skip|sync-pop|pop-terminal|error/.test(st.kind) } });
    }
    const last = r.trace[r.trace.length - 1];
    const fs = snaps.length ? snaps[snaps.length - 1] : null;
    F.add({ items: scene(fs ? { st: last, tree: fs.tree, focus: null } : null, { end: true }), say: last.kind === 'accept' ? last.say + (r.accepted ? ' The tree is complete; read its leaves left to right and you get ' + T.PX.show(w) + '.' : ' The tree has red nodes where the parser repaired the input; a compiler would report the errors and carry on checking the rest.') : 'The parse stopped at the error: ' + T.PX.show(w) + ' is not in the language.', mark: r.accepted ? 'accepted' : 'rejected', meta: { yes: r.accepted, errors: r.errors.length } });
    return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'tb', kind: 'table', title: 'The LL(1) table', corner: 'M', colHead: t.terminals, rowHead: G.nonterminals, rows: G.nonterminals.map((A) => t.terminals.map((a) => ((t.table[A] || {})[a] || []).map((id) => T.grammar.showRhs(G, G.productions[id].rhs)).join(' / '))) }, { id: 'how', kind: 'text', title: recover ? 'Panic mode' : 'The parser', text: recover ? 'An empty cell M[A, a]: if a is in A\'s synchronising set (here FOLLOW(A)) pop A, as if it had derived what is missing; otherwise skip a. A terminal on top that does not match is popped, as if it had been there.' : 'Top is a terminal: it must match the next input symbol; pop it and move on. Top is a nonterminal A: replace it by the right side of M[A, a], pushed right to left so its first symbol is on top. Both at $: accept. An empty cell or a mismatch: error.' }] } };
  }

  T.topic({
    id: 'll1-parse', family: 'll1', order: 30, title: 'The predictive parse',
    blurb: 'A stack of what is still expected, the next input symbol, and the table: expand the nonterminal on top by the rule its cell names, or match the terminal on top. The parse tree grows from the root down.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', check: (v) => T.PX.LL.checkG(v) },
      { id: 'w', kind: 'string', label: 'Input', def: '[x;x]', max: 8 },
    ],
    presets: [
      { label: 'A list: [x;x]', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;x]' } },
      { label: 'The empty list: []', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[]' } },
      { label: 'Rejected early: [x;]', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;]' } },
      { label: 'Sums: (n+n)+n', values: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: '(n+n)+n' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 8)(inp),
    counters: [{ id: 'steps', label: 'steps' }, { id: 'expanded', label: 'expansions' }, { id: 'matched', label: 'matches' }],
    run: (inp) => runLL(inp, false),
    predict: [
      { at: (f, i, fr) => i >= 1 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'expand' && fr[i + 1].meta.cell, once: true, pick: 'item', ask: 'A nonterminal is on top of the stack. Click the table cell the parser will use.', answer: (fr, i) => fr[i + 1].meta.cell, explain: (fr, i) => 'Row: the nonterminal on top; column: the next input symbol. ' + fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the parse succeed?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why are a rule\'s symbols pushed right to left?', options: ['To save space', 'So the leftmost symbol is on top and is dealt with first', 'Because the input is read right to left', 'It does not matter'], answer: 1, why: 'The parser builds a leftmost derivation: the leftmost symbol must be expanded or matched first.' },
      { q: 'The top of the stack is the terminal ; and the next input symbol is ]. What happens?', options: ['Pop ;', 'Expand', 'An error: they do not match', 'Accept'], answer: 2, why: 'A terminal on top must equal the next input symbol.' },
      { q: 'Which derivation does the predictive parser trace?', options: ['Rightmost', 'Leftmost', 'Rightmost in reverse', 'None'], answer: 1, why: 'It always expands the leftmost unexpanded nonterminal: the one on top of the stack.' },
      { q: 'How does the parser use A → ε?', options: ['It pushes ε', 'It pops A and pushes nothing', 'It skips an input symbol', 'It cannot'], answer: 1, why: 'The right side is empty, so A just disappears from the stack.' },
      { q: 'How many steps does an LL(1) parse take, roughly?', options: ['Exponentially many', 'Proportional to the input length (for a grammar without ε-cycles)', 'Quadratic', 'One per rule'], answer: 1, why: 'Each step either matches a symbol or expands a nonterminal that leads to a match soon after.' },
    ],
  });

  T.topic({
    id: 'll1-panic', family: 'll1', order: 40, title: 'Panic mode: recovering from errors',
    blurb: 'A real parser does not stop at the first error. In panic mode it skips input symbols until one it can synchronise on, or pops the nonterminal it was expanding, then carries on to find more errors.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: 'E → T P\nP → + T P | ε\nT → ( E ) | n', check: (v) => T.PX.LL.checkG(v) },
      { id: 'w', kind: 'string', label: 'Input with errors', def: 'n+)n', max: 8 },
    ],
    presets: [
      { label: 'A stray symbol: n+)n', values: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: 'n+)n' } },
      { label: 'Missing operand: (n+)', values: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: '(n+)' } },
      { label: 'Unclosed: (n+n', values: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: '(n+n' } },
      { label: 'A list with junk: [x;;x]', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;;x]' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 8)(inp),
    counters: [{ id: 'steps', label: 'steps' }, { id: 'errors', label: 'errors met' }, { id: 'skipped', label: 'symbols skipped' }],
    run: (inp) => runLL(inp, true),
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.err, once: true, pick: 'option', options: ['Skip the input symbol', 'Pop the top of the stack', 'Stop the parse'], ask: 'The next step meets an error. What will panic mode do?', answer: (fr, i) => (fr[i + 1].meta.kind === 'skip' ? 'Skip the input symbol' : 'Pop the top of the stack'), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['0', '1', '2', '3 or more'], ask: 'How many errors will the parser have met by the end?', answer: (fr) => { const n = fr[fr.length - 1].counters.errors; return n >= 3 ? '3 or more' : String(n); }, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What is a synchronising set for A in panic mode?', options: ['FIRST(A)', 'Symbols that can safely follow A, such as FOLLOW(A)', 'All terminals', 'The rules of A'], answer: 1, why: 'Seeing one of them means A can be given up on and parsing can continue after it.' },
      { q: 'Why skip input symbols instead of stopping?', options: ['To accept the input anyway', 'To report several errors in one run', 'To make the parse faster', 'To fix the grammar'], answer: 1, why: 'A compiler that stopped at the first error would make you recompile once per mistake.' },
      { q: 'With recovery, does a repaired input count as accepted?', options: ['Yes', 'No: it is still rejected; recovery only lets the parser keep looking', 'Only with one error', 'Only if no symbol was skipped'], answer: 1, why: 'The input is not in the language; the parser just reports more about it.' },
      { q: 'A terminal on top does not match the input. What does panic mode do with it?', options: ['Skip the input', 'Pop the terminal, as if it had been there', 'Push it again', 'Stop'], answer: 1, why: 'Assume it was missing: report it and continue with the rest of the stack.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  // The procedures a table becomes: one per nonterminal, a case for each rule chosen by the next symbol
  function procedures(G, t) {
    const lines = [];
    for (const A of G.nonterminals) {
      lines.push({ id: A + ':h', text: A + '():', A });
      const row = t.table[A] || {};
      const byProd = new Map();
      for (const a of t.terminals) if (row[a]) { const id = row[a][0]; if (!byProd.has(id)) byProd.set(id, []); byProd.get(id).push(a); }
      for (const [id, terms] of byProd) {
        const p = G.productions[id];
        const body = p.rhs.length ? p.rhs.map((s) => (T.grammar.isN(G, s) ? s + '()' : "match '" + s + "'")).join('; ') : 'return';
        lines.push({ id: A + ':p' + id, text: '  on ' + terms.join(' ') + ':  ' + body, A, prod: id });
      }
      lines.push({ id: A + ':e', text: '  else: error', A });
    }
    return lines;
  }

  T.topic({
    id: 'rd-codegen', family: 'll1', order: 50, title: 'Recursive descent, generated and running',
    blurb: 'Each nonterminal becomes a procedure; the LL(1) table row becomes a choice on the next symbol. Calling the start procedure parses the input, and the call stack is the path from the root of the parse tree.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar (LL(1))', def: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', check: (v) => T.PX.LL.checkG(v) || (T.ll.ll1Table(T.PX.G(v)).ll1 ? null : 'Grammar: it is not LL(1), so the procedures could not choose a rule from one symbol') },
      { id: 'w', kind: 'string', label: 'Input', def: '[x;x]', max: 8 },
    ],
    presets: [
      { label: 'A list: [x;x]', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[x;x]' } },
      { label: 'Nested sums: (n)+n', values: { g: 'E → T P\nP → + T P | ε\nT → ( E ) | n', w: '(n)+n' } },
      { label: 'An error: [x x]', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[xx]' } },
      { label: 'Extra input: [ ] ]', values: { g: 'L → [ A ]\nA → x R | ε\nR → ; x R | ε', w: '[]]' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 8)(inp),
    counters: [{ id: 'calls', label: 'calls' }, { id: 'matches', label: 'matches' }, { id: 'depth', label: 'deepest stack' }],
    run(inp) {
      const G = T.PX.G(inp.g), t = T.ll.ll1Table(G), w = T.PX.word(G, inp.w), toks = w.concat(['$']);
      const lines = procedures(G, t), F = new T.Frames(['calls', 'matches', 'depth']);
      const calls = [];
      let pos = 0, failed = null;
      const cw = 46, codeW = Math.max(300, ...lines.map((l) => T.geom.textWidth(l.text, 15, { mono: true }) + 30));
      const scene = (lit, o) => {
        o = o || {};
        const code = T.PX.panel({ prefix: 'cg', x: 200, y: 0, w: codeW, title: 'Generated procedures', rows: lines.map((l) => ({ id: l.id, text: l.text, cls: l.id === lit ? (o.bad ? 'bad' : 'hot') : l.text.endsWith(':') && !l.text.startsWith(' ') ? 'kernel' : '' })), rowH: 28, size: 15 });
        const cs = T.PX.panel({ prefix: 'cs', x: 0, y: 0, w: 170, title: 'Call stack', rows: calls.slice().reverse().map((c, k) => ({ id: c.id, text: c.A + '()', cls: k === 0 ? 'act' : '' })), rowH: 34, size: 16, minH: 260 });
        const s = K.string.draw({ text: toks, pos: o.end ? null : pos, x: 200, y: code.box.h + 30, cw, prefix: 'cgin', label: 'input', cls: (i) => (i === toks.length - 1 ? 'endmark' : '') });
        return code.items.concat(cs.items, s.items);
      };
      let seq = 0;
      const go = (A) => {
        calls.push({ A, id: 'k' + seq++ });
        F.count('calls').set('depth', Math.max(F.counts.depth, calls.length));
        const a = toks[pos], ids = (t.table[A] || {})[a];
        F.add({ items: scene(A + ':h'), say: 'Call ' + A + '(). The next input symbol is ' + a + '.', meta: { kind: 'call', A } });
        if (!ids) { failed = A + ':e'; F.add({ items: scene(A + ':e', { bad: true }), say: A + '() has no case for ' + a + ' (M[' + A + ', ' + a + '] is empty): report "expected ' + t.terminals.filter((b) => (t.table[A] || {})[b]).join(' or ') + '" and stop.', mark: 'error', meta: { kind: 'error' } }); return false; }
        const p = G.productions[ids[0]], lid = A + ':p' + p.id;
        F.add({ items: scene(lid), say: 'On ' + a + ', ' + A + '() takes the case for ' + T.grammar.showProd(G, p) + (p.rhs.length ? '.' : ': nothing to do, it returns at once.'), hl: { g: [p.id] }, meta: { kind: 'choose', line: lid } });
        for (const s of p.rhs) {
          if (T.grammar.isN(G, s)) { if (!go(s)) return false; F.add({ items: scene(lid), say: 'Back in ' + A + '(), after ' + s + '() returned.', hl: { g: [p.id] } }); continue; }
          if (toks[pos] !== s) { failed = lid; F.add({ items: scene(lid, { bad: true }), say: "match '" + s + "' fails: the next symbol is " + toks[pos] + '. Report it and stop.', mark: 'error', meta: { kind: 'error' } }); return false; }
          pos++; F.count('matches');
          F.add({ items: scene(lid), say: "match '" + s + "': it is the next symbol, so move past it.", hl: { g: [p.id] }, meta: { kind: 'match' } });
        }
        calls.pop();
        return true;
      };
      F.add({ items: scene(null), say: 'One procedure per nonterminal, written from the rows of the LL(1) table: each looks at the next symbol and runs the matching rule. Parsing ' + T.PX.show(w) + ' is just a call to ' + G.start + '().' });
      const ok = go(G.start);
      if (ok && toks[pos] === '$') F.add({ items: scene(null, { end: true }), say: G.start + '() returned and the next symbol is $: the whole input was parsed. Accept.', mark: 'accepted', meta: { yes: true } });
      else if (ok) F.add({ items: scene(null), say: G.start + '() returned, but ' + toks[pos] + ' is still unread: extra input. Reject.', mark: 'rejected', meta: { yes: false } });
      else F.add({ items: scene(failed, { bad: true }), say: 'The parse stopped with ' + calls.map((c) => c.A + '()').join(' → ') + ' on the call stack: ' + T.PX.show(w) + ' is not in the language.', mark: 'rejected', meta: { yes: false } });
      const js = T.ll.codegen(G);
      return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'js', kind: 'math', title: 'The same procedures in JavaScript', text: js.code }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'choose' && i > 2, once: true, pick: 'item', ask: 'Which line of the procedure will run next? Click it.', answer: (fr, i) => 'cg:r:' + fr[i + 1].meta.line, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the parse succeed?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What does the call stack of a recursive-descent parser correspond to?', options: ['The input read so far', 'The path from the root of the parse tree to the node being parsed', 'The LL(1) table', 'The tokens'], answer: 1, why: 'Each active call is a nonterminal whose subtree is being built.' },
      { q: 'Where does the case list of a procedure come from?', options: ['From the row of its nonterminal in the LL(1) table', 'From FOLLOW of the start symbol', 'From the input', 'It is written by hand'], answer: 0, why: 'For each terminal, the cell names the rule to run.' },
      { q: 'What does the case for A → ε do?', options: ['Matches ε', 'Returns without reading anything', 'Calls A again', 'Reports an error'], answer: 1, why: 'The rule produces nothing, so the procedure just returns.' },
      { q: 'Why would a left-recursive rule make A() never return?', options: ['It would call A() first, at the same input position, forever', 'It would match too much', 'It would skip input', 'It returns at once'], answer: 0, why: 'Nothing is read before the recursive call, so each call makes the same call again.' },
    ],
  });
})();
