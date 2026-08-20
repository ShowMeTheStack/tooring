// The LR family, part one: items and tables. The LR(0) automaton is built state by state, each new state's
// card filling with its kernel and then its closure; the same with LR(1) items and their lookaheads; the
// LR(0) and SLR(1) tables are filled row by row with the item behind every entry, and the conflicts are
// shown with the items that clash; LALR(1) merges LR(1) states with equal cores, and the state count drops.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'lr-items', part: 'parsing', order: 45, title: 'LR items, automata and tables', blurb: 'Items mark how much of a rule has been seen. Sets of items become the states of an automaton, and the automaton becomes the ACTION and GOTO tables of a shift-reduce parser.' });

  // our own grammars
  const PLUS = 'E → E + T | T\nT → x | ( E )';
  const TIMES = 'E → E + T | T\nT → T * x | x';
  const TWOC = 'S → c | A A\nA → B\nB → c';
  const SPLIT = 'S → a X b | c Y b | a Y d | c X d\nX → e\nY → e';
  const AMBIG = 'E → E + E | n';
  const OPTL = 'L → x L | ε';
  const checkG = (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 4, extra: (G) => (T.lr.lr0Collection(G).states.length > 14 ? 'Grammar: its LR(0) automaton has more than 14 states, too many to draw readably' : null) })(v);
  const LR = (T.PX.LR = { PLUS, TIMES, TWOC, SPLIT, AMBIG, OPTL, checkG });

  /** The automaton of a collection as a machine for the graph kit, laid out once */
  LR.machine = (coll) => {
    const states = coll.states.map((s) => String(s.id)), trans = [];
    for (const s of coll.states) for (const [X, t] of Object.entries(s.trans)) trans.push({ from: String(s.id), to: String(t), label: X });
    const accept = coll.states.filter((s) => s.items.some((it) => it.p === 0 && it.d === 1)).map((s) => String(s.id));
    return { kind: 'dfa', states, start: '0', accept, trans };
  };
  LR.layout = (m) => K.graph.layout(m, { gapX: 120, gapY: 96 }).pos;
  /** Only the states and transitions shown so far */
  LR.sub = (m, states, trans) => ({ kind: 'dfa', states: m.states.filter((q) => states.has(q)), start: '0', accept: m.accept.filter((q) => states.has(q)), trans: m.trans.filter((t) => trans.has(t.from + '>' + t.label)) });
  LR.box = (pos, m) => { const xs = m.states.map((q) => pos[q].x), ys = m.states.map((q) => pos[q].y); return { x: Math.min(...xs) - 40, y: Math.min(...ys) - 40, w: Math.max(...xs) - Math.min(...xs) + 80, h: Math.max(...ys) - Math.min(...ys) + 80 }; };
  const core = (aug, it) => T.lr.itemText(aug, { p: it.p, d: it.d });
  /** An item set as a card: kernel items shaded, lookaheads in a tag column */
  LR.card = (aug, items, opts) => {
    opts = opts || {};
    const rows = items.map((it) => ({ id: it.p + '.' + it.d, text: core(aug, it), tag: it.la ? [].concat(it.la).join(' ') : undefined, cls: [opts.kernel && opts.kernel(it) ? 'kernel' : '', opts.cls ? opts.cls(it) || '' : ''].filter(Boolean).join(' ') }));
    return T.PX.panel({ prefix: opts.prefix || 'card', x: opts.x, y: opts.y, title: opts.title, rows, rowH: 32, size: 16, w: opts.w, minH: opts.minH });
  };
  LR.cardW = (aug, coll, la) => Math.max(240, ...coll.states.flatMap((s) => s.items.map((it) => T.geom.textWidth(core(aug, it), 16, { mono: true }) + 40 + (la && it.la ? T.geom.textWidth(it.la.join(' '), 13, { mono: true }) + 22 : 0))));
  LR.cardH = (coll) => 30 + Math.max(...coll.states.map((s) => s.items.length)) * 36 + 8;
  LR.def = (G, extra) => ({ sections: [T.PX.gdef(T.lr.augment(G), { title: 'Augmented grammar (rule numbers)', numbered: true })].concat(extra || []) });

  // ---------------------------------------------------------------------------------------------------------------
  /** The automaton being built, state by state, for LR(0) or LR(1) items */
  function buildRun(inp, lr1) {
    const G = T.PX.G(inp.g), coll = lr1 ? T.lr.lr1Collection(G) : T.lr.lr0Collection(G), aug = coll.aug;
    const m = LR.machine(coll), pos = LR.layout(m), bx = LR.box(pos, m);
    const cw = LR.cardW(aug, coll, lr1), ch = LR.cardH(coll), cx = bx.x + bx.w + 50, cy = bx.y;
    const F = new T.Frames(['states', 'items', 'edges']);
    const shown = new Set(), edges = new Set(), cardOf = new Map();
    const scene = (o) => {
      const g = K.graph.draw(LR.sub(m, shown, edges), { pos, prefix: 'au', hot: o.state !== undefined ? [String(o.state)] : [], active: o.to !== undefined ? [String(o.to)] : [], taken: o.edge ? [o.edge] : [] });
      const items = g.items;
      if (o.state !== undefined) items.push(...LR.card(aug, cardOf.get(o.state) || [], { x: cx, y: cy, w: cw, minH: ch, title: 'State ' + o.state, kernel: (it) => it.kernel, cls: (it) => (o.hotItem && it.p === o.hotItem.p && it.d === o.hotItem.d ? 'hot' : o.from && it.p === o.from.p && it.d === o.from.d ? 'act' : o.sym && aug.productions[it.p].rhs[it.d] === o.sym ? 'act' : '') }).items);
      return items;
    };
    const say0 = lr1 ? 'Add a new start rule ' + aug.productions[0].A + ' → ' + G.start + ' so that accepting is a single reduction. The first state starts from [' + core(aug, { p: 0, d: 0 }) + ', $]: nothing seen yet, and only $ may follow.' : 'Add a new start rule ' + aug.productions[0].A + ' → ' + G.start + ' so that accepting is a single reduction. The first state starts from the item ' + core(aug, { p: 0, d: 0 }) + ': nothing of it has been seen yet.';
    F.add({ items: T.PX.panel({ prefix: 'card', x: cx, y: cy, w: cw, minH: ch, title: 'Augmented grammar', rows: aug.productions.map((p) => ({ id: 'g' + p.id, text: T.grammar.showProd(aug, p), cls: p.id === 0 ? 'hot' : '' })), rowH: 32, size: 16 }).items, say: say0 });
    for (const st of coll.trace) {
      if (st.kind === 'state') {
        shown.add(String(st.state)); F.count('states');
        cardOf.set(st.state, st.kernel.map((it) => Object.assign({ kernel: true }, it, lr1 ? { la: [].concat(it.la) } : {})));
        F.count('items', st.kernel.length);
        F.add({ items: scene({ state: st.state }), say: st.say + ' Its kernel: ' + st.kernel.map((it) => (lr1 ? '[' + core(aug, it) + ', ' + [].concat(it.la).join('/') + ']' : core(aug, it))).join(', ') + '.', meta: { kind: 'state', state: st.state } });
      } else if (st.kind === 'closure') {
        const list = cardOf.get(st.state);
        let it = list.find((x) => x.p === st.item.p && x.d === st.item.d);
        if (it && lr1) it.la = [...new Set(it.la.concat([st.item.la]))];
        else if (!it) { it = Object.assign({}, st.item, lr1 ? { la: [st.item.la] } : {}); list.push(it); F.count('items'); }
        F.add({ items: scene({ state: st.state, hotItem: st.item, from: st.from }), say: st.say, hl: { g: [st.item.p] }, meta: { kind: 'closure', state: st.state, from: st.from } });
      } else if (st.kind === 'transition') {
        edges.add(st.from + '>' + st.symbol); F.count('edges');
        F.add({ items: scene({ state: st.from, to: st.to, sym: st.symbol, edge: st.from + '>' + st.to }), say: st.say + ' Moving the dot over ' + st.symbol + ' in every item of state ' + st.from + ' that has it next gives ' + (st.existing ? 'a kernel that is already a state.' : 'a new kernel.'), meta: { kind: 'transition', from: st.from, to: st.to, existing: st.existing } });
      }
    }
    F.add({ items: K.graph.draw(m, { pos, prefix: 'au', good: m.accept }).items, say: 'The automaton is complete: ' + coll.states.length + ' states. ' + (lr1 ? 'With lookaheads, states with the same items can still differ in what may follow, so LR(1) can have more states than LR(0) (here ' + T.lr.lr0Collection(G).states.length + ').' : 'The state reached on ' + G.start + ' from state 0 holds ' + core(aug, { p: 0, d: 1 }) + ': reaching it at the end of the input means accept.'), mark: 'done' });
    return { frames: F.list, def: LR.def(G, [{ id: 'cl', kind: 'text', title: lr1 ? 'Closure with lookaheads' : 'Closure and goto', text: lr1 ? 'For [A → α • B β, a] add [B → • γ, b] for every rule B → γ and every b in FIRST(β a). goto(I, X) moves the dot over X, keeping each item\'s lookahead.' : 'Closure: for an item A → α • B β, add B → • γ for every rule of B, and repeat. goto(I, X): move the dot over X in every item of I that has X next, then take the closure.' }]) };
  }

  const itemQuiz = [
    { q: 'What does the item E → E + • T say?', options: ['E + T has been reduced', 'E + has been seen; a T is expected next', 'T has been seen', 'The parser must shift +'], answer: 1, why: 'Everything left of the dot has been recognised on the stack; the symbols right of it are still to come.' },
    { q: 'Why does closure add T → • x when an item has • T?', options: ['To accept early', 'Because a T is expected, so anything that begins a T may come next', 'To remove conflicts', 'Because x is a terminal'], answer: 1, why: 'Expecting T means expecting the start of any right side of T.' },
    { q: 'What is a kernel item?', options: ['Any item in state 0', 'The start item, or an item whose dot is not at the left end', 'An item with the dot at the end', 'An item added by closure'], answer: 1, why: 'Kernels come from goto; the rest of a state is their closure.' },
    { q: 'goto(I, X) leads to a kernel that already exists. What happens?', options: ['A copy is made', 'The edge points to the existing state', 'The construction stops', 'The grammar is ambiguous'], answer: 1, why: 'States are identified by their kernels, which is why the collection is finite.' },
  ];

  T.topic({
    id: 'lr0-items', family: 'lr-items', order: 10, title: 'LR(0) items: closure and goto',
    blurb: 'An item is a rule with a dot: how much of it has been seen. Each state of the automaton is a set of items, closed under "a dot before B means B may start here", and goto moves the dot over a symbol.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: PLUS, check: checkG }],
    presets: [
      { label: 'Sums with brackets', values: { g: PLUS } },
      { label: 'Lists: L → x L | ε', values: { g: OPTL } },
      { label: 'Sums and products', values: { g: TIMES } },
      { label: 'Ambiguous: E → E + E | n', values: { g: AMBIG } },
    ],
    counters: [{ id: 'states', label: 'states' }, { id: 'items', label: 'items' }, { id: 'edges', label: 'transitions' }],
    run: (inp) => buildRun(inp, false),
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'closure' && fr[i].meta && fr[i].meta.kind === 'state' && fr[i].meta.state === 0, once: true, pick: 'item', ask: 'Closure is about to add items to state 0. Click the item whose dot causes the next one.', answer: (fr, i) => { const f = fr[i + 1].meta.from; return 'card:r:' + f.p + '.' + f.d; }, explain: (fr, i) => 'A dot right before a nonterminal B calls for B\'s rules. ' + fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'transition' && fr[i + 1].meta.existing, once: true, pick: 'item', ask: 'The next goto leads to a kernel that already exists. Click the state it goes to.', answer: (fr, i) => 'au:s:' + fr[i + 1].meta.to, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: itemQuiz,
  });

  T.topic({
    id: 'lr1-items', family: 'lr-items', order: 20, title: 'LR(1) items: lookaheads',
    blurb: 'An LR(1) item carries the terminal that may follow once its rule is reduced. Closure works the lookaheads out from FIRST of what comes after; states that agree on items but not on lookaheads stay apart.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: TWOC, check: checkG }],
    presets: [
      { label: 'S → c | A A: lookaheads tell c apart', values: { g: TWOC } },
      { label: 'Lists: L → x L | ε', values: { g: OPTL } },
      { label: 'Sums and products', values: { g: TIMES } },
    ],
    counters: [{ id: 'states', label: 'states' }, { id: 'items', label: 'items' }, { id: 'edges', label: 'transitions' }],
    run: (inp) => buildRun(inp, true),
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'closure' && i > 0, once: true, pick: 'item', ask: 'The next closure item will get its lookahead from FIRST of what follows a dot. Click the item it comes from.', answer: (fr, i) => { const f = fr[i + 1].meta.from; return 'card:r:' + f.p + '.' + f.d; }, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Fewer than LR(0)', 'The same as LR(0)', 'At least as many as LR(0)'], ask: 'How does the number of LR(1) states compare with LR(0)?', answer: () => 'At least as many as LR(0)', explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: '[A → α • B β, a]. Which lookaheads do the new B-items get?', options: ['a only', 'FIRST(β a)', 'FOLLOW(B)', 'FIRST(B)'], answer: 1, why: 'After B comes β and then a; if β can vanish, a itself.' },
      { q: 'When does [A → γ •, a] call for a reduction?', options: ['On any terminal', 'Only when the next input symbol is a', 'On FOLLOW(A)', 'Never'], answer: 1, why: 'The lookahead says exactly which next symbol makes the reduction right.' },
      { q: 'Why can LR(1) have more states than LR(0)?', options: ['It has more rules', 'Two states with the same items but different lookaheads are kept apart', 'It adds ε-rules', 'It does not'], answer: 1, why: 'The lookaheads are part of the state.' },
      { q: 'What is the lookahead of the very first item?', options: ['ε', '$', 'FIRST of the start symbol', 'Anything'], answer: 1, why: 'After a whole sentence comes the end of the input.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  /** The ACTION and GOTO table, filled as the core builds it, beside the card of the state being done */
  function tableRun(inp, kind) {
    const G = T.PX.G(inp.g), tb = T.lr.buildTable(G, kind, { precedence: false }), aug = tb.aug;
    const coll = kind === 'lr0' || kind === 'slr' ? T.lr.lr0Collection(G) : T.lr.lr1Collection(G);
    const cols = tb.terminals.concat(tb.nonterminals), nT = tb.terminals.length;
    const cells = tb.states.map(() => ({}));
    const F = new T.Frames(['entries', 'conflicts']);
    const cw = LR.cardW(aug, coll, false), ch = LR.cardH(coll);
    const fol = (A) => T.ll.firstFollow(G).follow.get(A);
    const put = (s, a, txt) => { const c = (cells[s][a] = cells[s][a] || []); if (!c.includes(txt)) c.push(txt); };
    const table = (o) => K.table.draw({ prefix: 'at', rows: tb.states.map((s) => cols.map((a) => (cells[s.id][a] || []).join(' / '))), rowHead: tb.states.map((s) => String(s.id)), colHead: cols, corner: 'state', x: 0, y: 0, mono: true, size: 15, minW: 48, hot: o.hot || [], cls: (r, c) => ((cells[r][cols[c]] || []).length > 1 ? 'bad' : c >= nT ? 'mark' : '') });
    // measure the finished table first, so the card beside it never moves
    for (const st of tb.trace) { if (st.kind === 'goto') put(st.state, st.symbol, String(st.to)); else if (st.kind === 'shift') put(st.state, st.symbol, 's' + st.to); else if (st.kind === 'accept') put(st.state, '$', 'acc'); else if (st.kind === 'reduce') for (const a of st.on) put(st.state, a, 'r' + st.prod); }
    const cx = table({}).box.w + 50;
    for (const c of cells) for (const k of Object.keys(c)) delete c[k];
    const scene = (o) => {
      o = o || {};
      const items = table(o).items;
      if (o.state !== undefined) items.push(...LR.card(aug, coll.states[o.state].items, { x: cx, y: 0, w: cw, minH: ch, title: 'State ' + o.state, kernel: (it) => coll.states[o.state].kernel.some((k) => k.p === it.p && k.d === it.d), cls: (it) => (o.items && o.items.some((x) => x.p === it.p && x.d === it.d) ? (o.bad ? 'bad' : 'hot') : '') }).items);
      if (o.note) items.push(...T.PX.panel({ prefix: 'nt', x: cx, y: ch + 20, w: cw, rows: o.note.map((t, k) => ({ id: 'n' + k, text: t, cls: k === o.note.length - 1 ? 'act' : '' })), rowH: 30, size: 14, mono: false }).items);
      return items;
    };
    const ci = (a) => cols.indexOf(a);
    F.add({ items: scene({}), say: 'One row per state of the ' + (kind === 'slr' ? 'LR(0)' : kind.toUpperCase()) + ' automaton. ACTION columns: the terminals and $ (shift sN, reduce rN by rule N, accept); GOTO columns: the nonterminals (the state after a reduction).' + (kind === 'slr' ? ' SLR(1) uses the LR(0) automaton but reduces only on FOLLOW of the rule\'s left side.' : ' LR(0) looks at no input before reducing: a complete item reduces on every column.') });
    for (const st of tb.trace) {
      if (st.kind === 'goto') { put(st.state, st.symbol, String(st.to)); F.count('entries'); F.add({ items: scene({ state: st.state, hot: [[st.state, ci(st.symbol)]], items: coll.states[st.state].items.filter((it) => aug.productions[it.p].rhs[it.d] === st.symbol) }), say: st.say + ' After reducing to ' + st.symbol + ' with state ' + st.state + ' exposed, the parser goes to state ' + st.to + '.', meta: { kind: 'goto' } }); }
      else if (st.kind === 'shift') { put(st.state, st.symbol, 's' + st.to); F.count('entries'); F.add({ items: scene({ state: st.state, hot: [[st.state, ci(st.symbol)]], items: [st.item] }), say: st.say, meta: { kind: 'shift' } }); }
      else if (st.kind === 'accept') { put(st.state, '$', 'acc'); F.count('entries'); F.add({ items: scene({ state: st.state, hot: [[st.state, ci('$')]], items: [st.item] }), say: st.say, meta: { kind: 'accept' } }); }
      else if (st.kind === 'reduce') {
        for (const a of st.on) put(st.state, a, 'r' + st.prod);
        F.count('entries', st.on.length);
        const q = aug.productions[st.prod];
        F.add({ items: scene({ state: st.state, hot: st.on.map((a) => [st.state, ci(a)]), items: [st.item], note: kind === 'slr' ? ['FOLLOW(' + q.A + ') = ' + T.PX.set(T.PX.sortSet(fol(q.A))), 'so r' + st.prod + ' goes only under those'] : ['LR(0): a complete item', 'reduces on every column'] }), say: st.say, hl: { g: [st.prod] }, meta: { kind: 'reduce', state: st.state, cells: st.on.map((a) => 'at:' + st.state + ',' + ci(a)) } });
      }
    }
    for (const c of tb.conflicts) {
      F.count('conflicts');
      F.add({ items: scene({ state: c.state, hot: [[c.state, ci(c.symbol)]], items: c.items.map((x) => x.item), bad: true, note: [c.type + ' conflict on ' + c.symbol] }), say: c.type.charAt(0).toUpperCase() + c.type.slice(1) + ' conflict. ' + c.say.replace(/; .* wins by default\./, '.') + ' The clashing items are lit in the card.', mark: 'conflict', meta: { kind: 'conflict' } });
    }
    const ok = !tb.conflicts.length;
    const lr0c = kind === 'slr' ? T.lr.buildTable(G, 'lr0', { precedence: false }).conflicts.length : 0;
    F.add({ items: scene({}), say: ok ? 'No cell holds two actions: the grammar is ' + (kind === 'slr' ? 'SLR(1)' : 'LR(0)') + '.' + (kind === 'slr' && lr0c ? ' Its LR(0) table had ' + lr0c + ' conflict' + (lr0c > 1 ? 's' : '') + '; FOLLOW sets removed them.' : '') : tb.conflicts.length + ' cell' + (tb.conflicts.length > 1 ? 's hold' : ' holds') + ' two actions: the grammar is not ' + (kind === 'slr' ? 'SLR(1)' : 'LR(0)') + '.' + (kind === 'lr0' ? ' Looking at the next symbol (SLR, LALR, LR(1)) may settle it.' : ' FOLLOW is too coarse here: LALR(1) or LR(1) lookaheads may settle it.'), mark: ok ? kind.toUpperCase() : 'conflict', meta: { ok } });
    const extra = [{ id: 'act', kind: 'text', title: 'Reading the table', text: 'sN: shift the input symbol and go to state N. rN: reduce by rule N (numbers in the augmented grammar). acc: accept. A GOTO entry N: after reducing to that nonterminal from this state, go to state N.' }];
    if (kind === 'slr') extra.push({ id: 'fo', kind: 'table', title: 'FOLLOW sets', colHead: ['FOLLOW'], rowHead: G.nonterminals, rows: G.nonterminals.map((A) => [T.PX.set(T.PX.sortSet(fol(A)))]) });
    return { frames: F.list, def: LR.def(G, extra) };
  }
  const tableQuiz = (kind) => [
    { q: 'What does r2 in row 5, column + mean?', options: ['Shift + and go to state 2', 'With state 5 on top and + next, reduce by rule 2', 'Go to state 2', 'An error'], answer: 1, why: 'r for reduce; the number is the rule in the augmented grammar.' },
    { q: kind === 'slr' ? 'Where does SLR(1) put the reduce actions of A → γ •?' : 'Where does LR(0) put the reduce actions of A → γ •?', options: kind === 'slr' ? ['Every column', 'The columns of FOLLOW(A)', 'Only $', 'The columns of FIRST(γ)'] : ['Every terminal column and $', 'FOLLOW(A)', 'Only $', 'Nowhere'], answer: kind === 'slr' ? 1 : 0, why: kind === 'slr' ? 'A reduction to A only makes sense if the next symbol can follow A.' : 'LR(0) decides without looking at the next symbol.' },
    { q: 'A state holds E → T • and T → T • * x. Is there a conflict in the LR(0) table?', options: ['No', 'Yes, shift/reduce on *', 'Yes, reduce/reduce', 'Only on $'], answer: 1, why: 'The complete item reduces on every column, including *, where the other item shifts.' },
    { q: 'What are GOTO entries used for?', options: ['Shifting terminals', 'Finding the state after a reduction to a nonterminal', 'Error recovery', 'Accepting'], answer: 1, why: 'After popping a handle, the exposed state and the new nonterminal give the next state.' },
  ];

  T.topic({
    id: 'lr0-table', family: 'lr-items', order: 30, title: 'The LR(0) table and its conflicts',
    blurb: 'Shift where an item has a terminal after its dot, reduce where an item is complete, goto on nonterminals. LR(0) reduces without looking ahead, so a complete item next to a shift item is a conflict.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: TIMES, check: checkG }],
    presets: [
      { label: 'Sums and products: conflicts', values: { g: TIMES } },
      { label: 'Sums with brackets: none', values: { g: PLUS } },
      { label: 'Reduce/reduce: S → c | A A', values: { g: TWOC } },
      { label: 'An ε-rule: L → x L | ε', values: { g: OPTL } },
    ],
    counters: [{ id: 'entries', label: 'entries' }, { id: 'conflicts', label: 'conflicts' }],
    run: (inp) => tableRun(inp, 'lr0'),
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'reduce', once: true, pick: 'option', options: ['Only under $', 'Under FOLLOW of its left side', 'Under every terminal and $'], ask: 'A complete item is next. Where will LR(0) put its reduce action?', answer: () => 'Under every terminal and $', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['LR(0)', 'Not LR(0)'], ask: 'Is the grammar LR(0)?', answer: (fr) => (fr[fr.length - 1].meta.ok ? 'LR(0)' : 'Not LR(0)'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: tableQuiz('lr0'),
  });

  T.topic({
    id: 'slr-table', family: 'lr-items', order: 40, title: 'SLR(1): reduce only on FOLLOW',
    blurb: 'The same automaton as LR(0), but a complete item A → γ • reduces only when the next symbol can follow A. That one look ahead removes many conflicts, though FOLLOW is sometimes too coarse.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: TIMES, check: checkG }],
    presets: [
      { label: 'Sums and products: fixed by FOLLOW', values: { g: TIMES } },
      { label: 'Not SLR: S → c | A A', values: { g: TWOC } },
      { label: 'An ε-rule: L → x L | ε', values: { g: OPTL } },
      { label: 'Ambiguous: E → E + E | n', values: { g: AMBIG } },
    ],
    counters: [{ id: 'entries', label: 'entries' }, { id: 'conflicts', label: 'conflicts' }],
    run: (inp) => tableRun(inp, 'slr'),
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'reduce', once: true, pick: 'item', ask: 'A reduce action is next. Click one of the cells it goes into (look at FOLLOW).', answer: (fr, i) => fr[i + 1].meta.cells, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['SLR(1)', 'Not SLR(1)'], ask: 'Is the grammar SLR(1)?', answer: (fr) => (fr[fr.length - 1].meta.ok ? 'SLR(1)' : 'Not SLR(1)'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: tableQuiz('slr').concat([{ q: 'Why can SLR(1) fail where LALR(1) succeeds?', options: ['SLR uses no automaton', 'FOLLOW(A) lists what can follow A anywhere, not what can follow it in this state', 'SLR has fewer states', 'LALR uses two symbols'], answer: 1, why: 'LALR lookaheads are specific to the state, so they are subsets of FOLLOW.' }]),
  });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'lalr-merge', family: 'lr-items', order: 50, title: 'LALR(1): merging states with equal cores',
    blurb: 'LR(1) states that hold the same items with different lookaheads are merged, lookaheads united. The automaton shrinks to the size of LR(0), and usually nothing is lost; but a merge can create a reduce/reduce conflict.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: TWOC, check: checkG }],
    presets: [
      { label: 'S → c | A A: merging is safe', values: { g: TWOC } },
      { label: 'Merging creates a conflict', values: { g: SPLIT } },
      { label: 'Lists: L → x L | ε', values: { g: OPTL } },
      { label: 'Nothing to merge: sums and products', values: { g: TIMES } },
    ],
    counters: [{ id: 'states', label: 'states' }, { id: 'merged', label: 'merges' }],
    run(inp) {
      const G = T.PX.G(inp.g), M = T.lr.lalrByMerge(G), lr1 = M.lr1, aug = M.aug;
      const m1 = LR.machine(lr1), pos1 = LR.layout(m1);
      const F = new T.Frames(['states', 'merged']);
      const groups = M.states.map((s) => s.from);
      const groupOf = new Map(); groups.forEach((g, k) => g.forEach((id) => groupOf.set(id, k)));
      const done = new Set();
      const nameOf = (id) => (done.has(groupOf.get(id)) ? groups[groupOf.get(id)].join('+') : String(id));
      const machine = () => {
        const states = [...new Set(lr1.states.map((s) => nameOf(s.id)))], trans = [], seen = new Set();
        for (const t of m1.trans) { const a = nameOf(+t.from), b = nameOf(+t.to), k = a + '>' + b + '>' + t.label; if (!seen.has(k)) { seen.add(k); trans.push({ from: a, to: b, label: t.label }); } }
        return { kind: 'dfa', states, start: nameOf(0), accept: [...new Set(m1.accept.map((q) => nameOf(+q)))], trans };
      };
      const bx = LR.box(pos1, m1);
      const cw = LR.cardW(aug, lr1, true) + 40, cx = bx.x + bx.w + 50;
      const lalrT = T.lr.buildTable(G, 'lalr', { precedence: false, lalr: 'merge' }), lr1T = T.lr.buildTable(G, 'lr1', { precedence: false });
      const colour = (k) => 'c' + (k % 6);
      const scene = (o) => {
        o = o || {};
        const m = machine(), cls = {};
        for (const s of lr1.states) { const k = groupOf.get(s.id); if (groups[k].length > 1) cls[nameOf(s.id)] = 'grp' + colour(k); }
        const g = K.graph.draw(m, { pos: done.size ? LR.layout(m) : pos1, prefix: 'lm', cls, hot: o.hot || [], bad: o.bad || [], merged: o.merged });
        // after a merge the automaton is laid out afresh; states glide to their new places
        const items = g.items.map((it) => (it.kind === 'edge' && /^lm:e:/.test(it.key) ? Object.assign({}, it, { audit: 'edge-x' }) : it));
        if (o.card) items.push(...LR.card(aug, o.card.items, { x: cx, y: bx.y, w: cw, title: o.card.title, prefix: 'lc', kernel: () => false, cls: o.card.cls }).items);
        return { items, exits: g.exits };
      };
      F.set('states', lr1.states.length);
      const pairs = groups.filter((g) => g.length > 1);
      const s0 = scene();
      F.add({ items: s0.items, say: 'The canonical LR(1) automaton has ' + lr1.states.length + ' states. States drawn in the same colour hold the same items (the same core) and differ only in lookaheads: ' + (pairs.length ? pairs.map((g) => '{' + g.join(', ') + '}').join(', ') : 'none here') + '.', meta: { count: lr1.states.length } });
      groups.forEach((g, k) => {
        if (g.length < 2) return;
        const before = g.map((id) => lr1.states[id]);
        F.add({ items: scene({ hot: g.map(String), card: { title: 'States ' + g.join(' and ') + ': same core', items: before[0].items.map((it) => Object.assign({}, it, { la: before.map((s) => (s.items.find((x) => x.p === it.p && x.d === it.d) || { la: [] }).la.join(' ')).join(' | ') })) } }).items, say: 'States ' + g.join(' and ') + ' have the same items; their lookaheads (shown side by side) differ.', meta: { kind: 'pair' } });
        done.add(k);
        F.count('merged').set('states', machine().states.length);
        const name = g.join('+'); void name;
        const conflictHere = lalrT.conflicts.filter((c) => c.state === k);
        const sc = scene({ hot: conflictHere.length ? [] : [name], bad: conflictHere.length ? [name] : [], merged: { [name]: g.map(String) }, card: { title: 'Merged state ' + name, items: M.states[k].items, cls: (it) => (conflictHere.some((c) => c.items.some((x) => x.item.p === it.p && x.item.d === it.d)) ? 'bad' : '') } });
        F.add({ items: sc.items, exits: sc.exits, say: 'Merge them into one state with the union of the lookaheads. ' + (conflictHere.length ? conflictHere[0].say.replace(/; .* wins by default\./, '.') + ' Each of the old states was fine on its own: the merge mixed their lookaheads.' : 'No two actions clash in the merged state.'), mark: conflictHere.length ? 'conflict' : undefined, meta: { kind: 'merge', bad: conflictHere.length > 0 } });
      });
      const ok = !lalrT.conflicts.length;
      F.add({ items: scene().items, say: 'LALR(1): ' + M.states.length + ' states instead of ' + lr1.states.length + ', the same number as LR(0). ' + (ok ? 'The table has no conflicts, so the grammar is LALR(1).' : 'The merged table has ' + lalrT.conflicts.length + ' conflict' + (lalrT.conflicts.length > 1 ? 's' : '') + (lr1T.conflicts.length ? '.' : ' that canonical LR(1) does not have: the grammar is LR(1) but not LALR(1).')), mark: ok ? 'LALR(1)' : 'conflict', meta: { ok } });
      return { frames: F.list, def: LR.def(G, [{ id: 'm', kind: 'text', title: 'Merging', text: 'Two LR(1) states with the same core (the same items without lookaheads) become one state whose items have the union of the lookaheads. Shift actions never clash after a merge; reduce actions can, giving a reduce/reduce conflict.' }]) };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['As many as LR(1)', 'As many as LR(0)', 'Fewer than LR(0)'], ask: 'How many states will the LALR(1) automaton have?', answer: () => 'As many as LR(0)', explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'merge', once: true, pick: 'option', options: ['No conflict', 'A shift/reduce conflict', 'A reduce/reduce conflict'], ask: 'What will this merge produce?', answer: (fr, i) => (fr[i + 1].meta.bad ? 'A reduce/reduce conflict' : 'No conflict'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Which states does LALR(1) merge?', options: ['States with the same lookaheads', 'LR(1) states with the same core (items without lookaheads)', 'Any two states', 'States with no conflicts'], answer: 1, why: 'The core is what an LR(0) state would hold.' },
      { q: 'Can merging create a shift/reduce conflict that LR(1) did not have?', options: ['Yes, often', 'No: shifts do not depend on lookaheads, so such a conflict was already in one of the states', 'Only with ε-rules', 'Only for ambiguous grammars'], answer: 1, why: 'A new conflict from merging is always reduce/reduce.' },
      { q: 'Why do parser generators use LALR(1) rather than LR(1)?', options: ['It accepts more grammars', 'Its tables are as small as LR(0)\'s and it handles almost every practical grammar', 'It needs no lookahead', 'It is the only one that works'], answer: 1, why: 'LR(1) tables can be many times larger for little gain in practice.' },
      { q: 'LALR(1) has a conflict but LR(1) has none. Which kind is it?', options: ['Shift/reduce', 'Reduce/reduce', 'Either', 'Neither'], answer: 1, why: 'See the second question.' },
    ],
  });
})();
