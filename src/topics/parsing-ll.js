// Top-down predictive parsing, part one: FIRST and FOLLOW computed round by round, the LL(1) table filled
// cell by cell, and what an LL(1) conflict is (two rules in one cell) with the sets that collide drawn as
// overlapping circles. Sets are rows of chips that grow as terminals join them; an arrow says where each
// new member came from.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'first-follow', part: 'parsing', order: 10, title: 'FIRST and FOLLOW', blurb: 'Which terminals can begin what a symbol derives, and which can come right after it: the two sets every predictive parser is built from.' });
  T.family({ id: 'll1', part: 'parsing', order: 20, title: 'LL(1) parsing', blurb: 'One symbol of lookahead picks the rule: the table, its conflicts, the parse with a stack, error recovery and the recursive-descent code it turns into.' });

  // our own grammars
  const NEST = 'S → A B c\nA → a A | ε\nB → b | ε';
  const LIST = 'L → [ A ]\nA → x R | ε\nR → ; x R | ε';
  const STMT = 'S → x = E | x ( )\nE → x | n';
  const OPTA = 'S → A a b\nA → a | ε';
  const LEFTL = 'L → L ; x | x';
  const SUM = 'E → T P\nP → + T P | ε\nT → ( E ) | n';
  const CHAIN = 'S → A B\nA → C | a\nB → b B | ε\nC → c | ε';

  const checkG = (v) => T.PX.checkGrammar({ maxRules: 9, maxN: 5 })(v);
  T.PX.LL = { NEST, LIST, STMT, OPTA, LEFTL, SUM, CHAIN, checkG };

  /**
   * Rows of sets: a label cell then one chip per member. rows: [{id, label, members, cls}], opts: {prefix, x, y,
   * labelW, chipCls(rowId, m), hot: [row ids], gap}
   */
  function setRows(rows, opts) {
    const P = opts.prefix, items = [], lw = opts.labelW || 110, gap = opts.gap || 54, x0 = opts.x || 0, y0 = opts.y || 0;
    const hot = new Set(opts.hot || []);
    rows.forEach((r, i) => {
      const y = y0 + i * gap;
      items.push({ key: P + ':l:' + r.id, kind: 'cell', x: x0, y, w: lw, h: 42, text: r.label, cls: 'head' + (hot.has(r.id) ? ' hot' : '') + (r.cls ? ' ' + r.cls : ''), rx: 8, size: 15 });
      if (!r.members.length) items.push({ key: P + ':empty:' + r.id, kind: 'text', x: x0 + lw + 14, y: y + 26, text: '∅', cls: 'strong' });
      r.members.forEach((m, k) => items.push({ key: P + ':c:' + r.id + ':' + m, kind: 'cell', x: x0 + lw + 10 + k * 48, y: y + 2, w: 42, h: 38, text: m, cls: 'mono chip' + (m === 'ε' ? ' eps' : '') + (opts.chipCls ? ' ' + (opts.chipCls(r.id, m) || '') : ''), enter: 'grow', rx: 10, size: 16, pick: true }));
    });
    return items;
  }
  T.PX.setRows = setRows;
  const ruleRows = (G, lit, opts) => G.productions.map((p) => ({ id: String(p.id), text: T.grammar.showProd(G, p), cls: lit && lit.includes(p.id) ? 'hot' : (opts && opts.dim && opts.dim.includes(p.id) ? 'faint' : '') }));
  T.PX.ruleRows = ruleRows;
  const sortSet = (xs) => [...xs].sort((a, b) => (a === 'ε') - (b === 'ε') || (a === '$') - (b === '$') || (a < b ? -1 : a > b ? 1 : 0));
  T.PX.sortSet = sortSet;
  const arrow = (key, from, to, cls, bend) => ({ key, kind: 'edge', from, to, bend: bend === undefined ? -20 : bend, cls, audit: 'ignore', layer: 'top' });
  T.PX.arrow = arrow;

  const ffDef = (G, ff, which) => ({ sections: [
    T.PX.gdef(G),
    { id: 'sets', kind: 'table', title: 'The final sets', colHead: which === 'first' ? ['FIRST'] : ['FIRST', 'FOLLOW'], rowHead: G.nonterminals, rows: G.nonterminals.map((A) => (which === 'first' ? [T.PX.set(sortSet(ff.first.get(A)))] : [T.PX.set(sortSet(ff.first.get(A))), T.PX.set(sortSet(ff.follow.get(A)))])) },
    { id: 'rule', kind: 'text', title: which === 'first' ? 'The rules for FIRST' : 'The rules for FOLLOW', text: which === 'first' ? 'For A → X1 X2 … Xk: add FIRST(X1) without ε; if X1 can vanish, add FIRST(X2) without ε too, and so on. If every Xi can vanish (or k = 0), ε joins FIRST(A). The FIRST of a terminal is just itself. Repeat until a whole round changes nothing.' : 'Put $ in FOLLOW(start). For A → α B β: add FIRST(β) without ε to FOLLOW(B); if β can vanish (or is empty), everything in FOLLOW(A) goes into FOLLOW(B) too. Repeat until nothing changes.' },
  ] });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'first-sets', family: 'first-follow', order: 10, title: 'FIRST sets, round by round',
    blurb: 'FIRST(A) is every terminal a string derived from A can begin with, plus ε if A can vanish. Rules feed each other, so the sets grow in rounds until a round changes nothing.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: NEST, check: checkG }],
    presets: [
      { label: 'Vanishing prefixes', values: { g: NEST } },
      { label: 'A list in brackets', values: { g: LIST } },
      { label: 'A chain of ε', values: { g: CHAIN } },
      { label: 'Left recursion', values: { g: LEFTL } },
      { label: 'Sums', values: { g: SUM } },
    ],
    counters: [{ id: 'round', label: 'round' }, { id: 'added', label: 'terminals added' }],
    run(inp) {
      const G = T.PX.G(inp.g), ff = T.ll.firstFollow(G), F = new T.Frames(['round', 'added']);
      const sets = new Map(G.nonterminals.map((A) => [A, []]));
      const gx = 0, sx = Math.max(250, T.PX.panel({ rows: ruleRows(G) }).w + 50);
      const scene = (o) => {
        o = o || {};
        const pn = T.PX.panel({ prefix: 'gr', x: gx, y: 0, title: 'Rules', rows: ruleRows(G, o.rule === undefined ? null : [o.rule]), rowH: 34, size: 16 });
        const rows = G.nonterminals.map((A) => ({ id: A, label: 'FIRST(' + A + ')', members: sortSet(sets.get(A)) }));
        const items = pn.items.concat(setRows(rows, { prefix: 'fs', x: sx, y: 30, hot: o.hot ? [o.hot] : [], chipCls: (A, m) => (o.hot === A && o.added && o.added.includes(m) ? 'hot' : o.src === A ? 'act' : '') }));
        items.push({ key: 'fs:round', kind: 'text', x: sx, y: 12, text: o.roundText || '', cls: 'strong', size: 15 });
        if (o.rule !== undefined && o.added) items.push(arrow('fs:a1', 'gr:r:' + o.rule, 'fs:c:' + o.hot + ':' + o.added[0], 'scan', -16));
        if (o.src) items.push(arrow('fs:a2', 'fs:l:' + o.src, 'fs:l:' + o.hot, 'complete', 50));
        return items;
      };
      let round = 0;
      for (const st of ff.trace) {
        if (st.kind === 'phase' && st.phase === 'first') { F.add({ items: scene({ roundText: 'Start: every set empty' }), say: st.say + ' A terminal is its own FIRST; we need FIRST of the nonterminals ' + G.nonterminals.join(', ') + '.' }); continue; }
        if (st.kind === 'first') {
          if (st.round !== round) { round = st.round; F.set('round', round); }
          sets.get(st.A).push(...st.added);
          F.count('added', st.added.length);
          F.add({ items: scene({ rule: st.prod, hot: st.A, added: st.added, src: st.from && T.grammar.isN(G, st.from) && st.from !== st.A ? st.from : null, roundText: 'Round ' + round }), say: st.say, hl: { g: [st.prod] }, meta: { A: st.A, added: st.added } });
          continue;
        }
        if (st.kind === 'round' && st.phase === 'first') {
          F.add({ items: scene({ roundText: st.changed ? 'End of round ' + st.round : 'Round ' + st.round + ': no change' }), say: st.changed ? 'Round ' + st.round + ' is over and something changed, so go round again: a set that grew may feed another.' : st.say + ' ' + (ff.nullable.size ? 'The nonterminals that can vanish: ' + [...ff.nullable].join(', ') + '.' : 'No nonterminal can vanish.'), mark: st.changed ? undefined : 'done', meta: { roundEnd: st.round, changed: st.changed } });
          if (!st.changed) break;
        }
      }
      return { frames: F.list, def: ffDef(G, ff, 'first') };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.A && i > 0, once: true, pick: 'item', ask: 'Which set grows next? Click its name.', answer: (fr, i) => 'fs:l:' + fr[i + 1].meta.A, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i].meta && fr[i].meta.changed === true, once: true, pick: 'option', options: ['Yes, the sets are final', 'No, another round is needed'], ask: 'Something changed this round. Are the sets final now?', answer: () => 'No, another round is needed', explain: 'A round only proves the sets are final when it changes nothing; a set that grew may feed another set.' },
    ],
    quiz: [
      { q: 'S → A B c, A → a | ε, B → b | ε. What is FIRST(S)?', options: ['{a}', '{a, b}', '{a, b, c}', '{a, b, c, ε}'], answer: 2, why: 'A and B can both vanish, so S can begin with a, b or c; c cannot vanish, so ε is not in FIRST(S).' },
      { q: 'When does ε belong to FIRST(A)?', options: ['When A has a rule with a terminal', 'When A can derive the empty string', 'Always', 'When A is the start symbol'], answer: 1, why: 'ε in FIRST(A) records that A is nullable.' },
      { q: 'Why is FIRST computed in rounds?', options: ['To save memory', 'Because sets depend on each other, possibly in a cycle, so we repeat until nothing changes', 'Because grammars are ambiguous', 'It is not; one pass is enough'], answer: 1, why: 'FIRST(A) may use FIRST(B) which may use FIRST(A): a fixpoint is reached by repeating.' },
      { q: 'L → L ; x | x. What is FIRST(L)?', options: ['{;}', '{x}', '{x, ;}', '∅'], answer: 1, why: 'Every string of L begins with x; the left-recursive rule adds FIRST(L) to itself, which adds nothing.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'follow-sets', family: 'first-follow', order: 20, title: 'FOLLOW sets: what can come next',
    blurb: 'FOLLOW(B) is every terminal that can appear right after B in some sentential form, with $ for the end. Each new member arrives along an arrow: from what follows B in a rule, or from FOLLOW of the rule\'s left side.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: LIST, check: checkG }],
    presets: [
      { label: 'A list in brackets', values: { g: LIST } },
      { label: 'Vanishing prefixes', values: { g: NEST } },
      { label: 'Sums', values: { g: SUM } },
      { label: 'A chain of ε', values: { g: CHAIN } },
    ],
    counters: [{ id: 'round', label: 'round' }, { id: 'added', label: 'terminals added' }],
    run(inp) {
      const G = T.PX.G(inp.g), ff = T.ll.firstFollow(G), F = new T.Frames(['round', 'added']);
      const fol = new Map(G.nonterminals.map((A) => [A, []]));
      const pw = T.PX.panel({ rows: ruleRows(G) }).w;
      const fx = pw + 40, maxFirst = Math.max(1, ...G.nonterminals.map((A) => ff.first.get(A).size));
      const ox = fx + 110 + 10 + maxFirst * 48 + 40;
      const scene = (o) => {
        o = o || {};
        const pn = T.PX.panel({ prefix: 'gr', x: 0, y: 0, title: 'Rules', rows: ruleRows(G, o.rule === undefined || o.rule === null ? null : [o.rule]), rowH: 34, size: 16 });
        const fr = setRows(G.nonterminals.map((A) => ({ id: A, label: 'FIRST(' + A + ')', members: sortSet(ff.first.get(A)), cls: 'faint' })), { prefix: 'ffi', x: fx, y: 30, chipCls: (A) => (o.fromFirst === A ? 'act' : 'faint') });
        const or = setRows(G.nonterminals.map((A) => ({ id: A, label: 'FOLLOW(' + A + ')', members: sortSet(fol.get(A)) })), { prefix: 'ffo', x: ox, y: 30, hot: o.hot ? [o.hot] : [], chipCls: (A, m) => (o.hot === A && o.added && o.added.includes(m) ? 'hot' : o.fromFollow === A ? 'act' : '') });
        const items = pn.items.concat(fr, or);
        items.push({ key: 'ff:t1', kind: 'text', x: fx, y: 12, text: 'FIRST (for reference)', cls: 'strong', size: 15 });
        items.push({ key: 'ff:t2', kind: 'text', x: ox, y: 12, text: o.roundText || 'FOLLOW', cls: 'strong', size: 15 });
        if (o.rule !== undefined && o.rule !== null && o.added) items.push(arrow('ff:a1', 'gr:r:' + o.rule, 'ffo:l:' + o.hot, 'scan', -14));
        if (o.fromFirst) items.push(arrow('ff:a2', 'ffi:l:' + o.fromFirst, 'ffo:c:' + o.hot + ':' + o.added[0], 'complete', 30));
        if (o.fromFollow) items.push(arrow('ff:a3', 'ffo:l:' + o.fromFollow, 'ffo:l:' + o.hot, 'complete', o.fromFollow === o.hot ? 0 : 60));
        return items;
      };
      let round = 0, started = false;
      for (const st of ff.trace) {
        if (st.kind === 'phase' && st.phase === 'follow') { started = true; F.add({ items: scene({}), say: 'FIRST is already known (left). Now FOLLOW, where each set says which terminals can come right after its nonterminal. ' + st.say }); continue; }
        if (!started) continue;
        if (st.kind === 'follow') {
          if (st.round !== round) { round = st.round; F.set('round', round); }
          fol.get(st.A).push(...st.added);
          F.count('added', st.added.length);
          const p = st.prod === null ? null : G.productions[st.prod];
          const beta0 = p && st.via === 'first' ? p.rhs[st.pos + 1] : null;
          F.add({ items: scene({ rule: st.prod, hot: st.A, added: st.added, fromFirst: beta0 && T.grammar.isN(G, beta0) ? beta0 : null, fromFollow: st.via === 'follow' ? st.from : null, roundText: round ? 'FOLLOW, round ' + round : 'FOLLOW' }), say: st.say, hl: { g: st.prod === null ? [] : [st.prod] }, meta: { A: st.A, via: st.via || 'start' } });
          continue;
        }
        if (st.kind === 'round' && st.phase === 'follow') {
          F.add({ items: scene({ roundText: st.changed ? 'End of round ' + st.round : 'Round ' + st.round + ': no change' }), say: st.changed ? 'Round ' + st.round + ' changed something, so go round again.' : st.say + ' ' + G.nonterminals.map((A) => 'FOLLOW(' + A + ') = ' + T.PX.set(sortSet(fol.get(A)))).join(', ') + '.', mark: st.changed ? undefined : 'done' });
          if (!st.changed) break;
        }
      }
      return { frames: F.list, def: ffDef(G, ff, 'follow') };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.via === 'follow', once: true, pick: 'option', options: ['From FIRST of what comes after it', 'From FOLLOW of the rule\'s left side', 'From the start symbol\'s $ only'], ask: 'The next terminals to join a FOLLOW set come from where?', answer: () => 'From FOLLOW of the rule\'s left side', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.A && i > 0, once: true, pick: 'item', ask: 'Which FOLLOW set grows next? Click its name.', answer: (fr, i) => 'ffo:l:' + fr[i + 1].meta.A, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why is $ always in FOLLOW of the start symbol?', options: ['By convention, $ marks the end of input, which follows a whole sentence', 'Because the start symbol is nullable', 'It is not always', 'Because $ is a terminal of every grammar'], answer: 0, why: 'A complete sentence derived from the start symbol is followed by the end of the input.' },
      { q: 'In A → x B, what goes into FOLLOW(B)?', options: ['FIRST(x)', 'Everything in FOLLOW(A)', 'Nothing', 'FIRST(B)'], answer: 1, why: 'B is at the end of the rule, so whatever can follow A can follow B.' },
      { q: 'Can ε ever be in a FOLLOW set?', options: ['Yes, when B is nullable', 'No: FOLLOW holds terminals and $, never ε', 'Only for the start symbol', 'Only in left-recursive grammars'], answer: 1, why: 'Something always follows B, even if it is just the end marker $.' },
      { q: 'In S → A B c with B nullable, what does FOLLOW(A) get from this rule?', options: ['FIRST(B) only', 'FIRST(B) without ε, and c', 'c only', 'FOLLOW(S)'], answer: 1, why: 'FIRST(B c) without ε: FIRST(B) minus ε, and since B can vanish, c as well.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  /** The LL(1) table as a stage table: row per nonterminal, column per terminal and $, cells hold right sides */
  function llTable(G, t, filled, opts) {
    opts = opts || {};
    const cols = t.terminals, rows = G.nonterminals;
    const cell = (A, a) => { const ids = (filled[A] && filled[A][a]) || []; return ids.length ? ids.map((id) => T.grammar.showRhs(G, G.productions[id].rhs)).join(' / ') : ''; };
    return K.table.draw({ prefix: opts.prefix || 'lt', rows: rows.map((A) => cols.map((a) => cell(A, a))), rowHead: rows, colHead: cols, corner: 'M', x: opts.x || 0, y: opts.y || 0, mono: true, size: 15, minW: 52, hot: opts.hot ? [opts.hot] : [], cls: (r, c) => { const ids = (filled[rows[r]] && filled[rows[r]][cols[c]]) || []; return ids.length > 1 ? 'bad' : opts.good && ids.length ? 'good' : ''; } });
  }
  T.PX.llTable = llTable;
  const tableDef = (G, t) => ({ sections: [
    T.PX.gdef(G),
    { id: 'ff', kind: 'table', title: 'FIRST and FOLLOW', colHead: ['FIRST', 'FOLLOW'], rowHead: G.nonterminals, rows: G.nonterminals.map((A) => [T.PX.set(sortSet(t.first.get(A))), T.PX.set(sortSet(t.follow.get(A)))]) },
    { id: 'rule', kind: 'text', title: 'Filling M[A, a]', text: 'For each rule A → α: put it in M[A, a] for every terminal a in FIRST(α). If α can vanish, also put it in M[A, b] for every b in FOLLOW(A), $ included. A cell with two rules is a conflict: the grammar is not LL(1).' },
  ] });

  T.topic({
    id: 'll1-table', family: 'll1', order: 10, title: 'Building the LL(1) table',
    blurb: 'M[A, a] says which rule to use when A is on top of the stack and a is the next input symbol. Every rule goes in under the terminals that can begin it, and an ε-able rule also under what can follow its nonterminal.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: LIST, check: checkG }],
    presets: [
      { label: 'A list in brackets', values: { g: LIST } },
      { label: 'Sums', values: { g: SUM } },
      { label: 'Vanishing prefixes', values: { g: NEST } },
      { label: 'With a conflict', values: { g: OPTA } },
    ],
    counters: [{ id: 'entries', label: 'entries' }, { id: 'conflicts', label: 'conflicts' }],
    run(inp) {
      const G = T.PX.G(inp.g), t = T.ll.ll1Table(G), F = new T.Frames(['entries', 'conflicts']);
      const filled = {};
      const pw = T.PX.panel({ rows: ruleRows(G) }).w;
      const tx = pw + 50;
      const scene = (o) => {
        o = o || {};
        const pn = T.PX.panel({ prefix: 'gr', x: 0, y: 0, title: 'Rules', rows: ruleRows(G, o.prod === undefined ? null : [o.prod]), rowH: 34, size: 16 });
        const tb = llTable(G, t, filled, { x: tx, y: 0, hot: o.hot, good: o.done });
        const items = pn.items.concat(tb.items);
        if (o.why) items.push(...T.PX.panel({ prefix: 'why', x: tx, y: tb.box.h + 24, w: Math.max(360, tb.box.w), title: 'Why', rows: o.why.map((x, k) => ({ id: 'w' + k, text: x, cls: k === o.why.length - 1 ? 'hot' : '' })), rowH: 32, size: 15 }).items);
        if (o.hot) items.push(arrow('lt:arr', 'gr:r:' + o.prod, 'lt:' + o.hot[0] + ',' + o.hot[1], 'scan', -20));
        return items;
      };
      F.add({ items: scene({}), say: 'An empty table: a row for each nonterminal ' + G.nonterminals.join(', ') + ' and a column for each terminal and the end marker $. Rules go in one at a time.' });
      for (const st of t.trace) {
        if (st.kind !== 'entry') continue;
        ((filled[st.A] = filled[st.A] || {})[st.terminal] = filled[st.A][st.terminal] || []).push(st.prod);
        F.count('entries');
        if (st.clash) F.count('conflicts');
        const p = G.productions[st.prod], rhs = T.grammar.showRhs(G, p.rhs);
        const fa = T.ll.firstOf(G, p.rhs, { first: t.first, follow: t.follow }).set;
        const why = st.reason === 'first' ? ['FIRST(' + rhs + ') = ' + T.PX.set(sortSet(fa)), st.terminal + ' is in it, so M[' + st.A + ', ' + st.terminal + '] = ' + st.A + ' → ' + rhs] : [rhs + ' can vanish; FOLLOW(' + st.A + ') = ' + T.PX.set(sortSet(t.follow.get(st.A))), st.terminal + ' is in it, so M[' + st.A + ', ' + st.terminal + '] = ' + st.A + ' → ' + rhs];
        F.add({ items: scene({ prod: st.prod, hot: [G.nonterminals.indexOf(st.A), t.terminals.indexOf(st.terminal)], why }), say: st.say, hl: { g: [st.prod], ff: [String(G.nonterminals.indexOf(st.A))] }, meta: { cell: 'lt:' + G.nonterminals.indexOf(st.A) + ',' + t.terminals.indexOf(st.terminal), reason: st.reason } });
      }
      const v = t.trace[t.trace.length - 1];
      F.add({ items: scene({ done: t.ll1 }), say: v.say + (t.ll1 ? ' The empty cells are errors: with that nonterminal on the stack, that symbol cannot come next.' : ''), mark: t.ll1 ? 'LL(1)' : 'conflict' });
      return { frames: F.list, def: tableDef(G, t) };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.reason === 'follow', once: true, pick: 'item', ask: 'The next entry comes from FOLLOW, because a rule can vanish. Click the cell it goes into.', answer: (fr, i) => fr[i + 1].meta.cell, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === 1, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will every cell end up with at most one rule (is the grammar LL(1))?', answer: (fr) => (fr[fr.length - 1].mark === 'LL(1)' ? 'Yes' : 'No'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A → α, and α can derive ε. Under which columns does A → α go?', options: ['Only FIRST(α)', 'FIRST(α) without ε, and FOLLOW(A)', 'Only FOLLOW(A)', 'Every column'], answer: 1, why: 'When α vanishes, the next input symbol is whatever follows A.' },
      { q: 'What does an empty cell M[A, a] mean while parsing?', options: ['Use A → ε', 'A syntax error: no string from A can begin with a here', 'Skip a', 'Pop A'], answer: 1, why: 'No rule for A can start with a or vanish before a.' },
      { q: 'What makes a grammar LL(1)?', options: ['It has no ε-rules', 'Every table cell holds at most one rule', 'It is unambiguous', 'It has one nonterminal'], answer: 1, why: 'Then one symbol of lookahead always decides which rule to use.' },
      { q: 'How many columns does the table have?', options: ['One per nonterminal', 'One per terminal, plus $', 'One per rule', 'One per input symbol'], answer: 1, why: 'The lookahead is a terminal or the end marker $.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------------
  T.topic({
    id: 'll1-conflict', family: 'll1', order: 20, title: 'An LL(1) conflict, explained',
    blurb: 'Two rules in one cell: the parser cannot tell from one symbol which to use. Either both rules can begin with the same terminal (FIRST/FIRST), or one can vanish and a terminal that follows collides with the other (FIRST/FOLLOW).',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: STMT, check: checkG }],
    presets: [
      { label: 'FIRST/FIRST: x = … or x ( )', values: { g: STMT } },
      { label: 'FIRST/FOLLOW: an optional a', values: { g: OPTA } },
      { label: 'Left recursion', values: { g: LEFTL } },
      { label: 'No conflict at all', values: { g: LIST } },
    ],
    counters: [{ id: 'conflicts', label: 'conflicts' }],
    run(inp) {
      const G = T.PX.G(inp.g), t = T.ll.ll1Table(G), F = new T.Frames(['conflicts']);
      const full = t.table;
      const tb0 = llTable(G, t, full, {});
      const vx = tb0.box.w + 200, vy = tb0.box.h / 2 + 30;
      const scene = (o) => {
        o = o || {};
        const tb = llTable(G, t, o.table ? o.table.table : full, { hot: o.hot, good: o.good, prefix: o.prefix || 'lt' });
        const items = tb.items.slice();
        if (o.venn) items.push(...K.set.venn(Object.assign({ prefix: 'vn', x: vx, y: vy, r: 92 }, o.venn)).items);
        if (o.rules) items.push(...T.PX.panel({ prefix: 'cr', x: 0, y: tb.box.h + 30, title: o.rulesTitle || 'In the cell', rows: o.rules, rowH: 32, size: 15 }).items);
        return items;
      };
      F.add({ items: scene({}), say: 'The LL(1) table of the grammar, filled from FIRST and FOLLOW. ' + (t.ll1 ? 'Every cell holds at most one rule.' : t.conflicts.length + ' cell' + (t.conflicts.length > 1 ? 's hold' : ' holds') + ' two rules, shown in red.'), meta: { n: t.conflicts.length } });
      if (t.ll1) {
        F.add({ items: scene({ good: true }), say: 'No conflict: whatever nonterminal is on top of the stack, the next symbol names at most one rule. This grammar is LL(1), so a predictive parser can use it as it stands.', mark: 'LL(1)', meta: { ll1: true } });
        return { frames: F.list, def: tableDef(G, t) };
      }
      for (const c of t.conflicts.slice(0, 2)) {
        F.count('conflicts');
        const r = G.nonterminals.indexOf(c.A), col = t.terminals.indexOf(c.terminal);
        const ps = c.prods.map((id) => G.productions[id]);
        const fs = ps.map((p) => sortSet(T.ll.firstOf(G, p.rhs, { first: t.first, follow: t.follow }).set));
        const rules = ps.map((p, k) => ({ id: 'p' + p.id, text: T.grammar.showProd(G, p) + '    FIRST = ' + T.PX.set(fs[k]), cls: 'bad' }));
        let venn;
        if (c.type === 'FIRST/FIRST') {
          const [a, b] = fs.map((s) => s.filter((x) => x !== 'ε'));
          venn = { sets: [{ id: 'A', label: 'FIRST(' + T.grammar.showRhs(G, ps[0].rhs) + ')' }, { id: 'B', label: 'FIRST(' + T.grammar.showRhs(G, ps[1].rhs) + ')' }], members: { A: a.filter((x) => !b.includes(x)), B: b.filter((x) => !a.includes(x)), AB: a.filter((x) => b.includes(x)) }, hot: ['A', 'B'] };
        } else {
          const nul = ps.find((p, k) => fs[k].includes('ε')) || ps[1], other = ps.find((p) => p !== nul) || ps[0];
          const a = sortSet(T.ll.firstOf(G, other.rhs, { first: t.first, follow: t.follow }).set).filter((x) => x !== 'ε'), b = sortSet(t.follow.get(c.A));
          venn = { sets: [{ id: 'A', label: 'FIRST(' + T.grammar.showRhs(G, other.rhs) + ')' }, { id: 'B', label: 'FOLLOW(' + c.A + ')' }], members: { A: a.filter((x) => !b.includes(x)), B: b.filter((x) => !a.includes(x)), AB: a.filter((x) => b.includes(x)) }, hot: ['A', 'B'] };
        }
        F.add({ items: scene({ hot: [r, col], rules }), say: 'Look at M[' + c.A + ', ' + c.terminal + ']: with ' + c.A + ' on top of the stack and ' + c.terminal + ' next, both ' + ps.map((p) => T.grammar.showProd(G, p)).join(' and ') + ' fit.', hl: { g: c.prods }, meta: { cell: 'lt:' + r + ',' + col } });
        F.add({ items: scene({ hot: [r, col], rules, venn }), say: c.type + ' conflict. ' + c.say, hl: { g: c.prods }, mark: c.type, meta: { type: c.type } });
      }
      // a way out, when the usual rewritings help
      const lr = T.cfg.leftRecursive(G);
      let fixed = null, how = '';
      if (lr.length) { fixed = T.cfg.removeLeftRecursion(G).grammar; how = 'Removing the left recursion'; }
      else if (t.conflicts.some((c) => c.type === 'FIRST/FIRST')) { fixed = T.cfg.leftFactor(G).grammar; how = 'Left factoring'; }
      if (fixed) {
        const t2 = T.ll.ll1Table(fixed);
        const rows = fixed.productions.map((p) => ({ id: 'n' + p.id, text: T.grammar.showProd(fixed, p), cls: t2.ll1 ? 'good' : '' }));
        F.add({ items: llTable(fixed, t2, t2.table, { prefix: 'lt2', good: t2.ll1 }).items.concat(T.PX.panel({ prefix: 'cr2', x: 0, y: llTable(fixed, t2, t2.table, {}).box.h + 30, title: how + ' gives', rows, rowH: 32, size: 15 }).items), say: how + ' rewrites the grammar without changing its language. ' + (t2.ll1 ? 'Now every cell holds one rule: the new grammar is LL(1).' : 'It still has ' + t2.conflicts.length + ' conflict' + (t2.conflicts.length > 1 ? 's' : '') + ': ' + t2.conflicts[0].say), mark: t2.ll1 ? 'LL(1)' : 'still a conflict' });
      } else F.add({ items: scene({}), say: 'Factoring and removing left recursion do not help a FIRST/FOLLOW conflict: the grammar itself needs rethinking (here, the optional ' + t.conflicts[0].terminal + ' and the one after it look the same from one symbol away), or a parser with more lookahead.', mark: 'not LL(1)' });
      return { frames: F.list, def: tableDef(G, t) };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && fr[0].meta && fr[0].meta.n > 0, once: true, pick: 'item', ask: 'Click a cell that holds a conflict.', answer: (fr) => fr[1].meta.cell, explain: (fr) => fr[1].say },
      { at: (f, i, fr) => i === 0 && fr[0].meta && fr[0].meta.n === 0, once: true, pick: 'option', options: ['LL(1)', 'Not LL(1)'], ask: 'Is this grammar LL(1)?', answer: () => 'LL(1)', explain: (fr) => fr[1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.type, once: true, pick: 'option', options: ['FIRST/FIRST', 'FIRST/FOLLOW'], ask: 'Which kind of conflict is it?', answer: (fr, i) => fr[i + 1].meta.type, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'S → x = E | x ( ). What kind of conflict is in M[S, x]?', options: ['FIRST/FIRST', 'FIRST/FOLLOW', 'Shift/reduce', 'None'], answer: 0, why: 'Both right sides begin with x.' },
      { q: 'Which rewriting cures a FIRST/FIRST conflict between A → a b and A → a c?', options: ['Left factoring: A → a A\', A\' → b | c', 'Removing ε-rules', 'Adding a start symbol', 'Reversing the rules'], answer: 0, why: 'After factoring, the choice between b and c happens after a has been read.' },
      { q: 'Why is a left-recursive grammar never LL(1) (when the nonterminal has another rule)?', options: ['It has ε-rules', 'Both rules begin with the same terminals, FIRST(A α) containing FIRST(β)', 'It is ambiguous', 'It has no FOLLOW sets'], answer: 1, why: 'A → A α | β: anything that begins β also begins A α, so both rules sit in the same cells.' },
      { q: 'S → A a b, A → a | ε. Where is the conflict?', options: ['M[S, a]', 'M[A, a]', 'M[A, b]', 'M[S, $]'], answer: 1, why: 'A → a goes under a (FIRST), and A → ε goes under FOLLOW(A) = {a}: both in M[A, a].' },
      { q: 'Does an LL(1) conflict mean the grammar is ambiguous?', options: ['Always', 'No: unambiguous grammars can need more lookahead', 'Only for FIRST/FOLLOW', 'Only with left recursion'], answer: 1, why: 'L → L ; x | x is unambiguous yet not LL(1).' },
    ],
  });
})();
