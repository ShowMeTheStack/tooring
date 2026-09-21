// Tables to fill in: FIRST and FOLLOW sets, an LL(1) parse table, the CYK triangle, or any table an
// exercise spells out. T.Check.tableSpec(x) gives the layout and the expected value of every cell, from
// the core engines (so an exercise only names the grammar), and the checker compares cell by cell.
// Sets are typed as a, b, ε (braces optional; ∅ or nothing for the empty set); an LL(1) cell holds a
// right side (a S b, ε) or several separated by |, or nothing for an error entry.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = (T.Check = T.Check || {});
  K.kinds = K.kinds || {};
  const EPS = 'ε', END = '$';
  const setText = (s) => [...s].sort((a, b) => (a === EPS) - (b === EPS) || (a === END) - (b === END) || (a < b ? -1 : a > b ? 1 : 0)).join(', ');
  const rhsText = (G, p) => (p.rhs.length ? p.rhs.join(' ') : EPS);

  /**
   * {rows: [label], cols: [label], corner, cell(r, c) -> key | null (no cell), expected: {key: text}, kind: 'set' | 'rhs' | 'text', note}
   */
  K.tableSpec = function (x) {
    const kind = x.table;
    if (kind === 'custom') {
      const cells = x.cells || {};
      return { rows: x.rows, cols: x.cols, corner: x.corner || '', cell: (r, c) => { const k = x.rows[r] + '|' + x.cols[c]; return k in cells ? k : null; }, expected: Object.fromEntries(Object.entries(cells).map(([k, v]) => [k, Array.isArray(v) ? v.join(', ') : String(v)])), kind: x.cellKind || 'text' };
    }
    const G = T.grammar.parse(x.grammar);
    if (kind === 'first' || kind === 'follow') {
      const ff = T.ll.firstFollow(G);
      const map = kind === 'first' ? ff.first : ff.follow;
      const rows = G.nonterminals.slice();
      return { rows, cols: [kind === 'first' ? 'FIRST' : 'FOLLOW'], corner: '', cell: (r) => rows[r], expected: Object.fromEntries(rows.map((A) => [A, setText(map.get(A))])), kind: 'set', grammar: G };
    }
    if (kind === 'll1') {
      const t = T.ll.ll1Table(G);
      const rows = G.nonterminals.slice(), cols = G.terminals.concat([END]);
      const expected = {};
      for (const A of rows) for (const a of cols) expected[A + '|' + a] = (t.table[A][a] || []).map((id) => rhsText(G, G.productions[id])).join(' | ');
      return { rows, cols, corner: 'M', cell: (r, c) => rows[r] + '|' + cols[c], expected, kind: 'rhs', grammar: G, conflicts: t.conflicts.length };
    }
    if (kind === 'cyk') {
      const r = T.parse.cyk(G, x.word);
      const n = r.word.length;
      // row len (1..n) from the bottom up, column i (the start position): the cell for word[i .. i+len)
      const rows = Array.from({ length: n }, (_, k) => 'length ' + (n - k)), cols = r.word.slice();
      const expected = {};
      for (let len = 1; len <= n; len++) for (let i = 0; i + len <= n; i++) expected[len + ',' + i] = setText(new Set(r.cells[len][i].map((e) => e.A)));
      return { rows, cols, corner: '', cell: (row, c) => { const len = n - row; return c + len <= n ? len + ',' + c : null; }, expected, kind: 'set', grammar: G, accepted: r.accepted };
    }
    throw new Error('unknown table ' + kind);
  };

  const sameSet = (a, b) => { const A = K.asSet(a), B = K.asSet(b); return A.length === B.length && A.every((v, i) => v === B[i]); };
  const rhsSet = (s) => String(s || '').split(/[|\n;]/).map((v) => v.replace(/^.*?(→|->)/, '').trim().replace(/\s+/g, ' ')).filter((v) => v && v !== '–' && v !== '-').map((v) => (/^(eps|epsilon|λ)$/i.test(v) ? EPS : v.replace(/\s/g, ''))).sort();
  K.cellRight = function (kind, want, got) {
    if (kind === 'set') return sameSet(want, got);
    if (kind === 'rhs') { const A = rhsSet(want), B = rhsSet(got); return A.length === B.length && A.every((v, i) => v === B[i]); }
    return String(want).trim().replace(/\s+/g, ' ').toLowerCase() === String(got === undefined ? '' : got).trim().replace(/\s+/g, ' ').toLowerCase();
  };

  K.kinds.table = {
    check(x, a) {
      a = a || {};
      const S = K.tableSpec(x);
      const keys = Object.keys(S.expected);
      const cells = {};
      let wrong = 0, empty = 0;
      for (const k of keys) {
        const got = a[k] === undefined ? '' : String(a[k]);
        if (!got.trim() && S.expected[k] !== '') empty++;
        cells[k] = K.cellRight(S.kind, S.expected[k], got);
        if (!cells[k]) wrong++;
      }
      if (!wrong) return { ok: true, cells, message: 'Every one of the ' + keys.length + ' cells is right.' };
      const details = [];
      if (empty) details.push(K.plural(empty, 'cell is', 'cells are') + ' still empty.');
      if (S.kind === 'set') details.push('A set is written like a, b, ε; leave a cell empty (or write ∅) for the empty set.');
      if (S.kind === 'rhs') details.push('Write the right side of the rule for each cell, like a S b or ε; separate two rules with |.');
      return { ok: false, cells, message: K.plural(wrong, 'cell is', 'cells are') + ' not right yet (marked in red).', details };
    },
  };
})();
