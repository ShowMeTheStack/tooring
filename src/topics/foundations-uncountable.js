// Uncountable sets: Cantor's diagonal argument on a table the student fills in, the same argument for the
// power set (D = {x : x ∉ f(x)} is no f(x)), and the counting argument for languages: descriptions are
// finite strings and can be listed, languages cannot, so most languages have no finite description.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found, Geo = T.geom;
  const H = K.rel;

  T.family({ id: 'found-uncountable', part: 'foundations', order: 60, title: 'Uncountable sets and diagonalisation', blurb: 'Some sets are too big to list. Given any list, the diagonal argument builds an element that differs from every entry in at least one place, so the list missed it.' });

  // ---------------------------------------------------------------------------------------------------
  // Cantor's diagonal on a table
  // ---------------------------------------------------------------------------------------------------
  const flip = (v) => (v === 0 ? 1 : v === 1 ? 0 : v === 5 ? 4 : 5);
  T.topic({
    id: 'cantor-diagonal', family: 'found-uncountable', order: 10, title: 'Cantor\'s diagonal argument',
    blurb: 'Write any list of infinite 0/1 sequences, one per row. Walk down the diagonal and flip each digit: the new sequence differs from row i at place i, so it is in no row.',
    inputs: [{ id: 'rows', kind: 'list', label: 'Rows (digits; row i needs at least i + 1 of them)', def: ['0110100', '1011001', '0000000', '1110111', '0101010', '1100110'], min: 2, max: 7, check: (v) => { for (let i = 0; i < v.length; i++) { if (!/^[0-9]+$/.test(v[i])) return 'Rows: digits only, like 0110'; if (v[i].length < v.length) return 'Rows: row ' + i + ' needs at least ' + v.length + ' digits, one for each row, so the diagonal is defined'; if (v[i].length > 8) return 'Rows: at most 8 digits each, so the table stays readable'; } return null; } }],
    presets: [
      { label: 'Six bit sequences', values: { rows: ['0110100', '1011001', '0000000', '1110111', '0101010', '1100110'] } },
      { label: 'Row i has a 1 only at place i', values: { rows: ['10000', '01000', '00100', '00010', '00001'] } },
      { label: 'A list with 000… and 111… in it', values: { rows: ['00000', '11111', '01010', '10101', '00110'] } },
      { label: 'Decimals in [0, 1]: change 5 ↔ 4', values: { rows: ['141592', '718281', '414213', '577215', '302585', '693147'] } },
    ],
    counters: [{ id: 'diag', label: 'places flipped' }, { id: 'beaten', label: 'rows ruled out' }],
    run(inp) {
      const rows = inp.rows.map((r) => [...r].map(Number));
      const n = rows.length, cols = Math.max(...rows.map((r) => r.length));
      const res = F.diagonal(rows, n, flip);
      const F2 = new T.Frames(['diag', 'beaten']);
      const CW = 42;
      const tableAt = (hot, bad, good) => {
        const hs = new Set((hot || []).map((p) => p.join(','))), bs = new Set((bad || []).map((p) => p.join(','))), gs = new Set((good || []).map((p) => p.join(',')));
        return K.table.draw({ rows: rows.map((r) => r.map(String).concat(['⋯'])), rowHead: rows.map((_, i) => 's' + i), colHead: [...Array(cols).keys()].map(String).concat(['']), corner: 'place', cw: CW, ch: 38, mono: true, size: 17, prefix: 'cd',
          cls: (r, c) => (c === cols ? 'elide' : bs.has(r + ',' + c) ? 'bad' : hs.has(r + ',' + c) ? 'hot' : gs.has(r + ',' + c) ? 'act' : r === c ? 'mark' : '') });
      };
      const t0 = tableAt();
      const dy = t0.box.y + t0.box.h + 26;
      const cx = (c) => t0.cellBox(0, c).x;
      const dRow = (k, opts) => {
        opts = opts || {};
        const items = [{ key: 'd:lbl', kind: 'text', x: cx(0) - 12, y: dy + 25, text: 'd', anchor: 'end', cls: 'strong', size: 17 }];
        for (let i = 0; i < k; i++) items.push({ key: 'd:' + i, kind: 'cell', x: cx(i), y: dy, w: CW, h: 38, text: String(res.diag[i]), cls: 'mono ' + ((opts.bad || []).includes(i) ? 'bad' : 'good'), size: 17, enter: 'from', src: 'cd:' + i + ',' + i, pick: true });
        if (k === n) items.push({ key: 'd:more', kind: 'text', x: cx(n) + 6, y: dy + 25, text: '⋯', cls: 'strong', size: 16 });
        return items;
      };
      const bits = rows.every((r) => r.every((v) => v < 2));
      F2.add({ items: tableAt().items.concat(dRow(0)), say: 'Suppose someone claims this list holds every infinite sequence of ' + (bits ? 'bits' : 'digits') + ': s0, s1, s2, … (each row goes on for ever; we see its start). We build a sequence d that is not in the list.', hl: { def: ['0'] } });
      for (let i = 0; i < n; i++) {
        F2.add({ items: tableAt([[i, i]]).items.concat(dRow(i)), say: 'Place ' + i + ' of row s' + i + ' is ' + rows[i][i] + '.', hl: { def: ['1'] }, meta: { ask: i < 2, now: String(res.diag[i]), opts: bits ? ['0', '1'] : [String(rows[i][i]), String(res.diag[i])].sort() } });
        F2.count('diag');
        F2.add({ items: tableAt([[i, i]]).items.concat(dRow(i + 1)), say: 'So d gets ' + res.diag[i] + ' at place ' + i + (bits ? ', the opposite' : ' (5 becomes 4, anything else becomes 5)') + '. Whatever comes later, d ≠ s' + i + '.', hl: { def: ['1', '2'] } });
      }
      const show = Math.min(n, 3);
      for (let i = 0; i < show; i++) {
        F2.count('beaten');
        F2.add({ items: tableAt(null, [[i, i]], [...Array(cols).keys()].map((c) => [i, c]).filter(([, c]) => c !== i)).items.concat(dRow(n, { bad: [i] })), say: 'Is d = s' + i + '? Compare them at place ' + i + ': s' + i + ' has ' + rows[i][i] + ', d has ' + res.diag[i] + '. They differ, so no.', hl: { def: ['2'] }, meta: i === 1 ? { pickD: ['cd:1,1', 'd:1'] } : {} });
      }
      F2.set('beaten', n);
      F2.add({ items: tableAt(null, [...Array(n).keys()].map((i) => [i, i])).items.concat(dRow(n, { bad: [...Array(n).keys()] })), say: 'The same holds for every row: d differs from s' + 'i at place i. So d is in no row, and the list was not complete after all. No list can be: the infinite ' + (bits ? 'bit sequences' : 'decimals') + ' are uncountable.', hl: { def: ['3'] }, mark: 'missed' });
      F2.add({ items: tableAt(null, [...Array(n).keys()].map((i) => [i, i])).items.concat(dRow(n, { bad: [...Array(n).keys()] })), say: 'Adding d to the list does not help: the new list has a new diagonal and a new missing sequence. The argument works against every list, not just this one.' + (bits ? '' : ' Using 4 and 5 avoids 0.4999… = 0.5000…, two spellings of one number.'), hl: { def: ['3'] } });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The diagonal', text: ['a list s₀, s₁, s₂, … of infinite sequences', 'd(i) = the opposite of sᵢ(i)', 'd ≠ sᵢ, because d(i) ≠ sᵢ(i)', 'so d is in no list: the set is uncountable'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, pick: 'option', options: (fr, i) => fr[i].meta.opts, ask: 'Which digit does d get at this place?', answer: (fr, i) => fr[i].meta.now, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.pickD, pick: 'item', ask: 'Where is d sure to differ from s1? Click the place.', answer: (fr, i) => fr[i + 1].meta.pickD, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does d differ from row 7 of the list?', options: ['It might not', 'Because d was made different from row 7 at place 7', 'Because row 7 has more 1s', 'Because d is longer'], answer: 1, why: 'That is the whole construction: place i of d is chosen to disagree with row i.' },
      { q: 'Apply the same idea to a list of all finite bit strings. What goes wrong?', options: ['Nothing: they are uncountable too', 'A finite string has no place i for large i, and the diagonal sequence is infinite, so it is not a finite string', 'The flip is not defined'], answer: 1, why: 'The finite strings are countable (shortlex order lists them). The diagonal builds an infinite sequence, which was never supposed to be on that list.' },
      { q: 'The list is extended by putting d first. What happens?', options: ['Now the list is complete', 'The diagonal of the new list gives another missing sequence', 'The argument stops working'], answer: 1, why: 'The argument takes any list as input, so no list escapes it.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // The power set: D = {x : x ∉ f(x)}
  // ---------------------------------------------------------------------------------------------------
  const parseSub = (s) => (s === '' || s === '-' || s === '∅' || s === '{}' ? [] : [...s.replace(/[{},\s]/g, '')]);
  T.topic({
    id: 'cantor-powerset', family: 'found-uncountable', order: 20, title: 'No set is as big as its power set',
    blurb: 'Give each element x a subset f(x). Collect the elements that are not in their own subset: that set D differs from every f(x) at x, so no element is matched with D.',
    inputs: [
      { id: 'A', kind: 'list', label: 'A (single symbols)', def: ['a', 'b', 'c', 'd'], min: 1, max: 5, check: (v) => (v.some((x) => [...x].length !== 1) ? 'A: one symbol per element' : new Set(v).size !== v.length ? 'A: an element is listed twice' : null) },
      { id: 'f', kind: 'list', label: 'f(x) for each x in order (∅ or - for empty)', def: ['ab', '-', 'acd', 'b'], check: (v, inp) => { if (v.length !== (inp.A || []).length) return 'f: give one subset for each element of A, in order'; for (const s of v) for (const c of parseSub(s)) if (!inp.A.includes(c)) return 'f: ' + c + ' is not in A'; return null; } },
    ],
    presets: [
      { label: 'Four elements', values: { A: ['a', 'b', 'c', 'd'], f: ['ab', '-', 'acd', 'b'] } },
      { label: 'f(x) = {x}: D = ∅', values: { A: ['1', '2', '3'], f: ['1', '2', '3'] } },
      { label: 'f(x) = ∅ for every x: D = A', values: { A: ['p', 'q', 'r'], f: ['-', '-', '-'] } },
      { label: 'Five elements, D in the middle', values: { A: ['a', 'b', 'c', 'd', 'e'], f: ['bc', 'b', 'abcde', '-', 'ad'] } },
    ],
    counters: [{ id: 'looked', label: 'elements examined' }, { id: 'inD', label: 'in D' }],
    run(inp) {
      const A = inp.A, f = inp.f.map(parseSub);
      const fx = (x) => f[A.indexOf(x)];
      const res = F.cantorSet(A, fx);
      const F2 = new T.Frames(['looked', 'inD']);
      const STEP = 58, CW = 34, bagX = 90, bagW = A.length * CW + 20;
      const ry = (i) => i * STEP;
      const colX = (y) => bagX + 10 + A.indexOf(y) * CW;
      const dY = ry(A.length) + 30;
      const scene = (o) => {
        o = o || {};
        const items = [];
        A.forEach((x, i) => {
          items.push({ key: 'x:' + x, kind: 'state', x: 0, y: ry(i) + 21, r: 20, w: 40, h: 40, rx: 20, text: x, cls: 'state' + (o.now === x ? ' hot' : '') });
          items.push({ key: 'bag:' + x, kind: 'region', x: bagX, y: ry(i), w: bagW, h: 42, cls: 'r' + (i % 6) + (o.now === x ? ' hot' : ''), rx: 12 });
          items.push({ key: 'ar:' + x, kind: 'edge', from: 'x:' + x, to: { x: bagX - 2, y: ry(i) + 21 }, cls: o.now === x ? 'hot' : '' });
          for (const y of fx(x)) items.push({ key: 'm:' + x + ':' + y, kind: 'cell', x: colX(y) + 2, y: ry(i) + 7, w: CW - 4, h: 28, text: y, cls: 'mono' + (o.now === x && y === x ? ' good' : o.diff && y === x ? ' bad' : ''), size: 14, rx: 8 });
          if ((o.now === x || o.diff) && !fx(x).includes(x)) items.push({ key: 'gh:' + x, kind: 'cell', x: colX(x) + 2, y: ry(i) + 7, w: CW - 4, h: 28, text: x, cls: 'mono gone' + (o.diff ? ' bad' : ''), size: 14, rx: 8 });
          if (!fx(x).length) items.push({ key: 'emp:' + x, kind: 'text', x: bagX + bagW + 10, y: ry(i) + 26, text: '∅', cls: 'strong', size: 15 });
        });
        items.push({ key: 'Dlbl', kind: 'text', x: 0, y: dY + 26, text: 'D', anchor: 'middle', cls: 'big' });
        items.push({ key: 'bag:D', kind: 'region', x: bagX, y: dY, w: bagW, h: 42, cls: 'frame' + (o.Dhot ? ' hot' : ''), rx: 12 });
        for (const y of o.D || []) items.push({ key: 'D:' + y, kind: 'cell', x: colX(y) + 2, y: dY + 7, w: CW - 4, h: 28, text: y, cls: 'mono hot', size: 14, rx: 8, enter: 'from', src: 'x:' + y });
        if (o.D && !o.D.length && o.Dhot) items.push({ key: 'Demp', kind: 'text', x: bagX + bagW + 10, y: dY + 26, text: '∅', cls: 'strong', size: 15 });
        return items;
      };
      F2.add({ items: scene(), say: 'Each element x of A points to a subset f(x), drawn as a box with its members in fixed columns. If every subset of A were some f(x), the power set would be no bigger than A. Watch it fail.', hl: { def: ['0'] } });
      const D = [];
      res.trace.filter((s) => s.kind === 'diag').forEach((s, k) => {
        F2.add({ items: scene({ now: s.x, D: D.slice() }), say: 'Look at ' + s.x + ' and its own box f(' + s.x + ') = ' + (s.fx.length ? '{' + s.fx.join(', ') + '}' : '∅') + '. Is ' + s.x + ' inside?', hl: { def: ['1'] }, meta: { ask: k < 2, yes: !s.inside } });
        if (!s.inside) D.push(s.x);
        F2.count('looked').set('inD', D.length);
        F2.add({ items: scene({ now: s.x, D: D.slice() }), say: s.say, hl: { def: ['1', '2'] } });
      });
      F2.add({ items: scene({ D: D.slice(), Dhot: true, diff: true }), say: 'D = ' + (D.length ? '{' + D.join(', ') + '}' : '∅') + '. In each row, the red place is where D and f(x) disagree about x itself: x is in exactly one of them.', hl: { def: ['2'] } });
      F2.add({ items: scene({ D: D.slice(), Dhot: true, diff: true }), say: 'So D is no f(x), and nothing points to it: f misses a subset. This works for every f and every set, finite or infinite, so P(A) is always strictly bigger than A. For A = N, P(N) is uncountable.', hl: { def: ['3'] }, mark: 'missed' });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Cantor\'s theorem', text: ['f : A → P(A), any function', 'D = { x ∈ A : x ∉ f(x) }', 'D ≠ f(x): they disagree about x', 'so f is not onto, and |A| < |P(A)|'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, pick: 'option', options: ['Yes', 'No'], ask: 'Will this element go into D?', answer: (fr, i) => (fr[i].meta.yes ? 'Yes' : 'No'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'If D = f(x) for some x, is x in D?', options: ['Yes', 'No', 'Either answer leads to a contradiction'], answer: 2, why: 'If x ∈ D then x ∉ f(x) = D; if x ∉ D then x ∈ f(x) = D. So no such x exists.' },
      { q: 'A has 3 elements. How many subsets can f possibly hit?', options: ['All 8', 'At most 3, so at least 5 are missed', 'Exactly 3 always'], answer: 1, why: 'Three arrows reach at most three of the 8 subsets; the diagonal names one that is always missed.' },
      { q: 'What does the theorem say about N and P(N)?', options: ['Same size', 'P(N) is uncountable', 'P(N) is finite'], answer: 1, why: 'No f : N → P(N) is onto, so the subsets of N cannot be listed.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Descriptions are countable, languages are not
  // ---------------------------------------------------------------------------------------------------
  const okRegex = (r) => { const c = T.RE.check(r); if (!c.ok) return 'Descriptions: "' + r + '" is not a regular expression: ' + c.error; const al = T.RE.alphabet(c.ast); if (al.some((s) => s !== 'a' && s !== 'b')) return 'Descriptions: use only the symbols a and b'; if ([...r].length > 10) return 'Descriptions: at most 10 characters each'; return null; };
  T.topic({
    id: 'counting-languages', family: 'found-uncountable', order: 30, title: 'Most languages have no description',
    blurb: 'A description (a regex, a grammar, a program) is a finite string, so all descriptions can be listed. Diagonalise against the list and you get a language none of them describes.',
    inputs: [{ id: 'ds', kind: 'list', label: 'Descriptions (regexes over a, b)', def: ['a*', 'b', '(ab)*', 'a|b', 'ε', 'a*b*'], min: 3, max: 7, check: (v) => { for (const r of v) { const e = okRegex(r === '' ? 'ε' : r); if (e) return e; } return null; } }],
    presets: [
      { label: 'Six regexes', values: { ds: ['a*', 'b', '(ab)*', 'a|b', 'ε', 'a*b*'] } },
      { label: 'Including ∅ and (a|b)*', values: { ds: ['∅', '(a|b)*', 'aa', 'b*', 'ab|ba'] } },
      { label: 'Three descriptions', values: { ds: ['a', 'b*', '(a|b)(a|b)'] } },
    ],
    counters: [{ id: 'rows', label: 'descriptions listed' }, { id: 'diag', label: 'diagonal entries' }],
    run(inp) {
      const ds = inp.ds.map((r) => (r === '' ? 'ε' : r));
      const n = ds.length;
      const ws = F.sigmaStar(['a', 'b'], 3).slice(0, n);
      const M = ds.map((r) => { const m = T.RE.matcher(r); return ws.map((w) => (m(w) ? 1 : 0)); });
      const F2 = new T.Frames(['rows', 'diag']);
      const CW = 46;
      const narrow = H.narrow();
      const tbl = (shown, o) => {
        o = o || {};
        return K.table.draw({ rows: M.map((r, i) => (i < shown ? r.map(String) : r.map(() => ''))).map((r) => r.concat(['⋯'])), rowHead: ds.map((d, i) => 'd' + i + ': ' + d), colHead: ws.map(F.show).concat(['']), corner: 'w ∈ L(dᵢ)?', cw: CW, ch: 36, mono: true, size: 16, prefix: 'cl',
          cls: (r, c, v) => (c === n ? 'elide' : (o.bad || []).includes(r) && r === c ? 'bad' : o.hot === r && r === c ? 'hot' : r === c ? 'mark' : v === '1' ? 'one' : 'empty') });
      };
      const t0 = tbl(n);
      const dy = t0.box.y + t0.box.h + 24;
      const diagRow = (k, bad) => {
        const items = [{ key: 'ld:lbl', kind: 'text', x: t0.cellBox(0, 0).x - 12, y: dy + 24, text: 'L_diag', anchor: 'end', cls: 'strong', size: 15 }];
        for (let i = 0; i < k; i++) items.push({ key: 'ld:' + i, kind: 'cell', x: t0.cellBox(0, i).x, y: dy, w: CW, h: 36, text: String(1 - M[i][i]), cls: 'mono ' + (bad ? 'bad' : 'good'), size: 16, enter: 'from', src: 'cl:' + i + ',' + i });
        return items;
      };
      F2.add({ items: tbl(0).items.concat(diagRow(0)), say: 'A description is a finite string of symbols, so the descriptions can be listed in shortlex order: d0, d1, d2, … Here are a few regexes standing in for that list. The columns are all strings over {a, b} in shortlex order: ε, a, b, aa, …', hl: { def: ['0'] } });
      for (let i = 0; i < n; i++) {
        const lang = ws.filter((_, j) => M[i][j]);
        F2.count('rows');
        F2.add({ items: tbl(i + 1).items.concat(diagRow(0)), say: 'Row d' + i + ' = ' + ds[i] + ': a 1 under each string it matches. Of the strings shown, L(' + ds[i] + ') contains ' + (lang.length ? lang.map(F.show).join(', ') : 'none') + '.', hl: { def: ['1'] } });
      }
      for (let i = 0; i < n; i++) {
        F2.count('diag');
        F2.add({ items: tbl(n, { hot: i }).items.concat(diagRow(i + 1)), say: 'String ' + F.show(ws[i]) + ' is ' + (M[i][i] ? 'in' : 'not in') + ' L(d' + i + '), so put it ' + (M[i][i] ? 'out of' : 'into') + ' L_diag.', hl: { def: ['2'] }, meta: i === 0 ? { ask: true, v: String(1 - M[0][0]) } : {} });
      }
      const ld = ws.filter((_, i) => !M[i][i]);
      F2.add({ items: tbl(n, { bad: [...Array(n).keys()] }).items.concat(diagRow(n, true)), say: 'L_diag (so far: ' + (ld.length ? ld.map(F.show).join(', ') : 'nothing') + ') disagrees with L(dᵢ) about the string wᵢ, for every i. So no description on the full list describes L_diag, and the full list holds every description there is.', hl: { def: ['2', '3'] }, mark: 'undescribed' });
      // the count: descriptions of length ≤ k against languages of strings of length ≤ k
      const rows = [1, 2, 3, 4].map((k) => { let d = 0; for (let i = 0; i <= k; i++) d += Math.pow(8, i); const s = Math.pow(2, k + 1) - 1; return [String(k), String(d), '2^' + s + (s <= 15 ? ' = ' + Math.pow(2, s) : '')]; });
      const ct = K.table.draw({ rows, colHead: ['k', 'regexes ≤ k', 'languages ⊆ Σ^{≤k}'], x: narrow ? t0.box.x : t0.box.x + t0.box.w + 40, y: narrow ? dy + 70 : t0.box.y, prefix: 'cn', size: 15, mono: true, cls: (r, c) => (c === 2 && r >= 1 ? 'hot' : '') });
      F2.add({ items: tbl(n, { bad: [...Array(n).keys()] }).items.concat(diagRow(n, true), ct.items), say: 'Counting tells the same story. Regexes of length ≤ k use 8 symbols, so there are at most 1 + 8 + … + 8^k of them, while the strings of length ≤ k can be chosen in 2^(2^(k+1) − 1) ways. The languages win, and by more each time.', hl: { def: ['3'] } });
      F2.add({ items: tbl(n, { bad: [...Array(n).keys()] }).items.concat(diagRow(n, true), ct.items), say: 'Descriptions are countable; languages over {a, b} are subsets of the countable Σ*, so there are uncountably many (Cantor). Whatever kind of finite description you choose, almost every language has none.', hl: { def: ['3'] } });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The counting argument', text: ['descriptions: finite strings, listed d₀, d₁, …', 'strings of Σ*: listed w₀, w₁, … in shortlex order', 'L_diag = { wᵢ : wᵢ ∉ L(dᵢ) }', 'L_diag ≠ L(dᵢ) for every i: no description'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, pick: 'option', options: ['0', '1'], ask: 'Will L_diag contain this string (1) or not (0)?', answer: (fr, i) => fr[i].meta.v, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why are there only countably many regular expressions?', options: ['Each is a finite string over a finite set of symbols, and those can be listed', 'Each describes a finite language', 'There are only finitely many'], answer: 0, why: 'List them by length and then alphabetically: every regex appears at some finite position.' },
      { q: 'How many languages over {a, b} are there?', options: ['Countably many', 'Uncountably many: one for each subset of Σ*'], answer: 1, why: 'Σ* is countably infinite, and its power set is uncountable by Cantor\'s theorem.' },
      { q: 'What does the argument show about programs?', options: ['Every language is decided by some program', 'Most languages are decided by no program, since programs are finite texts', 'Programs are uncountable'], answer: 1, why: 'Programs, like regexes, can be listed; the diagonal language escapes all of them.' },
    ],
  });
})();
