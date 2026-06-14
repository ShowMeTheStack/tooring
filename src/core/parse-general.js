// General parsing: CYK on Chomsky normal form, Earley on any context-free grammar, backtracking
// recursive descent, and packrat parsing of PEGs (ordered choice) as a contrast.
// Inputs are words (arrays of terminals) or strings read with T.grammar.input.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const Gr = T.grammar;
  const { show, showProd, showRhs, EPS } = Gr;

  // ---------- CYK ----------
  // cells[len][i] holds the nonterminals deriving w[i .. i+len), each with every way it got there:
  // { prod, terminal } on the bottom row, { prod, split, B, C } above (B over the first `split` symbols).
  // opts.convert: put the grammar into Chomsky normal form first (the result carries the new grammar).
  function cyk(G, w0, opts) {
    opts = opts || {};
    let H = G, trace = [];
    if (!T.cfg.isCNF(G)) {
      if (!opts.convert) throw new Error('CYK needs a grammar in Chomsky normal form (pass { convert: true })');
      H = T.cfg.toCNF(G).grammar;
      trace.push({ kind: 'convert', grammar: H, say: 'Put the grammar into Chomsky normal form first.' });
    }
    const w = Gr.input(H, w0), n = w.length;
    const cells = [null];
    const get = (len, i) => cells[len][i];
    if (n === 0) {
      const p = H.productions.find((q) => q.A === H.start && !q.rhs.length);
      trace.push({ kind: p ? 'accept' : 'reject', say: p ? 'The input is empty and ' + showProd(H, p) + ' is a rule: accept.' : 'The input is empty and there is no rule ' + H.start + ' → ε: reject.' });
      return { grammar: H, word: w, accepted: !!p, cells, trace, tree: p ? { sym: H.start, prod: p.id, children: [] } : null, count: p ? 1 : 0 };
    }
    for (let len = 1; len <= n; len++) cells.push(Array.from({ length: n - len + 1 }, () => new Map()));
    const add = (len, i, A, src) => { const m = get(len, i); if (!m.has(A)) m.set(A, []); m.get(A).push(src); };
    for (let i = 0; i < n; i++) {
      const adds = [];
      for (const p of H.productions) if (p.rhs.length === 1 && p.rhs[0] === w[i]) { add(1, i, p.A, { prod: p.id, terminal: w[i] }); adds.push(p.A); }
      trace.push({ kind: 'cell', i, len: 1, adds, say: 'Cell (' + (i + 1) + ', ' + (i + 1) + ') for ' + w[i] + ': ' + (adds.length ? '{' + adds.join(', ') + '}, from ' + adds.map((A) => A + ' → ' + w[i]).join(', ') : 'no rule produces ' + w[i]) + '.' });
    }
    const pairRules = H.productions.filter((p) => p.rhs.length === 2);
    for (let len = 2; len <= n; len++) for (let i = 0; i + len <= n; i++) {
      const adds = [];
      for (let k = 1; k < len; k++) {
        const L = get(k, i), R = get(len - k, i + k), found = [];
        for (const p of pairRules) if (L.has(p.rhs[0]) && R.has(p.rhs[1])) {
          add(len, i, p.A, { prod: p.id, split: k, B: p.rhs[0], C: p.rhs[1] });
          found.push({ A: p.A, B: p.rhs[0], C: p.rhs[1], prod: p.id });
          if (!adds.includes(p.A)) adds.push(p.A);
        }
        trace.push({ kind: 'split', i, len, split: k, left: [...L.keys()], right: [...R.keys()], found,
          say: 'Split ' + show(w.slice(i, i + len)) + ' as ' + show(w.slice(i, i + k)) + ' · ' + show(w.slice(i + k, i + len)) + ': {' + [...L.keys()].join(', ') + '} × {' + [...R.keys()].join(', ') + '}' +
            (found.length ? ' gives ' + found.map((f) => f.A + ' (' + f.A + ' → ' + f.B + ' ' + f.C + ')').join(', ') : ' gives nothing') + '.' });
      }
      trace.push({ kind: 'cell', i, len, adds, say: 'Cell (' + (i + 1) + ', ' + (i + len) + ') = {' + adds.join(', ') + '}.' });
    }
    const top = get(n, 0), accepted = top.has(H.start);
    trace.push({ kind: accepted ? 'accept' : 'reject', say: H.start + (accepted ? ' is' : ' is not') + ' in the top cell, so ' + show(w) + (accepted ? ' is' : ' is not') + ' in the language.' });
    // number of trees for each entry (CNF has no cycles, so it is finite)
    const memo = new Map();
    const count = (A, i, len) => {
      const k = A + ' ' + i + ' ' + len; if (memo.has(k)) return memo.get(k);
      let c = 0;
      for (const s of get(len, i).get(A) || []) c += s.split ? count(s.B, i, s.split) * count(s.C, i + s.split, len - s.split) : 1;
      memo.set(k, c); return c;
    };
    const build = (A, i, len, pick) => {
      const s = (get(len, i).get(A) || [])[0];
      if (s.terminal !== undefined) return { sym: A, prod: s.prod, children: [Gr.leaf(s.terminal)], cell: [len, i] };
      return { sym: A, prod: s.prod, cell: [len, i], children: [build(s.B, i, s.split), build(s.C, i + s.split, len - s.split)] };
    };
    const tree = accepted ? build(H.start, 0, n) : null;
    // the cells as plain arrays for drawing: cells[len][i] = [{ A, sources }]
    const plain = cells.map((row) => row && row.map((m) => [...m].map(([A, sources]) => ({ A, sources }))));
    return { grammar: H, word: w, accepted, cells: plain, trace, tree, count: accepted ? count(H.start, 0, n) : 0 };
  }

  // ---------- Earley ----------
  // Items [A → α • β, origin] in chart sets 0..n. Each item lists every way it was made:
  //   { kind: 'init' }, { kind: 'predict', by: [set, item] },
  //   { kind: 'scan', pred: [set, item] }, { kind: 'complete', pred: [set, item], child: [set, item] }.
  // ε is handled exactly: when B finishes with an empty span in set j, items in set j waiting for B are
  // advanced whether they were added before or after that moment.
  function showItem(G, it) {
    const p = G.productions[it.prod];
    return '[' + p.A + ' → ' + [...p.rhs.slice(0, it.dot), '•', ...p.rhs.slice(it.dot)].join(' ') + ', ' + it.origin + ']';
  }
  function earley(G, w0, opts) {
    opts = Object.assign({ maxItems: 200000, maxTrees: 2 }, opts || {});
    const w = Gr.input(G, w0), n = w.length, N = Gr.info(G).N, byA = Gr.info(G).byA;
    const sets = Array.from({ length: n + 1 }, () => ({ items: [], index: new Map(), empty: new Map() }));
    const trace = [];
    let total = 0;
    const lkey = (l) => l.kind + (l.pred ? ':' + l.pred : '') + (l.child ? '/' + l.child : '') + (l.by ? '<' + l.by : '');
    function add(j, prod, dot, origin, link, why) {
      const S = sets[j], key = prod + '.' + dot + '.' + origin;
      let idx = S.index.get(key);
      if (idx === undefined) {
        if (++total > opts.maxItems) throw new Error('Earley chart too large');
        idx = S.items.length;
        S.items.push({ prod, dot, origin, links: [link] });
        S.index.set(key, idx);
        trace.push({ kind: link.kind, set: j, item: idx, prod, dot, origin, link, say: why(showItem(G, S.items[idx])) });
      } else {
        const it = S.items[idx];
        if (!it.links.some((l) => lkey(l) === lkey(link))) {
          it.links.push(link);
          if (link.kind !== 'predict') trace.push({ kind: 'link', set: j, item: idx, link, say: showItem(G, it) + ' in set ' + j + ' can also be reached another way (' + link.kind + ').' });
        }
      }
      return idx;
    }
    for (const p of byA.get(G.start) || []) add(0, p.id, 0, 0, { kind: 'init' }, (s) => 'Start: add ' + s + ' to set 0.');
    for (let j = 0; j <= n; j++) {
      const S = sets[j];
      trace.push({ kind: 'set', set: j, say: 'Set ' + j + (j < n ? ', next input symbol ' + w[j] : ', at the end of the input') + '.' });
      for (let q = 0; q < S.items.length; q++) {
        const it = S.items[q], p = G.productions[it.prod];
        if (it.dot < p.rhs.length) {
          const X = p.rhs[it.dot];
          if (N.has(X)) {
            for (const r of byA.get(X)) add(j, r.id, 0, j, { kind: 'predict', by: [j, q] }, (s) => 'Predict: ' + showItem(G, it) + ' expects ' + X + ', so add ' + s + '.');
            for (const c of S.empty.get(X) || []) add(j, it.prod, it.dot + 1, it.origin, { kind: 'complete', pred: [j, q], child: [j, c] },
              (s) => 'Complete: ' + X + ' already derived ε here (' + showItem(G, S.items[c]) + '), so add ' + s + '.');
          } else if (j < n && w[j] === X) {
            add(j + 1, it.prod, it.dot + 1, it.origin, { kind: 'scan', pred: [j, q] }, (s) => 'Scan: ' + X + ' matches input symbol ' + (j + 1) + ', so add ' + s + ' to set ' + (j + 1) + '.');
          }
        } else {
          const B = p.A, O = sets[it.origin];
          if (it.origin === j) { if (!S.empty.has(B)) S.empty.set(B, []); S.empty.get(B).push(q); }
          for (let r = 0; r < O.items.length; r++) {
            const w8 = O.items[r], pr = G.productions[w8.prod];
            if (w8.dot < pr.rhs.length && pr.rhs[w8.dot] === B)
              add(j, w8.prod, w8.dot + 1, w8.origin, { kind: 'complete', pred: [it.origin, r], child: [j, q] },
                (s) => 'Complete: ' + showItem(G, it) + ' finished, so ' + showItem(G, w8) + ' from set ' + it.origin + ' moves on: ' + s + '.');
          }
        }
      }
    }
    const finals = sets[n].items.map((it, i) => [it, i]).filter(([it]) => it.dot === G.productions[it.prod].rhs.length && it.origin === 0 && G.productions[it.prod].A === G.start);
    const accepted = finals.length > 0;
    trace.push({ kind: accepted ? 'accept' : 'reject', items: finals.map(([, i]) => i),
      say: accepted ? 'Set ' + n + ' holds ' + finals.map(([it]) => showItem(G, it)).join(', ') + ': accept.' : 'No completed ' + G.start + '-item with origin 0 in set ' + n + ': reject.' });
    // trees, following the links; an item may not be revisited along one branch (cycles A ⇒+ A)
    // Trees by following the links, eagerly and capped at maxTrees. The same item may appear at most twice
    // along one branch, so a cycle A ⇒+ A shows up as a second tree instead of looping.
    const max = opts.maxTrees, path = new Map();
    function kids(j, q) {          // child lists for the part of the rule before the dot
      const it = sets[j].items[q];
      if (it.dot === 0) return [[]];
      const key = j + '.' + q, c = path.get(key) || 0, out = [];
      if (c >= 2) return out;
      path.set(key, c + 1);
      for (const l of it.links) {
        if (out.length >= max) break;
        if (l.kind === 'scan') {
          const X = G.productions[it.prod].rhs[it.dot - 1];
          for (const left of kids(l.pred[0], l.pred[1])) { if (out.length >= max) break; out.push(left.concat([Gr.leaf(X)])); }
        } else if (l.kind === 'complete') {
          const lefts = kids(l.pred[0], l.pred[1]);
          if (!lefts.length) continue;
          const subs = node(l.child[0], l.child[1]);
          for (const left of lefts) for (const t of subs) { if (out.length >= max) break; out.push(left.concat([t])); }
        }
      }
      path.set(key, c);
      return out;
    }
    function node(j, q) {
      const it = sets[j].items[q], p = G.productions[it.prod];
      return kids(j, q).map((ch) => ({ sym: p.A, prod: p.id, children: ch }));
    }
    const trees = [];
    for (const [, i] of finals) { for (const t of node(n, i)) if (trees.length < max) trees.push(JSON.parse(JSON.stringify(t))); }
    const plain = sets.map((S) => S.items.map((it) => ({ prod: it.prod, dot: it.dot, origin: it.origin, links: it.links, text: showItem(G, it) })));
    return { word: w, accepted, sets: plain, trace, tree: trees[0] || null, trees, ambiguous: trees.length > 1 };
  }

  // ---------- backtracking recursive descent ----------
  // Each nonterminal tries its rules in order; every way a call can end is offered back to the caller, so
  // a later failure backtracks into earlier choices. Left recursion would loop forever, so it is refused.
  // opts.limited: return only the first way each call succeeds (no backtracking into a finished call),
  // which shows how a simple recursive-descent parser can wrongly reject.
  function recursiveDescent(G, w0, opts) {
    opts = Object.assign({ maxSteps: 20000, limited: false }, opts || {});
    const w = Gr.input(G, w0), N = Gr.info(G).N, byA = Gr.info(G).byA, trace = [];
    const lr = T.cfg.leftRecursive(G);
    if (lr.length) {
      trace.push({ kind: 'refuse', nonterminals: lr.map((x) => x.A), say: lr.map((x) => x.A).join(', ') + (lr.length > 1 ? ' are' : ' is') + ' left-recursive: a call would call itself again without reading anything, forever. Remove the left recursion first.' });
      return { word: w, accepted: false, refused: true, tree: null, trace, steps: 0 };
    }
    let steps = 0, gaveUp = false;
    const tick = () => { if (++steps > opts.maxSteps) { gaveUp = true; throw new Error('steps'); } };
    const note = (st) => { if (trace.length < opts.maxSteps) trace.push(st); };
    function* call(A, i, depth) {
      tick();
      note({ kind: 'call', A, pos: i, depth, say: 'Call ' + A + ' at position ' + (i + 1) + (i < w.length ? ' (next symbol ' + w[i] + ')' : ' (end of input)') + '.' });
      let any = false;
      for (const p of byA.get(A)) {
        note({ kind: 'try', A, prod: p.id, pos: i, depth, say: 'Try ' + showProd(G, p) + '.' });
        for (const r of seq(p.rhs, 0, i, depth)) {
          any = true;
          const t = { sym: A, prod: p.id, children: r.kids };
          note({ kind: 'return', A, prod: p.id, from: i, to: r.end, depth, say: A + ' succeeds on ' + show(w.slice(i, r.end)) + ' using ' + showProd(G, p) + '.' });
          yield { end: r.end, tree: t };
          if (opts.limited) return;
          note({ kind: 'backtrack', A, prod: p.id, pos: i, depth, say: 'Backtrack into ' + A + ' (it had matched ' + show(w.slice(i, r.end)) + '): look for another way.' });
        }
        note({ kind: 'fail-rule', A, prod: p.id, pos: i, depth, say: showProd(G, p) + ' has no (more) ways to match here.' });
      }
      if (!any) note({ kind: 'fail', A, pos: i, depth, say: A + ' fails at position ' + (i + 1) + '.' });
    }
    function* seq(rhs, k, i, depth) {
      if (k === rhs.length) { yield { end: i, kids: [] }; return; }
      const X = rhs[k];
      if (N.has(X)) {
        for (const r of call(X, i, depth + 1)) for (const rest of seq(rhs, k + 1, r.end, depth)) yield { end: rest.end, kids: [r.tree].concat(rest.kids) };
      } else {
        tick();
        if (i < w.length && w[i] === X) {
          note({ kind: 'match', sym: X, pos: i, depth, say: 'Match ' + X + ' at position ' + (i + 1) + '.' });
          for (const rest of seq(rhs, k + 1, i + 1, depth)) yield { end: rest.end, kids: [Gr.leaf(X)].concat(rest.kids) };
        } else note({ kind: 'mismatch', sym: X, pos: i, found: i < w.length ? w[i] : null, depth, say: 'Expected ' + X + ' at position ' + (i + 1) + ' but found ' + (i < w.length ? w[i] : 'the end') + '.' });
      }
    }
    let tree = null;
    try {
      for (const r of call(G.start, 0, 0)) {
        if (r.end === w.length) { tree = r.tree; break; }
        note({ kind: 'leftover', end: r.end, say: G.start + ' matched only ' + show(w.slice(0, r.end)) + '; input is left over, so keep looking.' });
      }
    } catch (e) { if (!gaveUp) throw e; }
    trace.push(gaveUp ? { kind: 'give-up', say: 'Gave up after ' + opts.maxSteps + ' steps.' }
      : tree ? { kind: 'accept', say: 'The whole input ' + show(w) + ' was matched: accept.' } : { kind: 'reject', say: 'Every choice failed: reject ' + show(w) + '.' });
    return { word: w, accepted: !!tree, refused: false, gaveUp, tree: tree ? JSON.parse(JSON.stringify(tree)) : null, trace, steps };
  }

  // ---------- PEG and packrat parsing ----------
  // A small PEG format:   Name <- e1 / e2      (ordered choice: the first alternative that works wins)
  //   sequence by juxtaposition; 'lit' or "lit"; . any symbol; [a-z0-9] classes; ( ); postfix * + ?;
  //   prefix & (and-predicate) and ! (not-predicate); # comments. The first rule is the start.
  // Expressions: {t:'lit', syms}, {t:'any'}, {t:'class', set, neg}, {t:'ref', name}, {t:'seq', items},
  //   {t:'alt', items}, {t:'star'|'plus'|'opt'|'and'|'not', e}.
  function parsePEG(text) {
    const rules = new Map(), order = [];
    const src = String(text).split(/\r?\n/).map((l) => (/^\s*#/.test(l) ? '' : l)).join('\n');
    let i = 0;
    const err = (m) => { throw new Error('PEG: ' + m + ' at ' + (src.slice(0, i).split('\n').length) + ':' + i); };
    const ws = () => { while (i < src.length && /[ \t\r\n]/.test(src[i])) i++; };
    const ident = () => { const m = /^[A-Za-z_][A-Za-z0-9_']*/.exec(src.slice(i)); if (!m) return null; i += m[0].length; return m[0]; };
    const atRuleStart = () => { const m = /^[A-Za-z_][A-Za-z0-9_']*\s*(<-|←)/.exec(src.slice(i)); return !!m; };
    function primary() {
      ws();
      const ch = src[i];
      if (ch === '(') { i++; const e = choice(); ws(); if (src[i] !== ')') err('expected )'); i++; return e; }
      if (ch === "'" || ch === '"') { const j = src.indexOf(ch, i + 1); if (j < 0) err('unclosed quote'); const s = src.slice(i + 1, j); i = j + 1; return { t: 'lit', syms: [...s] }; }
      if (ch === '.') { i++; return { t: 'any' }; }
      if (ch === '[') {
        const j = src.indexOf(']', i + 1); if (j < 0) err('unclosed ['); let body = src.slice(i + 1, j); i = j + 1;
        const neg = body[0] === '^'; if (neg) body = body.slice(1);
        const set = []; const cs = [...body];
        for (let k = 0; k < cs.length; k++) {
          if (cs[k + 1] === '-' && k + 2 < cs.length) { for (let c = cs[k].codePointAt(0); c <= cs[k + 2].codePointAt(0); c++) set.push(String.fromCodePoint(c)); k += 2; }
          else set.push(cs[k]);
        }
        return { t: 'class', set, neg };
      }
      const id = ident(); if (id) return { t: 'ref', name: id };
      err('unexpected ' + (ch === undefined ? 'end' : ch));
    }
    function postfix() {
      let e = primary();
      for (;;) { const c = src[i]; if (c === '*') { i++; e = { t: 'star', e }; } else if (c === '+') { i++; e = { t: 'plus', e }; } else if (c === '?') { i++; e = { t: 'opt', e }; } else return e; }
    }
    function prefix() { ws(); if (src[i] === '&') { i++; return { t: 'and', e: prefix() }; } if (src[i] === '!') { i++; return { t: 'not', e: prefix() }; } return postfix(); }
    function sequence() {
      const items = [];
      for (;;) { ws(); const c = src[i]; if (c === undefined || c === '/' || c === ')' || atRuleStart()) break; items.push(prefix()); }
      return items.length === 1 ? items[0] : { t: 'seq', items };
    }
    function choice() {
      const items = [sequence()];
      for (;;) { ws(); if (src[i] !== '/') break; i++; items.push(sequence()); }
      return items.length === 1 ? items[0] : { t: 'alt', items };
    }
    ws();
    while (i < src.length) {
      const name = ident(); if (!name) err('expected a rule name');
      ws(); if (src.startsWith('<-', i)) i += 2; else if (src[i] === '←') i++; else err('expected <-');
      const e = choice();
      if (rules.has(name)) err('rule ' + name + ' defined twice');
      rules.set(name, e); order.push(name); ws();
    }
    if (!order.length) throw new Error('PEG: no rules');
    for (const [, e] of rules) (function chk(x) { if (x.t === 'ref' && !rules.has(x.name)) throw new Error('PEG: undefined rule ' + x.name); (x.items || []).forEach(chk); if (x.e) chk(x.e); })(e);
    return { start: order[0], rules, order };
  }
  function showPEG(e) {
    switch (e.t) {
      case 'lit': return "'" + e.syms.join('') + "'";
      case 'any': return '.';
      case 'class': return '[' + (e.neg ? '^' : '') + e.set.join('') + ']';
      case 'ref': return e.name;
      case 'seq': return e.items.length ? e.items.map((x) => (x.t === 'alt' ? '(' + showPEG(x) + ')' : showPEG(x))).join(' ') : "''";
      case 'alt': return e.items.map(showPEG).join(' / ');
      default: { const inner = /^(seq|alt)$/.test(e.e.t) ? '(' + showPEG(e.e) + ')' : showPEG(e.e); return e.t === 'and' ? '&' + inner : e.t === 'not' ? '!' + inner : inner + { star: '*', plus: '+', opt: '?' }[e.t]; }
    }
  }
  // A CFG read as a PEG: the same rules with | turned into ordered choice /, in the written order.
  function pegFromGrammar(G) {
    const rules = new Map(), order = [];
    for (const A of G.nonterminals) {
      const alts = (Gr.info(G).byA.get(A) || []).map((p) => ({ t: 'seq', items: p.rhs.map((s) => (Gr.isN(G, s) ? { t: 'ref', name: s } : { t: 'lit', syms: [s] })) }));
      if (!alts.length) alts.push({ t: 'not', e: { t: 'seq', items: [] } });   // a nonterminal with no rules always fails
      rules.set(A, alts.length === 1 ? alts[0] : { t: 'alt', items: alts }); order.push(A);
    }
    return { start: G.start, rules, order };
  }
  // Packrat: every (rule, position) is evaluated at most once and memoised. A rule that calls itself at
  // the same position (left recursion) fails there, which the trace reports.
  // opts.full (default true): the start rule must consume the whole input.
  function packrat(peg, input, opts) {
    opts = Object.assign({ full: true, maxSteps: 50000 }, opts || {});
    const w = Array.isArray(input) ? input : [...String(input)];
    const memo = new Map(), trace = [], busy = new Set();
    let steps = 0, hits = 0;
    const note = (st) => { if (trace.length < opts.maxSteps) trace.push(st); };
    function ev(e, i, depth) {
      if (++steps > opts.maxSteps * 4) throw new Error('PEG: too many steps');
      switch (e.t) {
        case 'lit': {
          for (let k = 0; k < e.syms.length; k++) if (w[i + k] !== e.syms[k]) { note({ kind: 'mismatch', pos: i, expect: e.syms.join(''), depth, say: "Expected '" + e.syms.join('') + "' at position " + (i + 1) + '.' }); return null; }
          note({ kind: 'match', pos: i, text: e.syms.join(''), depth, say: "Match '" + e.syms.join('') + "' at position " + (i + 1) + '.' });
          return { end: i + e.syms.length, kids: e.syms.map((s) => Gr.leaf(s)) };
        }
        case 'any': return i < w.length ? { end: i + 1, kids: [Gr.leaf(w[i])] } : null;
        case 'class': return i < w.length && e.set.includes(w[i]) !== e.neg ? { end: i + 1, kids: [Gr.leaf(w[i])] } : null;
        case 'seq': { let j = i; const kids = []; for (const x of e.items) { const r = ev(x, j, depth); if (!r) return null; j = r.end; kids.push(...r.kids); } return { end: j, kids }; }
        case 'alt': {
          for (let k = 0; k < e.items.length; k++) {
            const r = ev(e.items[k], i, depth);
            if (r) { note({ kind: 'choose', alt: k, pos: i, depth, say: 'Alternative ' + (k + 1) + ' (' + showPEG(e.items[k]) + ') succeeds, so the later ones are never tried.' }); return r; }
            note({ kind: 'next-alt', alt: k, pos: i, depth, say: 'Alternative ' + (k + 1) + ' (' + showPEG(e.items[k]) + ') fails at position ' + (i + 1) + '; try the next.' });
          }
          return null;
        }
        case 'star': case 'plus': {
          let j = i; const kids = []; let n = 0;
          for (;;) { const r = ev(e.e, j, depth); if (!r || r.end === j) break; j = r.end; kids.push(...r.kids); n++; }
          return e.t === 'plus' && n === 0 ? null : { end: j, kids };
        }
        case 'opt': return ev(e.e, i, depth) || { end: i, kids: [] };
        case 'and': return ev(e.e, i, depth) ? { end: i, kids: [] } : null;
        case 'not': return ev(e.e, i, depth) ? null : { end: i, kids: [] };
        case 'ref': return rule(e.name, i, depth + 1);
      }
      throw new Error('PEG: bad expression');
    }
    function rule(name, i, depth) {
      const key = name + '@' + i;
      if (memo.has(key)) {
        hits++; const m = memo.get(key);
        note({ kind: 'memo', rule: name, pos: i, ok: !!m, end: m ? m.end : null, depth, say: 'Already know ' + name + ' at position ' + (i + 1) + ': ' + (m ? 'matches up to ' + m.end : 'fails') + ' (memo table).' });
        return m ? { end: m.end, kids: [m.tree] } : null;
      }
      if (busy.has(key)) { note({ kind: 'left-recursion', rule: name, pos: i, depth, say: name + ' calls itself at position ' + (i + 1) + ' without consuming input (left recursion); that call fails.' }); return null; }
      busy.add(key);
      note({ kind: 'call', rule: name, pos: i, depth, say: 'Call ' + name + ' at position ' + (i + 1) + '.' });
      const r = ev(peg.rules.get(name), i, depth);
      busy.delete(key);
      const out = r ? { end: r.end, tree: { sym: name, prod: null, children: r.kids } } : null;
      memo.set(key, out ? { end: out.end, tree: out.tree } : null);
      note({ kind: out ? 'return' : 'fail', rule: name, pos: i, end: out ? out.end : null, depth, say: name + (out ? ' matches ' + show(w.slice(i, out.end)) + ' (positions ' + (i + 1) + '–' + out.end + ').' : ' fails at position ' + (i + 1) + '.') });
      return out ? { end: out.end, kids: [out.tree] } : null;
    }
    const r = rule(peg.start, 0, 0);
    const accepted = !!r && (!opts.full || r.end === w.length);
    trace.push({ kind: accepted ? 'accept' : 'reject', say: !r ? peg.start + ' fails: reject.' : accepted ? 'Accept: ' + peg.start + ' matched ' + show(w.slice(0, r.end)) + '.' : peg.start + ' matched only ' + show(w.slice(0, r.end)) + ', leaving input unread: reject.' });
    const table = [...memo].map(([k, v]) => { const at = k.lastIndexOf('@'); return { rule: k.slice(0, at), pos: +k.slice(at + 1), ok: !!v, end: v ? v.end : null }; });
    return { accepted, end: r ? r.end : null, tree: r ? r.kids[0] : null, memo: table, hits, trace };
  }
  // Words up to length n where the CFG and the same rules read as a PEG disagree.
  function contrastPEG(G, n) {
    const peg = pegFromGrammar(G), inL = new Set(Gr.language(G, n).map((x) => x.join('\u0001'))), out = [];
    for (const x of Gr.allWords(G.terminals, n)) {
      const a = inL.has(x.join('\u0001'));
      let b; try { b = packrat(peg, x, { maxSteps: 5000 }).accepted; } catch (e) { b = false; }
      if (a !== b) out.push({ word: x, cfg: a, peg: b, say: show(x) + (a ? ' is in the CFG language but the PEG rejects it (ordered choice committed too early).' : ' is accepted by the PEG but not generated by the CFG.') });
    }
    return out;
  }

  T.parse = { cyk, earley, showItem, recursiveDescent, parsePEG, showPEG, pegFromGrammar, packrat, contrastPEG };
})();
