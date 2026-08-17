// Top-down parsing by trial and error. Backtracking recursive descent tries a nonterminal's rules in order
// and, when something later fails, goes back into an earlier call for another way: drawn as a call tree
// that grows, loses its failed branches and grows again. Packrat parsing reads the same rules as a PEG,
// where the first alternative that works wins for good, and remembers every (rule, position) it has tried
// in a memo table, so nothing is parsed twice.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'backtrack', part: 'parsing', order: 8, title: 'Trial and error: backtracking and packrat', blurb: 'The simplest top-down parsers try rules in order and back up when stuck; a packrat parser commits to the first rule that works and remembers every result.' });

  const TWO = 'S → A c | A d\nA → a b | a';
  const GREEDY = 'S → A b\nA → a b | a';
  const LEFT = 'E → E + n | n';
  const AMB = 'S → A A\nA → a a | a';
  const checkG = (v) => T.PX.checkGrammar({ maxRules: 8, maxN: 4 })(v);

  // ---- the call tree of backtracking recursive descent --------------------------------------------------------
  /** Replay the core's trace into snapshots of a call tree: call nodes, matched and mismatched terminals */
  function replay(r) {
    let seq = 0;
    const root = { id: 'root', kids: [] };      // a holder for the start call
    const cur = [];                              // cur[d]: the call working at depth d
    const snaps = [];
    const copy = (n) => ({ id: n.id, sym: n.sym, call: n.call, status: n.status, got: n.got, kids: n.kids.map(copy) });
    const parentOf = (d) => (d === 0 ? root : cur[d - 1]);
    for (const st of r.trace) {
      let focus = null, resumed = null;
      if (st.kind === 'call') {
        const n = { id: 'c' + seq++, sym: st.A, call: true, status: 'work', kids: [], pos: st.pos };
        parentOf(st.depth).kids.push(n); cur[st.depth] = n; cur.length = st.depth + 1; focus = n.id;
      } else if (st.kind === 'try') { const n = cur[st.depth]; n.kids = []; n.status = 'work'; focus = n.id; }
      else if (st.kind === 'match' || st.kind === 'mismatch') {
        const n = { id: 't' + seq++, sym: st.sym, call: false, status: st.kind === 'match' ? 'ok' : 'bad', got: st.kind === 'mismatch' ? (st.found === null ? 'end' : st.found) : null, kids: [] };
        cur[st.depth].kids.push(n); focus = n.id;
      } else if (st.kind === 'return') { cur[st.depth].status = 'ok'; focus = cur[st.depth].id; }
      else if (st.kind === 'backtrack') {
        // go back into the most recent finished call of A under the same parent: what came after it is dropped
        const par = parentOf(st.depth), k = par.kids.map((x) => x.sym === st.A && x.call).lastIndexOf(true);
        const n = par.kids[k];
        par.kids.length = k + 1; n.status = 'work'; cur[st.depth] = n; cur.length = st.depth + 1; focus = n.id; resumed = n.id;
      } else if (st.kind === 'fail-rule') { const n = cur[st.depth]; n.kids = []; focus = n.id; }
      else if (st.kind === 'fail') { cur[st.depth].status = 'fail'; focus = cur[st.depth].id; }
      snaps.push({ st, tree: root.kids.length ? copy(root.kids[0]) : null, focus, resumed });
    }
    return snaps;
  }
  const kitOf = (n, focus) => ({ id: n.id, label: n.sym, sub: n.got ? 'got ' + n.got : undefined, cls: [n.call ? 'nt' : 'term', n.status === 'ok' && !n.call ? 'good' : '', n.status === 'ok' && n.call ? 'accept-path' : '', n.status === 'bad' || n.status === 'fail' ? 'reject' : '', n.id === focus ? 'hot' : ''].filter(Boolean).join(' '), children: n.kids.map((c) => kitOf(c, focus)) });

  T.topic({
    id: 'rd-backtrack', family: 'backtrack', order: 10, title: 'Recursive descent with backtracking',
    blurb: 'Each nonterminal is a procedure that tries its rules in order. When a later symbol does not match, the parser goes back into an earlier call and asks it for another way.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: TWO, check: checkG },
      { id: 'w', kind: 'string', label: 'String', def: 'abd', max: 6 },
      { id: 'mode', kind: 'choice', label: 'Backtracking', def: 'full', options: [{ value: 'full', label: 'into finished calls too' }, { value: 'limited', label: 'none into finished calls' }] },
    ],
    presets: [
      { label: 'Back up twice: abd', values: { g: TWO, w: 'abd', mode: 'full' } },
      { label: 'Rejected: abb', values: { g: TWO, w: 'abb', mode: 'full' } },
      { label: 'Must undo a finished call: ab', values: { g: GREEDY, w: 'ab', mode: 'full' } },
      { label: 'Without that, wrongly rejected', values: { g: GREEDY, w: 'ab', mode: 'limited' } },
      { label: 'Left recursion: refused', values: { g: LEFT, w: 'n+n', mode: 'full' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 6)(inp),
    counters: [{ id: 'calls', label: 'calls' }, { id: 'matches', label: 'symbols matched' }, { id: 'backs', label: 'backtracks' }],
    run(inp) {
      const G = T.PX.G(inp.g), r = T.parse.recursiveDescent(G, inp.w, { limited: inp.mode === 'limited', maxSteps: 400 }), w = r.word;
      const F = new T.Frames(['calls', 'matches', 'backs']);
      const snaps = replay(r);
      // the input sits under the deepest tree any frame shows, so it never moves
      const depth = (n) => (n ? 1 + Math.max(0, ...n.kids.map(depth)) : 0);
      const maxD = Math.max(r.refused ? 3 : 1, ...snaps.map((s) => depth(s.tree)));
      const iy = maxD * 80 + 20, cw = 48;
      const scene = (tree, focus, pos, opts) => {
        const items = [];
        if (tree) items.push(...K.tree.draw(kitOf(tree, focus), { prefix: 'rd', gapY: 80, gapX: 26 }).items);
        items.push(...K.string.draw({ text: w, pos: pos === null ? null : Math.min(pos, w.length), x: -(Math.max(1, w.length) * cw) / 2, y: iy, cw, prefix: 'rdw', label: 'input', headText: pos >= w.length ? 'end' : 'next', cls: (i) => (opts && opts.span && i >= opts.span[0] && i < opts.span[1] ? 'act' : '') }).items);
        return items;
      };
      if (r.refused) {
        const lr = r.trace[0];
        const loop = { id: 'c0', sym: G.start, call: true, status: 'work', kids: [{ id: 'c1', sym: G.start, call: true, status: 'work', kids: [{ id: 'c2', sym: G.start, call: true, status: 'fail', kids: [] }] }] };
        F.add({ items: scene(null, null, 0), say: 'The grammar has ' + T.PX.set(G.productions.map((p) => T.grammar.showProd(G, p))) + '. Before parsing, look at the first rule of ' + lr.nonterminals[0] + '.' });
        F.add({ items: scene(loop, 'c2', 0), say: 'A procedure for ' + lr.nonterminals[0] + ' would first call ' + lr.nonterminals[0] + ' again at the same position, which calls it again, and so on: the calls never read a symbol and never end.', hl: { g: G.productions.filter((p) => p.rhs[0] === p.A).map((p) => p.id) } });
        F.add({ items: scene(loop, 'c2', 0), say: lr.say + ' (A parser that tries rules in order cannot use a left-recursive grammar as it stands.)', mark: 'refused', meta: { yes: false } });
        return { frames: F.list, def: { sections: [T.PX.gdef(G)] } };
      }
      F.add({ items: scene(null, null, 0), say: 'Parse ' + T.PX.show(w) + ' starting from ' + G.start + '. Every nonterminal is a procedure that tries its rules in the order they are written.' + (inp.mode === 'limited' ? ' This parser never goes back into a call that has already returned.' : '') });
      let pos = 0;
      snaps.forEach((s, k) => {
        const st = s.st;
        if (st.kind === 'accept' || st.kind === 'reject' || st.kind === 'give-up') return;
        if (st.pos !== undefined) pos = st.pos;
        if (st.kind === 'match') { F.count('matches'); pos = st.pos + 1; }
        if (st.kind === 'call') F.count('calls');
        if (st.kind === 'backtrack') F.count('backs');
        if (st.kind === 'return') pos = st.to;
        const say = st.kind === 'mismatch' ? st.say + ' This way fails.' : st.kind === 'backtrack' ? st.say + ' Everything after it is undone.' : st.kind === 'leftover' ? st.say : st.say;
        const hlp = st.prod !== undefined ? [st.prod] : [];
        const next = snaps[k + 1];
        F.add({ items: scene(s.tree, s.focus, pos, { span: st.kind === 'return' ? [st.from, st.to] : null }), say, hl: { g: hlp }, meta: { kind: st.kind, nextBack: next && next.st.kind === 'backtrack' ? next.resumed : null } });
      });
      const last = snaps.length ? snaps[snaps.length - 1].st : null;
      const final = snaps.filter((s) => s.tree).pop();
      F.add({ items: scene(final ? final.tree : null, null, r.accepted ? w.length : pos), say: last.say + (r.accepted ? '' : inp.mode === 'limited' && r.word.length ? ' Yet the string is in the language: going back into the finished call would have found it.' : ''), mark: r.accepted ? 'accepted' : 'rejected', meta: { yes: r.accepted } });
      return { frames: F.list, def: { sections: [T.PX.gdef(G), { id: 'how', kind: 'text', title: 'How it works', text: 'parse(A): for each rule A → X1 … Xk in order, match X1 … Xk one after another (a terminal must equal the next input symbol; a nonterminal is a call). When something fails, go back to the most recent call that can still offer another way.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i].meta && fr[i].meta.kind === 'mismatch' && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'backtrack', once: true, pick: 'item', ask: 'That symbol did not match. Which earlier call will the parser go back into? Click it.',
        answer: (fr, i) => { const m = fr[i + 1].say; void m; return 'rd:n:' + fr[i].meta.nextBack; }, explain: (fr, i) => 'The most recent call that has returned and might still have another way to match. ' + fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the parser accept the string?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why can a backtracking parser take exponential time?', options: ['It reads the input many times from the start', 'The same nonterminal may be parsed again and again at the same position after each backtrack', 'It builds the parse table first', 'It never stops'], answer: 1, why: 'Nothing is remembered: undoing a choice throws away work that later has to be redone, and the choices multiply.' },
      { q: 'A procedure for E → E + n | n calls itself first, at the same position. What happens?', options: ['It reads n', 'It recurses forever without reading anything', 'It backtracks to n', 'It fails at once'], answer: 1, why: 'Left recursion: each call makes the same call before consuming a symbol.' },
      { q: 'With S → A b and A → a b | a, the input ab is rejected by a parser that never re-enters a finished call. Why?', options: ['ab is not in the language', 'A takes ab first, b then fails, and nobody asks A for its shorter way', 'The grammar is ambiguous', 'b is not a terminal'], answer: 1, why: 'A → a b succeeds first and returns; only going back into A finds A → a, after which b matches.' },
      { q: 'What does a backtracking parser do when the start symbol matches only a prefix of the input?', options: ['Accepts', 'Keeps looking for another way that matches all of it', 'Rejects at once', 'Skips the rest'], answer: 1, why: 'Leftover input is just another failure; the parser asks for another way.' },
    ],
  });

  // ---- packrat parsing of a PEG ---------------------------------------------------------------------------------
  T.topic({
    id: 'peg-packrat', family: 'backtrack', order: 20, title: 'Packrat parsing: ordered choice and a memo table',
    blurb: 'Read the rules as a parsing expression grammar: the first alternative that works wins, for good. Every result for a rule at a position goes into a memo table, so nothing is parsed twice.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Rules (read in order as A ← α / β)', def: TWO, check: checkG },
      { id: 'w', kind: 'string', label: 'String', def: 'abd', min: 1, max: 6 },
    ],
    presets: [
      { label: 'Remembered, not redone: abd', values: { g: TWO, w: 'abd' } },
      { label: 'Commits too early: ab', values: { g: GREEDY, w: 'ab' } },
      { label: 'Two CFG trees, one PEG parse: aaa', values: { g: AMB, w: 'aaa' } },
      { label: 'Left recursion fails: n+n', values: { g: LEFT, w: 'n+n' } },
    ],
    check: (inp) => T.PX.checkWord('g', 'w', 6)(inp),
    counters: [{ id: 'evals', label: 'rule evaluations' }, { id: 'hits', label: 'memo hits' }],
    run(inp) {
      const G = T.PX.G(inp.g), peg = T.parse.pegFromGrammar(G), w = T.PX.word(G, inp.w), n = w.length;
      const r = T.parse.packrat(peg, w);
      const cfg = T.parse.earley(G, w, { maxTrees: 2 });
      const F = new T.Frames(['evals', 'hits']);
      const rules = peg.order, memo = {};
      const stack = [];
      const cw = 66;
      const cellText = (A, j) => { const m = memo[A + '@' + j]; return m === undefined ? '' : m === 'busy' ? '…' : m === null ? '✗' : m === j ? 'ε' : T.PX.show(w.slice(j, m)); };
      const scene = (opts) => {
        opts = opts || {};
        const rows = rules.map((A) => Array.from({ length: n + 1 }, (_, j) => cellText(A, j)));
        const tb = K.table.draw({ prefix: 'pm', rows, rowHead: rules, x: 0, y: 70, cw, mono: true, size: 16, hot: opts.hot ? [opts.hot] : [], cls: (ri, j) => { const m = memo[rules[ri] + '@' + j]; return m === null ? 'bad' : m === 'busy' ? 'act' : m !== undefined ? 'good' : ''; } });
        const x0 = tb.cellBox(0, 0).x;
        const s = K.string.draw({ text: w.concat(['$']), pos: opts.pos === undefined ? null : opts.pos, x: x0, y: 0, cw, prefix: 'pmw', head: 'above', headText: 'at', cls: (i) => (i === n ? 'endmark' : opts.span && i >= opts.span[0] && i < opts.span[1] ? 'act' : '') });
        const px = x0 + (n + 1) * cw + 46;
        const pn = T.PX.panel({ prefix: 'pms', x: px, y: 70, w: 170, title: 'Calls', rows: stack.slice().reverse().map((c, k) => ({ id: c.id, text: c.rule + ' at ' + (c.pos + 1), cls: k === 0 ? 'hot' : '' })), rowH: 32, size: 15, minH: 40 + 5 * 36 });
        const items = tb.items.concat(s.items, pn.items);
        if (opts.verdict) items.push(...T.PX.panel({ prefix: 'pmv', x: px, y: 70 + 40 + 5 * 36 + 16, w: 230, title: 'Verdicts', rows: opts.verdict, rowH: 30, size: 14, mono: false }).items);
        return items;
      };
      const pegText = rules.map((A) => A + ' ← ' + T.parse.showPEG(peg.rules.get(A)));
      F.add({ items: scene({ pos: 0 }), say: 'The rules read as a PEG: ' + pegText.join(';  ') + '. Each row of the table will say, for its rule and each starting position, whether it matches and what it takes.' });
      let seq = 0;
      for (const st of r.trace) {
        const at = st.pos;
        if (st.kind === 'call') { memo[st.rule + '@' + at] = 'busy'; stack.push({ id: 'k' + seq++, rule: st.rule, pos: at }); F.count('evals'); F.add({ items: scene({ pos: at, hot: [rules.indexOf(st.rule), at] }), say: st.say + ' Nothing is known about it yet, so work it out.', meta: { kind: 'call' } }); continue; }
        if (st.kind === 'return' || st.kind === 'fail') {
          memo[st.rule + '@' + at] = st.kind === 'return' ? st.end : null; stack.pop();
          F.add({ items: scene({ pos: st.kind === 'return' ? st.end : at, hot: [rules.indexOf(st.rule), at], span: st.kind === 'return' ? [at, st.end] : null }), say: st.say + ' The result goes into the table.', meta: { kind: st.kind } });
          continue;
        }
        if (st.kind === 'memo') { F.count('hits'); F.add({ items: scene({ pos: at, hot: [rules.indexOf(st.rule), at] }), say: st.say + ' No work is repeated: this is what makes packrat parsing linear.', meta: { kind: 'memo', cell: 'pm:' + rules.indexOf(st.rule) + ',' + at } }); continue; }
        if (st.kind === 'left-recursion') { F.add({ items: scene({ pos: at, hot: [rules.indexOf(st.rule), at] }), say: st.say + ' A PEG cannot grow a left-recursive rule.', meta: { kind: st.kind } }); continue; }
        if (st.kind === 'accept' || st.kind === 'reject') continue;
        F.add({ items: scene({ pos: at }), say: st.say, meta: { kind: st.kind, next: st.kind === 'next-alt' } });
      }
      const cfgSay = cfg.accepted ? 'in the language' + (cfg.ambiguous ? ', with two or more trees' : '') : 'not in the language';
      const verdict = [{ id: 'c', text: 'As a CFG: ' + (cfg.accepted ? 'accept' : 'reject') + (cfg.ambiguous ? ' (ambiguous)' : ''), cls: cfg.accepted ? 'good' : 'bad' }, { id: 'p', text: 'As a PEG: ' + (r.accepted ? 'accept (one parse)' : 'reject'), cls: r.accepted ? 'good' : 'bad' }];
      const lastSay = r.trace[r.trace.length - 1].say;
      F.add({ items: scene({ pos: r.end === null ? 0 : r.end, verdict }), say: lastSay + ' Read as an ordinary grammar, ' + T.PX.show(w) + ' is ' + cfgSay + '. ' + (cfg.accepted !== r.accepted ? 'They disagree: ordered choice committed to an alternative and never came back to try another.' : cfg.ambiguous ? 'Both accept, but the PEG gives exactly one parse: ordered choice removes the ambiguity.' : 'Here the two readings agree.'), mark: r.accepted ? 'accepted' : 'rejected', meta: { yes: r.accepted, cfg: cfg.accepted } });
      return { frames: F.list, def: { sections: [{ id: 'peg', kind: 'math', title: 'The rules as a PEG (/ is ordered choice)', text: pegText.join('\n') }, T.PX.gdef(G, { title: 'The same rules as a grammar' }), { id: 'cell', kind: 'text', title: 'The memo table', text: 'Row A, column j: what A matches starting at symbol j (ε when it matches nothing), ✗ when it fails there, … while it is being worked out.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'memo', once: true, pick: 'item', ask: 'The parser is about to need a rule at a position it has tried before. Click the table cell it will reuse.', answer: (fr, i) => fr[i + 1].meta.cell, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the PEG accept the string?', answer: (fr) => (fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'In a PEG, A ← α / β. When is β tried?', options: ['Always, to find every parse', 'Only when α fails at this position', 'Only when α succeeds', 'Never'], answer: 1, why: 'Ordered choice: the first alternative that succeeds is the result, and no other is ever considered there.' },
      { q: 'Why does packrat parsing run in linear time?', options: ['It never backtracks', 'Each (rule, position) pair is evaluated at most once and remembered', 'PEGs are regular', 'It reads the input once from the right'], answer: 1, why: 'There are |rules| × (n + 1) table cells, each filled once; everything else is a lookup.' },
      { q: 'Can a PEG be ambiguous?', options: ['Yes, like a CFG', 'No: each rule at each position has at most one result', 'Only with left recursion', 'Only with ε'], answer: 1, why: 'The result of a rule at a position is unique, so there is at most one parse.' },
      { q: 'With A ← a b / a and S ← A b, why is ab rejected?', options: ['A takes ab and never gives back the b', 'ab has no tree', 'b is not a terminal', 'The memo table is full'], answer: 0, why: 'The first alternative of A succeeds, so A is committed to ab; S then needs a b that is gone.' },
      { q: 'What does the memo table cost?', options: ['Nothing', 'Memory: one entry per rule and position', 'It makes parsing exponential', 'It needs the grammar in a normal form'], answer: 1, why: 'Space proportional to the number of rules times the input length: the price of the speed.' },
    ],
  });
})();
