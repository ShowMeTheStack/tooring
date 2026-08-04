// Regular expressions: reading one as a tree (built bottom-up by precedence), Thompson's construction with
// each fragment in its own nested box, the position automaton with its first, last and follow sets,
// derivatives as the states of a DFA, and simplification one named rule at a time. The topics that go from
// automata back to expressions, and equivalence, are in regular-regex2.js.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg, RE = T.RE;
  const X = (T.RegX = T.RegX || {});

  T.family({ id: 'regex', part: 'regular', order: 50, title: 'Regular expressions', blurb: 'Union, concatenation and star: expressions as trees, turned into automata (Thompson, positions, derivatives) and back again (state elimination, the R table), simplified and compared.' });

  // ---- helpers shared with regular-regex2.js ---------------------------------------------------------------
  /** A regex input with friendly errors and a size limit */
  X.input = (id, label, def, max) => ({
    id, kind: 'regex', label, def,
    check: (v) => {
      const c = RE.check(v);
      if (!c.ok) return label + ': ' + c.error;
      if (RE.size(c.ast) > (max || 12)) return label + ': at most ' + (max || 12) + ' symbols and operators, so the picture stays readable';
      if (RE.alphabet(c.ast).length > 3) return label + ': at most 3 different symbols';
      return null;
    },
  });
  const PREC = { alt: 1, cat: 2, star: 3, plus: 3, opt: 3, sym: 4, eps: 4, empty: 4 };
  const OPL = { alt: '|', cat: '·', star: '*', plus: '+', opt: '?', eps: 'ε', empty: '∅' };
  /**
   * The expression printed the way the engine prints it, with every node knowing the characters it covers:
   * {chars, root, post (nodes in post-order)}. A node is {id, t, c, kids, ast, span: [from, to), text}.
   */
  X.annotate = function (ast) {
    const chars = [], post = [];
    const go = (r, ctx, id) => {
      const paren = PREC[r.t] < ctx, st = chars.length;
      if (paren) chars.push('(');
      const n = { id, t: r.t, c: r.c, ast: r, kids: [] };
      if (r.t === 'sym') chars.push(r.c);
      else if (r.t === 'eps') chars.push('ε');
      else if (r.t === 'empty') chars.push('∅');
      else if (r.t === 'alt') { n.kids.push(go(r.a, 1, id + 'l')); chars.push('|'); n.kids.push(go(r.b, 1, id + 'r')); }
      else if (r.t === 'cat') { n.kids.push(go(r.a, 2, id + 'l')); n.kids.push(go(r.b, 2, id + 'r')); }
      else { n.kids.push(go(r.x, 3, id + 'x')); chars.push(OPL[r.t]); }
      if (paren) chars.push(')');
      n.span = [st, chars.length];
      n.text = RE.show(r);
      n.op = r.t === 'alt' ? chars.lastIndexOf('|', chars.length - 1 - (paren ? 1 : 0)) : null;
      post.push(n);
      return n;
    };
    const root = go(ast, 0, 'n');
    // the | of an alternative: the one between its two children
    for (const n of post) if (n.t === 'alt') n.op = n.kids[0].span[1];
    return { chars, root, post };
  };
  /** The tree for the tree kit (labels: the operator, or the symbol) */
  X.treeNode = (n, hide, cls) => ({ id: n.id, label: n.t === 'sym' ? n.c : OPL[n.t], cls: (n.t === 'sym' || n.t === 'eps' || n.t === 'empty' ? 'leaf term' : '') + (cls && cls(n) ? ' ' + cls(n) : ''), mono: n.t === 'sym', children: n.kids.filter((k) => !hide || !hide(k)).map((k) => X.treeNode(k, hide, cls)) });
  /** The expression as a row of cells, the part of the current node lit */
  X.exprRow = (A, o) => K.string.draw({ text: A.chars, x: o.x, y: o.y, cw: o.cw || 36, ch: 40, pos: null, head: false, prefix: o.prefix || 'ex', label: o.label, cls: (i) => (o.cls ? o.cls(i) : '') });
  X.sample = function (ast, alphabet) {
    if (RE.isEmptyLang(ast)) return 'matches nothing (∅)';
    const ws = RE.enumerate(ast, { max: 5, maxLen: 4, alphabet });
    const more = RE.enumerate(ast, { max: 6, maxLen: 6, alphabet }).length > ws.length;
    return 'matches ' + ws.map(R.w).join(', ') + (more ? ' and more' : '');
  };
  X.edgeX = (items) => items.map((it) => (it.kind === 'edge' && /\btr\b/.test(it.cls || '') ? Object.assign({}, it, { audit: 'edge-x' }) : it));
  /** Do any two routed edges of a drawn machine cross? */
  X.crosses = (g) => { for (let i = 0; i < g.routes.length; i++) for (let j = i + 1; j < g.routes.length; j++) { const a = g.routes[i], b = g.routes[j]; if (a.from === b.to && a.to === b.from) continue; if (Geo.polyCross(a.pts, b.pts)) return true; } return false; };
  const desc = { alt: 'a union: either side', cat: 'a concatenation: left part then right part', star: 'a star: zero or more copies', plus: 'a plus: one or more copies', opt: 'an option: zero or one copy', sym: 'a symbol', eps: 'ε, the empty string', empty: '∅, the empty language' };

  // ---- the tree --------------------------------------------------------------------------------------------------
  T.topic({
    id: 'regex-tree', family: 'regex', order: 10, title: 'Reading a regex as a tree',
    blurb: 'Star binds tightest, then concatenation, then union. Build the tree bottom-up, one operator at a time, and see what each piece matches.',
    inputs: [X.input('r', 'Expression', 'ab*|c', 12)],
    presets: [
      { label: 'ab*|c: which operator goes first?', values: { r: 'ab*|c' } },
      { label: '(a|b)*abb', values: { r: '(a|b)*abb' } },
      { label: 'Parentheses change it: (ab)*', values: { r: '(ab)*|a' } },
      { label: 'A star inside a star: (a*b)*', values: { r: '(a*b)*' } },
      { label: 'ε and ∅ as leaves', values: { r: '(ε|a)b∅|c' } },
    ],
    counters: [{ id: 'nodes', label: 'nodes built' }],
    run(inp) {
      const ast = RE.parse(inp.r);
      const A = X.annotate(ast);
      const al = RE.alphabet(ast);
      const built = new Set();
      const F = new T.Frames(['nodes']);
      const tr0 = K.tree.draw(X.treeNode(A.root), { gapX: 26, gapY: 80, y: 120 });
      // the expression and the card about the current node side by side, above the tree
      const cw = 36, NW = Math.max(...A.post.map((n) => R.note('w', { x: 0, y: 0, title: 'this node', lines: [n.text, desc[n.t], X.sample(n.ast, al)], size: 15 }).box.w)), ex0 = tr0.box.x + tr0.box.w / 2 - (A.chars.length * cw + 36 + NW) / 2;
      const noteX = ex0 + A.chars.length * cw + 36;
      const scene = (cur, extra) => {
        const items = [];
        const row = X.exprRow(A, { x: ex0, y: 0, cls: (i) => (cur && i >= cur.span[0] && i < cur.span[1] ? 'hot' : built.size === A.post.length ? 'good' : '') });
        items.push(...row.items);
        if (built.size) {
          const t = K.tree.draw(X.treeNode(A.root, null, (n) => (!built.has(n.id) ? 'hidden' : cur && n.id === cur.id ? 'hot' : '')), { gapX: 26, gapY: 80, y: 120 });
          for (const it of t.items) {
            const id = it.key.split(':').pop().split('>').pop();
            if (!built.has(id)) continue;
            if (it.kind === 'edge') { const p = it.key.split(':').pop().split('>')[0]; if (!built.has(p)) continue; }
            items.push(it);
          }
        }
        if (cur) {
          const nt = R.note('note', { x: noteX, y: -24, w: NW + 24, title: 'this node', lines: [cur.text, desc[cur.t], X.sample(cur.ast, al)], size: 15 });
          items.push(...nt.items);
        }
        return items.concat(extra || []);
      };
      F.add({ items: scene(null), say: 'Read ' + RE.show(ast) + '. Postfix *, + and ? bind tightest, then concatenation (writing side by side), then | last of all; parentheses override this. The tree is built from the leaves up.', meta: { rootT: A.root.t } });
      for (const n of A.post) {
        built.add(n.id);
        F.count('nodes');
        const kids = n.kids.map((k) => k.text);
        const why = n.t === 'alt' ? kids[0] + ' | ' + kids[1] + ': union joins two finished pieces, so it comes after the stars and concatenations inside them'
          : n.t === 'cat' ? kids[0] + ' then ' + kids[1] + ': concatenation joins two pieces written side by side'
            : n.t === 'star' || n.t === 'plus' || n.t === 'opt' ? OPL[n.t] + ' applies only to ' + kids[0] + ', the piece just before it'
              : n.t === 'sym' ? 'the symbol ' + n.c + ' is a leaf' : n.t === 'eps' ? 'ε is a leaf that matches only the empty string' : '∅ is a leaf that matches nothing at all';
        F.add({ items: scene(n), say: n.text + ': ' + why + '; it ' + X.sample(n.ast, al) + '.', meta: { node: n }, hl: { prec: [String(n.t === 'alt' ? 2 : n.t === 'cat' ? 1 : 0)] } });
      }
      F.add({ items: scene(null), say: 'The root is the operator applied last, ' + (A.root.t === 'cat' ? 'a concatenation' : A.root.t === 'alt' ? 'the union |' : desc[A.root.t]) + '. The whole expression ' + X.sample(ast, al) + '.', mark: 'done' });
      return { frames: F.list, def: { sections: [{ id: 'prec', kind: 'math', title: 'Precedence, tightest first', text: 'r*  r+  r?   repeat\nr s          concatenate\nr | s        union\n( )          group first' }, { id: 'lang', kind: 'math', title: 'What each operator means', text: 'L(r|s) = L(r) ∪ L(s)\nL(rs)  = { xy : x ∈ L(r), y ∈ L(s) }\nL(r*)  = {ε} ∪ L(r) ∪ L(rr) ∪ …\nL(ε) = {ε},  L(∅) = ∅' }] } };
    },
    predict: [
      { at: (f, i) => i === 0, once: true, pick: 'option', options: ['union |', 'concatenation', 'star *', 'plus +', 'option ?', 'a single symbol'], ask: 'Which operator is applied last, at the root of the tree?', answer: (fr) => ({ alt: 'union |', cat: 'concatenation', star: 'star *', plus: 'plus +', opt: 'option ?' })[fr[0].meta.rootT] || 'a single symbol', explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => i > 0 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.node && ['star', 'plus', 'opt'].includes(fr[i + 1].meta.node.t), once: true, pick: 'item', ask: (fr, i) => 'The next node is ' + OPL[fr[i + 1].meta.node.t] + '. Click a character of the expression it repeats.', answer: (fr, i) => { const n = fr[i + 1].meta.node.kids[0]; const out = []; for (let k = n.span[0]; k < n.span[1]; k++) out.push('ex:c:' + k); return out; }, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'How is ab* read?', options: ['(ab)*', 'a(b*)', '(a|b)*', 'a*b*'], answer: 1, why: 'Star binds tighter than concatenation, so it repeats only the b.' },
      { q: 'How is ab|c read?', options: ['a(b|c)', '(ab)|c', 'a|bc', '(a|b)c'], answer: 1, why: 'Concatenation binds tighter than union: the two choices are ab and c.' },
      { q: 'What does ∅* match?', options: ['Nothing', 'Only ε', 'Every string', 'Only ∅'], answer: 1, why: 'Zero copies of anything is ε, and there is no non-empty copy to add.' },
      { q: 'What does a∅ match?', options: ['a', 'ε', 'Nothing', 'a and ε'], answer: 2, why: 'A concatenation needs a piece from each side, and ∅ has none.' },
      { q: 'The leaves of the tree, read left to right, give…', options: ['the symbols of the expression in order', 'a string the expression matches', 'the alphabet', 'the shortest match'], answer: 0, why: 'The tree keeps the order of the expression; which strings match depends on the operators above the leaves.' },
    ],
  });

  // ---- Thompson -------------------------------------------------------------------------------------------------
  // Every fragment is laid out as a box: its start state at the far left, its accepting state at the far
  // right, so a star's loop back and its skip can arc over and under the piece they repeat.
  const SR = 17, GAP = 34, PAD = 9, BAND = 22;
  function thompsonLayout(A, tr) {
    // fragment for node k of the post-order is tr[k]
    const frag = new Map();
    A.post.forEach((n, k) => {
      const f = tr[k];
      let w, h, cy, place;
      if (!n.kids.length) {
        w = 2 * SR + 52 + 2 * SR; h = 2 * SR; cy = SR;
        place = (x, y, P) => { P.st[f.start] = { x: x + SR, y: y + cy }; P.st[f.accept] = { x: x + w - SR, y: y + cy }; };
      } else if (n.t === 'cat') {
        const [p, q] = n.kids.map((c) => frag.get(c.id));
        cy = Math.max(p.cy, q.cy); w = p.W + 30 + q.W; h = cy + Math.max(p.H - p.cy, q.H - q.cy);
        place = (x, y, P) => { p.place(x, y + cy - p.cy, P); q.place(x + p.W + 30, y + cy - q.cy, P); };
      } else if (n.t === 'alt') {
        const [p, q] = n.kids.map((c) => frag.get(c.id));
        const inner = Math.max(p.W, q.W);
        w = 4 * SR + 2 * GAP + inner; h = p.H + 14 + q.H; cy = h / 2;
        place = (x, y, P) => { P.st[f.start] = { x: x + SR, y: y + cy }; P.st[f.accept] = { x: x + w - SR, y: y + cy }; const cx = x + 2 * SR + GAP; p.place(cx + (inner - p.W) / 2, y, P); q.place(cx + (inner - q.W) / 2, y + p.H + 14, P); };
      } else {
        const p = frag.get(n.kids[0].id);
        const iw = 4 * SR + 2 * GAP + p.W;
        // the loop runs above the piece and the skip below it, each in a lane of its own
        const up = n.t !== 'opt' ? 24 : 0, down = n.t !== 'plus' ? 24 : 0;
        w = iw; cy = p.cy + up; h = up + p.H + down;
        place = (x, y, P) => { P.st[f.start] = { x: x + SR, y: y + cy }; P.st[f.accept] = { x: x + w - SR, y: y + cy }; p.place(x + 2 * SR + GAP, y + up, P); };
      }
      // the box around the fragment: padding, and a band below for its name
      const W = w + 2 * PAD, H = h + PAD + BAND + (n.kids.length ? PAD : 0);
      const top = PAD;
      const me = { W, H, cy: cy + top, place: null, f, n };
      me.place = (x, y, P) => { P.box[n.id] = { x, y, w: W, h: H }; place(x + PAD, y + top, P); };
      frag.set(n.id, me);
    });
    const P = { st: {}, box: {} };
    const root = frag.get(A.root.id);
    root.place(0, 0, P);
    return { P, frag };
  }

  T.topic({
    id: 'regex-thompson', family: 'regex', order: 20, title: 'Thompson\'s construction',
    blurb: 'Every piece of the expression becomes a small NFA with one way in and one way out. Pieces are glued with ε-moves: side by side for concatenation, in parallel for union, with a loop and a skip for star.',
    inputs: [X.input('r', 'Expression', '(a|b)*b', 8)],
    presets: [
      { label: '(a|b)*b', values: { r: '(a|b)*b' } },
      { label: 'ab|c', values: { r: 'ab|c' } },
      { label: 'Star on a concatenation: (ab)*', values: { r: '(ab)*' } },
      { label: 'Plus and option: a+b?', values: { r: 'a+b?' } },
      { label: 'ε and ∅ fragments: (ε|a)∅', values: { r: '(ε|a)∅' } },
    ],
    counters: [{ id: 'states', label: 'states' }, { id: 'eps', label: 'ε-moves' }, { id: 'sym', label: 'symbol moves' }],
    run(inp) {
      const ast = RE.parse(inp.r);
      const A = X.annotate(ast);
      const th = RE.thompson(ast);
      const tr = th.trace;
      const { P } = thompsonLayout(A, tr);
      const nodeOf = new Map(A.post.map((n, k) => [n.id, k]));
      const depth = (n) => n.id.length - 1;
      const born = new Set(), madeEdges = [], doneNodes = new Set();
      const F = new T.Frames(['states', 'eps', 'sym']);
      const rootBox = P.box[A.root.id];
      const cw = 34, ex0 = rootBox.x + rootBox.w / 2 - (A.chars.length * cw) / 2;
      // which bend each ε-move takes: a star's loop arcs over its piece, its skip under it
      const laneOf = (e, k) => {
        const n = A.post[k], f = tr[k];
        if (!['star', 'plus', 'opt'].includes(n.t)) return null;
        const inner = tr[nodeOf.get(n.kids[0].id)], b = P.box[n.kids[0].id];
        if (e.from === inner.accept && e.to === inner.start) return b.y - 12;
        if (e.from === f.start && e.to === f.accept) return b.y + b.h + 12;
        return null;
      };
      // regions outermost first, so inner boxes are drawn on top of the ones around them
      const byDepth = A.post.slice().sort((x, y) => depth(x) - depth(y));
      const scene = (cur, opts) => {
        opts = opts || {};
        const items = [];
        const row = X.exprRow(A, { x: ex0, y: -70, cw, cls: (i) => (cur && i >= cur.span[0] && i < cur.span[1] ? 'hot' : '') });
        items.push(...row.items);
        for (const n of byDepth) {
          const b = P.box[n.id], on = doneNodes.has(n.id);
          items.push({ key: 'box:' + n.id, kind: 'region', x: b.x, y: b.y, w: b.w, h: b.h, rx: 10, cls: 'rk' + (depth(n) % 8) + (cur && cur.id === n.id ? ' rk-hot' : ''), opacity: on ? 1 : 0 });
          items.push({ key: 'boxl:' + n.id, kind: 'text', x: b.x + 8, y: b.y + b.h - 7, text: n.text, cls: 'mono', size: 13, opacity: on ? 1 : 0 });
        }
        for (const q of born) items.push({ key: 'q:' + q, kind: 'state', x: P.st[q].x, y: P.st[q].y, w: 2 * SR, h: 2 * SR, rx: SR, text: q, size: 13, cls: (opts.fresh && opts.fresh.includes(q) ? 'active' : '') + (opts.pick && opts.pick === q ? '' : ''), accept: opts.final && q === th.fa.accept[0], pick: true, enter: 'grow' });
        for (const m of madeEdges) {
          const e = m.e, hot = opts.newEdges && opts.newEdges.includes(m);
          const cls = (e.sym === '' ? 'alt' : 'tr') + (hot ? ' hot' : ''), key = 'e:' + e.from + '>' + e.to;
          if (m.lane !== null) {
            const fx = P.st[e.from].x, tx = P.st[e.to].x, y = m.lane;
            items.push({ key: key + ':1', kind: 'edge', from: 'q:' + e.from, to: { x: fx, y }, head: false, cls });
            items.push({ key: key + ':2', kind: 'edge', from: { x: fx, y }, to: { x: tx, y }, head: false, cls });
            items.push({ key: key + ':3', kind: 'edge', from: { x: tx, y }, to: 'q:' + e.to, cls });
            continue;
          }
          const it = { key, kind: 'edge', from: 'q:' + e.from, to: 'q:' + e.to, cls };
          if (e.sym !== '') { const a = P.st[e.from], b = P.st[e.to]; it.label = e.sym; it.lx = (a.x + b.x) / 2; it.ly = (a.y + b.y) / 2 - 15; it.size = 15; it.labelCls = hot ? 'hot' : ''; }
          items.push(it);
        }
        if (opts.final) {
          const s = P.st[th.fa.start];
          items.push({ key: 'start', kind: 'edge', from: { x: s.x - SR - 40, y: s.y }, to: 'q:' + th.fa.start, cls: 'start-arrow taken' });
        }
        return items;
      };
      F.add({ items: scene(null), say: 'Build an NFA for ' + RE.show(ast) + ' from the inside out: every subexpression becomes a fragment with one start state (left) and one accepting state (right). Purple arrows are ε-moves.' });
      tr.forEach((s, k) => {
        const n = A.post[k];
        const fresh = [s.start, s.accept].filter((q) => !born.has(q));
        fresh.forEach((q) => born.add(q));
        const have = new Set(madeEdges.map((m) => m.e.from + '>' + m.e.to));
        const own = s.edges.filter((e) => !have.has(e.from + '>' + e.to));
        const newEdges = own.map((e) => ({ e, lane: laneOf(e, k) }));
        madeEdges.push(...newEdges);
        doneNodes.add(n.id);
        F.set('states', born.size).count('eps', own.filter((e) => e.sym === '').length).count('sym', own.filter((e) => e.sym !== '').length);
        const what = { sym: 'two new states and one move on ' + n.c, eps: 'two new states joined by one ε-move', empty: 'two new states and no move at all, so nothing can get from start to end', alt: 'a new start with ε-moves into both pieces, and ε-moves from both ends to a new accepting state', cat: 'one ε-move from the end of ' + (n.kids[0] && n.kids[0].text) + ' to the start of ' + (n.kids[1] && n.kids[1].text) + '; no new states', star: 'new start and end states, an ε-move to enter, one to skip the piece (zero copies), one looping back for another copy, and one to leave', plus: 'new start and end states, ε-moves to enter, loop back and leave, but no skip: at least one copy', opt: 'new start and end states, ε-moves to enter or to skip the piece' }[n.t];
        F.add({ items: scene(n, { fresh, newEdges }), say: n.text + ': ' + what + '.', hl: { rules: [String(['sym', 'eps', 'empty', 'alt', 'cat', 'star', 'plus', 'opt'].indexOf(n.t))] }, meta: { node: n.t, newEps: own.filter((e) => e.sym === '').length, catFrom: n.t === 'cat' ? tr[nodeOf.get(n.kids[0].id)].accept : null } });
      });
      const nE = th.fa.trans.filter((e) => e.sym === '').length;
      F.add({ items: scene(null, { final: true }), say: 'Done: start in ' + th.fa.start + ', accept in ' + th.fa.accept[0] + '. ' + th.fa.states.length + ' states and ' + th.fa.trans.length + ' moves, ' + nE + ' of them ε: at most two states per symbol or operator, which is why the construction is used in practice.', mark: 'done' });
      const dt = R.delta(th.fa);
      return { frames: F.list, def: { sections: [{ id: 'rules', kind: 'math', title: 'One fragment per node', text: 'a     s -a-> f\nε     s -ε-> f\n∅     s   f  (no move)\nr|s   new s, f; ε in, ε out\nrs    ε: end of r → start of s\nr*    new s, f; in, skip, loop, out\nr+    new s, f; in, loop, out\nr?    new s, f; in, skip' }, dt.section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.node === 'cat', once: true, pick: 'item', ask: 'The next fragment is a concatenation. Click the state the new ε-move leaves from.', answer: (fr, i) => 'q:' + fr[i + 1].meta.catFrom, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && ['star', 'alt', 'plus', 'opt'].includes(fr[i + 1].meta.node), once: true, pick: 'option', options: ['1', '2', '3', '4', '5'], ask: (fr, i) => 'How many ε-moves will the next fragment (' + { star: 'a star', alt: 'a union', plus: 'a plus', opt: 'an option' }[fr[i + 1].meta.node] + ') add?', answer: (fr, i) => String(fr[i + 1].meta.newEps), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why does every Thompson fragment have exactly one start and one accepting state?', options: ['To save states', 'So fragments can be glued together with single ε-moves', 'Because NFAs must', 'To avoid ε-moves'], answer: 1, why: 'Concatenation, union and star only need to connect one way in and one way out of each piece.' },
      { q: 'In the fragment for r*, which ε-move makes ε acceptable?', options: ['The loop from r\'s end back to its start', 'The skip from the new start straight to the new end', 'The move into r', 'None of them'], answer: 1, why: 'Skipping the piece altogether reads zero copies, which is the empty string.' },
      { q: 'How many states does Thompson\'s construction give for an expression with k symbols and operators (counting each symbol, ε and ∅ too, but not concatenations)?', options: ['k', 'at most 2k', 'k²', '2ᵏ'], answer: 1, why: 'Each symbol, ε, ∅, union or star adds two states; concatenation adds none.' },
      { q: 'What is special about the fragment for ∅?', options: ['It has one state', 'It has no move from its start to its end', 'It accepts ε', 'It loops'], answer: 1, why: 'Nothing can get through it, so whatever is concatenated with it matches nothing.' },
    ],
  });

  // ---- positions ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'regex-glushkov', family: 'regex', order: 30, title: 'The position automaton',
    blurb: 'Number every symbol occurrence. Which positions can begin a word, which can end one, and which can follow which: those three sets are a whole NFA, with no ε-moves.',
    inputs: [X.input('r', 'Expression', '(ab|b)*a', 10)],
    presets: [
      { label: '(ab|b)*a', values: { r: '(ab|b)*a' } },
      { label: 'a(a|b)*b', values: { r: 'a(a|b)*b' } },
      { label: 'Matches ε: (ab)*', values: { r: '(ab)*' } },
      { label: 'Same symbol twice: a*ab', values: { r: 'a*ab' } },
    ],
    counters: [{ id: 'pos', label: 'positions' }, { id: 'moves', label: 'moves' }],
    run(inp) {
      const ast = RE.parse(inp.r);
      const A = X.annotate(ast);
      const gl = RE.glushkov(ast);
      const tr = gl.trace;
      const posNames = tr.find((s) => s.kind === 'positions').positions;
      const first = tr.find((s) => s.kind === 'first').set, last = tr.find((s) => s.kind === 'last').set;
      const nl = tr.find((s) => s.kind === 'last').nullable;
      const follow = tr.filter((s) => s.kind === 'follow');
      // which character of the expression each position is
      const symIdx = [];
      A.chars.forEach((c, i) => { const n = A.post.find((p) => p.t === 'sym' && p.span[0] === i); if (n) symIdx.push(i); });
      const posOf = (i) => symIdx.indexOf(i);
      const F = new T.Frames(['pos', 'moves']);
      const m = R.dia(gl.fa);
      const pos = K.graph.layout(m, { gapX: 170, gapY: 130 }).pos;
      const g0 = K.graph.draw(m, { pos });
      const cross = X.crosses(g0);
      const cw = 38;
      const tableRows = (k) => [['first', '{' + first.join(', ') + '}'], ['last', '{' + last.join(', ') + '}' + (nl ? '  + ε' : '')]].concat(follow.map((f, j) => (j < k ? ['follow(' + f.position + ')', '{' + f.set.join(', ') + '}'] : ['follow(' + f.position + ')', ''])));
      const gx = g0.box.x, gy = g0.box.y;
      const ex0 = gx - 410, ey = gy;
      const scene = (o) => {
        const items = [];
        const row = X.exprRow(A, { x: ex0, y: ey, cw, cls: (i) => { const p = posOf(i); if (p < 0) return ''; const nm = posNames[p]; return (o.hot === nm ? 'hot' : o.lit && o.lit.includes(nm) ? 'act' : o.numbered ? '' : ''); } });
        // the position numbers under the symbols
        if (o.numbered) symIdx.forEach((i, p) => items.push({ key: 'pn:' + p, kind: 'text', x: ex0 + i * cw + cw / 2, y: ey + 58, text: String(p + 1), anchor: 'middle', cls: 'hot', size: 14 }));
        items.push(...row.items);
        if (o.rows !== undefined) {
          const rows = tableRows(o.rows).slice(0, o.showLast ? 2 + o.rows : o.showFirst ? 1 : 0);
          if (rows.length) items.push(...K.table.draw({ rows: rows.map((r) => [r[1]]), rowHead: rows.map((r) => r[0]), x: ex0, y: ey + 84, mono: true, size: 14, ch: 32, cw: 200, prefix: 'ft', hot: o.trow !== undefined ? [[o.trow, 0]] : [] }).items);
        }
        if (o.machine) {
          let g = K.graph.draw(Object.assign({}, m, { trans: m.trans.filter((t) => o.machine.edges.includes(t.from)), accept: o.machine.accept ? m.accept : [] }), { pos, enter: 'grow', hot: o.machine.hot || [], taken: o.machine.taken || [], hideStart: false }).items;
          if (cross) g = X.edgeX(g);
          items.push(...g);
        }
        return items;
      };
      F.add({ items: scene({}), say: 'The expression ' + RE.show(ast) + ' uses ' + posNames.length + ' symbol occurrence' + (posNames.length === 1 ? '' : 's') + '. The automaton will have one state for each, plus a start state i.' });
      F.set('pos', posNames.length);
      F.add({ items: scene({ numbered: true }), say: 'Number the occurrences: ' + posNames.join(', ') + '. Two occurrences of the same symbol are different positions.' });
      F.add({ items: scene({ numbered: true, rows: 0, showFirst: true, lit: first, trow: 0 }), say: 'first = {' + first.join(', ') + '}: the positions that can begin a matching word.', meta: { lit: first, ask: 'first', symIdx, names: posNames } });
      F.add({ items: scene({ numbered: true, rows: 0, showLast: true, lit: last, trow: 1 }), say: 'last = {' + last.join(', ') + '}: the positions that can end a word' + (nl ? '; the expression also matches ε, so the start state will accept.' : '.') });
      follow.forEach((f, j) => F.add({ items: scene({ numbered: true, rows: j + 1, showLast: true, hot: f.position, lit: f.set, trow: 2 + j }), say: 'follow(' + f.position + ') = {' + f.set.join(', ') + '}: ' + (f.set.length ? 'the positions that can come right after ' + f.position + ' in a matching word.' : 'nothing can come after ' + f.position + '.'), meta: { follow: f, lit: f.set } }));
      const all = ['i'].concat(posNames);
      const done = [];
      F.add({ items: scene({ numbered: true, rows: follow.length, showLast: true, machine: { edges: [] } }), say: 'One state per position, plus i. A move into position p always reads p\'s symbol, so the state names say what was just read.' });
      for (const q of all) {
        done.push(q);
        const outs = gl.fa.trans.filter((e) => e.from === q);
        F.count('moves', outs.length);
        F.add({ items: scene({ numbered: true, rows: follow.length, showLast: true, hot: q === 'i' ? null : q, lit: q === 'i' ? first : (follow.find((f) => f.position === q) || { set: [] }).set, trow: q === 'i' ? 0 : 2 + posNames.indexOf(q), machine: { edges: done.slice(), hot: [q], taken: outs.map((e) => q + '>' + e.to) } }), say: q === 'i' ? 'From i, a move to every position in first: ' + (outs.map((e) => 'i -' + e.sym + '-> ' + e.to).join(', ') || 'none') + '.' : 'From ' + q + ', a move to every position in follow(' + q + '): ' + (outs.map((e) => q + ' -' + e.sym + '-> ' + e.to).join(', ') || 'none') + '.' });
      }
      F.add({ items: scene({ numbered: true, rows: follow.length, showLast: true, machine: { edges: all, accept: true } }), say: 'Accept in the last positions ' + R.set(last) + (nl ? ' and in i' : '') + '. ' + all.length + ' states, no ε-moves: the position automaton.', mark: 'done' });
      return { frames: F.list, def: { sections: [{ id: 'rule', kind: 'math', title: 'The automaton', text: 'states: i, one per position\ni -a-> p   p ∈ first\nq -a-> p   p ∈ follow(q)\n(a is the symbol of p)\naccept: last, and i if ε matches' }, R.delta(gl.fa).section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.ask === 'first', once: true, pick: 'item', ask: 'Click a symbol of the expression that can begin a matching word.', answer: (fr, i) => fr[i + 1].meta.lit.map((nm) => 'ex:c:' + fr[i + 1].meta.symIdx[fr[i + 1].meta.names.indexOf(nm)]), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.follow && fr[i + 1].meta.follow.set.length, once: true, pick: 'option', options: (fr, i) => R.numberOptions(fr[i + 1].meta.follow.set.length), ask: (fr, i) => 'How many positions are in follow(' + fr[i + 1].meta.follow.position + ')?', answer: (fr, i) => String(fr[i + 1].meta.follow.set.length), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'How many states does the position automaton of an expression with n symbol occurrences have?', options: ['n', 'n + 1', '2n', '2ⁿ'], answer: 1, why: 'One per position and one start state.' },
      { q: 'Does the position automaton have ε-moves?', options: ['Yes, like Thompson\'s', 'No', 'Only for stars', 'Only when the expression matches ε'], answer: 1, why: 'Every move reads the symbol of the position it enters.' },
      { q: 'When is the start state i accepting?', options: ['Always', 'Never', 'When the expression matches ε', 'When first is empty'], answer: 2, why: 'Accepting in i means accepting the empty input.' },
      { q: 'In (ab|b)*a, why is a1 in follow(b2)?', options: ['Because a follows b in the alphabet', 'Because after ab the star can start another copy with ab', 'Because a1 is in last', 'It is not'], answer: 1, why: 'b2 ends the piece ab, and the star lets a new piece begin, possibly with a1.' },
    ],
  });

  // ---- derivatives -------------------------------------------------------------------------------------------------
  T.topic({
    id: 'regex-derivatives', family: 'regex', order: 40, title: 'Derivatives: expressions as states',
    blurb: 'The derivative of r by a is what is left to match after reading a. Take derivatives over and over: each new expression is a new state, and ∅ is the dead state.',
    inputs: [X.input('r', 'Expression', '(ab|b)*a', 10)],
    presets: [
      { label: '(ab|b)*a', values: { r: '(ab|b)*a' } },
      { label: 'Ends with ab: (a|b)*ab', values: { r: '(a|b)*ab' } },
      { label: 'Finite: ab|ba', values: { r: 'ab|ba' } },
      { label: 'Everything: (a|b)*', values: { r: '(a|b)*' } },
      { label: 'Nothing: a∅', values: { r: 'a∅|∅b' } },
    ],
    counters: [{ id: 'states', label: 'states' }, { id: 'derivs', label: 'derivatives taken' }],
    run(inp) {
      const ast = RE.parse(inp.r);
      const dd = RE.derivativeDFA(ast, { alphabet: RE.alphabet(ast).length ? RE.alphabet(ast) : ['a'] });
      const fa = dd.fa, labels = dd.labels;
      const boxes = {};
      for (const q of fa.states) boxes[q] = [q + ' = ' + (labels[q] === '∅' ? '∅ (dead)' : labels[q])];
      const m = R.dia(fa);
      const pos = K.graph.layout(m, { boxes }).pos;
      const g0 = K.graph.draw(m, { pos, boxes });
      const cross = X.crosses(g0);
      const born = [], edges = [];
      const F = new T.Frames(['states', 'derivs']);
      const b0 = R.bounds(g0.items);
      const noteY = b0.y + b0.h + 30;
      const card = (s) => R.note('card', { x: b0.x + b0.w / 2 - 200, y: noteY, title: 'derivative', lines: s ? ['∂' + s.sym + '(' + labels[s.from] + ')', '= ' + s.raw, s.raw !== s.regex ? '= ' + s.regex + '  (tidied)' : ' '] : [' ', ' ', ' '], mono: true, size: 15 }).items;
      const scene = (o) => {
        const mm = Object.assign({}, m, { states: born.slice(), accept: fa.accept.filter((q) => born.includes(q)), trans: m.trans.filter(() => false) });
        // edges added so far (merged per pair)
        const by = new Map();
        for (const e of edges) { const k = e.from + '>' + e.to; if (!by.has(k)) by.set(k, { from: e.from, to: e.to, label: e.sym }); else by.get(k).label += ', ' + e.sym; }
        mm.trans = [...by.values()];
        let it = K.graph.draw(mm, { pos, boxes, enter: 'grow', hot: o.hot || [], taken: o.taken || [], good: o.good || [], dead: born.filter((q) => labels[q] === '∅') }).items;
        if (cross) it = X.edgeX(it);
        return it.concat(card(o.step));
      };
      const tr = dd.trace;
      born.push('d0');
      F.set('states', 1);
      F.add({ items: scene({ hot: ['d0'] }), say: 'The first state is the expression itself, d0 = ' + labels.d0 + (fa.accept.includes('d0') ? '. It matches ε, so it accepts.' : '. It does not match ε, so it does not accept.'), hl: { st: ['0'] } });
      tr.filter((s) => s.kind === 'derivative').forEach((s) => {
        F.count('derivs');
        if (s.fresh) { born.push(s.to); F.set('states', born.length); }
        edges.push(s);
        F.add({ items: scene({ step: s, hot: [s.from], taken: [s.from + '>' + s.to], good: s.fresh ? [s.to] : [] }), say: '∂' + s.sym + '(' + labels[s.from] + ') = ' + s.regex + (s.regex === '∅' ? ' (nothing can follow)' : '') + '. ' + (s.fresh ? 'A new expression, so a new state ' + s.to + (s.accepting ? ', accepting because it matches ε.' : '.') : 'That is ' + s.to + ' again: no new state.'), hl: { st: [String(fa.states.indexOf(s.to))] }, meta: { step: s } });
      });
      F.add({ items: scene({}), say: R.plural(fa.states.length, 'distinct derivative') + ', so a DFA with ' + R.plural(fa.states.length, 'state') + '. Accepting states are the expressions that match ε. Tidying (sorting and merging unions, dropping ∅ and ε) is what keeps the number finite.', mark: 'done' });
      const rows = fa.states.map((q) => [labels[q], fa.accept.includes(q) ? 'yes' : 'no']);
      return { frames: F.list, def: { sections: [{ id: 'rules', kind: 'math', title: 'Rules', text: '∂a(a) = ε,  ∂a(b) = ∅\n∂a(ε) = ∂a(∅) = ∅\n∂a(r|s) = ∂a(r) | ∂a(s)\n∂a(rs) = ∂a(r)s | ∂a(s)  (r ∋ ε)\n∂a(rs) = ∂a(r)s  (otherwise)\n∂a(r*) = ∂a(r) r*' }, { id: 'st', kind: 'table', title: 'States', colHead: ['expression', 'accepts'], rowHead: fa.states, rows }] } };
    },
    predict: [
      { at: (f, i, fr) => i > 1 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.step && !fr[i + 1].meta.step.fresh, once: true, pick: 'item', ask: (fr, i) => { const s = fr[i + 1].meta.step; return 'Take ∂' + s.sym + ' of ' + s.from + '. It turns out to be a state that already exists: click it.'; }, answer: (fr, i) => 'g:s:' + fr[i + 1].meta.step.to, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.step && i > 0, once: true, pick: 'option', options: ['A new state', 'A state we already have'], ask: (fr, i) => 'Will ∂' + fr[i + 1].meta.step.sym + '(' + fr[i + 1].meta.step.from + ') be a new expression?', answer: (fr, i) => (fr[i + 1].meta.step.fresh ? 'A new state' : 'A state we already have'), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What is ∂a(ab*)?', options: ['b*', 'ab*', '∅', 'ε'], answer: 0, why: 'After reading a, what is left to match is b*.' },
      { q: 'What is ∂b(ab*)?', options: ['b*', 'a', '∅', 'ε'], answer: 2, why: 'Every word of ab* starts with a, so nothing is left after b.' },
      { q: 'When does the derivative state accept?', options: ['When its expression is ∅', 'When its expression matches ε', 'When it has a loop', 'Always'], answer: 1, why: 'Accepting after reading w means w itself matched, i.e. what remains matches ε.' },
      { q: 'Why do we tidy each derivative (merge equal unions, drop ∅)?', options: ['To make it shorter to print', 'Without it the expressions can grow for ever and the DFA would not be finite', 'To make it nondeterministic', 'To remove the dead state'], answer: 1, why: 'Up to these simple identities there are only finitely many derivatives.' },
      { q: 'What does the state ∅ do?', options: ['Accepts everything', 'Acts as the dead state', 'Is the start', 'Matches ε'], answer: 1, why: 'Every derivative of ∅ is ∅ and it never matches ε.' },
    ],
  });

  // ---- simplification -------------------------------------------------------------------------------------------
  const RULES = ['r|∅ = r', 'r∅ = ∅r = ∅', 'rε = εr = r', '∅* = ε* = ε', 'ε+ = ε? = ε', '∅+ = ∅', '∅? = ε', '(r*)* = r*', '(r*)+ = (r*)? = r*', '(r+)+ = r+', '(r?)? = r?', '(r+)? = (r?)+ = r*', 'r? = r when r matches ε', 'r|r = r', 'r|s = s when r ⊆ s', '(ε|r)* = r*', '(r|s*)* = (r|s)*', '(r*s*)* = (r|s)*', 'r*r* = r*', 'rs|rt = r(s|t)', 'sr|tr = (s|t)r', 'rr* = r*r = r+', 'ε|r = r?'];
  // replace the first node (post-order) printed as `before` by the parse of `after`
  function rewrite(ast, before, after) {
    let done = false, found = null;
    const go = (r, path) => {
      if (done) return r;
      let n = r;
      if (r.t === 'alt' || r.t === 'cat') n = { t: r.t, a: go(r.a, path + 'l'), b: go(r.b, path + 'r') };
      else if (r.t === 'star' || r.t === 'plus' || r.t === 'opt') n = { t: r.t, x: go(r.x, path + 'x') };
      if (!done && RE.show(n) === before) { done = true; found = path; return RE.parse(after); }
      return n;
    };
    const out = go(ast, 'n');
    if (done) return { ast: out, path: found };
    // the engine's grouping may differ from ours: rewrite the text instead
    const s = RE.show(ast), k = s.indexOf(before);
    if (k >= 0) return { ast: RE.parse(s.slice(0, k) + '(' + after + ')' + s.slice(k + before.length)), path: null };
    return { ast, path: null };
  }
  T.topic({
    id: 'regex-simplify', family: 'regex', order: 80, title: 'Simplifying an expression',
    blurb: 'Rules like (r*)* = r* and r|∅ = r shrink an expression without changing its language. Watch them fire one at a time on the tree.',
    inputs: [X.input('r', 'Expression', '(a*)*b|∅', 14)],
    presets: [
      { label: 'Nested stars: (a*)*b', values: { r: '(a*)*b|∅' } },
      { label: 'ε and ∅: ∅*a|a∅', values: { r: '∅*a|a∅' } },
      { label: 'Swallowed: a|ε|a*', values: { r: 'a|ε|a*' } },
      { label: 'Factoring: ab|ac', values: { r: 'ab|ac' } },
      { label: '(a*b*)* is (a|b)*', values: { r: '(a*b*)*' } },
      { label: 'Already simple: ab*', values: { r: 'ab*' } },
    ],
    counters: [{ id: 'rules', label: 'rules applied' }, { id: 'size', label: 'size' }],
    run(inp) {
      let ast = RE.parse(inp.r);
      const s = RE.simplify(ast);
      const F = new T.Frames(['rules', 'size']);
      const draw = (a, hot, card) => {
        const A = X.annotate(a);
        const sub = new Set();
        if (hot) for (const n of A.post) if (n.id.startsWith(hot)) sub.add(n.id);
        const t = K.tree.draw(X.treeNode(A.root, null, (n) => (sub.has(n.id) ? 'hot' : '')), { gapX: 24, gapY: 74, y: 90 });
        const cw = 34, ex = t.box.x + t.box.w / 2 - (A.chars.length * cw) / 2;
        const hn = hot ? A.post.find((n) => n.id === hot) : null;
        const row = X.exprRow(A, { x: ex, y: 0, cw, prefix: 'sx', cls: (i) => (hn && i >= hn.span[0] && i < hn.span[1] ? 'hot' : '') });
        const items = t.items.concat(row.items);
        if (card) items.push(...R.note('card', { x: Math.max(t.box.x + t.box.w, ex + A.chars.length * cw) + 40, y: 70, title: 'rule', lines: card, mono: true, size: 15 }).items);
        return { items, A };
      };
      F.set('size', RE.size(ast));
      F.add({ items: draw(ast).items, say: RE.show(ast) + ' has ' + RE.size(ast) + ' symbols and operators. Rules are tried from the leaves up; each one keeps the language the same.' });
      if (!s.trace.length) F.add({ items: draw(ast).items, say: 'No rule applies: ' + RE.show(ast) + ' is already as simple as these rules can make it.', mark: 'done' });
      s.trace.forEach((st) => {
        const r = rewrite(ast, st.before, st.after);
        const pre = draw(ast, r.path, [st.rule, st.before + '  →  ' + st.after]);
        F.add({ items: pre.items, say: 'The rule ' + st.rule + ' fits ' + st.before + '.', hl: { rules: [String(RULES.indexOf(st.rule))] }, meta: { rule: st.rule, path: r.path, keys: r.path ? pre.A.post.filter((n) => n.id.startsWith(r.path)).map((n) => 'tr:n:' + n.id) : null } });
        ast = r.ast;
        F.count('rules').set('size', RE.size(ast));
        F.add({ items: draw(ast, null, [st.rule, st.before + '  →  ' + st.after]).items, say: st.before + ' becomes ' + st.after + ': the expression is now ' + RE.show(ast) + '.', hl: { rules: [String(RULES.indexOf(st.rule))] } });
      });
      if (s.trace.length) {
        const eq = RE.equivalent(inp.r, s.regex);
        F.add({ items: draw(s.ast).items, say: 'No rule fits any more: ' + RE.show(RE.parse(inp.r)) + ' simplifies to ' + s.regex + ' (size ' + RE.size(RE.parse(inp.r)) + ' → ' + RE.size(s.ast) + ')' + (eq.equal ? ', and a check of their automata confirms the language is unchanged.' : '.'), mark: 'done' });
      }
      return { frames: F.list, def: { sections: [{ id: 'rules', kind: 'math', title: 'The rules', text: RULES.join('\n') }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.keys && fr[i + 1].meta.keys.length && i === 0, once: true, pick: 'item', ask: 'Click a node of the part of the tree the first rule will rewrite.', answer: (fr, i) => fr[i + 1].meta.keys, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i > 0 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.rule, once: true, pick: 'option', options: (fr, i) => { const r = fr[i + 1].meta.rule; const others = ['(r*)* = r*', 'r|∅ = r', 'rε = εr = r', 'r|s = s when r ⊆ s', 'rs|rt = r(s|t)', 'r*r* = r*'].filter((x) => x !== r).slice(0, 3); return [r].concat(others).sort(); }, ask: 'Which rule will fire next?', answer: (fr, i) => fr[i + 1].meta.rule, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Simplify (a*)*.', options: ['a', 'a*', 'a+', 'ε'], answer: 1, why: 'Repeating a repetition repeats the same thing: (r*)* = r*.' },
      { q: 'Simplify a|∅.', options: ['∅', 'a', 'a|ε', 'ε'], answer: 1, why: '∅ adds nothing to a union.' },
      { q: 'Simplify a∅b.', options: ['ab', '∅', 'ε', 'a|b'], answer: 1, why: 'A concatenation with ∅ in it has nothing to take from that part.' },
      { q: 'Is a|a* equal to a*?', options: ['Yes: a is already in a*', 'No: a* lacks a', 'Only for long strings', 'No: a|a* also has ε'], answer: 0, why: 'L(a) ⊆ L(a*), so the union adds nothing: r|s = s when r ⊆ s.' },
      { q: 'Can such rules always find the shortest equivalent expression?', options: ['Yes', 'No: finding the smallest equivalent expression is a hard problem in general', 'Only for finite languages', 'Only without stars'], answer: 1, why: 'Rules are local rewrites; deciding the minimum takes far more work in general.' },
    ],
  });
})();
