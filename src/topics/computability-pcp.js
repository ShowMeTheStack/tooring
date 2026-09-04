// The Post correspondence problem: a domino puzzle the student plays, the search tree a solver walks
// (overhangs, dead ends, repeats and the bound), the modified problem turned into the plain one with
// stars, and a Turing machine turned into dominoes whose only match spells its accepting computation.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const Geo = T.geom;

  T.family({ id: 'pcp', part: 'computability', order: 70, title: 'Post correspondence', blurb: 'Dominoes with a string on top and one below: can you line some up so the two rows read the same? A puzzle simple enough for a child and too hard for any algorithm.' });

  const show = (s) => (s === '' ? 'ε' : s);
  /** "a/aab" -> {top, bottom}; ε for an empty side */
  const parseDom = (x) => { const p = String(x).split('/'); return { top: p[0] === 'ε' ? '' : p[0], bottom: p[1] === 'ε' ? '' : p[1] }; };
  const checkDominoes = (v, label, maxN, maxLen) => {
    if (!Array.isArray(v) || !v.length) return label + ': write the dominoes as top/bottom, like ab/a, b/bb';
    if (v.length > maxN) return label + ': at most ' + maxN + ' dominoes, so the picture stays readable';
    for (const x of v) {
      const p = String(x).split('/');
      if (p.length !== 2) return label + ': "' + x + '" should be top/bottom, like ab/a';
      for (const s of p) {
        if (s === 'ε') continue;
        if (!s) return label + ': "' + x + '" has an empty side; write ε for the empty string';
        if (!/^[ab01]+$/.test(s)) return label + ': "' + x + '" may only use a, b, 0 and 1';
        if (s.length > maxLen) return label + ': "' + x + '" is too long (at most ' + maxLen + ' symbols a side)';
      }
      if (p[0] === p[1] || (p[0] === 'ε' && p[1] === 'ε')) return label + ': "' + x + '" is a match all by itself; the puzzle would be trivial';
    }
    return null;
  };
  /** How two rows compare: {bad: first clash or -1, side, over} */
  const compare = (top, bot) => {
    const n = Math.min(top.length, bot.length);
    for (let i = 0; i < n; i++) if (top[i] !== bot[i]) return { bad: i };
    return { bad: -1, side: top.length >= bot.length ? 'top' : 'bottom', over: top.length >= bot.length ? top.slice(n) : bot.slice(n) };
  };
  const domTable = (tiles, extra) => ({ id: 'dom', kind: 'table', title: 'The dominoes', colHead: ['top', 'bottom'].concat(extra ? ['role'] : []), rowHead: tiles.map((_, i) => String(i + 1)), rows: tiles.map((t) => [show(t.top), show(t.bottom)].concat(extra ? [t.role || ''] : [])) });

  // ---------------------------------------------------------------- pcp-play: the puzzle
  const PLAY = ['a/aab', 'a/b', 'ba/a'];
  const SHORT = ['abb/b', 'a/aab', 'b/ba'];
  T.topic({
    id: 'pcp-play', family: 'pcp', order: 10, title: 'The domino puzzle',
    blurb: 'Lay dominoes side by side, using any of them as often as you like, until the string along the top equals the string along the bottom. Type your own sequence and watch the rows agree, run ahead or clash.',
    inputs: [
      { id: 'd', kind: 'list', label: 'Dominoes (top/bottom)', def: PLAY, check: (v) => checkDominoes(v, 'Dominoes', 5, 4) },
      { id: 's', kind: 'list', label: 'Your sequence (domino numbers)', def: ['1', '1', '3', '2', '3', '3', '2', '3'], check: (v, inp) => {
        if (!v.length) return 'Your sequence: give at least one domino number';
        if (v.length > 10) return 'Your sequence: at most 10 dominoes';
        const n = (inp.d || []).length;
        const bad = v.find((x) => !/^\d+$/.test(x) || +x < 1 || +x > n);
        return bad !== undefined ? 'Your sequence: "' + bad + '" is not a domino number from 1 to ' + n : null;
      } },
    ],
    presets: [
      { label: 'A long match: eight dominoes', values: { d: PLAY, s: ['1', '1', '3', '2', '3', '3', '2', '3'] } },
      { label: 'A wrong move: the rows clash', values: { d: PLAY, s: ['1', '1', '3', '3'] } },
      { label: 'Stopped too soon: the top is behind', values: { d: PLAY, s: ['1', '1', '3', '2'] } },
      { label: 'A short puzzle', values: { d: SHORT, s: ['2', '1'] } },
      { label: 'A wrong first domino', values: { d: PLAY, s: ['2', '1'] } },
    ],
    counters: [{ id: 'laid', label: 'dominoes laid' }, { id: 'agree', label: 'symbols agreeing' }],
    run(inp) {
      const tiles = inp.d.map(parseDom);
      const seq = inp.s.map((x) => +x - 1);
      const F = new T.Frames(['laid', 'agree']);
      const set = (hot) => K.dominoes.set({ tiles, y: 0, hot: hot === undefined ? [] : [hot] }).items;
      const valid = (st) => tiles.map((t, i) => (T.pcp.extend(st, t) ? i : -1)).filter((i) => i >= 0);
      const SY = 170;
      const scene = (k, hot, brText) => {
        const items = set(hot);
        if (!k) return items.concat([{ key: 'hint', kind: 'text', x: 0, y: SY + 40, text: 'Your row of dominoes will appear here.', cls: 'strong' }]);
        const sq = K.dominoes.sequence({ tiles, seq: seq.slice(0, k), y: SY });
        items.push(...sq.items);
        if (brText) {
          const L = Math.min(sq.top.length, sq.bottom.length), R = Math.max(sq.top.length, sq.bottom.length);
          items.push({ key: 'over', kind: 'bracket', x1: L * 30, x2: R * 30, y: SY + 78 + 34 + 76, side: 'below', text: brText, cls: 'y' });
        }
        return items;
      };
      let st = { side: 'top', over: '' };
      const v0 = valid(st);
      F.add({ items: scene(0), say: 'There are ' + tiles.length + ' dominoes. Line some up, repeats allowed, so that the top row and the bottom row spell the same string. ' + (v0.length ? 'Only ' + v0.map((i) => i + 1).join(' or ') + ' can start: any other disagrees at once.' : 'No domino can even start: each one disagrees with itself in its first symbol, so there is no match.'), meta: { only: v0.length === 1 ? 'pcp:d' + v0[0] : null, why: v0.length === 1 ? 'Domino ' + (v0[0] + 1) + ' is the only one whose top and bottom begin the same way.' : '' }, hl: { dom: [] } });
      let top = '', bot = '';
      for (let k = 1; k <= seq.length; k++) {
        const i = seq[k - 1], t = tiles[i];
        top += t.top; bot += t.bottom;
        const c = compare(top, bot);
        F.count('laid');
        const head = 'Domino ' + (i + 1) + ' (' + show(t.top) + ' over ' + show(t.bottom) + ') goes next: the top now reads ' + show(top) + ' and the bottom ' + show(bot) + '.';
        if (c.bad >= 0) {
          F.set('agree', c.bad);
          const could = valid(st);
          F.add({ items: scene(k, i), say: head + ' At position ' + (c.bad + 1) + ' the top has ' + top[c.bad] + ' but the bottom has ' + bot[c.bad] + ': a clash, and nothing laid later can repair it. ' + (could.length ? 'Domino ' + could.map((j) => j + 1).join(' or ') + ' would have kept the rows agreeing.' : 'In fact no domino could have continued from there.'), mark: 'clash', hl: { dom: [String(i)] } });
          break;
        }
        F.set('agree', Math.min(top.length, bot.length));
        st = { side: c.side, over: c.over };
        if (c.over === '') {
          F.add({ items: scene(k, i), say: head + ' Both rows read ' + top + ': a match with ' + k + ' domino' + (k > 1 ? 'es' : '') + '!' + (k < seq.length ? ' Your sequence goes on, but you could stop here.' : ''), mark: 'match', hl: { dom: [String(i)] } });
          if (k < seq.length) { st = { side: 'top', over: '' }; }
          continue;
        }
        const nxt = valid(st);
        const ahead = c.side === 'top' ? 'top' : 'bottom';
        const say = head + ' They agree so far; the ' + ahead + ' is ahead by ' + c.over + ', and the ' + (ahead === 'top' ? 'bottom' : 'top') + ' must catch up with exactly that. ' + (nxt.length ? (nxt.length === 1 ? 'Only domino ' + (nxt[0] + 1) + ' fits next.' : 'Dominoes ' + nxt.map((j) => j + 1).join(' and ') + ' could follow.') : 'No domino can follow: this is a dead end.');
        const ask = nxt.length === 1 && k < seq.length && F.list.filter((f) => f.meta && f.meta.only).length < 3;
        F.add({ items: scene(k, i, ahead + ' ahead: ' + c.over), say, meta: { only: ask ? 'pcp:d' + nxt[0] : null, why: nxt.length === 1 ? 'Only domino ' + (nxt[0] + 1) + ' starts its ' + (ahead === 'top' ? 'bottom' : 'top') + ' in a way that agrees with the overhang ' + c.over + '.' : '' }, hl: { dom: [String(i)] } });
        if (k === seq.length) F.add({ items: scene(k, i, ahead + ' ahead: ' + c.over), say: 'Your sequence ends here with the ' + ahead + ' still ahead by ' + c.over + ', so this is not a match yet. ' + (nxt.length ? 'Try adding domino ' + nxt.map((j) => j + 1).join(' or ') + '.' : 'And no domino can continue, so this start leads nowhere.'), mark: 'unfinished', hl: { dom: [] } });
      }
      return { frames: F.list, def: { sections: [domTable(tiles), { id: 'rule', kind: 'math', title: 'A match', text: 'a sequence i₁, i₂, …, iₖ (k ≥ 1, repeats allowed)\ntop(i₁) top(i₂) … top(iₖ) = bottom(i₁) bottom(i₂) … bottom(iₖ)' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.only, pick: 'item', ask: 'Only one domino keeps the two rows agreeing from here. Click it in the set at the top.', answer: (fr, i) => fr[i].meta.only, explain: (fr, i) => fr[i].meta.why },
    ],
    quiz: [
      { q: 'In a partial match the top is ahead by ab. What must the next domino do?', options: ['Its top must begin with ab', 'Its bottom must begin with ab, or be a prefix of ab', 'It must be the same domino again', 'Anything: the rows can disagree for a while'], answer: 1, why: 'The bottom has to catch up: the next bottom string must agree with the overhang ab, so it starts with ab or is a beginning of it.' },
      { q: 'Once the two rows disagree at some position, can later dominoes fix it?', options: ['Yes, by adding more symbols', 'No: dominoes only add symbols at the end', 'Only if a domino has ε on one side', 'Only in the modified problem'], answer: 1, why: 'Laying a domino appends to both rows; a clash in the middle stays there for ever.' },
      { q: 'May a match use the same domino more than once?', options: ['No, each domino once', 'Yes, any number of times', 'Only the first domino', 'Only in pairs'], answer: 1, why: 'A match is any sequence of domino numbers, with repeats allowed; that is why there are infinitely many candidates.' },
      { q: 'Why can a computer not simply try every sequence and answer no when none works?', options: ['There are infinitely many sequences, so "none works" is never reached', 'Sequences are too hard to check', 'The rows might be equal by accident', 'It can: the problem is decidable'], answer: 0, why: 'Searching finds a match if one exists, but when none exists the search goes on for ever. In general no algorithm decides the problem.' },
      { q: 'Every domino in a set has a bottom at least as long as its top, and one has a strictly longer bottom. What follows?', options: ['There is always a match', 'A match can only use the dominoes whose two sides are equally long', 'The bottom row always wins', 'Nothing can be said'], answer: 1, why: 'In a match both rows have the same length, so every domino used must add as much to the top as to the bottom; any domino with a longer bottom is useless.' },
    ],
  });

  // ---------------------------------------------------------------- pcp-search: the solver's tree
  const S_MATCH = ['ba/bbb', 'bb/abb', 'bba/b'];
  const S_NONE = ['b/bba', 'ba/aa', 'aba/ab'];
  const S_LIMIT = ['a/aa', 'b/ab'];
  T.topic({
    id: 'pcp-search', family: 'pcp', order: 20, title: 'Searching for a match',
    blurb: 'A solver does not need to remember whole rows: only which row is ahead and by what. Watch it explore those overhangs breadth first, cutting dead ends and repeats, until a match appears, the possibilities run out, or the bound stops it.',
    inputs: [
      { id: 'd', kind: 'list', label: 'Dominoes (top/bottom)', def: S_MATCH, check: (v) => checkDominoes(v, 'Dominoes', 4, 3) },
      { id: 'bound', kind: 'number', label: 'Longest overhang allowed', def: 5, min: 2, max: 8 },
    ],
    presets: [
      { label: 'A match, six dominoes deep', values: { d: S_MATCH, bound: 5 } },
      { label: 'No match: every path dies out', values: { d: S_NONE, bound: 5 } },
      { label: 'No match within the bound: overhang grows', values: { d: S_LIMIT, bound: 5 } },
      { label: 'The same, with a smaller bound', values: { d: S_LIMIT, bound: 3 } },
    ],
    counters: [{ id: 'tried', label: 'dominoes tried' }, { id: 'live', label: 'overhangs waiting' }, { id: 'seen', label: 'overhangs seen' }],
    run(inp) {
      const tiles = inp.d.map(parseDom), bound = inp.bound;
      const F = new T.Frames(['tried', 'live', 'seen']);
      const lab = (s) => (s.over === '' ? '' : (s.side === 'top' ? '↑' : '↓') + s.over);
      const root = { id: 'r', label: 'start', children: [], cls: '' };
      const seen = new Set();
      let queue = [{ node: root, s: { side: 'top', over: '' }, depth: 0 }];
      let verdict = 'none', path = null, cut = 0, asked = 0;
      const byId = new Map([['r', { parent: null }]]);
            // the tree only; the domino set is placed beside it once the whole tree is known
      const scene = (hot, opts) => {
        opts = opts || {};
        return K.tree.draw(root, { y: 0, gapX: 16, gapY: 70, hot: hot ? [hot] : [], path: opts.path || [] }).items;
      };
      const pathTo = (id) => { const out = []; for (let x = id; x; x = byId.get(x).parent) out.unshift(x); return out; };
      F.add({ items: scene('r'), say: 'Start with nothing laid. From here the solver tries every domino; it keeps only the overhang, the part one row has that the other has not caught up with yet.', hl: { dom: [] } });
      let n = 0;
      outer: while (queue.length) {
        const next = [];
        for (const q of queue) {
          const opts = tiles.map((t, i) => T.pcp.extend(q.s, t) ? i : -1).filter((i) => i >= 0);
          // a question before the children appear: which dominoes can follow this overhang?
          if (q.node !== root && asked < 2 && opts.length && opts.length < tiles.length) {
            asked++;
            F.add({ items: scene(q.node.id), say: 'Next the solver expands the overhang ' + lab(q.s) + '.', meta: { ask: opts.map((i) => 'pcp:d' + i), from: lab(q.s), why: 'Dominoes ' + opts.map((i) => i + 1).join(' and ') + ' agree with the overhang ' + lab(q.s) + '; the others clash at once.' }, hl: { dom: [] } });
          }
          const born = [];
          for (let i = 0; i < tiles.length; i++) {
            F.count('tried');
            const t = T.pcp.extend(q.s, tiles[i]);
            const id = 'n' + (++n);
            byId.set(id, { parent: q.node.id });
            const child = { id, mono: true, dom: i };
            if (!t) { child.label = (i + 1) + ': ✗'; child.cls = 'bad'; born.push('domino ' + (i + 1) + ' clashes'); }
            else if (t.over === '') { child.label = (i + 1) + ': ✓'; child.cls = 'good'; q.node.children.push(child); verdict = 'match'; path = pathTo(id); born.push('domino ' + (i + 1) + ' closes the gap'); break; }
            else if (t.over.length > bound) { child.label = (i + 1) + ': ' + lab(t); child.cls = 'hot'; cut++; born.push('domino ' + (i + 1) + ' makes the overhang ' + lab(t) + ', longer than the bound ' + bound); }
            else if (seen.has(t.side + t.over)) { child.label = (i + 1) + ': ' + lab(t); child.cls = 'pruned'; born.push('domino ' + (i + 1) + ' gives ' + lab(t) + ' again, already being explored'); }
            else { seen.add(t.side + t.over); child.children = []; child.label = (i + 1) + ': ' + lab(t); next.push({ node: child, s: t, depth: q.depth + 1 }); born.push('domino ' + (i + 1) + ' leaves ' + lab(t)); }
            q.node.children.push(child);
          }
          F.set('live', next.length + queue.length - queue.indexOf(q) - 1).set('seen', seen.size);
          const where = q.node === root ? 'From the start' : 'From ' + lab(q.s);
          F.add({ items: scene(q.node.id), say: where + ': ' + born.join(', ') + '.', hl: { dom: [] }, meta: { size: n } });
          if (verdict === 'match') break outer;
          if (n > 40) { verdict = 'big'; break outer; }
        }
        queue = next;
      }
      if (verdict === 'match') {
        const ids = path.slice(1).map((id) => { let node = null; const find = (x) => { if (x.id === id) node = x; (x.children || []).forEach(find); }; find(root); return node; });
        const seq = ids.map((x) => x.dom);
        const v = T.pcp.verify(tiles, seq);
        F.add({ items: scene(null, { path }), say: 'Follow the lit path back to the start: dominoes ' + seq.map((i) => i + 1).join(', ') + ' make both rows read ' + v.top + '. Breadth first means no shorter match exists.', mark: 'match', hl: { dom: seq.map(String) } });
      } else if (verdict === 'big') {
        F.add({ items: scene(null), say: 'The tree is getting too big to draw, so the picture stops here; a real solver would keep going and might never stop.', mark: 'limit' });
      } else if (cut) {
        F.add({ items: scene(null), say: 'Nothing is left to explore within the bound: ' + cut + ' branch' + (cut > 1 ? 'es were' : ' was') + ' cut off for an overhang longer than ' + bound + '. So no match within the bound, but a bigger bound might still find one: the search alone can never say no.', mark: 'limit' });
      } else {
        F.add({ items: scene(null), say: 'Every overhang has been explored and each path ends in a clash or a repeat. With nothing left to try, the solver can say for certain: no match exists. Instances like this one are the lucky ones.', mark: 'none' });
      }
      // the dominoes and a legend to the left of the widest the tree ever gets
      let minX = 0, maxY = 0;
      for (const f of F.list) for (const it of f.items) if (it.kind === 'state') { minX = Math.min(minX, it.x - it.w / 2); maxY = Math.max(maxY, it.y); }
      const sw = K.dominoes.set({ tiles, h: 66 }).box.w;
      const sx = minX - sw - 70;
      const side = K.dominoes.set({ tiles, x: sx, y: 0, h: 66 }).items.concat([
        { key: 'lg0', kind: 'text', x: sx, y: 128, text: '↑ab  the top is ahead by ab', cls: 'strong' },
        { key: 'lg1', kind: 'text', x: sx, y: 154, text: '↓ab  the bottom is ahead by ab', cls: 'strong' },
        { key: 'lg2', kind: 'text', x: sx, y: 180, text: 'k: …  after laying domino k', cls: 'strong' },
      ]);
      for (const f of F.list) f.items = side.concat(f.items);
      return { frames: F.list, def: { sections: [domTable(tiles), { id: 'rule', kind: 'math', title: 'The overhang', text: 'after a partial match one row is a prefix of the other\nkeep only the extra part: ↑u (top ahead) or ↓u (bottom ahead)\na match is reached when the overhang becomes empty\ndifferent sequences with the same overhang continue alike' }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, pick: 'item', ask: (fr, i) => 'The solver is about to expand ' + fr[i].meta.from + '. Click a domino that can follow without a clash.', answer: (fr, i) => fr[i].meta.ask, explain: (fr, i) => fr[i].meta.why },
    ],
    quiz: [
      { q: 'Why may the solver throw away a branch whose overhang it has already seen?', options: ['To save memory only; it might lose a match', 'Two partial matches with the same overhang can be continued in exactly the same ways', 'Repeated overhangs always clash', 'Because dominoes cannot repeat'], answer: 1, why: 'What happens next depends only on the overhang, so the second copy has nothing new to offer, and its continuations would be found from the first.' },
      { q: 'The search explores every overhang and finds no match. What can it conclude?', options: ['Nothing', 'There is no match at all', 'There is a match longer than it tried', 'The instance is too big'], answer: 1, why: 'Every partial match leads to one of the overhangs explored, so if none closes up, no match exists. This happens when the overhangs stay few.' },
      { q: 'With dominoes a/aa and b/ab the overhang keeps growing. Why is there certainly no match?', options: ['Every bottom is longer than its top, so the bottom row is always longer', 'Because a and b differ', 'Because the bound was too small', 'There is one, it is just long'], answer: 0, why: 'Each domino adds more symbols below than on top, so the two rows can never be equally long. The solver cannot see this; the argument about lengths can.' },
      { q: 'Why does breadth-first search find a shortest match?', options: ['It tries all sequences of length k before any of length k + 1', 'It tries the shortest dominoes first', 'It always goes deepest first', 'It does not'], answer: 0, why: 'Level k of the tree holds the partial matches of k dominoes, and each level is finished before the next.' },
      { q: 'Why can no bound on the overhang be right for every instance?', options: ['Matches can be arbitrarily long, and in general no computable bound exists, or PCP would be decidable', 'Overhangs never exceed 10', 'The bound only affects speed', 'Because the alphabet is finite'], answer: 0, why: 'A bound you could compute from the instance would turn the search into a decider, and the problem is undecidable.' },
    ],
  });

  // ---------------------------------------------------------------- pcp-mpcp: modified to plain
  const M1 = ['aa/a', 'b/aa', 'a/ba'];
  const M2 = ['b/ba', 'a/b', 'ba/a'];
  const M3 = ['b/a', 'a/ab', 'ba/a'];
  T.topic({
    id: 'pcp-mpcp', family: 'pcp', order: 30, title: 'Forcing the first domino',
    blurb: 'The modified puzzle insists that a match starts with domino 1. Stars hidden between the symbols turn it into the ordinary puzzle: only a starred copy of domino 1 can begin, and a closing domino tidies up the end.',
    inputs: [
      { id: 'd', kind: 'list', label: 'Dominoes (domino 1 must start)', def: M1, check: (v) => checkDominoes(v, 'Dominoes', 3, 2) },
    ],
    presets: [
      { label: 'A match that starts with domino 1', values: { d: M1 } },
      { label: 'Another: three dominoes', values: { d: M2 } },
      { label: 'Only matches that start elsewhere', values: { d: M3 } },
    ],
    counters: [{ id: 'made', label: 'dominoes made' }],
    run(inp) {
      const tiles = inp.d.map(parseDom);
      const conv = T.pcp.mpcpToPcp(tiles);
      const out = conv.dominoes;
      const F = new T.Frames(['made']);
      const OY = 0, NY = 150;
      const orig = (hot) => K.dominoes.set({ tiles, y: OY, prefix: 'old', hot: hot === undefined ? [] : [hot] }).items.concat([{ key: 'oldT', kind: 'text', x: 0, y: OY - 18, text: 'modified puzzle: domino 1 must start', cls: 'title' }]);
      const made = (k, hot) => {
        const list = out.slice(0, k);
        const it = K.dominoes.set({ tiles: list, y: NY, prefix: 'new', hot: hot === undefined ? [] : [hot] }).items;
        // number the new dominoes by their role underneath instead of 1, 2, 3
        return it.concat([{ key: 'newT', kind: 'text', x: 0, y: NY - 18, text: 'ordinary puzzle: any domino may start', cls: 'title' }]);
      };
      const mod = T.pcp.solve(tiles, { mpcp: true, maxNodes: 20000, maxOver: 20, trace: false });
      const plainOrig = T.pcp.solve(tiles, { maxNodes: 20000, maxOver: 20, trace: false });
      F.add({ items: orig(0), say: 'In the modified puzzle a match must begin with domino 1, ' + show(tiles[0].top) + ' over ' + show(tiles[0].bottom) + '. ' + (plainOrig.verdict === 'match' && plainOrig.seq[0] !== 0 ? 'Without that rule ' + plainOrig.seq.map((i) => i + 1).join(', ') + ' would already be a match, starting elsewhere.' : 'We want an ordinary puzzle with a match exactly when this one has one.'), hl: { dom: ['0'] } });
      const pre = (u) => [...u].map((c) => '*' + c).join(''), post = (u) => [...u].map((c) => c + '*').join('');
      tiles.forEach((t, i) => {
        F.set('made', i + 2);
        F.add({ items: orig(i).concat(made(i + 2, i + 1)), say: 'Domino ' + (i + 1) + ', ' + show(t.top) + ' over ' + show(t.bottom) + ', becomes ' + show(pre(t.top)) + ' over ' + show(post(t.bottom)) + ': a star before each symbol on top, after each symbol below.' + (i === 0 ? ' Since every top now begins with * and no bottom does, none of these can start a match.' : ''), hl: { dom: [String(i)], new: [String(i + 1)] } });
      });
      F.set('made', out.length - 1);
      F.add({ items: orig().concat(made(out.length - 1, 0)), say: 'The new first domino is the starred domino 1 with one more star at the start of its bottom: ' + out[0].top + ' over ' + out[0].bottom + '. It is the only domino whose two sides begin alike, so every match must start with it.', hl: { new: ['0'] } });
      F.set('made', out.length);
      F.add({ items: orig().concat(made(out.length, out.length - 1)), say: 'A match in starred dominoes always ends with the top one star short, so add the closing domino ' + out[out.length - 1].top + ' over ' + out[out.length - 1].bottom + ' to absorb it.', hl: { new: [String(out.length - 1)] } });
      const SY = NY + 170;
      if (mod.verdict === 'match') {
        const seq2 = conv.mapSeq(mod.seq);
        const a = K.dominoes.sequence({ tiles, seq: mod.seq, y: SY, prefix: 'mq' });
        F.add({ items: orig().concat(made(out.length), a.items), say: 'The modified puzzle has the match ' + mod.seq.map((i) => i + 1).join(', ') + ', starting with domino 1 as required; both rows read ' + a.top + '.', hl: { dom: mod.seq.map(String) } });
        const b = K.dominoes.sequence({ tiles: out, seq: seq2, y: SY, prefix: 'pq' });
        const v = T.pcp.verify(out, seq2);
        F.add({ items: orig().concat(made(out.length), b.items), say: 'Translated: the starred first domino, the starred copies of the rest, then the closing domino. Both rows read ' + v.top + ', the old match with stars woven in.', mark: 'match', hl: { new: seq2.map(String) } });
      } else {
        const c = T.pcp.solve(out, { maxNodes: 20000, maxOver: 30, trace: false });
        F.add({ items: orig().concat(made(out.length, 0)), say: 'This modified puzzle has no match: ' + (plainOrig.verdict === 'match' ? 'its only matches, like ' + plainOrig.seq.map((i) => i + 1).join(', ') + ', start with another domino. ' : '') + 'And the new puzzle has none either' + (c.verdict === 'none' ? ', as a full search confirms' : '') + ': the stars stop any match that does not start with the starred domino 1.', mark: 'none', hl: { new: ['0'] } });
      }
      return { frames: F.list, def: { sections: [domTable(tiles), { id: 'new', kind: 'table', title: 'The ordinary puzzle', colHead: ['top', 'bottom', 'made from'], rowHead: out.map((_, i) => String(i + 1)), rows: out.map((t) => [t.top, t.bottom, t.role]) }, { id: 'rule', kind: 'math', title: 'With stars', text: '★u = *u₁*u₂…*uₙ   u★ = u₁*u₂*…uₙ*\nfirst: ★top(1) over *bottom(1)★\nfor each i: ★top(i) over bottom(i)★\nlast: *$ over $' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && /new first domino/.test(fr[i + 1].say || ''), once: true, pick: 'option', options: ['None of them', 'Domino 1 only', 'All of them', 'Only the last one'], ask: 'After the stars are added, which of the starred dominoes could begin a match?', answer: () => 'None of them', explain: 'Every starred top begins with *, every starred bottom begins with a letter, so the first symbols always clash. That is why a special starred domino 1 is needed.' },
    ],
    quiz: [
      { q: 'Why can none of the plain starred copies start a match?', options: ['Their tops begin with * and their bottoms do not', 'They are too long', 'They contain $', 'They can'], answer: 0, why: 'A match needs the first symbols of the two rows to agree; * against a letter is an immediate clash.' },
      { q: 'What is the closing domino for?', options: ['After the starred dominoes the top is one * short, and *$ over $ evens it up', 'To end every row with the same letter', 'It marks the start', 'Nothing: it could be left out'], answer: 0, why: 'Every bottom symbol is followed by a star, and the special first domino adds a leading star below, so at the end the top lacks a final *; *$ over $ supplies it and closes both rows with $.' },
      { q: 'If the modified puzzle has no match, can the new ordinary puzzle have one?', options: ['No: any match must start with the starred domino 1 and translates back into a modified match', 'Yes, always', 'Only if domino 1 is short', 'Only without the closing domino'], answer: 0, why: 'The construction is faithful both ways: matches of the new puzzle drop their stars and $ to give a match of the old one that starts with domino 1.' },
      { q: 'Why bother with the modified puzzle at all?', options: ['A Turing machine\'s computation is easiest to encode when the match is forced to start with the start configuration', 'It is easier to solve', 'It is decidable', 'For shorter matches'], answer: 0, why: 'The undecidability proof first builds a modified puzzle whose match must begin with the machine\'s start configuration, then this construction removes the restriction.' },
    ],
  });

  // ---------------------------------------------------------------- pcp-tm: a machine as dominoes
  const MACHINES = {
    flip: { label: 'Turn 0s into 1s until a 1', text: 'start: p\naccept: qa\ninput: 0 1\np, 0 -> p, 1, R\np, 1 -> qa, 1, S' },
    skip: { label: 'Skip a 0, then accept on 1', text: 'start: p\naccept: qa\ninput: 0 1\np, 0 -> r, 0, R\nr, 1 -> qa, 1, S' },
  };
  T.topic({
    id: 'pcp-tm', family: 'pcp', order: 40, title: 'A machine made of dominoes',
    blurb: 'Every Turing machine and input can be turned into dominoes whose only matches spell out the machine\'s accepting computation, one configuration per round, the bottom row always one configuration ahead.',
    inputs: [
      { id: 'm', kind: 'choice', label: 'Machine', def: 'flip', options: Object.keys(MACHINES).map((k) => ({ value: k, label: MACHINES[k].label })) },
      { id: 'w', kind: 'string', label: 'Input', def: '01', alphabet: '01', min: 1, max: 3 },
    ],
    presets: [
      { label: 'Flip 0s until a 1: 01', values: { m: 'flip', w: '01' } },
      { label: 'Accept at once: 1', values: { m: 'flip', w: '1' } },
      { label: 'Two flips: 001', values: { m: 'flip', w: '001' } },
      { label: 'A machine that rejects: no match', values: { m: 'flip', w: '00' } },
      { label: 'Two states: 01', values: { m: 'skip', w: '01' } },
    ],
    counters: [{ id: 'rounds', label: 'rounds' }, { id: 'used', label: 'dominoes used' }],
    run(inp) {
      const M = T.tm.compile(MACHINES[inp.m].text, { name: 'M' });
      const conv = T.pcp.tmToMpcp(M, inp.w);
      const dom = conv.dominoes, sym = conv.symbols;
      const run = T.tm.run(M, inp.w, { maxSteps: 50 });
      const F = new T.Frames(['rounds', 'used']);
      // the dominoes by role, in three short rows
      const groups = [
        { id: 'g0', label: 'start and moves', ids: dom.map((d, i) => i).filter((i) => i === 0 || /→/.test(dom[i].role)) },
        { id: 'g1', label: 'copy, next configuration, add a blank', ids: dom.map((d, i) => i).filter((i) => /copy|next|blank/.test(dom[i].role)) },
        { id: 'g2', label: 'the accepting state eats the tape', ids: dom.map((d, i) => i).filter((i) => /accept|finish/.test(dom[i].role)) },
      ];
      const setItems = (hot, dim) => {
        const items = [];
        let y = 0;
        for (const g of groups) {
          let x = 16;
          const H = 62;
          const start = items.length;
          for (const i of g.ids) {
            const d = dom[i];
            const w = Math.max(50, Geo.textWidth(d.top, 15, { mono: true }) + 22, Geo.textWidth(d.bottom, 15, { mono: true }) + 22);
            items.push({ key: 'd' + i, kind: 'domino', x, y: y + 30, w, h: H, top: d.top, bottom: d.bottom, cls: hot && hot.includes(i) ? 'hot' : '', dim: dim && !(hot || []).includes(i), pick: true });
            items.push({ key: 'dn' + i, kind: 'text', x: x + w / 2, y: y + 30 + H + 17, text: String(i + 1), anchor: 'middle', cls: 'strong' });
            x += w + 10;
          }
          items.splice(start, 0, { key: g.id, kind: 'region', x: 0, y, w: x + 6, h: H + 56, text: g.label, cls: 'r' + groups.indexOf(g) });
          y += H + 70;
        }
        return { items, h: y };
      };
      const names = Object.entries(sym).map(([q, c]) => q + ' = ' + c).join(', ');
      const configs = run.history.length ? run.history : [];
      const cfgOf = (s) => s.split(' ').map((x) => (sym[x] !== undefined ? sym[x] : x)).join('');
      F.add({ items: setItems().items, say: 'The machine ' + (MACHINES[inp.m].label.toLowerCase()) + ' on ' + inp.w + ' becomes ' + dom.length + ' dominoes. A configuration is written as the tape with the state letter just before the head\'s cell (' + names + ').', hl: { dom: [] } });
      F.add({ items: setItems([0]).items, say: 'Domino 1, # over #' + cfgOf(configs[0] || '') + '#, must start: it puts the start configuration on the bottom row while the top has only #.', hl: { dom: ['0'] } });
      const moves = groups[0].ids.slice(1);
      F.add({ items: setItems(moves).items, say: 'One domino per rule of the machine: its top is the state letter and the symbol it reads, its bottom is what that spot looks like one step later.', hl: { dom: moves.map(String) } });
      F.add({ items: setItems(groups[1].ids).items, say: 'Copy dominoes carry every other cell over unchanged, # over # closes a configuration, and # over ⊔# lets the tape grow by a blank on the right.', hl: { dom: groups[1].ids.map(String) } });
      F.add({ items: setItems(groups[2].ids).items, say: 'Once the accepting state ' + sym[M.accept[0]] + ' appears, these dominoes let it swallow one neighbour per round, and the last one closes the match with ##.', hl: { dom: groups[2].ids.map(String) } });
      const sol = T.pcp.solve(dom, { mpcp: true, maxNodes: 200000, maxOver: 40, trace: false });
      if (sol.verdict !== 'match') {
        F.add({ items: setItems([0]).items, say: 'On ' + inp.w + ' the machine ' + (run.verdict === 'reject' ? 'gets stuck and rejects' : 'does not accept') + ', so the accepting state never appears; the bottom stays a configuration ahead for ever and ' + (sol.verdict === 'none' ? 'a full search confirms there is no match.' : 'no match turns up.'), mark: 'none', hl: { dom: ['0'] } });
        return { frames: F.list, def: { sections: [domTable(dom, true)] } };
      }
      // split the match into rounds: a round ends with a domino whose top ends in #
      const rounds = [];
      let cur = [];
      for (const i of sol.seq) { cur.push(i); if (dom[i].top.endsWith('#')) { rounds.push(cur); cur = []; } }
      if (cur.length) rounds.push(cur);
      // the history column on the right: the configurations the bottom row spells, one per round
      const bottomCfgs = [];
      { let b = ''; for (const r of rounds) { const s = r.map((i) => dom[i].bottom).join(''); b += s; } b.split('#').filter((x) => x !== '').forEach((c) => bottomCfgs.push(c)); }
      const RY = 0, RH = 62, CX0 = 0;
      const dw = (d) => Math.max(46, Geo.textWidth(d.top, 15, { mono: true }) + 20, Geo.textWidth(d.bottom, 15, { mono: true }) + 20);
      const widest = Math.max(...rounds.map((r) => r.reduce((a, i) => a + dw(dom[i]) + 6, 0)));
      const roundItems = (upTo, opts) => {
        opts = opts || {};
        const items = [];
        let maxX = 0;
        for (let k = 0; k <= upTo; k++) {
          let x = CX0 + 92;
          const y = RY + k * (RH + 22);
          items.push({ key: 'rl' + k, kind: 'text', x: CX0, y: y + RH / 2 + 5, text: 'round ' + k, cls: 'title' });
          rounds[k].forEach((i, j) => {
            const d = dom[i];
            const w = Math.max(46, Geo.textWidth(d.top, 15, { mono: true }) + 20, Geo.textWidth(d.bottom, 15, { mono: true }) + 20);
            items.push({ key: 'r' + k + ':' + j, kind: 'domino', x, y, w, h: RH, top: d.top, bottom: d.bottom, cls: k === upTo ? 'hot' : '', enter: 'drop' });
            x += w + 6;
          });
          maxX = Math.max(maxX, x);
        }
        // configurations on the right
        const hx = CX0 + 92 + widest + 50;
        items.push({ key: 'hT', kind: 'text', x: hx, y: RY - 14, text: 'computation history', cls: 'title' });
        bottomCfgs.forEach((c, j) => {
          const y = RY + j * (RH + 22) + 10;
          const reached = j <= upTo;
          items.push({ key: 'h' + j, kind: 'cell', x: hx, y, w: 150, h: 40, text: c, cls: 'mono ' + (opts.ask && j === upTo + 1 ? '' : reached ? (j === upTo ? 'hot' : 'good') : 'gone'), pick: true });
        });
        return { items, maxX };
      };
      const textOf = (k) => { let t = '', b = ''; for (let j = 0; j <= k; j++) for (const i of rounds[j]) { t += dom[i].top; b += dom[i].bottom; } return { t, b }; };
      for (let k = 0; k < rounds.length; k++) {
        F.count('rounds', k ? 1 : 0).count('used', rounds[k].length);
        const r = roundItems(k);
        const { t, b } = textOf(k);
        const topCfg = rounds[k].map((i) => dom[i].top).join('').replace(/#$/, '');
        const botCfg = rounds[k].map((i) => dom[i].bottom).join('').replace(/#$/, '');
        let say;
        if (k === 0) say = 'Round 0: domino 1 alone. Top #, bottom #' + bottomCfgs[0] + '#: the bottom is one whole configuration ahead.';
        else if (rounds[k].some((i) => /finish/.test(dom[i].role))) say = 'Last round: ' + rounds[k].map((i) => i + 1).join(', ') + ' finish it. The top catches up and both rows read ' + t + ': a match, and it exists only because the machine accepted.';
        else say = 'Round ' + k + ': dominoes ' + rounds[k].map((i) => i + 1).join(', ') + ' copy ' + topCfg + ' on top while writing ' + botCfg + ' below' + (rounds[k].some((i) => /→/.test(dom[i].role)) ? ', one step of the machine' : ', the accepting state eating a neighbour') + '. Top ' + t + ', bottom ' + b + '.';
        const hlD = rounds[k].map(String);
        F.add({ items: r.items, say, hl: { dom: hlD }, meta: { round: k, next: k + 1 < bottomCfgs.length ? 'h' + (k + 1) : null }, mark: k === rounds.length - 1 ? 'match' : undefined });
      }
      return { frames: F.list, def: { sections: [domTable(dom, true), { id: 'hist', kind: 'math', title: 'The machine\'s run', text: configs.map((c, i) => 'C' + i + ' = ' + cfgOf(c) + '   (' + c + ')').join('\n') + '\n' + (run.verdict === 'accept' ? 'accepted' : run.verdict) }] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.round !== undefined && f.meta.next && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.round !== undefined && f.meta.round < 2, pick: 'item', ask: 'In the next round the top copies the newest configuration. Click the configuration the bottom will write in that round.', answer: (fr, i) => 'h' + (fr[i].meta.round + 1), explain: 'The top always copies what the bottom wrote one round earlier, while the move and copy dominoes make the bottom write the configuration after it: one step of the machine per round.' },
    ],
    quiz: [
      { q: 'Why is the bottom row always one configuration ahead of the top?', options: ['The first domino puts the whole start configuration below and only # on top', 'Bottoms are longer by design', 'The machine moves right', 'It is not'], answer: 0, why: 'Domino 1 is # over #C₀#; from then on each round copies one configuration on top while writing the next one below.' },
      { q: 'Why can the match never close if the machine does not accept?', options: ['Only the accepting state\'s dominoes let the top catch up; without them the bottom stays a configuration ahead', 'Because the dominoes run out', 'Because the top is longer', 'It can close anyway'], answer: 0, why: 'Every move and copy domino keeps the gap of one configuration; only the dominoes that let the accepting state eat the tape shrink it to nothing.' },
      { q: 'What does this construction show?', options: ['A decider for PCP would decide whether a machine accepts an input, which is impossible', 'PCP is decidable', 'Machines are dominoes', 'Every machine accepts'], answer: 0, why: 'The dominoes have a match exactly when the machine accepts the input, so PCP is at least as hard as the acceptance problem.' },
      { q: 'Why does this construction give the modified puzzle, with domino 1 forced first?', options: ['A match must start from the start configuration, not from an arbitrary copy domino', 'To keep it short', 'Because # must be first', 'It does not matter'], answer: 0, why: 'Without the rule, a copy domino such as 0 over 0 would be a match on its own. The star construction then turns the modified puzzle into an ordinary one.' },
    ],
  });
})();
