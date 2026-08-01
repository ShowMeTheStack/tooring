// Nondeterministic finite automata: a run as a cloud of live states with a token for every branch (tokens
// split when a state has two moves, merge when two branches land on one state, and die when there is no
// move), the ε-closure spreading out from a state with its to-do list, the computation tree of a run set
// beside the states it merges into, and the NFA that guesses the k-th symbol from the end.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg;

  T.family({ id: 'nfa', part: 'regular', order: 20, title: 'Nondeterministic finite automata', blurb: 'Several moves on one symbol, moves on no symbol at all: an NFA is in many states at once and accepts if any branch does.' });

  const ENDS_AB = 'start p\naccept r\np -a,b-> p\np -a-> q\nq -b-> r';
  const TWO_WAYS = 'start s\naccept f\ns -a-> x\ns -a-> y\nx -b-> f\ny -a-> f';
  const MERGE = 'start s\naccept m\ns -a-> x\ns -a-> y\nx -b-> m\ny -b-> m\nm -a-> m';
  const EPS_RUN = 'start s\naccept t\ns -ε-> u\ns -ε-> v\nu -a-> u\nu -b-> t\nv -b-> v\nv -a-> t';
  const tokenAt = (p) => ({ x: p.x, y: p.y + 16 });

  // ---- a run as a cloud ---------------------------------------------------------------------------------------
  T.topic({
    id: 'nfa-run', family: 'nfa', order: 10, title: 'An NFA runs on a string',
    blurb: 'An NFA can be in several states at once. Each dot is a branch of the run: it splits when a state has two moves, merges when two branches meet, and dies when there is no move.',
    inputs: [
      R.machineInput({ id: 'm', label: 'NFA', def: ENDS_AB, kind: 'nfa', max: 7 }),
      { id: 'w', kind: 'string', label: 'Input', def: 'abab', max: 8 },
    ],
    presets: [
      { label: 'Ends in ab: abab', values: { m: ENDS_AB, w: 'abab' } },
      { label: 'Two guesses, one survives: ab', values: { m: TWO_WAYS, w: 'ab' } },
      { label: 'Every branch dies: ba', values: { m: TWO_WAYS, w: 'ba' } },
      { label: 'Branches merge: aba', values: { m: MERGE, w: 'aba' } },
      { label: 'ε-moves split the start: aab', values: { m: EPS_RUN, w: 'aab' } },
      { label: 'The empty string', values: { m: ENDS_AB, w: '' } },
    ],
    check: R.alphaCheck('m', 'w'),
    counters: [{ id: 'read', label: 'symbols read' }, { id: 'live', label: 'live states' }],
    run(inp) {
      const m = T.Machine.parse(inp.m);
      const fa = R.fa(m);
      const w = [...inp.w];
      const res = T.FA.run(fa, inp.w);
      const steps = res.trace.filter((s) => s.kind === 'start' || s.kind === 'read' || s.kind === 'stuck');
      const pos = K.graph.layout(m).pos;
      const g0 = K.graph.draw(m, { pos });
      const dt = R.delta(fa);
      const sets = steps.map((s) => R.set(s.states));
      const cw = Math.max(46, ...sets.map((s) => Geo.textWidth(s, 14, { mono: true }) + 16));
      const n = w.length;
      const sx = g0.box.x + g0.box.w / 2 - ((n + 1) * cw) / 2;
      const gy = g0.box.y + g0.box.h + 60, ly = gy + 92;
      const F = new T.Frames(['read', 'live']);
      const tok = (k, q) => 'tk:' + k + ':' + q;
      // tokens of step k, each growing out of the token it came from
      const tokens = (k, states, src) => states.map((q) => { const p = tokenAt(pos[q]); const it = { key: tok(k, q), kind: 'token', x: p.x, y: p.y, r: 7, cls: 'act', audit: 'overlap-ok' }; if (src && src[q]) { it.enter = 'from'; it.src = src[q]; } return it; });
      const below = (k, live, opts) => {
        opts = opts || {};
        const s = K.string.draw({ text: w, pos: k, x: sx + cw, y: gy, cw, headText: k >= n ? 'end' : 'next' });
        const out = s.items.concat([
          { key: 'lb:in', kind: 'text', x: sx - 14, y: gy + 27, text: 'input', anchor: 'end', cls: 'title' },
          { key: 'lb:st', kind: 'text', x: sx + cw / 2, y: gy + 27, text: 'start', anchor: 'middle', cls: 'title' },
          { key: 'lb:live', kind: 'text', x: sx - 14, y: ly + 22, text: 'live', anchor: 'end', cls: 'title' },
        ]);
        for (let j = 0; j <= k && j < steps.length; j++) out.push({ key: 'live:' + j, kind: 'cell', x: sx + j * cw, y: ly, w: cw, h: 36, text: sets[j], size: 14, cls: 'mono ' + (j === k ? (opts.last || (steps[j].states.length ? 'act' : 'bad')) : steps[j].states.length ? '' : 'bad'), enter: 'grow' });
        return out;
      };
      const s0 = steps[0];
      const startEps = (s0.closure || []).map((c) => c.from + '>' + c.to);
      const src0 = {};
      for (const c of s0.closure || []) src0[c.to] = tok(0, c.from);
      F.set('live', s0.states.length);
      F.add({ items: K.graph.draw(m, { pos, active: s0.states, taken: startEps, startHot: true }).items.concat(tokens(0, s0.states, src0), below(0)), say: s0.states.length > 1 ? 'Start in ' + fa.start + '; its ε-moves let the run be in ' + R.set(s0.states) + ' before reading anything: one branch (dot) in each.' : 'Start in ' + fa.start + ', with one branch of the run there (the dot).', hl: { delta: s0.states.map(dt.row) }, meta: { live: s0.states } });
      for (let k = 1; k < steps.length; k++) {
        const s = steps[k], prev = steps[k - 1].states, a = w[k - 1];
        const edges = s.edges || [];
        const src = {}, from = {};
        for (const e of edges) { if (!src[e.to]) src[e.to] = tok(k - 1, e.from); (from[e.to] = from[e.to] || []).push(e.from); }
        for (const c of s.closure || []) if (!src[c.to]) src[c.to] = tok(k, c.from);
        const exits = {};
        for (const p of prev) { const e = edges.find((x) => x.from === p); exits[tok(k - 1, p)] = e ? { exit: 'into', into: tok(k, e.to) } : { exit: 'shrink' }; }
        const died = prev.filter((p) => !edges.some((e) => e.from === p));
        const merged = Object.keys(from).filter((q) => from[q].length > 1);
        const split = prev.filter((p) => edges.filter((e) => e.from === p).length > 1);
        const taken = edges.map((e) => e.from + '>' + e.to).concat((s.closure || []).map((c) => c.from + '>' + c.to));
        F.count('read').set('live', s.states.length);
        let say;
        if (s.kind === 'stuck') say = 'Read ' + a + ': none of ' + R.set(prev) + ' has a move on ' + a + ', so every branch dies. The set of live states is ∅ and the string is rejected without reading the rest.';
        else {
          say = 'Read ' + a + ': ' + edges.map((e) => e.from + ' → ' + e.to).join(', ');
          if ((s.closure || []).length) say += ', then ε-moves add ' + s.closure.map((c) => c.to).join(', ');
          say += '. Live: ' + R.set(s.states) + '.';
          if (split.length) say += ' The branch in ' + split.join(' and ') + ' splits.';
          if (merged.length) say += ' Branches from ' + from[merged[0]].join(' and ') + ' merge in ' + merged[0] + '.';
          if (died.length) say += ' The branch in ' + died.join(' and ') + ' dies: no move on ' + a + '.';
        }
        F.add({ items: K.graph.draw(m, { pos, active: s.states, taken }).items.concat(tokens(k, s.states, src), below(k)), exits, say, hl: { delta: prev.map((p) => dt.rc(p, a)) }, meta: { live: s.states } });
      }
      const last = steps[steps.length - 1];
      const hit = last.states.filter((q) => fa.accept.includes(q));
      const ok = hit.length > 0;
      F.add({ items: K.graph.draw(m, { pos, active: last.states.filter((q) => !hit.includes(q)), good: hit }).items.concat(tokens(steps.length - 1, last.states), below(steps.length - 1, null, { last: ok ? 'good' : 'bad' })), say: ok ? 'Accept: ' + hit.join(', ') + (hit.length > 1 ? ' are' : ' is') + ' accepting, so at least one branch of the run ends happily. The other branches do not matter.' : last.states.length ? 'Reject: the live states ' + R.set(last.states) + ' include no accepting state. Every branch failed.' : 'Reject: no branch is alive at all.', mark: ok ? 'accepted' : 'rejected', meta: { verdict: ok ? 'Accept' : 'Reject' } });
      return { frames: F.list, def: { sections: [R.tuple(fa), dt.section, { id: 'rule', kind: 'text', title: 'The rule', text: 'After each symbol the live set is every state some branch can be in: follow every move on the symbol from every live state, then every ε-move. Accept if the final set holds an accepting state.' }] } };
    },
    predict: [
      { at: (f, i, fr) => i >= 1 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.live && fr[i + 1].meta.live.length > 0 && i < fr.length - 2, once: true, pick: 'item', ask: 'Click a state that will be live after the next symbol.', answer: (fr, i) => fr[i + 1].meta.live.map((q) => 'g:s:' + q), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2 && i > 0, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the NFA accept the whole string?', answer: (fr) => fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'When does an NFA accept a string?', options: ['When every branch ends in an accepting state', 'When at least one branch ends in an accepting state', 'When most branches accept', 'When no branch dies'], answer: 1, why: 'One successful run is enough; the other branches are ignored.' },
      { q: 'Two branches reach the same state after the same prefix. Do we need to follow both?', options: ['Yes, they may behave differently later', 'No: from the same state they behave the same, so one is enough', 'Only if the state accepts', 'Only with ε-moves'], answer: 1, why: 'What happens next depends only on the state and the rest of the input, so branches in one state can merge. That is why a set of states is enough.' },
      { q: 'The live set becomes ∅ in the middle of the input. What happens?', options: ['The NFA restarts', 'It stays ∅ and the string is rejected', 'It accepts', 'It jumps to the start state'], answer: 1, why: 'No state has a move from nowhere, so the empty set stays empty: reject.' },
      { q: 'An NFA has 5 states. At most how many different live sets can a run pass through?', options: ['5', '10', '25', '32'], answer: 3, why: 'A live set is a subset of the 5 states: there are 2⁵ = 32 of them. That is the subset construction in a nutshell.' },
      { q: 'How long does simulating an NFA on a string of length n take, keeping live sets?', options: ['Exponential in n', 'About n × (number of moves)', 'n²', 'It may never finish'], answer: 1, why: 'Each symbol updates the set once, looking at each move at most once: no backtracking over branches is needed.' },
    ],
  });

  // ---- ε-closure ------------------------------------------------------------------------------------------------
  const CHAIN = 'start a\naccept d\na -ε-> b\nb -ε-> c\nc -x-> d\nb -y-> d';
  const CYCLE = 'start p\naccept s\np -ε-> q\nq -ε-> r\nr -ε-> p\nr -a-> s\nq -b-> q';
  const DIAMOND = 'start s\naccept f\ns -ε-> u\ns -ε-> v\nu -ε-> w\nv -ε-> w\nw -a-> f\nu -b-> f';
  T.topic({
    id: 'nfa-eclosure', family: 'nfa', order: 20, title: 'The ε-closure spreads',
    blurb: 'Everything reachable by ε-moves alone: start with one state, follow every ε-arrow, and keep going from what you add. A state is added only once, so even an ε-cycle stops.',
    inputs: [
      R.machineInput({ id: 'm', label: 'ε-NFA', def: CYCLE, kind: 'nfa', max: 7 }),
      { id: 'q', kind: 'text', label: 'Closure of state', def: 'p' },
    ],
    presets: [
      { label: 'An ε-cycle: closure of p', values: { m: CYCLE, q: 'p' } },
      { label: 'A chain: closure of a', values: { m: CHAIN, q: 'a' } },
      { label: 'Two ε-paths to one state', values: { m: DIAMOND, q: 's' } },
      { label: 'No ε-moves out: closure of d is {d}', values: { m: CHAIN, q: 'd' } },
      { label: 'Into the cycle from r', values: { m: CYCLE, q: 'r' } },
    ],
    check: (inp) => { const m = T.Machine.parse(inp.m); return m.states.includes(String(inp.q).trim()) ? null : 'Closure of state: "' + inp.q + '" is not a state of the machine (' + m.states.join(', ') + ')'; },
    counters: [{ id: 'added', label: 'states in the closure' }, { id: 'looked', label: 'ε-moves looked at' }],
    run(inp) {
      const m = T.Machine.parse(inp.m);
      const fa = R.fa(m);
      const q0 = String(inp.q).trim();
      const pos = K.graph.layout(m).pos;
      const g0 = K.graph.draw(m, { pos });
      const dt = R.delta(fa);
      const epsFrom = new Map();
      for (const e of fa.trans) if (e.sym === '') epsFrom.set(e.from, (epsFrom.get(e.from) || []).concat([e.to]));
      // ε-only edges stand out; edges reading symbols are drawn faint, since the closure never uses them
      const edgeCls = {};
      for (const e of K.graph.edges(m)) if (!e.labels.includes('ε')) edgeCls[e.from + '>' + e.to] = 'soft';
      const cw = Math.max(46, ...fa.states.map((q) => Geo.textWidth(q, 15, { bold: true }) + 20));
      const rowY = g0.box.y + g0.box.h + 56;
      const x0 = g0.box.x + g0.box.w / 2 - (fa.states.length * (cw + 6)) / 2 + 30;
      const rows = (stack, closure, hot) => {
        const out = [
          { key: 'lb:todo', kind: 'text', x: x0 - 14, y: rowY + 24, text: 'to do', anchor: 'end', cls: 'title' },
          { key: 'lb:cl', kind: 'text', x: x0 - 14, y: rowY + 74, text: 'closure', anchor: 'end', cls: 'title' },
        ];
        if (!stack.length) out.push({ key: 'todo:empty', kind: 'cell', x: x0, y: rowY, w: cw, h: 36, text: '∅', cls: 'mono empty' });
        stack.forEach((q, i) => out.push({ key: 'todo:' + q, kind: 'cell', x: x0 + i * (cw + 6), y: rowY, w: cw, h: 36, text: q, cls: 'mono' + (i === stack.length - 1 ? ' act' : ''), enter: 'drop', exit: 'rise' }));
        closure.forEach((q, i) => out.push({ key: 'cl:' + q, kind: 'cell', x: x0 + i * (cw + 6), y: rowY + 50, w: cw, h: 36, text: q, cls: 'mono' + (q === hot ? ' hot' : ' good'), enter: 'from', src: 'g:s:' + q }));
        return out;
      };
      const F = new T.Frames(['added', 'looked']);
      const seen = new Set([q0]), closure = [q0], stack = [q0];
      F.set('added', 1);
      F.add({ items: K.graph.draw(m, { pos, active: [q0], edgeCls }).items.concat(rows(stack, closure, q0)), say: 'The ε-closure of ' + q0 + ' starts with ' + q0 + ' itself (reading nothing, the machine may simply stay). Put ' + q0 + ' on the to-do list.', hl: { delta: [dt.rc(q0, '')] }, meta: {} });
      while (stack.length) {
        const x = stack.pop();
        const outs = epsFrom.get(x) || [];
        F.add({ items: K.graph.draw(m, { pos, active: closure.filter((q) => q !== x), hot: [x], edgeCls }).items.concat(rows(stack, closure)), say: 'Take ' + x + ' off the to-do list. ' + (outs.length ? 'It has ε-moves to ' + outs.join(', ') + '.' : 'It has no ε-moves: nothing to follow.'), hl: { delta: [dt.rc(x, '')] }, meta: { from: x } });
        for (const r of outs) {
          F.count('looked');
          if (seen.has(r)) {
            F.add({ items: K.graph.draw(m, { pos, active: closure.filter((q) => q !== x), hot: [x], taken: [x + '>' + r], edgeCls, cls: { [r]: 'good' } }).items.concat(rows(stack, closure, r)), say: 'ε-move ' + x + ' → ' + r + ': ' + r + ' is already in the closure, so skip it.' + (closure.indexOf(r) < closure.indexOf(x) ? ' This is what stops an ε-cycle from going round for ever.' : ''), hl: { delta: [dt.rc(x, '')] }, meta: { skip: r } });
            continue;
          }
          seen.add(r); closure.push(r); stack.push(r);
          F.count('added');
          F.add({ items: K.graph.draw(m, { pos, active: closure.filter((q) => q !== x && q !== r), hot: [x], good: [r], taken: [x + '>' + r], edgeCls }).items.concat(rows(stack, closure, r)), say: 'ε-move ' + x + ' → ' + r + ': add ' + r + ' to the closure and to the to-do list.', hl: { delta: [dt.rc(x, '')] }, meta: { add: r } });
        }
      }
      const si = new Map(fa.states.map((q, i) => [q, i]));
      const final = closure.slice().sort((a, b) => si.get(a) - si.get(b));
      const core = T.FA.closure(fa, [q0]).result;
      F.add({ items: K.graph.draw(m, { pos, good: final, edgeCls }).items.concat(rows([], closure)), say: 'The to-do list is empty: ε-closure(' + q0 + ') = ' + R.set(final) + (core.join() === final.join() ? '' : ' (the engine says ' + R.set(core) + ')') + '. From ' + q0 + ', the machine can be in any of these without reading a symbol.' + (final.some((q) => fa.accept.includes(q)) ? ' It holds an accepting state, so ' + q0 + ' accepts ε.' : ''), mark: 'done', meta: { size: final.length } });
      return { frames: F.list, def: { sections: [R.tuple(fa), dt.section, { id: 'alg', kind: 'math', title: 'The closure', text: 'closure ← {' + q0 + '}, to do ← [' + q0 + ']\nwhile to do is not empty:\n  take x; for each ε-move x → r:\n    if r ∉ closure: add r to both' }] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && fr[fr.length - 1].meta.size > 1, once: true, pick: 'option', options: (fr) => R.numberOptions(fr[fr.length - 1].meta.size), ask: 'How many states will the ε-closure hold, counting the state itself?', answer: (fr) => String(fr[fr.length - 1].meta.size), explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr) => i > 0 && fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.add, once: true, pick: 'item', ask: 'Which state will the closure add next? Click it.', answer: (fr, i) => 'g:s:' + fr[i + 1].meta.add, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Is a state always in its own ε-closure?', options: ['Yes: following no moves at all is allowed', 'Only if it has an ε-loop', 'Only for the start state', 'No'], answer: 0, why: 'The closure is everything reachable by zero or more ε-moves; zero moves leaves you where you are.' },
      { q: 'p -ε-> q and q -ε-> p. Why does computing the closure of p stop?', options: ['It does not stop', 'Each state is added at most once, and a state already in is skipped', 'ε-cycles are not allowed', 'The machine forbids it'], answer: 1, why: 'The closure only grows, and it is a subset of a finite set of states, so it must stop.' },
      { q: 'q -ε-> r and r -a-> s. Is s in the ε-closure of q?', options: ['Yes', 'No: reaching s reads an a', 'Only if s accepts', 'Only if a = ε'], answer: 1, why: 'The closure follows ε-moves only. Moves that read a symbol belong to the next step of a run.' },
      { q: 'When does an ε-NFA accept the empty string?', options: ['When its start state accepts', 'When the ε-closure of its start state holds an accepting state', 'Never', 'When it has an ε-loop'], answer: 1, why: 'Reading nothing, the machine can be anywhere in the closure of its start; one accepting state there is enough.' },
    ],
  });

  // ---- the computation tree -------------------------------------------------------------------------------------
  const BRANCHY = 'start p\naccept r\np -a,b-> p\np -a-> q\nq -a,b-> r';
  // every branch of the run, as a tree: nodes {id, q, depth, kids, dies}
  function computationTree(fa, w) {
    const by = new Map();
    for (const e of fa.trans) by.set(e.from + '\u0000' + e.sym, (by.get(e.from + '\u0000' + e.sym) || []).concat([e.to]));
    const root = { id: 'r', q: fa.start, depth: 0, kids: [] };
    let level = [root], count = 1, widest = 1;
    const levels = [level];
    for (let i = 0; i < w.length; i++) {
      const next = [];
      for (const n of level) {
        const to = by.get(n.q + '\u0000' + w[i]) || [];
        if (!to.length) n.dies = i;
        to.forEach((q, k) => { const c = { id: n.id + '.' + k, q, depth: i + 1, kids: [] }; n.kids.push(c); next.push(c); });
      }
      count += next.length; widest = Math.max(widest, next.length);
      levels.push(next);
      level = next;
    }
    return { root, levels, count, widest };
  }
  T.topic({
    id: 'nfa-tree', family: 'nfa', order: 30, title: 'The computation tree',
    blurb: 'Every choice an NFA makes is a fork in a tree of branches. The tree can double at every symbol, but beside each level the branches collapse into a small set of states.',
    inputs: [
      R.machineInput({ id: 'm', label: 'NFA (no ε-moves)', def: BRANCHY, kind: 'nfa', max: 6, eps: false }),
      { id: 'w', kind: 'string', label: 'Input', def: 'abab', max: 6 },
    ],
    presets: [
      { label: 'Second from last is a: abab', values: { m: BRANCHY, w: 'abab' } },
      { label: 'Second from last is a: aaaa (the tree doubles)', values: { m: BRANCHY, w: 'aaaa' } },
      { label: 'Branches die off: ab', values: { m: TWO_WAYS, w: 'ab' } },
      { label: 'Every branch dies: ba', values: { m: TWO_WAYS, w: 'ba' } },
      { label: 'Two branches, one state: aba', values: { m: MERGE, w: 'aba' } },
    ],
    check: (inp) => {
      const e = R.alphaCheck('m', 'w')(inp);
      if (e) return e;
      const t = computationTree(R.fa(inp.m), [...inp.w]);
      if (t.count > 40 || t.widest > 12) return 'Input: the tree would have ' + t.count + ' branches (' + t.widest + ' side by side); try a shorter string so it fits on the picture';
      return null;
    },
    counters: [{ id: 'branches', label: 'branches at this level' }, { id: 'states', label: 'distinct states' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const w = [...inp.w];
      const t = computationTree(fa, w);
      const acc = new Set(fa.accept);
      // the tree up to a depth, as the tree kit wants it
      const snap = (depth, final) => {
        const go = (n) => {
          const kids = n.depth < depth ? n.kids.map(go) : [];
          let cls = n.dies !== undefined && n.dies < depth ? 'pruned' : '';
          if (final && n.depth === w.length) cls = acc.has(n.q) ? 'good' : 'reject';
          return { id: n.id, label: n.q, children: kids, cls };
        };
        return go(t.root);
      };
      const full = K.tree.draw(snap(w.length), { gapY: 76 });
      const fb = full.box;
      const colX = fb.x + fb.w + 70, symX = fb.x - 40;
      const sets = t.levels.map((l) => [...new Set(l.map((n) => n.q))].sort((a, b) => fa.states.indexOf(a) - fa.states.indexOf(b)));
      const cw = Math.max(70, ...sets.map((s) => Geo.textWidth(R.set(s), 14, { mono: true }) + 18));
      const side = (depth) => {
        const out = [
          { key: 'h:live', kind: 'text', x: colX + cw / 2, y: -36, text: 'states', anchor: 'middle', cls: 'title' },
          { key: 'h:read', kind: 'text', x: symX, y: -36, text: 'read', anchor: 'middle', cls: 'title' },
        ];
        for (let d = 0; d <= depth; d++) {
          out.push({ key: 'set:' + d, kind: 'cell', x: colX, y: d * 76 - 18, w: cw, h: 36, text: R.set(sets[d]), size: 14, cls: 'mono' + (d === depth ? ' act' : '') + (!sets[d].length ? ' bad' : ''), enter: 'grow' });
          out.push({ key: 'cnt:' + d, kind: 'text', x: colX + cw + 12, y: d * 76 + 5, text: t.levels[d].length + ' → ' + sets[d].length, cls: 'strong' });
          if (d < depth) out.push({ key: 'sym:' + d, kind: 'text', x: symX, y: d * 76 + 43, text: w[d], anchor: 'middle', cls: 'mono' });
        }
        return out;
      };
      const F = new T.Frames(['branches', 'states']);
      F.set('branches', 1).set('states', 1);
      F.add({ items: K.tree.draw(snap(0), { gapY: 76 }).items.concat(side(0)), say: 'The root is the start state ' + fa.start + '. Each level of the tree will be one more symbol of ' + R.w(inp.w) + ' read.', meta: { next: t.levels[1] ? t.levels[1].length : 0 } });
      for (let d = 1; d <= w.length; d++) {
        const died = t.levels[d - 1].filter((n) => n.dies === d - 1);
        const forks = t.levels[d - 1].filter((n) => n.kids.length > 1);
        F.set('branches', t.levels[d].length).set('states', sets[d].length);
        let say = 'Read ' + w[d - 1] + ': ' + t.levels[d].length + ' branch' + (t.levels[d].length === 1 ? '' : 'es') + ' now';
        if (forks.length) say += ' (' + forks.map((n) => n.q).join(', ') + ' fork' + (forks.length === 1 ? 's' : '') + ')';
        say += '.';
        if (died.length) say += ' ' + died.length + ' branch' + (died.length === 1 ? '' : 'es') + ' in ' + [...new Set(died.map((n) => n.q))].join(', ') + ' die' + (died.length === 1 ? 's' : '') + ': no move on ' + w[d - 1] + '.';
        say += ' But they sit in only ' + sets[d].length + ' distinct state' + (sets[d].length === 1 ? '' : 's') + ': ' + R.set(sets[d]) + '.';
        F.add({ items: K.tree.draw(snap(d), { gapY: 76 }).items.concat(side(d)), say, meta: { next: t.levels[d + 1] ? t.levels[d + 1].length : null } });
      }
      const leaves = t.levels[w.length];
      const good = leaves.filter((n) => acc.has(n.q));
      // one accepting path, lit from the root
      const path = [];
      if (good.length) { let id = good[0].id; while (id) { path.unshift(id); id = id.includes('.') ? id.slice(0, id.lastIndexOf('.')) : null; } }
      F.add({ items: K.tree.draw(snap(w.length, true), { gapY: 76, path }).items.concat(side(w.length)), say: good.length ? good.length + ' of the ' + leaves.length + ' branches end in an accepting state, so ' + R.w(inp.w) + ' is accepted; the lit path is one accepting run. A simulator never needs the whole tree, only the column of sets on the right.' : (leaves.length ? 'None of the ' + leaves.length + ' branches ends in an accepting state' : 'Every branch died') + ', so ' + R.w(inp.w) + ' is rejected. The column of sets on the right tells the same story with far less work.', mark: good.length ? 'accepted' : 'rejected', meta: { verdict: good.length ? 'Yes' : 'No' } });
      return { frames: F.list, def: { sections: [R.tuple(fa), R.delta(fa).section, { id: 'why', kind: 'text', title: 'Tree against sets', text: 'The tree may have up to (largest number of choices)ⁿ branches after n symbols, but a level never holds more distinct states than the machine has. Merging branches in the same state is the subset view.' }] } };
    },
    predict: [
      { at: (f, i, fr) => i === 1 && f.meta && f.meta.next !== null && f.meta.next !== undefined, once: true, pick: 'option', options: (fr, i) => R.numberOptions(fr[i].meta.next), ask: 'How many branches will the tree have after the next symbol?', answer: (fr, i) => String(fr[i].meta.next), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will some branch end in an accepting state?', answer: (fr) => fr[fr.length - 1].meta.verdict, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'An NFA has two choices at every symbol. How many branches can its tree have after 10 symbols?', options: ['10', '20', '100', '1024'], answer: 3, why: 'Each level can double: 2¹⁰ = 1024 leaves.' },
      { q: 'The same NFA has 4 states. How many distinct states can a level hold?', options: ['At most 4', 'At most 16', 'At most 1024', 'Exactly 1'], answer: 0, why: 'Branches in the same state behave the same from then on, so a level is just a subset of the 4 states.' },
      { q: 'A branch reaches a state with no move on the next symbol. What happens to it?', options: ['It restarts', 'It dies; the others carry on', 'The whole run rejects', 'It waits'], answer: 1, why: 'A missing move kills only that branch. The string is rejected only if every branch dies or fails.' },
      { q: 'Why is searching the tree depth-first a poor way to simulate an NFA?', options: ['It gives wrong answers', 'It may explore exponentially many branches, while the sets need only n steps', 'It needs a stack', 'It ignores ε-moves'], answer: 1, why: 'Backtracking can try a branch for every leaf; the level-by-level sets never grow beyond the number of states.' },
    ],
  });

  // ---- guessing the k-th symbol from the end -----------------------------------------------------------------
  const guessNFA = (k) => {
    const trans = [{ from: 'q0', sym: 'a', to: 'q0' }, { from: 'q0', sym: 'b', to: 'q0' }, { from: 'q0', sym: 'a', to: 'q1' }];
    for (let j = 1; j < k; j++) for (const c of ['a', 'b']) trans.push({ from: 'q' + j, sym: c, to: 'q' + (j + 1) });
    return T.FA.make({ states: Array.from({ length: k + 1 }, (_, j) => 'q' + j), alphabet: ['a', 'b'], start: 'q0', accept: ['q' + k], trans });
  };
  T.topic({
    id: 'nfa-guess', family: 'nfa', order: 40, title: 'Guessing the k-th symbol from the end',
    blurb: 'An NFA for "the k-th symbol from the end is a" simply guesses which a it is and checks that exactly k − 1 symbols follow. Watch every guess start, and all but the right one die.',
    inputs: [
      { id: 'k', kind: 'number', label: 'k', def: 3, min: 1, max: 4 },
      { id: 'w', kind: 'string', label: 'Input', def: 'abaab', max: 10, alphabet: 'ab' },
    ],
    presets: [
      { label: 'k = 3: abaab', values: { k: 3, w: 'abaab' } },
      { label: 'k = 3: abbb (the right symbol is b)', values: { k: 3, w: 'abbb' } },
      { label: 'k = 2: aaaa (many guesses at once)', values: { k: 2, w: 'aaaa' } },
      { label: 'k = 3: too short, ab', values: { k: 3, w: 'ab' } },
      { label: 'k = 1: ends in a', values: { k: 1, w: 'bba' } },
    ],
    counters: [{ id: 'guesses', label: 'guesses made' }, { id: 'alive', label: 'guesses alive' }],
    run(inp) {
      const k = inp.k, w = [...inp.w], n = w.length;
      const fa = guessNFA(k);
      const d = R.dia(fa);
      const pos = R.row(fa.states, 0, 0, 140);
      const g0 = K.graph.draw(d, { pos });
      const cw = 46, sx = g0.box.x + g0.box.w / 2 - (Math.max(n, 1) * cw) / 2, sy = g0.box.y + g0.box.h + 56;
      const dt = R.delta(fa);
      // guess j (an a at position j) is in state q(pos - j) after pos symbols, and dies past qk
      const guesses = w.map((c, j) => (c === 'a' ? j : -1)).filter((j) => j >= 0);
      const state = (j, p) => (p <= j ? null : p - j <= k ? 'q' + (p - j) : 'dead');
      const brackets = (p, final) => guesses.filter((j) => j < p).map((j) => {
        const s = state(j, p);
        const done = s === 'dead';
        const win = final && s === 'q' + k;
        const lost = done || (final && s !== 'q' + k);
        return { id: 'g' + j, from: j, to: Math.min(j + k, n), level: j % k, text: lost ? '✗' : win ? '✓' : s, cls: win ? 'z' : lost ? 'x' : 'y' };
      });
      const scene = (p, gopts, final) => K.graph.draw(d, Object.assign({ pos }, gopts)).items.concat(K.string.draw({ text: w, pos: p, x: sx, y: sy, cw, label: 'input', headText: p >= n ? 'end' : 'next', brackets: brackets(p, final), cls: (i) => (final && i === n - k && w[i] === 'a' ? 'good' : '') }).items);
      const live = (p) => ['q0'].concat(guesses.map((j) => state(j, p)).filter((s) => s && s !== 'dead')).filter((x, i, a) => a.indexOf(x) === i);
      const F = new T.Frames(['guesses', 'alive']);
      F.add({ items: scene(0, { active: ['q0'], startHot: true }), say: 'q0 reads anything and stays. On an a it may also guess "this a is the ' + (k === 1 ? 'last symbol' : k + (k === 2 ? 'nd' : k === 3 ? 'rd' : 'th') + ' symbol from the end') + '" and move on to q1; the guess must then reach q' + k + ' exactly when the input ends.', meta: { live: ['q0'] } });
      for (let p = 1; p <= n; p++) {
        const c = w[p - 1];
        const L = live(p);
        const prev = live(p - 1);
        const dying = guesses.filter((j) => state(j, p) === 'dead' && state(j, p - 1) === 'q' + k);
        const taken = prev.flatMap((q) => fa.trans.filter((e) => e.from === q && e.sym === c).map((e) => e.from + '>' + e.to));
        if (c === 'a') F.count('guesses');
        F.set('alive', guesses.filter((j) => j < p && state(j, p) !== 'dead').length);
        let say = 'Read ' + c + ': ' + (c === 'a' ? 'q0 stays, and a new guess starts in q1 (maybe this a is the one)' : 'q0 stays; a b cannot start a guess');
        const moving = guesses.filter((j) => j < p - 1 && state(j, p) !== 'dead');
        if (moving.length) say += '; ' + (moving.length === 1 ? 'the older guess moves' : 'older guesses move') + ' on to ' + moving.map((j) => state(j, p)).join(', ');
        say += '.';
        if (dying.length) say += ' The guess at position ' + (dying[0] + 1) + ' was in q' + k + ' with input left: no move, it dies (that a was too early).';
        F.add({ items: scene(p, { active: L, taken }), say, hl: { delta: prev.map((q) => dt.rc(q, c)) }, meta: { live: L } });
      }
      const ok = n >= k && w[n - k] === 'a';
      const tooLate = guesses.filter((j) => j > n - k);
      F.add({ items: scene(n, ok ? { good: ['q' + k], active: live(n).filter((q) => q !== 'q' + k) } : { active: live(n) }, true), say: ok ? 'The input is used up and the guess made at position ' + (n - k + 1) + ' is exactly in q' + k + ': it guessed right, so the NFA accepts.' + (tooLate.length ? ' Later guesses were too late: they never reached q' + k + '.' : '') : n < k ? 'The input is shorter than ' + k + ', so no guess can reach q' + k + ': reject.' : 'The ' + k + (k === 1 ? 'st' : k === 2 ? 'nd' : k === 3 ? 'rd' : 'th') + ' symbol from the end is b, so no guess started there; every guess was too early or too late: reject.', mark: ok ? 'accepted' : 'rejected', meta: { verdict: ok ? 'Accept' : 'Reject', win: ok ? n - k : null } });
      const dfaSize = T.FA.minimizeHopcroft(T.FA.subset(fa).fa).fa.states.length;
      const nb = R.note('cmp', { x: g0.box.x + g0.box.w / 2 - 150, y: sy + 44 + 40 + Math.max(1, Math.min(k, guesses.length)) * 44 + 24, title: 'the price of determinism', lines: ['this NFA: ' + (k + 1) + ' states', 'smallest DFA: ' + dfaSize + ' = 2^' + k + ' states'], size: 16 });
      F.add({ items: scene(n, ok ? { good: ['q' + k] } : {}, true).concat(nb.items), say: 'An NFA can guess; a DFA cannot, so it must remember all of the last ' + k + ' symbols, one state per possible window: the smallest DFA has ' + dfaSize + ' states against ' + (k + 1) + ' here.', mark: 'compare' });
      return { frames: F.list, def: { sections: [R.tuple(fa), dt.section] } };
    },
    predict: [
      { at: (f, i, fr) => i === 1 && fr.length > 4, once: true, pick: 'item', ask: 'Click a state that will be live after the next symbol.', answer: (fr, i) => fr[i + 1].meta.live.map((q) => 'g:s:' + q), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 3 && fr[fr.length - 2].meta.win !== null, once: true, pick: 'item', ask: 'Click the a whose guess will turn out right.', answer: (fr) => 's:c:' + fr[fr.length - 2].meta.win, explain: (fr) => fr[fr.length - 2].say },
      { at: (f, i, fr) => i === fr.length - 3 && fr[fr.length - 2].meta.win === null, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will any guess turn out right?', answer: () => 'Reject', explain: (fr) => fr[fr.length - 2].say },
    ],
    quiz: [
      { q: 'How many states does this NFA have for the k-th symbol from the end?', options: ['k', 'k + 1', '2k', '2ᵏ'], answer: 1, why: 'q0 to wait, then q1 … qk to count the k − 1 symbols after the guessed a.' },
      { q: 'And the smallest DFA for the same language?', options: ['k + 1', '2k', 'k²', '2ᵏ'], answer: 3, why: 'It must remember which of the last k symbols were a: any two different windows can be told apart by a suitable tail.' },
      { q: 'A guess reaches qk while symbols are still left. What happens?', options: ['Accept', 'The branch dies: qk has no moves', 'It goes back to q0', 'It waits for the end'], answer: 1, why: 'That a was more than k symbols from the end; the branch has nowhere to go.' },
      { q: 'With k = 3, is "ab" accepted?', options: ['Yes', 'No: there is no third symbol from the end', 'Only if it starts with a', 'It depends on the run'], answer: 1, why: 'A string shorter than k has no k-th symbol from the end, so no guess can finish.' },
    ],
  });
})();
