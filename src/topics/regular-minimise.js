// Minimisation: the table of pairs filled with a reason for every mark (and an arrow to the pair it
// depends on), partition refinement with blocks splitting on a shelf beside the machine, the double
// reversal that minimises by determinising twice, and why the minimal DFA is unique: two machines for
// one language shrink to the same one, matched state for state in colour.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, Geo = T.geom, R = T.Reg, FA = T.FA;

  T.family({ id: 'minimise', part: 'regular', order: 70, title: 'Minimisation', blurb: 'Merge the states no string can tell apart: table filling, partition refinement and double reversal, and why the smallest DFA for a language is unique.' });

  const SIX = 'start A\naccept C F\nA -a-> B\nA -b-> D\nB -a-> C\nB -b-> E\nC -a-> C\nC -b-> E\nD -a-> E\nD -b-> D\nE -a-> F\nE -b-> D\nF -a-> F\nF -b-> E';
  const RING6 = 'start z0\naccept z0 z3\nz0 -a-> z1\nz1 -a-> z2\nz2 -a-> z3\nz3 -a-> z4\nz4 -a-> z5\nz5 -a-> z0';
  const UNREACH = 'start p\naccept r\np -a-> q\np -b-> p\nq -a-> r\nq -b-> p\nr -a,b-> r\nu -a-> r\nu -b-> q';
  const PARTIAL = 'start s\naccept f\ns -a-> x\ns -b-> y\nx -a,b-> f\ny -b-> f\nf -a-> f\nf -b-> t\nt -a,b-> t';
  const MOD3 = 'start r0\naccept r0\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r0\nr2 -0-> r1\nr2 -1-> r2';

  /** The machine minimisation works on: complete, and with the unreachable states gone */
  function prep(fa) {
    const comp = FA.complete(fa, 'dead');
    const rm = FA.removeUnreachable(comp.fa);
    return { d: rm.fa, dead: comp.dead, removed: rm.removed };
  }
  const prepSay = (P) => [P.dead ? 'Missing moves go to a new state ' + P.dead + ', so the machine is complete.' : '', P.removed.length ? R.set(P.removed) + ' cannot be reached from the start: drop ' + (P.removed.length > 1 ? 'them' : 'it') + ' first.' : ''].filter(Boolean).join(' ');
  /** The minimal machine drawn where its blocks were: a merged state sits at the middle of its members */
  function mergedDraw(minFa, blocks, pos, opts) {
    const name = (b) => (b.length === 1 ? b[0] : FA.setName(b));
    const pos2 = {}, merged = {};
    for (const b of blocks) { const n = name(b); pos2[n] = { x: b.reduce((a, q) => a + pos[q].x, 0) / b.length, y: b.reduce((a, q) => a + pos[q].y, 0) / b.length }; if (b.length > 1) merged[n] = b; }
    // members of a block may sit on top of other states once merged: nudge apart if two land too close
    const names = Object.keys(pos2);
    for (let i = 0; i < names.length; i++) for (let j = i + 1; j < names.length; j++) { const a = pos2[names[i]], b = pos2[names[j]]; if (Math.hypot(a.x - b.x, a.y - b.y) < 70) { b.y += 80; } }
    return K.graph.draw(R.dia(minFa), Object.assign({ pos: pos2, merged }, opts || {}));
  }

  // ---- table filling ---------------------------------------------------------------------------------------------
  T.topic({
    id: 'min-table', family: 'minimise', order: 10, title: 'Table filling: mark the pairs a string tells apart',
    blurb: 'Every pair of states gets a cell. Mark a pair when ε separates it (one accepts, one not), then when some symbol leads it to a marked pair. Pairs never marked are equivalent and merge.',
    inputs: [R.machineInput({ id: 'm', label: 'DFA', def: SIX, kind: 'dfa', max: 7 })],
    presets: [
      { label: 'Six states, two merge', values: { m: SIX } },
      { label: 'Counting a\'s mod 6, accepting mod 3', values: { m: RING6 } },
      { label: 'An unreachable state is dropped first', values: { m: UNREACH } },
      { label: 'Missing moves: the dead state merges too', values: { m: PARTIAL } },
      { label: 'Already minimal: every pair is marked', values: { m: MOD3 } },
    ],
    counters: [{ id: 'pairs', label: 'pairs' }, { id: 'marked', label: 'marked' }, { id: 'round', label: 'round' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const P = prep(fa);
      const d = P.d, Q = d.states, n = Q.length;
      const res = FA.minimizeTable(fa);
      const dd = R.dia(d);
      const pos = K.graph.layout(dd).pos;
      const g0 = K.graph.draw(dd, { pos });
      const ix = new Map(Q.map((q, i) => [q, i]));
      const cell = (p, q) => { const i = ix.get(p), j = ix.get(q); return i > j ? [i - 1, j] : [j - 1, i]; };
      const marks = new Map();
      const tx = g0.box.x + g0.box.w + 70, ty = g0.box.y + g0.box.h / 2 - ((n - 1) * 50 + 34) / 2;
      const sub = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉'];
      const table = (o) => {
        o = o || {};
        const rows = [];
        for (let r = 0; r < n - 1; r++) { rows.push([]); for (let c = 0; c < n - 1; c++) { const k = r + ',' + c; rows[r].push(c <= r ? (marks.has(k) ? '×' + sub[Math.min(9, marks.get(k).round)] : o.same && o.same.includes(k) ? '=' : '') : ''); } }
        return K.table.draw({ rows, skip: (r, c) => c > r, rowHead: Q.slice(1), colHead: Q.slice(0, -1), corner: '', x: tx, y: ty, cw: 60, ch: 50, size: 20, hot: o.hot ? [o.hot] : [], cls: (r, c) => (marks.has(r + ',' + c) ? 'rmark' + (o.fresh && o.fresh.includes(r + ',' + c) ? ' hot' : '') : o.same && o.same.includes(r + ',' + c) ? 'rsame' : ''), arrows: o.arrow ? [{ from: o.arrow[0], to: o.arrow[1], bend: -30 }] : [] });
      };
      const dt = R.delta(d);
      const F = new T.Frames(['pairs', 'marked', 'round']);
      F.set('pairs', n * (n - 1) / 2);
      const scene = (g, t) => K.graph.draw(dd, Object.assign({ pos }, g || {})).items.concat(table(t).items);
      F.add({ items: scene(), say: (prepSay(P) ? prepSay(P) + ' ' : '') + 'The ' + n + ' states make ' + n * (n - 1) / 2 + ' pairs, one cell each. A pair gets marked (×) as soon as some string is accepted from one state and rejected from the other.' });
      const tr = res.trace;
      const zero = tr.filter((s) => s.kind === 'mark' && s.round === 0);
      const fresh0 = zero.map((s) => cell(s.pair[0], s.pair[1]).join(','));
      for (const s of zero) marks.set(cell(s.pair[0], s.pair[1]).join(','), { round: 0 });
      F.set('marked', marks.size);
      F.add({ items: scene({ good: d.accept }, { fresh: fresh0 }), say: zero.length ? 'Round 0: ε itself separates every accepting state (' + R.set(d.accept) + ') from every non-accepting one. That marks ' + R.plural(zero.length, 'pair') + '.' : 'Round 0: ' + (d.accept.length ? 'every state accepts' : 'no state accepts') + ', so ε separates nothing.', meta: { round: 0 } });
      let round = 0;
      for (const s of tr.filter((x) => x.kind === 'mark' && x.round > 0 || x.kind === 'round')) {
        if (s.kind === 'round') { F.set('round', s.round); F.add({ items: scene(), say: 'Round ' + s.round + ' marks nothing new, so no later round can either: the table is finished.', meta: { finished: true } }); continue; }
        round = s.round;
        F.set('round', round);
        const c = cell(s.pair[0], s.pair[1]), v = cell(s.via[0], s.via[1]);
        marks.set(c.join(','), { round });
        F.set('marked', marks.size);
        const [p, q] = s.pair;
        const p2 = d.trans.find((e) => e.from === p && e.sym === s.sym).to, q2 = d.trans.find((e) => e.from === q && e.sym === s.sym).to;
        F.add({ items: scene({ hot: [p, q], taken: [p + '>' + p2, q + '>' + q2], active: [p2, q2].filter((x) => x !== p && x !== q) }, { hot: c, fresh: [c.join(',')], arrow: [v, c] }), say: 'Round ' + round + ': on ' + s.sym + ', ' + p + ' goes to ' + p2 + ' and ' + q + ' goes to ' + q2 + '. {' + s.via.join(', ') + '} is already marked, so {' + p + ', ' + q + '} is too: ' + s.sym + ' followed by what separates ' + s.via.join(' and ') + ' separates them.', hl: { delta: [dt.rc(p, s.sym), dt.rc(q, s.sym)] }, meta: { mark: c } });
      }
      const same = tr.filter((s) => s.kind === 'equal').map((s) => cell(s.pair[0], s.pair[1]).join(','));
      const unm = [];
      for (let r = 0; r < n - 1; r++) for (let c = 0; c <= r; c++) if (!marks.has(r + ',' + c)) unm.push(r + ',' + c);
      F.add({ items: scene({}, { same: unm }), say: unm.length ? 'The cells left empty (=) are pairs no string can tell apart: ' + tr.filter((s) => s.kind === 'equal').map((s) => '{' + s.pair.join(', ') + '}').join(', ') + '. They can be merged.' : 'Every cell is marked: all ' + n + ' states are different, so the DFA is already minimal.', meta: { same: unm, nmin: res.fa.states.length } });
      void same;
      const mg = mergedDraw(res.fa, res.blocks, pos);
      const merges = res.blocks.filter((b) => b.length > 1);
      F.add({ items: mg.items.concat(table({ same: unm }).items), exits: mg.exits, say: merges.length ? 'Merge ' + merges.map((b) => b.join(' and ')).join('; ') + ': the minimal DFA has ' + res.fa.states.length + ' states instead of ' + n + ', and accepts exactly the same strings.' : 'Nothing merges: ' + n + ' states is the least any DFA for this language can have.', mark: 'done' });
      const minDt = R.delta(res.fa, { id: 'min', title: 'The minimal DFA' });
      return { frames: F.list, def: { sections: [R.tuple(d, 'The machine (complete, reachable)'), dt.section, { id: 'rule', kind: 'text', title: 'The rule', text: 'Mark {p, q} in round 0 when exactly one of p, q accepts. Mark it in round k when some symbol a takes it to a pair marked before round k. A mark made in round k means a separating string of length k.' }, minDt.section] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.mark && !(f.meta && f.meta.mark), once: true, pick: 'item', ask: 'Round 0 is done. Click a cell that the next round will mark: a pair that some symbol sends to a marked pair.', answer: (fr, i) => { const out = []; for (let k = i + 1; k < fr.length && fr[k].meta && fr[k].meta.mark; k++) out.push('tb:' + fr[k].meta.mark.join(',')); return out; }, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.same, once: true, pick: 'option', options: (fr) => { const f = fr.find((x) => x.meta && x.meta.same); return R.numberOptions(f.meta.nmin); }, ask: 'When the table is finished, how many states will the minimal DFA have?', answer: (fr) => String(fr.find((x) => x.meta && x.meta.same).meta.nmin), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A pair is marked in round 2. What does that tell you?', options: ['The states are equivalent', 'Some string of length 2 separates them, and no shorter one does', 'They both accept', 'They are both unreachable'], answer: 1, why: 'Round k marks exactly the pairs whose shortest separating string has length k.' },
      { q: 'Why remove unreachable states before filling the table?', options: ['They would break the algorithm', 'They do not affect the language, and leaving them in keeps extra states', 'They are always equivalent to the start', 'To save colour'], answer: 1, why: 'Table filling only merges equivalent states; an unreachable state may be equivalent to none and would survive into the result.' },
      { q: 'p and q both go to the same state on every symbol, and both accept. Will {p, q} be marked?', options: ['Yes, in round 1', 'Never', 'Only if the alphabet is large', 'Yes, in round 0'], answer: 1, why: 'Round 0 needs one accepting and one not; later rounds need a symbol leading to a marked pair, but they always go to the same state.' },
      { q: 'How many cells has the table for a DFA with 8 states?', options: ['8', '28', '56', '64'], answer: 1, why: 'One per unordered pair: 8 × 7 / 2 = 28.' },
      { q: 'When does table filling stop?', options: ['After n rounds exactly', 'When a round marks nothing new', 'When the start is marked', 'When half the cells are marked'], answer: 1, why: 'Marks in a round depend only on earlier marks; a round with no new marks means the next would find none either.' },
    ],
  });

  // ---- partition refinement ----------------------------------------------------------------------------------------
  T.topic({
    id: 'min-partition', family: 'minimise', order: 20, title: 'Partition refinement: blocks that split',
    blurb: 'Start with two blocks, accepting and not. Split a block whenever its states disagree about which block some symbol leads to. When nothing splits, each block is one state of the minimal DFA.',
    inputs: [
      R.machineInput({ id: 'm', label: 'DFA', def: SIX, kind: 'dfa', max: 7 }),
      { id: 'how', kind: 'choice', label: 'Method', def: 'moore', options: [{ value: 'moore', label: 'round by round (Moore)' }, { value: 'hopcroft', label: 'with splitters (Hopcroft)' }] },
    ],
    presets: [
      { label: 'Six states, round by round', values: { m: SIX, how: 'moore' } },
      { label: 'Six states, with splitters', values: { m: SIX, how: 'hopcroft' } },
      { label: 'Counting a\'s mod 6, accepting mod 3', values: { m: RING6, how: 'moore' } },
      { label: 'Missing moves: dead joins a block', values: { m: PARTIAL, how: 'moore' } },
      { label: 'Already minimal: every block ends alone', values: { m: MOD3, how: 'moore' } },
    ],
    counters: [{ id: 'blocks', label: 'blocks' }, { id: 'splits', label: 'splits' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const P = prep(fa);
      const d = P.d, dd = R.dia(d);
      const res = inp.how === 'hopcroft' ? FA.minimizeHopcroft(fa) : FA.minimizeMoore(fa);
      const pos = K.graph.layout(dd).pos;
      const g0 = K.graph.draw(dd, { pos });
      const box = R.bounds(g0.items);
      const sx = box.x + box.w + 60;
      // colours stay with blocks: the first part of a split keeps its colour, the other takes a fresh one
      const colour = new Map();
      let nextColour = 0;
      const keyOf = (b) => b.slice().sort().join('\u0000');
      const colourOf = (b) => { const k = keyOf(b); if (!colour.has(k)) colour.set(k, nextColour++ % 8); return colour.get(k); };
      const chipW = Math.max(40, ...d.states.map((q) => Geo.textWidth(q, 15, { bold: true }) + 18));
      const shelf = (blocks, hot) => {
        const items = [R.caption('sh:title', sx, box.y - 2, 'blocks', 'title', 'start')];
        let y = box.y + 14;
        blocks.forEach((b) => {
          const c = colourOf(b);
          const w = b.length * (chipW + 8) + 22;
          items.push({ key: 'blk:' + keyOf(b), kind: 'region', x: sx, y, w, h: 50, rx: 12, cls: 'rk' + c + (hot && keyOf(hot) === keyOf(b) ? ' rk-hot' : '') });
          b.forEach((q, i) => items.push({ key: 'chip:' + q, kind: 'cell', x: sx + 11 + i * (chipW + 8), y: y + 9, w: chipW, h: 32, rx: 16, text: q, cls: 'rk' + c, size: 15 }));
          y += 60;
        });
        return items;
      };
      const stateCls = (blocks) => { const o = {}; for (const b of blocks) for (const q of b) o[q] = 'rk' + colourOf(b); return o; };
      const scene = (blocks, g, hot) => K.graph.draw(dd, Object.assign({ pos, cls: stateCls(blocks) }, g || {})).items.concat(shelf(blocks, hot));
      const F = new T.Frames(['blocks', 'splits']);
      const dt = R.delta(d);
      let blocks = null;
      const say0 = prepSay(P);
      for (const s of res.trace) {
        if (s.kind === 'partition' && blocks === null) {
          blocks = s.blocks.map((b) => b.slice());
          blocks.forEach(colourOf);
          F.set('blocks', blocks.length);
          F.add({ items: K.graph.draw(dd, { pos }).items, say: (say0 ? say0 + ' ' : '') + 'Which states can be merged? Start by trusting nothing but acceptance.' });
          F.add({ items: scene(blocks), say: 'Two blocks to begin: accepting ' + R.set(d.accept) + ' and non-accepting ' + R.set(d.states.filter((q) => !d.accept.includes(q))) + '. ε already tells them apart.', meta: { blocks: blocks.length } });
          continue;
        }
        if (s.kind === 'splitter') {
          F.add({ items: scene(blocks, { hot: s.pre }), say: 'Splitter ' + R.set(s.block) + ' on ' + s.sym + ': the states that reach it on ' + s.sym + ' are ' + R.set(s.pre) + '. Any block holding some of these and some others must split.' });
          continue;
        }
        if (s.kind === 'split') {
          const idx = blocks.findIndex((b) => keyOf(b) === keyOf(s.block));
          const taken = s.block.map((q) => q + '>' + d.trans.find((e) => e.from === q && e.sym === s.sym).to);
          F.add({ items: scene(blocks, { taken, hot: s.block }, s.block), say: 'Look at ' + R.set(s.block) + ' on ' + s.sym + ': ' + s.block.map((q) => q + ' → ' + d.trans.find((e) => e.from === q && e.sym === s.sym).to).join(', ') + '. The targets lie in different blocks (see the colours).', hl: { delta: s.block.map((q) => dt.rc(q, s.sym)) }, meta: { split: s.into.length, before: blocks.length } });
          const [first, ...rest] = s.into;
          colour.set(keyOf(first), colourOf(s.block));
          rest.forEach(colourOf);
          blocks.splice(idx, 1, ...s.into.map((b) => b.slice()));
          F.count('splits').set('blocks', blocks.length);
          F.add({ items: scene(blocks, { taken }), say: 'So ' + R.set(s.block) + ' splits into ' + s.into.map(R.set).join(' and ') + '.', hl: { delta: s.block.map((q) => dt.rc(q, s.sym)) } });
          continue;
        }
        if (s.kind === 'partition' && s.stable) {
          F.add({ items: scene(blocks), say: (inp.how === 'hopcroft' ? 'No splitters are left' : 'A whole round splits nothing') + ': the partition is stable with ' + R.plural(blocks.length, 'block') + '. Within a block, every symbol leads every state to the same block.', meta: { stable: blocks.length } });
        }
      }
      const mg = mergedDraw(res.fa, res.blocks, pos, { cls: Object.fromEntries(res.blocks.map((b) => [b.length === 1 ? b[0] : FA.setName(b), 'rk' + colourOf(blocks.find((x) => keyOf(x) === keyOf(b)) || b)])) });
      F.add({ items: mg.items.concat(shelf(blocks)), exits: mg.exits, say: 'Each block becomes one state: ' + res.fa.states.join(', ') + '. The minimal DFA has ' + R.plural(res.fa.states.length, 'state') + ' (from ' + d.states.length + ').', mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(d, 'The machine (complete, reachable)'), dt.section, { id: 'rule', kind: 'text', title: 'When a block splits', text: inp.how === 'hopcroft' ? 'A splitter (S, a) cuts every block into the states that reach S on a and the rest. When a block splits, its halves join the queue (only the smaller one if the block was not already waiting).' : 'Two states stay in one block only while, for every symbol, their moves land in the same block. Each round compares every block against the blocks of the round before.' }, R.delta(res.fa, { id: 'min', title: 'The minimal DFA' }).section] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.split, once: true, pick: 'option', options: (fr, i) => R.numberOptions(fr[i].meta.before + fr[i].meta.split - 1), ask: 'This block is about to split by colour of where its moves land. How many blocks will there be after it splits?', answer: (fr, i) => String(fr[i].meta.before + fr[i].meta.split - 1), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.stable !== undefined && !(f.meta && f.meta.split), once: true, pick: 'option', options: ['Yes', 'No'], ask: 'Will anything split any more?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Why start with exactly two blocks, accepting and non-accepting?', options: ['Because ε tells those two kinds apart and nothing else is known yet', 'Because the alphabet has two symbols', 'Because a DFA has two kinds of moves', 'It is an arbitrary choice'], answer: 0, why: 'The empty string is accepted from one kind and rejected from the other; every finer distinction is found by splitting.' },
      { q: 'States p and q are in one block, but on b, p goes to block X and q to block Y. What happens?', options: ['Nothing', 'p and q are separated', 'X and Y merge', 'The machine is not a DFA'], answer: 1, why: 'b followed by a string separating X from Y separates p from q.' },
      { q: 'Can two blocks ever merge again during refinement?', options: ['Yes, often', 'No: blocks only ever split', 'Only in the last round', 'Only with splitters'], answer: 1, why: 'Every split is justified by a separating string, which never stops separating.' },
      { q: 'What does the splitter method gain over round by round refinement?', options: ['A smaller result', 'Speed: about n log n work, by re-queuing only the smaller half of a split', 'It works on NFAs', 'Nothing'], answer: 1, why: 'Both give the same partition; queueing only the smaller half bounds how often each state is looked at.' },
    ],
  });

  // ---- double reversal -------------------------------------------------------------------------------------------
  const ENDS_AB = 'start q0\naccept q2\nq0 -a-> q1\nq0 -b-> q3\nq1 -a-> q1\nq1 -b-> q2\nq2 -a-> q4\nq2 -b-> q3\nq3 -a-> q4\nq3 -b-> q3\nq4 -a-> q4\nq4 -b-> q2';
  T.topic({
    id: 'min-brzozowski', family: 'minimise', order: 30, title: 'Double reversal: determinise twice',
    blurb: 'Reverse the machine, determinise it, reverse again, determinise again. Surprisingly, what comes out is always the minimal DFA.',
    inputs: [R.machineInput({ id: 'm', label: 'Machine', def: SIX, kind: 'any', max: 6 })],
    presets: [
      { label: 'Six states, two merge', values: { m: SIX } },
      { label: 'Ends in ab, with redundant states', values: { m: ENDS_AB } },
      { label: 'Counting a\'s mod 6, accepting mod 3', values: { m: RING6 } },
      { label: 'An NFA works too', values: { m: 'start p\naccept r\np -a,b-> p\np -a-> q\nq -b-> r' } },
    ],
    counters: [{ id: 'states', label: 'states now' }],
    run(inp) {
      const fa = R.fa(inp.m);
      const res = FA.minimizeBrzozowski(fa);
      const steps = res.trace;
      const labels = ['M', 'reverse', 'determinise', 'reverse', 'determinise'];
      const machines = [fa, steps[0].fa, steps[1].fa, steps[2].fa, steps[3].fa];
      const starts = [[fa.start], steps[0].starts, [steps[1].fa.start], steps[2].starts, [steps[3].fa.start]];
      // reversed machines keep the positions of the machine they came from, so the arrows visibly turn round
      const pos = [];
      pos[0] = K.graph.layout(R.dia(fa)).pos;
      pos[1] = pos[0];
      pos[2] = K.graph.layout(R.dia(machines[2])).pos;
      pos[3] = pos[2];
      pos[4] = K.graph.layout(R.dia(machines[4])).pos;
      const draws = machines.map((m, k) => {
        const dm = R.dia(m);
        if (k === 1 || k === 3) dm.kind = 'nfa';
        return K.graph.draw(Object.assign(dm, { start: starts[k].length === 1 ? starts[k][0] : null }), { pos: pos[k], prefix: 'g' + k, active: starts[k].length > 1 ? starts[k] : [], hideStart: starts[k].length !== 1, good: k === 4 ? [] : [] });
      });
      // a strip of the five stages over the machine, the current one lit
      const top = Math.min(...draws.map((g) => R.bounds(g.items).y)) - 70;
      const cx = Math.min(...draws.map((g) => R.bounds(g.items).x));
      const strip = (k) => {
        const out = [];
        let x = cx;
        labels.forEach((l, i) => {
          const t = l + (i <= k ? ': ' + machines[i].states.length : '');
          const w = Geo.textWidth(t, 14, { bold: true }) + 22;
          out.push({ key: 'st:' + i, kind: 'cell', x, y: top, w, h: 32, rx: 16, text: t, size: 14, cls: i === k ? 'hot' : i < k ? 'read' : '' });
          if (i) out.push({ key: 'st:e' + i, kind: 'edge', from: 'st:' + (i - 1), to: 'st:' + i, cls: i <= k ? 'soft' : 'soft dim' });
          x += w + 26;
        });
        return out;
      };
      const F = new T.Frames(['states']);
      const say = [
        'The machine M has ' + R.plural(fa.states.length, 'state') + '. Minimise it without comparing a single pair of states.',
        'Reverse it: every arrow turns round, and the old accepting states ' + R.set(fa.accept) + ' all become initial (lit), while ' + fa.start + ' becomes the only accepting state. This accepts the reversed strings.',
        'Determinise the reversal, building only the subsets reachable from the initial set: ' + R.plural(machines[2].states.length, 'state') + '.',
        'Reverse that DFA again: back to the original language. Since it was deterministic, each state now has at most one way in on each symbol.',
        'Determinise once more: ' + R.plural(machines[4].states.length, 'state') + '. Because every subset reached comes from a machine with unique ways in, no two of them accept the same strings: this DFA is minimal.',
      ];
      machines.forEach((m, k) => {
        F.set('states', m.states.length);
        const extra = starts[k].length > 1 ? [R.caption('cap' + k, R.bounds(draws[k].items).x + R.bounds(draws[k].items).w / 2, R.bounds(draws[k].items).y + R.bounds(draws[k].items).h + 26, 'initial: ' + R.set(starts[k]), 'hot')] : [];
        F.add({ items: strip(k).concat(draws[k].items, extra), say: say[k], meta: { k, n: m.states.length } });
      });
      const hop = FA.minimizeHopcroft(fa).fa.states.length;
      F.add({ items: strip(4).concat(K.graph.draw(R.dia(machines[4]), { pos: pos[4], prefix: 'g4', good: machines[4].accept }).items), say: 'Check: refining the partition of the complete machine also gives ' + R.plural(hop, 'state') + '. Two very different roads, one destination: the minimal DFA is unique.', mark: 'done' });
      return { frames: F.list, def: { sections: [R.tuple(fa, 'M'), { id: 'steps', kind: 'math', title: 'The recipe', text: 'det(rev(det(rev(M))))\nrev: turn arrows, swap start and accepting\ndet: subset construction, reachable only' }, R.delta(machines[4], { id: 'min', title: 'The result' }).section] } };
    },
    predict: [
      { at: (f, i) => f.meta && f.meta.k === 3, once: true, pick: 'option', options: (fr, i) => R.numberOptions(fr[i + 1].meta.n), ask: 'Determinise once more. How many states will the result have?', answer: (fr, i) => String(fr[i + 1].meta.n), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i) => f.meta && f.meta.k === 0, once: true, pick: 'option', options: ['Yes', 'No'], ask: 'After reversing, does the machine accept the same strings as M?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'What does reversing a DFA give, in general?', options: ['A DFA for the same language', 'An NFA (perhaps with several initial states) for the reversed language', 'The complement', 'The minimal DFA'], answer: 1, why: 'Turning arrows round can give a state two ways out on a symbol, and the old accepting states all become starts.' },
      { q: 'Why can the first determinisation be large?', options: ['It never is', 'Subset construction can need up to 2ⁿ subsets', 'Because of ε-moves', 'Because reversal adds states'], answer: 1, why: 'The reversed language may need exponentially many states, so the intermediate DFA can blow up.' },
      { q: 'What property of the second reversal makes the final determinisation minimal?', options: ['It has no accepting states', 'Each state has at most one way in on each symbol (it came from a DFA)', 'It is complete', 'It has one start state'], answer: 1, why: 'Reachable subsets of such a machine accept pairwise different languages, so nothing could be merged.' },
      { q: 'Do double reversal and table filling always give the same number of states?', options: ['Yes: the minimal DFA is unique (up to names)', 'No, double reversal is smaller', 'No, table filling is smaller', 'Only for complete DFAs'], answer: 0, why: 'Every minimal DFA for a language is the same machine with different names (counting the dead state the same way).' },
    ],
  });

  // ---- uniqueness ----------------------------------------------------------------------------------------------
  const EVEN_A1 = 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o';
  const EVEN_A2 = 'start s\naccept s t\ns -a-> u\ns -b-> t\nt -a-> v\nt -b-> s\nu -a-> t\nu -b-> v\nv -a-> s\nv -b-> u';
  const ENDS_AB2 = 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a-> y\nz -b-> x';
  const HAS_AB = 'start x\naccept z\nx -a-> y\nx -b-> x\ny -a-> y\ny -b-> z\nz -a,b-> z';
  T.topic({
    id: 'min-unique', family: 'minimise', order: 40, title: 'The minimal DFA is unique',
    blurb: 'Two machines that look nothing alike but accept the same strings shrink to the same minimal DFA: match the start states, follow the moves, and every state finds its twin.',
    inputs: [
      R.machineInput({ id: 'a', label: 'Machine A', def: EVEN_A1, kind: 'dfa', max: 6, complete: true }),
      R.machineInput({ id: 'b', label: 'Machine B', def: EVEN_A2, kind: 'dfa', max: 6, complete: true }),
    ],
    presets: [
      { label: 'Even number of a\'s: 2 states and 4', values: { a: EVEN_A1, b: EVEN_A2 } },
      { label: 'Ends in ab: two designs', values: { a: ENDS_AB2, b: ENDS_AB } },
      { label: 'Different languages: the matching fails', values: { a: ENDS_AB2, b: HAS_AB } },
      { label: 'The same machine renamed', values: { a: EVEN_A1, b: 'start P\naccept P\nP -a-> Q\nQ -a-> P\nP -b-> P\nQ -b-> Q' } },
    ],
    check: (inp) => { const x = T.Machine.alphabet(T.Machine.parse(inp.a)).join(), y = T.Machine.alphabet(T.Machine.parse(inp.b)).join(); return x !== y ? 'The two machines must read the same alphabet ({' + x + '} and {' + y + '})' : null; },
    counters: [{ id: 'matched', label: 'states matched' }],
    run(inp) {
      const A = R.fa(inp.a), B = R.fa(inp.b);
      const mA = FA.minimizeHopcroft(A), mB = FA.minimizeHopcroft(B);
      const pa = K.graph.layout(R.dia(A)).pos, pb0 = K.graph.layout(R.dia(B)).pos;
      const ga0 = K.graph.draw(R.dia(A), { pos: pa, prefix: 'a' });
      const ba = R.bounds(ga0.items);
      const bb0 = R.bounds(K.graph.draw(R.dia(B), { pos: pb0, prefix: 'b' }).items);
      const dx = ba.x + ba.w + 110 - bb0.x, dy = ba.y + ba.h / 2 - (bb0.y + bb0.h / 2);
      const pb = {};
      for (const q in pb0) pb[q] = { x: pb0[q].x + dx, y: pb0[q].y + dy };
      const capY = Math.min(ba.y, bb0.y + dy) - 26;
      const caps = (ta, tb) => [R.caption('capA', ba.x + ba.w / 2, capY, ta, 'title'), R.caption('capB', bb0.x + dx + bb0.w / 2, capY, tb, 'title')];
      const F = new T.Frames(['matched']);
      F.add({ items: ga0.items.concat(K.graph.draw(R.dia(B), { pos: pb, prefix: 'b' }).items, caps('A: ' + A.states.length + ' states', 'B: ' + B.states.length + ' states')), say: 'A has ' + A.states.length + ' states and B has ' + B.states.length + '. Do they accept the same strings? Minimise both and compare.' });
      // minimise each in place: merged states form where their members were
      const place = (fa0, res, pos) => {
        const blocks = res.blocks || [];
        const p2 = {};
        for (const b of blocks) { const n = b.length === 1 ? b[0] : FA.setName(b); p2[n] = { x: b.reduce((s, q) => s + pos[q].x, 0) / b.length, y: b.reduce((s, q) => s + pos[q].y, 0) / b.length }; }
        // a dead state added by completion has no old position
        for (const q of res.fa.states) if (!p2[q]) p2[q] = { x: Math.max(...Object.values(pos).map((p) => p.x)) + 120, y: 0 };
        return p2;
      };
      const qa = place(A, mA, pa), qb = place(B, mB, pb);
      const merged = (res) => Object.fromEntries((res.blocks || []).filter((b) => b.length > 1).map((b) => [FA.setName(b), b]));
      const drawMin = (o) => {
        const x = K.graph.draw(R.dia(mA.fa), Object.assign({ pos: qa, prefix: 'a', merged: merged(mA) }, o.a || {}));
        const y = K.graph.draw(R.dia(mB.fa), Object.assign({ pos: qb, prefix: 'b', merged: merged(mB) }, o.b || {}));
        return { items: x.items.concat(y.items), exits: Object.assign({}, x.exits, y.exits) };
      };
      const m0 = drawMin({});
      F.add({ items: m0.items.concat(caps('A minimised: ' + mA.fa.states.length, 'B minimised: ' + mB.fa.states.length)), exits: m0.exits, say: 'Minimise each: A goes from ' + A.states.length + ' to ' + mA.fa.states.length + ' states, B from ' + B.states.length + ' to ' + mB.fa.states.length + '.' + (mA.fa.states.length !== mB.fa.states.length ? ' Different sizes already: the languages must differ.' : '') });
      const iso = FA.isomorphic(mA.fa, mB.fa);
      const eq = FA.equivalent(A, B);
      if (iso.iso) {
        // the matching found breadth-first from the starts, one colour per pair
        const order = Object.keys(iso.map);
        const cls = { a: {}, b: {} };
        order.forEach((p, k) => {
          cls.a[p] = 'rk' + (k % 8); cls.b[iso.map[p]] = 'rk' + (k % 8);
          F.set('matched', k + 1);
          const via = k === 0 ? 'The starts must match: ' + p + ' with ' + iso.map[p] + '.' : (() => { const e = mA.fa.trans.find((t) => order.indexOf(t.from) < k && t.to === p); const f = e && mB.fa.trans.find((t) => t.from === iso.map[e.from] && t.sym === e.sym); return e ? 'On ' + e.sym + ', ' + e.from + ' goes to ' + p + ' and its twin ' + iso.map[e.from] + ' goes to ' + (f ? f.to : iso.map[p]) + ', so ' + p + ' matches ' + iso.map[p] + '.' : p + ' matches ' + iso.map[p] + '.'; })();
          const m = drawMin({ a: { cls: Object.assign({}, cls.a), hot: [p] }, b: { cls: Object.assign({}, cls.b), hot: [iso.map[p]] } });
          F.add({ items: m.items.concat(caps('A minimised', 'B minimised')), say: via + (mA.fa.accept.includes(p) ? ' Both accept.' : ' Neither accepts.'), meta: { pair: [p, iso.map[p]], k } });
        });
        const m = drawMin({ a: { cls: cls.a }, b: { cls: cls.b } });
        F.add({ items: m.items.concat(caps('A minimised', 'B minimised')), say: 'Every state has a twin of the same colour, with the same moves and the same verdict: the two minimal DFAs are the same machine with different names. So A and B accept the same language.', mark: 'equal' });
      } else {
        F.add({ items: drawMin({ a: { bad: [mA.fa.start] }, b: { bad: [mB.fa.start] } }).items.concat(caps('A minimised', 'B minimised')), say: 'The matching fails: ' + iso.reason + ' So the languages differ' + (eq.counterexample !== null && eq.counterexample !== undefined ? ': ' + R.w(eq.counterexample) + ' is accepted by ' + eq.acceptedBy + ' only.' : '.'), mark: 'different' });
      }
      return { frames: F.list, def: { sections: [R.delta(mA.fa, { id: 'ma', title: 'A minimised' }).section, R.delta(mB.fa, { id: 'mb', title: 'B minimised' }).section, { id: 'thm', kind: 'text', title: 'Why unique', text: 'Each state of a minimal DFA stands for one Myhill–Nerode class: the set of strings after which the same suffixes are accepted. The classes depend only on the language, so any two minimal DFAs for it match class for class.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.k === 1, once: true, pick: 'item', ask: (fr, i) => 'Which state of B is the twin of ' + fr[i + 1].meta.pair[0] + '? Click it.', answer: (fr, i) => 'b:s:' + fr[i + 1].meta.pair[1], explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Two DFAs for one language have 5 and 9 states. What do you know about their minimal DFAs?', options: ['Nothing', 'They are the same machine up to renaming', 'The 9-state one minimises to 9', 'They differ by 4 states'], answer: 1, why: 'Minimisation of any DFA for a language gives the unique minimal DFA (up to names).' },
      { q: 'How is the matching of states forced?', options: ['By state names', 'Starts match starts, and matched states must move to matched states on each symbol', 'By counting edges', 'At random'], answer: 1, why: 'Following the moves from the starts leaves no choice: each reachable state gets exactly one twin.' },
      { q: 'This gives a test for equivalence of DFAs. Which?', options: ['Compare the numbers of states', 'Minimise both and check the results are isomorphic', 'Run both on ε', 'Compare their alphabets'], answer: 1, why: 'Equal languages give identical minimal DFAs; different languages cannot.' },
      { q: 'One minimised machine has a dead state and the other is partial. Are they isomorphic as drawn?', options: ['Yes', 'Not as drawn: completing both first makes them comparable', 'Never equivalent', 'Only for finite languages'], answer: 1, why: 'Uniqueness is stated for complete DFAs (or for trimmed ones); mixing the two conventions adds or removes the dead state.' },
    ],
  });
})();
