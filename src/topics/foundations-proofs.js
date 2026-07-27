// Three proof techniques, acted out. Induction as a row of dominoes: the base knocks over the first, the
// step makes each fallen domino knock over the next, and a claim that breaks leaves one standing. The
// pigeonhole principle as pigeons dropping into holes until two must share. Diagonalisation as a recipe:
// from any list of functions build one that differs from the n-th at n.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found, Geo = T.geom;
  const H = K.rel;

  T.family({ id: 'found-proofs', part: 'foundations', order: 70, title: 'Proof techniques', blurb: 'Induction, the pigeonhole principle and diagonalisation: the three arguments that the rest of the theory leans on, each one played out on a picture.' });

  const isPrime = (v) => { if (v < 2) return false; for (let d = 2; d * d <= v; d++) if (v % d === 0) return false; return true; };
  const factor = (v) => { for (let d = 2; d * d <= v; d++) if (v % d === 0) return d + ' · ' + v / d; return String(v); };
  const sumTo = (n) => (n * (n + 1)) / 2;
  const stamps = (n) => { for (let b = 0; 5 * b <= n; b++) if ((n - 5 * b) % 3 === 0) return { a: (n - 5 * b) / 3, b }; return null; };

  // each claim: P(n) with a readable check, whether its step can be proved (and from where), and the step's algebra
  const CLAIMS = {
    sum: { label: '1 + 2 + … + n = n(n + 1)/2', from: 1, P: (n) => true, check: (n) => (n <= 4 ? [...Array(n).keys()].map((i) => i + 1).join(' + ') : '1 + … + ' + n) + ' = ' + sumTo(n) + ' = ' + n + '·' + (n + 1) + '/2', step: (k) => 'add ' + (k + 1) + ' to both sides: ' + k + '·' + (k + 1) + '/2 + ' + (k + 1) + ' = ' + (k + 1) + '·' + (k + 2) + '/2', stepOk: () => true },
    odd: { label: '1 + 3 + … + (2n − 1) = n²', from: 1, P: () => true, check: (n) => (n <= 4 ? [...Array(n).keys()].map((i) => 2 * i + 1).join(' + ') : '1 + 3 + … + ' + (2 * n - 1)) + ' = ' + n * n + ' = ' + n + '²', step: (k) => 'add the next odd number ' + (2 * k + 1) + ': ' + k + '² + ' + (2 * k + 1) + ' = ' + (k + 1) + '²', stepOk: () => true },
    pow: { label: '2ⁿ > n²', from: 5, P: (n) => Math.pow(2, n) > n * n, check: (n) => '2^' + n + ' = ' + Math.pow(2, n) + (Math.pow(2, n) > n * n ? ' > ' : ' ≤ ') + n * n + ' = ' + n + '²', step: (k) => '2^' + (k + 1) + ' = 2·2^' + k + ' > 2·' + k + '² ≥ (' + k + ' + 1)², true once k ≥ 3', stepOk: (k) => k >= 3 },
    prime: { label: 'n² + n + 11 is prime', from: 3, P: (n) => isPrime(n * n + n + 11), check: (n) => n + '² + ' + n + ' + 11 = ' + (n * n + n + 11) + (isPrime(n * n + n + 11) ? ', prime' : ' = ' + factor(n * n + n + 11) + ', not prime'), step: () => 'no algebra turns P(k) into P(k + 1): we only checked a number', stepOk: () => false },
    stamps: { label: 'every n ≥ 8 is a sum of 3s and 5s', from: 8, bases: 3, back: 3, P: (n) => !!stamps(n), check: (n) => { const s = stamps(n); return s ? n + ' = ' + [...Array(s.a).fill('3'), ...Array(s.b).fill('5')].join(' + ') : n + ' cannot be made from 3s and 5s'; }, step: (k) => (k + 1) + ' = ' + (k - 2) + ' + 3: take the payment for ' + (k - 2) + ' and add a 3', stepOk: () => true },
    even: { label: 'n² + n is odd', from: 1, P: (n) => (n * n + n) % 2 === 1, check: (n) => n + '² + ' + n + ' = ' + (n * n + n) + ((n * n + n) % 2 ? ', odd' : ', even'), step: (k) => 'if k² + k is odd, (k + 1)² + (k + 1) = (k² + k) + 2(k + 1) is odd too', stepOk: () => true },
  };

  T.topic({
    id: 'induction-dominoes', family: 'found-proofs', order: 10, title: 'Induction: a row of dominoes',
    blurb: 'Prove P(base), and prove that P(k) forces P(k + 1). Then the first domino falls and each knocks over the next. Try a claim whose step breaks, one whose base is false, and one that only looks true.',
    inputs: [
      { id: 'claim', kind: 'choice', label: 'Claim P(n)', def: 'sum', options: Object.entries(CLAIMS).map(([value, c]) => ({ value, label: c.label })) },
      { id: 'from', kind: 'number', label: 'Start at n =', def: 1, min: 0, max: 12 },
    ],
    presets: [
      { label: 'Sum of 1 … n', values: { claim: 'sum', from: 1 } },
      { label: 'Odd numbers add to squares', values: { claim: 'odd', from: 1 } },
      { label: '2ⁿ > n² from n = 5', values: { claim: 'pow', from: 5 } },
      { label: '2ⁿ > n² from n = 1: the step breaks', values: { claim: 'pow', from: 1 } },
      { label: 'n² + n + 11 prime? Many cases are not a proof', values: { claim: 'prime', from: 3 } },
      { label: '3s and 5s: strong induction', values: { claim: 'stamps', from: 8 } },
      { label: 'A good step, a false base', values: { claim: 'even', from: 1 } },
    ],
    counters: [{ id: 'fallen', label: 'dominoes fallen' }, { id: 'checked', label: 'cases checked' }],
    run(inp) {
      const C = CLAIMS[inp.claim], b0 = inp.from, bases = C.bases || 1, back = C.back || 1;
      const narrow = H.narrow();
      const N = 8, per = narrow ? 4 : 8, SP = 74, DW = 20, DH = 62, ROW = 150;
      const ns = [...Array(N).keys()].map((i) => b0 + i);
      const px = (i) => (i % per) * SP, py = (i) => Math.floor(i / per) * ROW;
      const state = {};
      const F2 = new T.Frames(['fallen', 'checked']);
      const scene = (o) => {
        o = o || {};
        const items = [{ key: 'claim', kind: 'text', x: -10, y: -DH - 132, text: 'P(n): ' + C.label, cls: 'big', size: 18 }];
        if (o.check) items.push({ key: 'check', kind: 'text', x: -10, y: -DH - 102, text: o.check, cls: o.ok === false ? 'bad' : o.ok ? 'good' : 'strong', size: 15 });
        ns.forEach((n, i) => {
          const s = state[n];
          const fallen = s === 'fallen';
          items.push({ key: 'dom:' + n, kind: 'cell', x: px(i), y: py(i) + (fallen ? -DW : -DH), w: fallen ? DH : DW, h: fallen ? DW : DH, cls: 'domino' + (fallen ? ' fallen' : s === 'stuck' ? ' stuck' : '') + (o.next === n ? ' next' : ''), text: '', pick: true });
          items.push({ key: 'lbl:' + n, kind: 'text', x: px(i) + DW / 2, y: py(i) + 22, text: String(n), anchor: 'middle', cls: s === 'stuck' ? 'bad' : fallen ? 'good' : 'strong', size: 15 });
          if (i % per === 0) items.push({ key: 'gnd:' + Math.floor(i / per), kind: 'line', x1: -10, y1: py(i) + 1, x2: Math.min(per, N - Math.floor(i / per) * per) * SP - 10, y2: py(i) + 1, audit: 'ignore' });
        });
        for (const [a, c] of o.arrows || []) if (Math.floor(ns.indexOf(a) / per) === Math.floor(ns.indexOf(c) / per)) items.push({ key: 'push:' + a + '>' + c, kind: 'edge', from: 'dom:' + a, to: 'dom:' + c, bend: Math.floor(ns.indexOf(a) / per) === Math.floor(ns.indexOf(c) / per) ? Math.max(30, (c - a) * SP * 0.34) : 0, cls: o.arrowCls || 'hot', audit: 'edge-x' });
        return items;
      };
      F2.add({ items: scene(), say: 'One domino for each n from ' + b0 + ' on (the row goes on for ever; we show ' + N + '). Domino n falls when P(n) is proved. Induction needs two things: the first domino falls (the base), and any fallen domino knocks over the next (the step).', hl: { def: ['0'] } });
      // base cases
      let failAt = null;
      for (let b = b0; b < b0 + bases; b++) {
        const ok = C.P(b);
        F2.count('checked');
        state[b] = ok ? 'fallen' : 'stuck';
        if (ok) F2.count('fallen');
        F2.add({ items: scene({ check: 'P(' + b + '): ' + C.check(b), ok }), say: 'Base case n = ' + b + ': ' + C.check(b) + '. ' + (ok ? 'True, so domino ' + b + ' falls.' : 'False! Domino ' + b + ' does not fall.'), hl: { def: ['1'] }, meta: {} });
        if (!ok) { failAt = b; break; }
      }
      if (failAt !== null) {
        const good = C.stepOk(b0);
        const pairs = ns.slice(0, -1).map((n, i) => [n, ns[i + 1]]);
        F2.add({ items: scene({ check: 'step: ' + C.step(b0), ok: good, arrows: good ? pairs : [], arrowCls: 'soft' }), say: good ? 'The step is fine: ' + C.step(b0) + '. Every domino would knock over the next, but the first one never falls, so nothing does.' : 'Without the base, nothing starts. The claim is false at n = ' + failAt + '.', hl: { def: ['2'] } });
        F2.add({ items: scene({ check: 'base fails at n = ' + failAt, ok: false }), say: 'No proof: a correct step without a true base proves nothing. (Indeed ' + (inp.claim === 'even' ? 'n² + n = n(n + 1) is always even, so P(n) is false for every n.' : 'P(' + failAt + ') is false.') + ')', hl: { def: ['1', '2'] }, mark: 'base fails' });
        return out(F2, C, b0, bases);
      }
      for (let k = b0 + bases - 1; k < ns[N - 1]; k++) {
        const n = k + 1;
        const ok = C.P(n), provable = C.stepOk(k) && ok;
        const src = n - back;
        F2.add({ items: scene({ check: 'step: P(' + (back > 1 ? src : k) + ') ⇒ P(' + n + ')?', next: n, arrows: [[src, n]] }), say: 'Step: ' + (C.stepOk(k) ? C.step(k) + '.' : 'can P(' + k + ') be turned into P(' + n + ')? ' + C.step(k) + '.') + (back > 1 ? ' This uses P(' + src + '), three back: strong induction may lean on any earlier domino.' : ''), hl: { def: ['2'] }, meta: { next: n, falls: ok, first: k === b0 + bases - 1, breaks: !ok } });
        F2.count('checked');
        state[n] = ok ? 'fallen' : 'stuck';
        if (ok) F2.count('fallen');
        F2.add({ items: scene({ check: 'P(' + n + '): ' + C.check(n), ok, arrows: [[src, n]], arrowCls: ok ? 'good' : 'bad' }), say: ok ? (provable ? 'Domino ' + n + ' falls: ' + C.check(n) + '.' : 'P(' + n + ') happens to hold (' + C.check(n) + '), but only because we checked it; nothing proved it from P(' + k + ').') : 'Domino ' + n + ' stays up: ' + C.check(n) + '. ' + (C.stepOk(k) ? '' : 'The step from ' + k + ' to ' + n + ' was never valid' + (inp.claim === 'pow' ? ' (it needs k ≥ 3)' : '') + '.'), hl: { def: [ok ? '1' : '2'] } });
        if (!ok) {
          F2.add({ items: scene({ check: 'P(' + n + ') is false', ok: false }), say: inp.claim === 'pow' ? 'The base held, but the step only works from k = 3 on, and P(2) and P(3) are false. Start at 5 instead and every domino falls.' : inp.claim === 'prime' ? 'P held for n = ' + b0 + ' to ' + (n - 1) + ', yet fails at ' + n + '. Checking many cases is evidence, never a proof; the step is what does the work.' : 'The claim breaks at n = ' + n + '.', hl: { def: ['2'] }, mark: 'step fails' });
          return out(F2, C, b0, bases);
        }
      }
      F2.add({ items: scene({ check: 'P(n) holds for every n ≥ ' + b0, ok: true }), say: 'Every domino shown has fallen, and the step does not stop at the edge of the picture: it holds for every k ≥ ' + (b0 + bases - 1) + ', so P(n) is true for every n ≥ ' + b0 + '.', hl: { def: ['3'] }, mark: 'proved' });
      return out(F2, C, b0, bases);
      function out(fr, c, b, nb) {
        return { frames: fr.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Induction', text: ['P(n): ' + c.label, 'base: P(' + b + ')' + (nb > 1 ? ' … P(' + (b + nb - 1) + ')' : '') + ' is true', 'step: P(k)' + (c.back ? ' (or earlier cases)' : '') + ' ⇒ P(k + 1)', 'so P(n) for every n ≥ ' + b].join('\n') }] } };
      }
    },
    predict: [
      { at: (f) => f.meta && f.meta.first, pick: 'option', options: ['Yes', 'No'], ask: (fr, i) => 'Will domino ' + fr[i].meta.next + ' fall?', answer: (fr, i) => (fr[i].meta.falls ? 'Yes' : 'No'), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.breaks && !f.meta.first, pick: 'option', options: ['Yes', 'No'], ask: (fr, i) => 'Will domino ' + fr[i].meta.next + ' fall?', answer: () => 'No', explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'The step P(k) ⇒ P(k + 1) is proved, but P(base) is false. What follows?', options: ['P(n) for all n', 'Nothing at all about P', 'P(n) is false for all n'], answer: 1, why: 'No domino falls. (P might still be true from some other start, or false everywhere.)' },
      { q: 'n² + n + 11 is prime for n = 0, 1, …, 9. Is that a proof for all n?', options: ['Yes', 'No: at n = 10 it is 121 = 11 · 11'], answer: 1, why: 'Checked cases are not a step. A proof must carry P(k) to P(k + 1) for every k.' },
      { q: 'Why does the 3s-and-5s claim need three base cases?', options: ['Because 3 is odd', 'The step for n uses n − 3, so the first three values must be done by hand', 'It does not'], answer: 1, why: 'P(n) leans on P(n − 3); 8, 9 and 10 have nothing three back inside the claim.' },
      { q: 'For 2ⁿ > n², the step works when k ≥ 3. Which start gives a proof?', options: ['n = 1', 'n = 2', 'n = 5', 'n = 3'], answer: 2, why: 'The base must hold and the step must work from there: P(5) is true (32 > 25), P(3) and P(4) are false.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Pigeonhole
  // ---------------------------------------------------------------------------------------------------
  const MONTHS = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];
  const SCEN = {
    mod: { label: 'remainders: numbers into holes mod k' },
    pairs: { label: 'neighbours: k + 1 numbers from 1 … 2k' },
    months: { label: 'birth months: 13 people' },
    general: { label: 'many in one hole: n items, k holes' },
  };
  T.topic({
    id: 'pigeonhole', family: 'found-proofs', order: 20, title: 'The pigeonhole principle',
    blurb: 'Put more pigeons than holes into holes and some hole gets two. Drop them in one at a time and watch the collision become unavoidable.',
    inputs: [
      { id: 'scen', kind: 'choice', label: 'Situation', def: 'mod', options: Object.entries(SCEN).map(([value, s]) => ({ value, label: s.label })) },
      { id: 'items', kind: 'list', label: 'Numbers', def: ['17', '4', '9', '22', '30'], min: 1, max: 9, check: (v) => (v.some((x) => !/^\d+$/.test(x)) ? 'Numbers: whole numbers like 7, 12' : null) },
      { id: 'k', kind: 'number', label: 'Holes k', def: 4, min: 2, max: 6 },
    ],
    check: (inp) => (inp.scen === 'pairs' && inp.items.some((x) => +x < 1 || +x > 2 * inp.k) ? 'Numbers: for neighbours, pick numbers from 1 to 2k = ' + 2 * inp.k : inp.scen === 'general' && inp.items.length < inp.k ? 'Numbers: use at least k items' : null),
    presets: [
      { label: '5 numbers mod 4', values: { scen: 'mod', items: ['17', '4', '9', '22', '30'], k: 4 } },
      { label: '4 numbers mod 4: no promise', values: { scen: 'mod', items: ['8', '13', '6', '3'], k: 4 } },
      { label: '5 numbers from 1 … 8: two are neighbours', values: { scen: 'pairs', items: ['2', '5', '8', '3', '6'], k: 4 } },
      { label: '13 birth months', values: { scen: 'months', items: ['1'], k: 2 } },
      { label: '9 items in 4 holes: one holds 3', values: { scen: 'general', items: ['1', '2', '3', '4', '5', '6', '7', '8', '9'], k: 4 } },
    ],
    counters: [{ id: 'placed', label: 'pigeons placed' }, { id: 'most', label: 'most in one hole' }],
    run(inp) {
      const sc = inp.scen;
      let holes, items, holeOf, names, why;
      if (sc === 'months') { holes = MONTHS; items = [...Array(13).keys()].map((i) => 'p' + (i + 1)); holeOf = (x, i) => MONTHS[i < 12 ? i : 2]; why = 'each person goes to their birth month'; }
      else if (sc === 'pairs') { holes = [...Array(inp.k).keys()].map((i) => (2 * i + 1) + ',' + (2 * i + 2)); items = inp.items; holeOf = (x) => holes[Math.floor((+x - 1) / 2)]; why = 'each number goes to the pair {2i − 1, 2i} it belongs to'; }
      else if (sc === 'general') { holes = [...Array(inp.k).keys()].map((i) => 'h' + (i + 1)); items = inp.items.map((x, i) => 'x' + (i + 1)); holeOf = (x, i) => holes[i % inp.k]; why = 'the items are spread as evenly as possible, round and round'; }
      else { holes = [...Array(inp.k).keys()].map(String); items = inp.items; holeOf = (x) => String(+x % inp.k); why = 'each number goes to the hole of its remainder mod ' + inp.k; }
      names = items;
      const narrow = H.narrow();
      const per = narrow ? 6 : 12;
      const HW = 58, PW = 48, PH = 28;
      const cnt = {};
      items.forEach((x, i) => { const h = holeOf(x, i); cnt[h] = (cnt[h] || 0) + 1; });
      const maxStack = Math.max(2, ...Object.values(cnt));
      const HH = 34 + maxStack * (PH + 6) + 6;
      const hx = (j) => (j % per) * (HW + 10), hy = (j) => Math.floor(j / per) * (HH + 26);
      const qPer = narrow ? 6 : 9;
      const qy = -110 - Math.floor((items.length - 1) / qPer) * 40;
      const where = {};
      const F2 = new T.Frames(['placed', 'most']);
      const stackOf = (h) => Object.keys(where).filter((x) => where[x] === h);
      const scene = (o) => {
        o = o || {};
        const items2 = [];
        holes.forEach((h, j) => items2.push({ key: 'hole:' + h, kind: 'region', x: hx(j), y: hy(j), w: HW, h: HH, text: sc === 'pairs' ? '{' + h + '}' : sc === 'mod' ? '≡ ' + h : h, textPos: 'top', cls: 'r' + (j % 6) + ((o.hotHole || []).includes(h) ? ' hot' : ''), rx: 10, pick: true }));
        items.forEach((x, i) => {
          const h = where[x];
          let p;
          if (h === undefined) p = { x: (i % qPer) * (PW + 6), y: qy + Math.floor(i / qPer) * 40 };
          else { const j = holes.indexOf(h), s = stackOf(h).indexOf(x); p = { x: hx(j) + (HW - PW) / 2, y: hy(j) + HH - 6 - (s + 1) * (PH + 6) }; }
          items2.push({ key: 'pg:' + x, kind: 'cell', x: p.x, y: p.y, w: PW, h: PH, text: x, cls: 'mono pigeon' + ((o.bad || []).includes(x) ? ' bad' : ''), size: 14 });
        });
        return items2;
      };
      F2.add({ items: scene(), say: items.length + ' pigeon' + (items.length === 1 ? '' : 's') + ' and ' + holes.length + ' holes: ' + why + '. ' + (items.length > holes.length ? 'There are more pigeons than holes, so some hole must end up with two.' : 'There are not more pigeons than holes, so nothing is promised.'), hl: { def: ['0'] } });
      let collided = false;
      items.forEach((x, i) => {
        const h = holeOf(x, i);
        const before = stackOf(h);
        where[x] = h;
        F2.count('placed').set('most', Math.max(...holes.map((hh) => stackOf(hh).length)));
        const clash = before.length > 0 && !collided && sc !== 'general';
        const nxt = items[i + 1];
        const meta = nxt !== undefined ? { nextHole: 'hole:' + holeOf(nxt, i + 1), nextClash: stackOf(holeOf(nxt, i + 1)).length > 0 && !collided && sc !== 'general' } : {};
        if (clash) collided = true;
        F2.add({ items: scene(clash ? { bad: [x, before[0]], hotHole: [h] } : {}), say: clash ? x + ' lands in ' + (sc === 'mod' ? 'remainder ' + h : sc === 'pairs' ? '{' + h + '}' : h) + ', where ' + before[0] + ' already is. ' + (sc === 'mod' ? before[0] + ' and ' + x + ' leave the same remainder, so their difference ' + Math.abs(+x - +before[0]) + ' is divisible by ' + inp.k + '.' : sc === 'pairs' ? before[0] + ' and ' + x + ' are neighbours.' : sc === 'months' ? 'Even with the first twelve people in twelve different months, the thirteenth has to share.' : '') : x + ' goes into ' + (sc === 'mod' ? 'remainder ' + h + ' (' + x + ' = ' + Math.floor(+x / inp.k) + '·' + inp.k + ' + ' + h + ')' : sc === 'pairs' ? '{' + h + '}' : h) + '.', hl: { def: ['1'] }, meta });
      });
      const most = Math.max(...holes.map((h) => stackOf(h).length));
      const full = holes.filter((h) => stackOf(h).length === most);
      if (sc === 'general') F2.add({ items: scene({ hotHole: full }), say: items.length + ' items in ' + holes.length + ' holes, spread as evenly as possible, and still some hole holds ' + most + ' = ⌈' + items.length + '/' + holes.length + '⌉. If every hole held at most ' + (most - 1) + ', there would be at most ' + (most - 1) * holes.length + ' items.', hl: { def: ['2'] }, mark: 'bound' });
      else if (!collided) F2.add({ items: scene(), say: 'No two share a hole. With ' + items.length + ' pigeons and ' + holes.length + ' holes this can happen; the principle only promises a collision when there are more pigeons than holes.', hl: { def: ['0'] }, mark: 'no promise' });
      else F2.add({ items: scene({ hotHole: full.filter((h) => stackOf(h).length > 1) }), say: 'A collision, as promised. The principle never says which hole, only that one must hold two: ' + items.length + ' > ' + holes.length + '.', hl: { def: ['0', '1'] }, mark: 'collision' });
      void names;
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The pigeonhole principle', text: ['n pigeons, k holes, n > k ⇒ some hole holds ≥ 2', 'the map: ' + why, 'in general: some hole holds ≥ ⌈n / k⌉'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.nextClash, once: true, pick: 'item', ask: 'Which hole will the next pigeon land in? Click it.', answer: (fr, i) => fr[i].meta.nextHole, explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr, inp) => i === 0 && inp.scen === 'general', pick: 'option', options: ['1', '2', '3', '4', '5'], ask: 'Spread as evenly as possible, how many items will the fullest hole hold?', answer: (fr, i, inp) => String(Math.ceil(inp.items.length / inp.k)), explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr, inp) => i === 0 && inp.scen === 'mod' && inp.items.length <= inp.k, pick: 'option', options: ['Yes', 'No'], ask: 'Is a collision guaranteed here?', answer: () => 'No', explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'How many people guarantee two with the same birthday (366 possible days)?', options: ['183', '365', '366', '367'], answer: 3, why: '367 people, 366 days: one day must be shared. With 366 they could all differ.' },
      { q: 'Why do two of any k + 1 numbers from 1 … 2k differ by exactly 1?', options: ['Luck', 'The k holes {1, 2}, {3, 4}, …, {2k − 1, 2k} receive k + 1 numbers, so one pair is hit twice', 'Because k + 1 is odd'], answer: 1, why: 'Two numbers in the same hole {2i − 1, 2i} are neighbours.' },
      { q: '25 items go into 6 holes. What is the least the fullest hole can hold?', options: ['4', '5', '6', '25'], answer: 1, why: '⌈25/6⌉ = 5: with at most 4 per hole there would be at most 24 items.' },
      { q: 'A DFA has 5 states and reads a string of length 5. What must happen?', options: ['It accepts', 'Some state is visited twice: 6 states are visited counting the start', 'It gets stuck'], answer: 1, why: 'Six visits, five states: this is the heart of the pumping lemma.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Diagonalisation as a recipe
  // ---------------------------------------------------------------------------------------------------
  const FNS = {
    sq: { label: 'n²', f: (n) => n * n }, dbl: { label: '2n', f: (n) => 2 * n }, inc: { label: 'n + 1', f: (n) => n + 1 },
    pow: { label: '2ⁿ', f: (n) => Math.pow(2, n) }, fact: { label: 'n!', f: (n) => { let r = 1; for (let i = 2; i <= n; i++) r *= i; return r; } },
    seven: { label: '7', f: () => 7 }, id: { label: 'n', f: (n) => n }, zero: { label: '0', f: () => 0 }, tri: { label: 'n(n+1)/2', f: (n) => (n * (n + 1)) / 2 },
  };
  const CHANGES = {
    plus: { label: 'add 1', g: (v) => v + 1, text: 'fₙ(n) + 1' },
    times: { label: 'double (a broken recipe)', g: (v) => 2 * v, text: '2 · fₙ(n)' },
  };
  T.topic({
    id: 'diagonal-functions', family: 'found-proofs', order: 30, title: 'Diagonalisation: beat any list',
    blurb: 'List functions f₀, f₁, f₂, … from numbers to numbers. Define g(n) = fₙ(n) + 1: it disagrees with fₙ at n, so it is on no list. The same move later proves the halting problem undecidable.',
    inputs: [
      { id: 'fs', kind: 'list', label: 'The list (from: ' + Object.keys(FNS).join(', ') + ')', def: ['sq', 'inc', 'seven', 'pow', 'id'], min: 3, max: 6, check: (v) => { const bad = v.find((x) => !FNS[x]); return bad !== undefined ? 'The list: ' + bad + ' is not one of ' + Object.keys(FNS).join(', ') : null; } },
      { id: 'change', kind: 'choice', label: 'Change the diagonal by', def: 'plus', options: Object.entries(CHANGES).map(([value, c]) => ({ value, label: c.label })) },
    ],
    presets: [
      { label: 'Five functions, add 1', values: { fs: ['sq', 'inc', 'seven', 'pow', 'id'], change: 'plus' } },
      { label: 'Fast growers: add 1 still wins', values: { fs: ['fact', 'pow', 'sq', 'tri'], change: 'plus' } },
      { label: 'Doubling breaks on 0', values: { fs: ['zero', 'inc', 'sq', 'dbl'], change: 'times' } },
      { label: 'Doubling happens to work here', values: { fs: ['seven', 'inc', 'sq', 'pow'], change: 'times' } },
    ],
    counters: [{ id: 'diag', label: 'diagonal entries' }, { id: 'beaten', label: 'functions beaten' }],
    run(inp) {
      const fs = inp.fs.map((k) => FNS[k]), ch = CHANGES[inp.change];
      const n = fs.length, cols = n + 1;
      const vals = fs.map((f) => [...Array(cols).keys()].map(f.f));
      const g = vals.map((r, i) => ch.g(r[i]));
      const F2 = new T.Frames(['diag', 'beaten']);
      const CW = 50;
      const tbl = (o) => {
        o = o || {};
        return K.table.draw({ rows: vals.map((r) => r.map(String).concat(['⋯'])), rowHead: fs.map((f, i) => 'f' + i + '(n) = ' + f.label), colHead: [...Array(cols).keys()].map((c) => 'n=' + c).concat(['']), cw: CW, ch: 38, mono: true, size: 16, prefix: 'df',
          cls: (r, c) => (c === cols ? 'elide' : (o.bad || []).includes(r) && r === c ? 'bad' : (o.good || []).includes(r) && r === c ? 'good' : o.hot === r && r === c ? 'hot' : r === c ? 'mark' : '') });
      };
      const t0 = tbl();
      const gy = t0.box.y + t0.box.h + 24;
      const gRow = (k, o) => {
        o = o || {};
        const items = [{ key: 'g:lbl', kind: 'text', x: t0.cellBox(0, 0).x - 12, y: gy + 25, text: 'g(n) = ' + ch.text, anchor: 'end', cls: 'strong', size: 15 }];
        for (let i = 0; i < k; i++) items.push({ key: 'g:' + i, kind: 'cell', x: t0.cellBox(0, i).x, y: gy, w: CW, h: 38, text: String(g[i]), cls: 'mono ' + ((o.bad || []).includes(i) ? 'bad' : 'good'), size: 16, enter: 'from', src: 'df:' + i + ',' + i });
        return items;
      };
      F2.add({ items: tbl().items.concat(gRow(0)), say: 'Here is a list of functions from N to N, one per row; row i shows fᵢ(0), fᵢ(1), … We will build a function g that is not anywhere on the list, by looking only at the diagonal.', hl: { def: ['0'] } });
      for (let i = 0; i < n; i++) {
        F2.count('diag');
        F2.add({ items: tbl({ hot: i }).items.concat(gRow(i + 1)), say: 'f' + i + '(' + i + ') = ' + vals[i][i] + ', so g(' + i + ') = ' + ch.text.replace('fₙ(n)', String(vals[i][i])) + ' = ' + g[i] + '.' + (g[i] === vals[i][i] ? ' That is the same value: the change did nothing here.' : ''), hl: { def: ['1'] }, meta: i === 1 ? { ask: String(g[1]), opts: [...new Set([vals[1][1], g[1], vals[1][1] + 2, vals[1][1] * 3 + 1].map(String))].sort((a, b) => a - b) } : {} });
      }
      const same = g.map((v, i) => v === vals[i][i]);
      const broken = same.some(Boolean);
      F2.set('beaten', same.filter((x) => !x).length);
      F2.add({ items: tbl({ good: [...Array(n).keys()].filter((i) => !same[i]), bad: [...Array(n).keys()].filter((i) => same[i]) }).items.concat(gRow(n, { bad: [...Array(n).keys()].filter((i) => same[i]) })), say: broken ? 'The recipe failed at n = ' + same.indexOf(true) + ': doubling leaves 0 as 0, so g agrees with f' + same.indexOf(true) + ' there, and g might be f' + same.indexOf(true) + ' itself. The change must alter every value it touches; "add 1" always does.' : 'g differs from fᵢ at n = i for every row, so g is not on the list. ' + (inp.change === 'times' ? 'Doubling worked only because no diagonal entry was 0; on another list it would fail.' : 'Every list of functions misses one: the functions from N to N are uncountable.'), hl: { def: [broken ? '1' : '2'] }, mark: broken ? 'broken' : 'beaten' });
      F2.add({ items: tbl({ good: [...Array(n).keys()].filter((i) => !same[i]), bad: [...Array(n).keys()].filter((i) => same[i]) }).items.concat(gRow(n, { bad: [...Array(n).keys()].filter((i) => same[i]) })), say: 'The same move, with programs as the list and "run program n on input n, then do the opposite" as g, shows that no program can decide whether programs halt: g would have to be on the list and cannot be.', hl: { def: ['3'] } });
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'The diagonal recipe', text: ['a list f₀, f₁, f₂, … of functions N → N', 'g(n) = ' + ch.text, 'g(i) ≠ fᵢ(i), so g ≠ fᵢ for every i', 'with programs: the halting problem'].join('\n') }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.ask, pick: 'option', options: (fr, i) => fr[i + 1].meta.opts, ask: 'What will g(1) be?', answer: (fr, i) => fr[i + 1].meta.ask, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'g(n) = fₙ(n) + 1. Why can g not be f₄?', options: ['f₄ grows faster', 'g(4) = f₄(4) + 1 ≠ f₄(4)', 'g is not a function'], answer: 1, why: 'Two functions that disagree at 4 are different.' },
      { q: 'Why is "double the diagonal" a broken recipe?', options: ['Doubling is too slow', 'If fₙ(n) = 0 then 2 · 0 = 0 and g agrees with fₙ at n', 'Doubling is not computable'], answer: 1, why: 'The change must never leave a value unchanged.' },
      { q: 'What does the argument prove about the set of all functions N → N?', options: ['It is countable', 'It is uncountable: no list contains them all', 'It is finite'], answer: 1, why: 'Every list misses its own diagonal function.' },
    ],
  });
})();
