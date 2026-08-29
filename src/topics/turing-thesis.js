// The Church–Turing thesis as a gallery: one function computed in five models side by side, and the
// simulations that turn each model into the next, so that all of them compute the same class.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'church-turing', part: 'turing', order: 70, title: 'The Church–Turing thesis', blurb: 'Tapes, registers, counters, recursive definitions, λ-terms: every reasonable model of computation turns out to compute the same functions. The thesis says that this class is what "computable" means.' });

  const RAM_DOUBLE = 'loop: jz r1 done\n  dec r1\n  inc r0\n  inc r0\n  jmp loop\ndone: halt';
  const CTR_ADD = 'm: dec B m1 h\nm1: inc A m\nh: halt';
  const FUNS = {
    add: {
      name: (a) => 'add(' + a.join(', ') + ')', n: 2, val: (a) => a[0] + a[1],
      tm: (a) => { const r = T.tm.run(T.tmLib.get('unary-add'), '1'.repeat(a[0]) + '+' + '1'.repeat(a[1]), { trace: false }); return { v: r.output.length, cost: r.steps + ' steps' }; },
      ram: (a) => { const r = T.ram.run(T.ram.lib.find((x) => x.id === 'add').text, [0, a[0], a[1]], { trace: false }); return { v: r.output, cost: r.steps + ' instructions' }; },
      ctr: (a) => { const r = T.counter.run(CTR_ADD, { A: a[0], B: a[1] }, { trace: false }); return { v: r.counters.A, cost: r.steps + ' moves' }; },
      rec: (a) => { const r = T.rec.evaluate('add', a, T.rec.library(), { trace: false }); return { v: r.value, cost: r.calls + ' calls' }; },
      lam: (a) => { const r = T.lambda.normalize('PLUS ' + a[0] + ' ' + a[1], { trace: false }); return { v: T.lambda.unchurch(r.term), cost: r.steps + ' β-steps' }; },
      code: { tm: '1ˣ+1ʸ: fill the +, drop a 1', ram: 'move r1, then r2, into r0', ctr: 'pour B into A', rec: 'R(P(1,1), C(S; P(3,3)))', lam: 'λm n f x. m f (n f x)' },
    },
    double: {
      name: (a) => 'double(' + a[0] + ')', n: 1, val: (a) => 2 * a[0],
      tm: (a) => { const r = T.tm.run(T.tmLib.get('unary-double'), '1'.repeat(a[0]), { trace: false }); return { v: r.output.length, cost: r.steps + ' steps' }; },
      ram: (a) => { const r = T.ram.run(RAM_DOUBLE, [0, a[0]], { trace: false }); return { v: r.output, cost: r.steps + ' instructions' }; },
      ctr: (a) => { const r = T.counter.run(T.counter.lib.find((x) => x.id === 'double').text, { A: a[0], B: 0 }, { trace: false }); return { v: r.counters.A, cost: r.steps + ' moves' }; },
      rec: (a) => { const r = T.rec.evaluate('double', a, T.rec.library(), { trace: false }); return { v: r.value, cost: r.calls + ' calls' }; },
      lam: (a) => { const r = T.lambda.normalize('PLUS ' + a[0] + ' ' + a[0], { trace: false }); return { v: T.lambda.unchurch(r.term), cost: r.steps + ' β-steps' }; },
      code: { tm: 'cross off a 1, write two', ram: 'take one from r1, add two to r0', ctr: 'A to B two at a time, then back', rec: 'C(add; P(1,1), P(1,1))', lam: 'λn. PLUS n n' },
    },
  };
  const MODELS = [
    { id: 'tm', title: 'Turing machine', how: 'a tape, a head and finitely many states' },
    { id: 'ram', title: 'Register machine', how: 'registers of any size: inc, dec, jump if zero' },
    { id: 'ctr', title: 'Two counters', how: 'two piles of pebbles and a finite program' },
    { id: 'rec', title: 'μ-recursive', how: 'Z, S, projections, composition, recursion and μ' },
    { id: 'lam', title: 'λ-calculus', how: 'substitution, nothing else' },
  ];
  // the simulations around the ring, each model's work done by the next
  const LINKS = [
    ['tm', 'ram', 'A register machine keeps the tape as two numbers, the part left of the head and the part from the head on, written in base |Γ|; moving the head is multiplying and dividing by |Γ|. And a Turing machine keeps registers on its tape in unary, separated by #.'],
    ['ram', 'ctr', 'Any number of registers r₁, r₂, … fit into one counter as 2^r₁·3^r₂·5^r₃…; incrementing r₂ is multiplying by 3, testing r₂ = 0 is testing divisibility by 3, each done with a second counter as scratch. Counters are registers, so the way back is free.'],
    ['ctr', 'rec', 'A counter machine\'s configuration (state, A, B) is a triple of numbers, and one step is a primitive recursive function of it. Running until the halting state is a μ-search for the first step count that reaches it. Conversely, a register machine can evaluate any μ-recursive definition with a stack kept in registers.'],
    ['rec', 'lam', 'Church numerals give Z, S and projections at once; composition is application; primitive recursion becomes iteration (a numeral applies a function n times); μ becomes a loop built with a fixed-point combinator such as Y. And a λ-term can be coded as a number, its normal-order reduction as a μ-recursive function.'],
    ['lam', 'tm', 'A Turing machine can store a λ-term as a string and perform leftmost-outermost β-steps by string rewriting; a λ-term can encode a machine\'s configuration and one step of it, iterated with a fixed-point combinator. So the ring closes.'],
  ];
  T.topic({
    id: 'tm-church-turing', family: 'church-turing', order: 10, title: 'Many models, one class',
    blurb: 'One function, five models: a Turing machine, a register machine, two counters, μ-recursion and the λ-calculus all give the same answer. Then follow the simulations round the ring: each model can do everything the next can.',
    inputs: [
      { id: 'f', kind: 'choice', label: 'Function', def: 'add', options: [{ value: 'add', label: 'add(x, y)' }, { value: 'double', label: 'double(x)' }] },
      { id: 'a', kind: 'text', label: 'Arguments', def: '2, 3', check: (v, inp) => { const a = String(v).split(/[\s,]+/).filter(Boolean).map(Number); if (a.some((x) => !Number.isInteger(x) || x < 0 || x > 5)) return 'Arguments: whole numbers from 0 to 5'; if (a.length !== FUNS[inp.f].n) return 'Arguments: this function takes ' + FUNS[inp.f].n; return null; } },
    ],
    presets: [
      { label: 'add(2, 3)', values: { f: 'add', a: '2, 3' } },
      { label: 'add(0, 0)', values: { f: 'add', a: '0, 0' } },
      { label: 'double(3)', values: { f: 'double', a: '3' } },
    ],
    counters: [{ id: 'models', label: 'models run' }, { id: 'links', label: 'simulations shown' }],
    run(inp) {
      const X = FUNS[inp.f];
      const a = String(inp.a).split(/[\s,]+/).filter(Boolean).map(Number);
      const want = X.val(a);
      const res = {};
      for (const m of MODELS) res[m.id] = X[m.id](a);
      const R = 230, CHd = 104;
      const CWd = Math.max(240, ...MODELS.map((m) => Math.max(...[m.title, X.code[m.id], X.name(a) + ' = ' + res[m.id].v + ' · ' + res[m.id].cost].map((l) => T.geom.textWidth(l, 15, { bold: true }))) + 30));
      const at = (i) => { const t = -Math.PI / 2 + (2 * Math.PI * i) / MODELS.length; return { x: Math.cos(t) * R * 1.3, y: Math.sin(t) * R }; };
      const F = new T.Frames(['models', 'links']);
      const scene = (done, hotCard, hotLink, all) => {
        const items = [];
        MODELS.forEach((m, i) => {
          const p = at(i), r = res[m.id];
          const lines = [m.title, X.code[m.id], done.has(m.id) ? X.name(a) + ' = ' + r.v + ' · ' + r.cost : '…'];
          items.push({ key: 'card' + m.id, kind: 'state', x: p.x, y: p.y, w: CWd, h: CHd, rx: 14, lines, size: 15, cls: 'tu-card' + (hotCard === m.id ? ' hot' : all ? ' good' : ''), pick: true });
        });
        LINKS.forEach(([x, y], k) => items.push({ key: 'link' + k, kind: 'edge', from: 'card' + x, to: 'card' + y, bend: 0, head: true, cls: k === hotLink ? 'hot' : all ? 'good' : 'soft' }));
        items.push({ key: 'mid1', kind: 'text', x: 0, y: -8, text: all ? 'one class:' : X.name(a), anchor: 'middle', cls: 'strong', size: 18 });
        items.push({ key: 'mid2', kind: 'text', x: 0, y: 18, text: all ? 'the computable functions' : 'should be ' + want, anchor: 'middle', cls: all ? 'good' : 'tu-small' });
        return items;
      };
      const done = new Set();
      F.add({ items: scene(done), say: 'Five models of computation, each with a program for ' + X.name(a) + '. They look nothing alike. Run each one.' });
      MODELS.forEach((m) => {
        done.add(m.id);
        F.count('models');
        F.add({ items: scene(done, m.id), say: m.title + ' (' + m.how + '): ' + X.name(a) + ' = ' + res[m.id].v + ', in ' + res[m.id].cost + '.', meta: { model: m.id } });
      });
      F.add({ items: scene(done), say: 'All five say ' + want + '. The costs differ wildly, the answers do not. That is no accident: each model can simulate the next one round the ring.' });
      LINKS.forEach(([x, y], k) => { F.count('links'); F.add({ items: scene(done, null, k), say: MODELS.find((m) => m.id === x).title + ' and ' + MODELS.find((m) => m.id === y).title.toLowerCase() + ': ' + LINKS[k][2] }); });
      F.add({ items: scene(done, null, -1, true), say: 'Round the ring, every model simulates every other, so they compute exactly the same functions. The Church–Turing thesis goes one step further: any procedure a person could carry out mechanically, by rules, with paper enough, computes a function in this class. It is a claim about the world, not a theorem, and no reasonable model found so far has broken it.', mark: 'one class' });
      const fr = F.list;
      const li = fr.findIndex((f) => f.meta && f.meta.model === 'lam');
      if (li > 0) fr[li - 1].predict = { ask: 'The λ-calculus is last. What will it give for ' + X.name(a) + '?', options: [...new Set([want, want + 1, Math.max(0, want - 1), want * 2])].map(String).sort((p, q) => p - q), answer: String(want), explain: 'Every model computes the same function: ' + want + '.', pick: 'option' };
      return { frames: fr, def: { sections: [
        { id: 'models', kind: 'table', title: 'The models', colHead: ['model', 'what it has', 'result'], rows: MODELS.map((m) => [m.title, m.how, String(res[m.id].v)]) },
        { id: 'thesis', kind: 'text', title: 'The thesis', text: 'Every effectively calculable function is computable by a Turing machine. Evidence: every model ever proposed (these five, Post systems, cellular automata, programming languages) computes the same class. It cannot be proved, since "effectively calculable" is an informal idea; it could only be refuted by a mechanical procedure no machine can follow.' },
      ] } };
    },
    quiz: [
      { q: 'Why is the Church–Turing thesis not a theorem?', options: ['Nobody has tried', 'It links an informal idea, an effective procedure, to a formal one, so there is nothing formal to prove it from', 'It is false', 'It is a theorem'], answer: 1, why: 'Equivalences between formal models are theorems; the thesis is the claim that they capture the informal notion.' },
      { q: 'The five models take very different numbers of steps. Does that weaken the thesis?', options: ['Yes', 'No: the thesis is about what can be computed, not how fast', 'Only for counters', 'Only for λ'], answer: 1, why: 'Speed differs by simulation overheads; the set of computable functions does not. (How fast is the subject of complexity theory.)' },
      { q: 'What would refute the thesis?', options: ['A faster computer', 'A procedure that people could follow mechanically but that computes a function no Turing machine can', 'A new programming language', 'A bigger tape'], answer: 1, why: 'Every proposal so far, including quantum computers, computes the same functions (perhaps faster).' },
      { q: 'Which of these is not as powerful as the others?', options: ['A machine with two counters', 'A machine with one counter', 'The λ-calculus', 'μ-recursive functions'], answer: 1, why: 'One counter is not enough (its halting problem is decidable); two are.' },
    ],
  });
})();
