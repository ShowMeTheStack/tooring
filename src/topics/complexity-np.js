// NP: a certificate checked one test at a time by a polynomial verifier; nondeterministic time as a tree
// of guesses (depth is the time, width the work a deterministic simulation pays); P versus NP as two
// pictures of the same classes, one collapsing into the other; and co-NP, where the short certificate is
// for the answer no.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'cx-np', part: 'complexity', order: 30, title: 'NP', blurb: 'Problems whose yes-answers come with a short proof that can be checked fast, the tree of guesses behind them, and the question whether checking is really easier than finding.' });

  // ---------------------------------------------------------------------------------------------------------
  // shared bits
  const ledger = (P, lines, x, y) => lines.map((l, i) => ({ key: P + ':' + i, kind: 'text', x, y: y + i * 26, text: (l.ok ? '✓ ' : '✗ ') + l.say, anchor: 'start', size: 14, cls: l.ok ? 'good' : 'bad' }));
  const hexPos = (n, R) => Array.from({ length: n }, (_, i) => { const a = -Math.PI / 2 + (2 * Math.PI * i) / n; return { x: Math.round(Math.cos(a) * R), y: Math.round(Math.sin(a) * R) }; });
  const ekey = (a, b) => (a < b ? a + '|' + b : b + '|' + a);

  // ---------------------------------------------------------------------------------------------------------
  // 1. checking a certificate
  const INST = {
    clique: { title: 'CLIQUE', n: 6, edges: [[0, 1], [0, 3], [0, 5], [1, 2], [1, 4], [1, 5], [2, 3], [2, 4], [2, 5], [3, 4], [4, 5]], k: 4, ask: 'Does this graph have a clique of 4 vertices, every two of them joined?' },
    hampath: { title: 'HAM-PATH', n: 6, edges: [[0, 3], [3, 2], [2, 1], [1, 4], [4, 5], [0, 1], [2, 5]], ask: 'Is there a path through all 6 vertices, each visited once?' },
    subset: { title: 'SUBSET SUM', nums: [7, 12, 5, 19, 8, 3], target: 27, ask: 'Do some of 7, 12, 5, 19, 8, 3 add up to exactly 27?' },
    sat: { title: 'SAT', text: '(a ∨ ¬b ∨ c) ∧ (¬a ∨ b) ∧ (¬b ∨ ¬c) ∧ (b ∨ c ∨ ¬d)', ask: 'Can a, b, c, d be set so that every clause is true?' },
  };
  const SATF = T.sat.parse(INST.sat.text);
  const CERT_HINT = { clique: 'vertex numbers, like 1 2 4 5', hampath: 'the vertices in order, like 0 3 2 1 4 5', subset: 'the numbers chosen, like 12 7 8', sat: 'a value for each variable, like a=1 b=0 c=1 d=0' };
  function readCert(problem, text) {
    const s = String(text || '').trim();
    if (problem === 'sat') {
      const a = new Array(SATF.n + 1).fill(null);
      for (const tok of s.split(/[\s,;]+/).filter(Boolean)) {
        const m = /^([A-Za-z_]\w*)\s*=\s*([01TFtf]|true|false)$/.exec(tok);
        if (!m) throw new Error('Certificate: write values like a=1 b=0, not "' + tok + '"');
        const v = SATF.names.indexOf(m[1]);
        if (v < 1) throw new Error('Certificate: the formula has no variable ' + m[1]);
        a[v] = /^(1|t|true)$/i.test(m[2]);
      }
      const miss = SATF.names.slice(1).filter((_, i) => a[i + 1] === null);
      if (miss.length) throw new Error('Certificate: give a value to every variable; ' + miss.join(', ') + ' has none');
      return a;
    }
    const nums = s.split(/[\s,;]+/).filter(Boolean).map((x) => { if (!/^\d+$/.test(x)) throw new Error('Certificate: ' + CERT_HINT[problem] + '; "' + x + '" is not a number'); return +x; });
    if (problem === 'subset') {
      const used = new Set(), idx = [];
      for (const v of nums) {
        const i = INST.subset.nums.findIndex((x, j) => x === v && !used.has(j));
        if (i < 0) throw new Error('Certificate: ' + v + ' is not one of the numbers left to choose from (7, 12, 5, 19, 8, 3)');
        used.add(i); idx.push(i);
      }
      return idx;
    }
    if (nums.some((v) => v > 5)) throw new Error('Certificate: the vertices are numbered 0 to 5');
    if (nums.length > 8) throw new Error('Certificate: at most 8 vertices');
    return nums;
  }

  T.topic({
    id: 'cx-verify', family: 'cx-np', order: 10, title: 'Checking a certificate',
    blurb: 'A problem is in NP when every yes-instance has a short certificate that a polynomial-time verifier can check. Hand one over and watch each check pass, or the first one fail.',
    inputs: [
      { id: 'problem', kind: 'choice', label: 'Problem', def: 'clique', options: [{ value: 'clique', label: 'CLIQUE' }, { value: 'hampath', label: 'HAM-PATH' }, { value: 'subset', label: 'SUBSET SUM' }, { value: 'sat', label: 'SAT' }] },
      { id: 'cert', kind: 'text', label: 'Certificate', def: '1 2 4 5' },
    ],
    check: (inp) => { try { readCert(inp.problem, inp.cert); return null; } catch (e) { return e.message; } },
    presets: [
      { label: 'A clique that checks out', values: { problem: 'clique', cert: '1 2 4 5' } },
      { label: 'A clique with a missing edge', values: { problem: 'clique', cert: '0 1 2 3' } },
      { label: 'A Hamiltonian path', values: { problem: 'hampath', cert: '0 3 2 1 4 5' } },
      { label: 'A path that skips a vertex', values: { problem: 'hampath', cert: '0 3 2 5 4' } },
      { label: 'Subset sum: 12 + 7 + 8', values: { problem: 'subset', cert: '12 7 8' } },
      { label: 'SAT with a wrong assignment', values: { problem: 'sat', cert: 'a=1 b=0 c=1 d=1' } },
    ],
    counters: [{ id: 'checks', label: 'checks made' }, { id: 'size', label: 'certificate size' }],
    run(inp) {
      const pr = inp.problem, I = INST[pr];
      const cert = readCert(pr, inp.cert);
      const F = new T.Frames(['checks', 'size']);
      const certList = pr === 'sat' ? SATF.names.slice(1).map((nm, i) => nm + ' = ' + (cert[i + 1] ? 1 : 0)) : pr === 'subset' ? cert.map((i) => String(I.nums[i])) : cert.map(String);
      F.set('size', certList.length);
      let V;
      if (pr === 'clique') V = T.cx.verifyClique({ n: I.n, edges: I.edges }, I.k, cert);
      else if (pr === 'hampath') V = T.cx.verifyHamPath({ n: I.n, edges: I.edges }, cert);
      else if (pr === 'subset') V = T.cx.verifySubsetSum(I.nums, I.target, cert);
      else V = T.cx.verifySat(SATF, cert);
      const checks = [];
      for (const c of V.trace) { checks.push(c); if (c.kind === 'fail') break; }
      const isGraph = pr === 'clique' || pr === 'hampath';
      const pos = hexPos(6, 130);
      const chipsY = isGraph ? 200 : 170;
      const chips = (hot, done) => {
        const items = [{ key: 'cert:label', kind: 'text', x: -170, y: chipsY + 25, text: 'certificate', anchor: 'end', cls: 'title' }];
        let x = -160;
        certList.forEach((t, i) => {
          const w = Math.max(44, T.geom.textWidth(t, 16, { mono: true }) + 18);
          items.push({ key: 'cert:' + i, kind: 'cell', x, y: chipsY, w, h: 40, rx: 8, text: t, cls: 'mono ' + (hot.includes(i) ? 'hot' : done ? 'act' : ''), enter: 'drop', pick: true });
          x += w + 6;
        });
        return items;
      };
      // the picture of the instance, with what the current check looks at lit
      const picture = (look, opts) => {
        opts = opts || {};
        if (isGraph) {
          const certSet = opts.cert ? cert : [];
          const nodes = pos.map((p, i) => ({ id: i, label: String(i), x: p.x, y: p.y, cls: look.nodes && look.nodes.includes(i) ? 'hot' : '' }));
          const edges = I.edges.map(([a, b]) => ({ a, b, cls: look.edge && ekey(look.edge[0], look.edge[1]) === ekey(a, b) ? 'hot thick' : (opts.okEdges && opts.okEdges.has(ekey(a, b)) ? 'cert' : '') }));
          const items = K.gadget.draw({ nodes, edges, cert: certSet.filter((v) => !(look.nodes || []).includes(v)), prefix: 'g' }).items;
          if (look.edge && !I.edges.some(([a, b]) => ekey(a, b) === ekey(look.edge[0], look.edge[1]))) items.push({ key: 'g:miss', kind: 'edge', from: 'g:v:' + look.edge[0], to: 'g:v:' + look.edge[1], head: false, gapB: 0, cls: 'bad dead thick', audit: 'edge-x' });
          return items;
        }
        if (pr === 'subset') {
          const items = [];
          const chosen = new Set(opts.cert ? cert : []);
          I.nums.forEach((v, i) => items.push({ key: 'num:' + i, kind: 'cell', x: -160 + i * 62, y: -20, w: 54, h: 46, rx: 8, text: String(v), cls: 'mono ' + ((look.nums || []).includes(i) ? 'hot' : chosen.has(i) ? 'act' : ''), pick: true }));
          items.push({ key: 'num:label', kind: 'text', x: -170, y: 9, text: 'numbers', anchor: 'end', cls: 'title' });
          const sum = (look.sum === undefined ? 0 : look.sum);
          items.push(...K.cx.bars({ rows: [{ id: 'sum', label: 'sum', value: sum, cls: sum === I.target ? 's1' : sum > I.target ? 's4' : 's0' }, { id: 'target', label: 'target', value: I.target, cls: 'sm-bar s3' }], x: -100, y: 60, w: 300, barH: 26, gap: 10, max: Math.max(I.target, cert.reduce((s, i) => s + I.nums[i], 0)), prefix: 'sb' }).items);
          return items;
        }
        return K.cx.formula({ f: SATF, a: opts.cert ? cert : [], x: -170, y: -40, maxW: 720, labels: true, hot: look.clause === undefined ? [] : [look.clause] }).items;
      };
      const ledX = -160, ledY = chipsY + 76;
      const say0 = I.title + ': ' + I.ask + ' Finding the answer may take a long search; checking a proposed answer should not.';
      F.add({ items: picture({}), say: say0 });
      F.add({ items: picture({}, { cert: true }).concat(chips([], false)), say: 'Someone hands over a certificate: ' + certList.join(', ') + '. It is short, ' + certList.length + ' entries, and the verifier now checks it without any search.', meta: { cert: true } });
      const lines = [];
      let sum = 0;
      if (pr === 'subset') {
        cert.forEach((i, k) => {
          sum += I.nums[i];
          F.count('checks');
          F.add({ items: picture({ nums: [i], sum }, { cert: true }).concat(chips([k], true)), say: 'Add ' + I.nums[i] + ': the running sum is ' + sum + (k === cert.length - 1 ? ', with the target ' + I.target + ' to compare.' : '.'), hl: { def: [1] } });
        });
      }
      const okEdges = new Set();
      checks.forEach((c, k) => {
        lines.push({ ok: c.kind === 'check', say: c.say });
        F.count('checks');
        let look = {}, hotChips = [];
        if (c.pair) { look = { nodes: c.pair, edge: c.pair }; hotChips = c.pair.map((v) => cert.indexOf(v)); }
        else if (c.edge) { look = { nodes: c.edge, edge: c.edge }; const at = cert.findIndex((v, i) => v === c.edge[0] && cert[i + 1] === c.edge[1]); hotChips = [at, at + 1]; }
        else if (c.clause !== undefined) look = { clause: c.clause };
        else if (pr === 'subset') look = { sum };
        else if (isGraph) { look = { nodes: cert.slice() }; hotChips = cert.map((_, i) => i); }
        if (pr === 'subset') look.sum = sum;
        const items = picture(look, { cert: true, okEdges }).concat(chips(hotChips, true), ledger('led', lines, ledX, ledY));
        if ((c.pair || c.edge) && c.kind === 'check') okEdges.add(ekey(...(c.pair || c.edge)));
        F.add({ items, say: 'Check ' + (k + 1) + ': ' + c.say + (c.kind === 'fail' ? ' That is enough to reject this certificate: one failed check sinks it.' : ''), meta: { fail: c.kind === 'fail' }, hl: { def: [Math.min(k + 2, 2)] } });
      });
      const ok = V.ok;
      const nChecks = F.counts.checks;
      const bound = pr === 'clique' ? 'about k²/2 pairs' : pr === 'hampath' ? 'one test per step of the path' : pr === 'subset' ? 'one addition per number' : 'one look at each clause';
      const last = picture({}, { cert: true, okEdges }).concat(chips([], true), ledger('led', lines, ledX, ledY));
      F.add({ items: last, say: ok ? 'Every check passed in ' + nChecks + ' steps (' + bound + '), so the verifier accepts: the answer is yes, and this certificate proves it.' : 'The verifier rejects this certificate. That does not mean the answer is no: it only means this certificate is not a proof. A verifier must accept some certificate exactly when the answer is yes.', mark: ok ? 'accepted' : 'rejected', meta: { ok } });
      const defText = pr === 'clique' ? 'G: 6 vertices, ' + I.edges.length + ' edges, k = 4\ncertificate: a set S of vertices\ncheck |S| ≥ k, then every pair in S is an edge' : pr === 'hampath' ? 'G: 6 vertices, ' + I.edges.length + ' edges\ncertificate: an order of the vertices\ncheck each vertex once, then each step is an edge' : pr === 'subset' ? 'numbers 7, 12, 5, 19, 8, 3, target 27\ncertificate: some of the numbers\ncheck they are distinct picks and sum to 27' : SATF.clauses.map((c, i) => 'C' + (i + 1) + ' = ' + T.sat.toText({ clauses: [c], names: SATF.names })).join('\n');
      return { frames: F.list, result: ok, def: { sections: [
        { id: 'def', kind: 'math', title: I.title + ' and its verifier', text: defText },
        { id: 'np', kind: 'text', title: 'NP', text: 'L is in NP when there is a verifier V running in time polynomial in |x| with: x ∈ L exactly when V accepts ⟨x, c⟩ for some certificate c of polynomial length.' },
      ] } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.cert && fr[fr.length - 1].meta, once: true, pick: 'option', options: ['Yes, every check will pass', 'No, some check will fail'], ask: 'Look at the certificate. Will the verifier accept it?', answer: (fr) => (fr[fr.length - 1].meta.ok ? 'Yes, every check will pass' : 'No, some check will fail'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What makes a certificate useful for putting a problem in NP?', options: ['It is short and can be checked in polynomial time', 'It is unique', 'It can be found in polynomial time', 'It proves the answer is no'], answer: 0, why: 'NP asks only that yes-instances have certificates of polynomial length that a polynomial-time verifier accepts; finding them may be hard.' },
      { q: 'The verifier rejects a certificate for a CLIQUE instance. What follows?', options: ['The graph has no clique of that size', 'Only that this certificate is not a proof', 'The problem is not in NP', 'The verifier is wrong'], answer: 1, why: 'A different set of vertices might still be a clique. The answer is no only when every certificate is rejected.' },
      { q: 'How many pair checks does the CLIQUE verifier make for a set of k vertices?', options: ['k', 'k(k − 1)/2', '2ᵏ', 'k!'], answer: 1, why: 'Each of the k(k − 1)/2 pairs must be an edge: polynomial in the input.' },
      { q: 'Why is every problem in P also in NP?', options: ['Because P = NP', 'A verifier can ignore the certificate and solve the problem itself', 'Because polynomial problems have no certificates', 'It is not'], answer: 1, why: 'If a polynomial algorithm decides L, the verifier runs it and ignores c; the empty certificate works for every yes-instance.' },
      { q: 'For SUBSET SUM, why is the list of chosen numbers a short certificate?', options: ['It has at most as many entries as the input', 'It is sorted', 'It is always 3 numbers', 'It contains the target'], answer: 0, why: 'At most n numbers, each already written in the input, and checking means one addition per number and a comparison.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // 2. nondeterministic time: the tree of guesses
  const NTM = 'ntm-repeat';
  const guessF = (text) => T.sat.parse(text);
  T.topic({
    id: 'cx-ntime', family: 'cx-np', order: 20, title: 'Nondeterministic time: a tree of guesses',
    blurb: 'A nondeterministic machine may branch at each step. Its running time is the depth of the tree, not its size: an accepting branch of depth t means acceptance in time t, though a deterministic machine may have to search the whole tree.',
    inputs: [
      { id: 'mode', kind: 'choice', label: 'Machine', def: 'ntm', options: [{ value: 'ntm', label: 'Guess where a letter repeats' }, { value: 'sat', label: 'Guess an assignment, then check' }] },
      { id: 'w', kind: 'string', label: 'Input (for the repeat machine)', def: 'abca', alphabet: 'abc', max: 5 },
      { id: 'f', kind: 'text', label: 'Formula (for guessing)', def: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z)' },
    ],
    check: (inp) => { if (inp.mode !== 'sat') return null; let f; try { f = guessF(inp.f); } catch (e) { return 'Formula: ' + e.message; } if (f.n > 4) return 'Formula: at most 4 variables, so the 2ⁿ leaves fit on the screen'; if (!f.clauses.length) return 'Formula: give at least one clause'; return null; },
    presets: [
      { label: 'abca: some branch finds the a', values: { mode: 'ntm', w: 'abca' } },
      { label: 'cab: no branch accepts', values: { mode: 'ntm', w: 'cab' } },
      { label: 'bcab: the repeat is late', values: { mode: 'ntm', w: 'bcab' } },
      { label: 'Guess 3 bits for a formula', values: { mode: 'sat', f: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z)' } },
      { label: 'Guessing for an unsatisfiable formula', values: { mode: 'sat', f: '(x ∨ y) ∧ (¬x ∨ y) ∧ (¬y ∨ z) ∧ (¬z)' } },
    ],
    counters: [{ id: 'time', label: 'time (depth)' }, { id: 'width', label: 'branches at this depth' }, { id: 'total', label: 'nodes a simulation visits' }],
    run(inp) {
      const F = new T.Frames(['time', 'width', 'total']);
      let nodes, verdict, path = [], f = null, M = null;
      if (inp.mode === 'sat') {
        f = guessF(inp.f);
        nodes = [{ id: 0, parent: -1, depth: 0, label: 'start', a: [] }];
        let frontier = [0];
        for (let v = 1; v <= f.n; v++) {
          const next = [];
          for (const id of frontier) for (const b of [true, false]) { const a = nodes[id].a.slice(); a[v] = b; nodes.push({ id: nodes.length, parent: id, depth: v, label: T.sat.litText(f, v) + '=' + (b ? 1 : 0), a }); next.push(nodes.length - 1); }
          frontier = next;
        }
        for (const id of frontier) nodes[id].status = T.sat.evaluate(f, nodes[id].a) ? 'accept' : 'reject';
        const acc = frontier.find((id) => nodes[id].status === 'accept');
        verdict = acc === undefined ? 'reject' : 'accept';
        for (let i = acc === undefined ? -1 : acc; i >= 0; i = nodes[i].parent) path.unshift(i);
      } else {
        M = T.tmLib.get(NTM);
        const r = T.tm.ntmTree(M, inp.w, { maxDepth: 9, maxNodes: 60 });
        nodes = r.nodes.map((n) => Object.assign({}, n, { label: n.config.replace(/ /g, '·') }));
        verdict = r.verdict; path = r.path;
      }
      const maxD = Math.max(...nodes.map((n) => n.depth));
      const build = (d, final) => {
        const mk = (n) => {
          const kids = nodes.filter((c) => c.parent === n.id && c.depth <= d);
          let cls = '';
          if (final) {
            if (n.status === 'accept') cls = 'good';
            else if (n.status === 'reject' || (inp.mode === 'ntm' && n.status !== 'expanded' && n.status !== 'accept' && verdict === 'reject')) cls = 'bad';
            else if (verdict === 'accept' && !path.includes(n.id) && !kids.length) cls = 'pruned';
          }
          return { id: 'n' + n.id, label: n.label, mono: inp.mode === 'ntm', cls, children: kids.map(mk) };
        };
        return mk(nodes[0]);
      };
      const levelOf = (d) => nodes.filter((n) => n.depth === d).length;
      const top = f ? 130 : 0;
      const draw = (d, opts) => {
        opts = opts || {};
        const tr = K.tree.draw(build(d, opts.final), { y: top, gapY: 76, gapX: inp.mode === 'ntm' ? 14 : 10, path: opts.final && verdict === 'accept' ? path.map((i) => 'n' + i) : [], hot: (opts.hot || []).map((i) => 'n' + i), prefix: 'tr' });
        return tr;
      };
      // a time axis on the left, at a fixed place: left of the widest tree
      let minX = Infinity, maxX = -Infinity;
      for (let d = 0; d <= maxD; d++) for (const fin of [false, true]) { const b = draw(d, { final: fin }).box; minX = Math.min(minX, b.x); maxX = Math.max(maxX, b.x + b.w); }
      const axis = (d) => {
        const out = [];
        for (let k = 0; k <= d; k++) out.push({ key: 'ax:' + k, kind: 'text', x: minX - 24, y: top + k * 76 + 5, text: 't = ' + k, anchor: 'end', cls: k === d ? 'hot' : 'strong', size: 14 });
        return out;
      };
      const head = () => (f ? K.cx.formula({ f, x: Math.min(minX - 70, (minX + maxX) / 2 - 300), y: -10, maxW: Math.max(560, maxX - minX + 70), prefix: 'fm' }).items : []);
      let total = 1;
      F.set('time', 0).set('width', 1).set('total', 1);
      F.add({ items: head().concat(draw(0).items, axis(0)), say: inp.mode === 'sat' ? 'The machine will guess a value for each of ' + f.names.slice(1).join(', ') + ', one per step, and then check the clauses. The root is the start, before any guess.' : 'The machine reads ' + (inp.w || 'ε') + '. In q0 it may move on, or guess that this letter is the first of a repeated pair and remember it (pa, pb or pc). The root is the start configuration ' + nodes[0].config + '.' });
      for (let d = 1; d <= maxD; d++) {
        const lv = levelOf(d);
        total += lv;
        F.set('time', d).set('width', lv).set('total', total);
        const fresh = nodes.filter((n) => n.depth === d).map((n) => n.id);
        const say = inp.mode === 'sat'
          ? 'Step ' + d + ': every branch guesses ' + T.sat.litText(f, d) + ' = 1 or 0, so the tree doubles to ' + lv + ' branches. Time so far: ' + d + ' steps on each branch.'
          : 'Step ' + d + ': ' + lv + ' configuration' + (lv === 1 ? '' : 's') + ' at depth ' + d + ', for example ' + nodes[fresh[0]].config + '. Each branch has taken just ' + d + ' steps.';
        F.add({ items: head().concat(draw(d, { hot: fresh }).items, axis(d)), say, meta: { level: d, next: d < maxD ? levelOf(d + 1) : null } });
      }
      const accN = path.length ? nodes[path[path.length - 1]] : null;
      const finalSay = verdict === 'accept'
        ? (inp.mode === 'sat' ? 'The leaves check the formula: the branch ' + accN.label.split('=')[0] + '… marked green satisfies it, so the machine accepts after ' + maxD + ' guesses plus a polynomial check. A deterministic search may visit all ' + total + ' nodes.' : 'The branch ' + accN.config + ' reached qa at depth ' + accN.depth + ': the machine accepts in time ' + accN.depth + '. The faded branches were never needed; a deterministic simulation pays for them anyway (' + total + ' nodes so far).')
        : (inp.mode === 'sat' ? 'All ' + levelOf(maxD) + ' leaves fail the check: no branch accepts, so the machine rejects. Saying no needed the whole tree; there was no single branch to point at.' : 'Every branch halts without accepting: there is no repeated letter in ' + inp.w + ', so the machine rejects. A nondeterministic machine accepts if some branch does, and rejects only when none does.');
      F.add({ items: head().concat(draw(maxD, { final: true }).items, axis(maxD)), say: finalSay, mark: verdict === 'accept' ? 'accepted' : 'rejected', meta: { verdict } });
      const sections = inp.mode === 'sat'
        ? [{ id: 'f', kind: 'math', title: 'Formula', text: f.clauses.map((c, i) => 'C' + (i + 1) + ' = ' + T.sat.toText({ clauses: [c], names: f.names })).join('\n') }]
        : [{ id: 'm', kind: 'math', title: 'The machine (guesses in q0)', text: 'q0: move on, or remember the letter (pa, pb, pc)\npa: move on, or accept on another a\npb: move on, or accept on another b\npc: move on, or accept on another c' }];
      sections.push({ id: 'nt', kind: 'text', title: 'NTIME', text: 'A nondeterministic machine runs in time t(n) when every branch halts within t(n) steps. NP is the union of NTIME(nᵏ): the depth is polynomial, the number of branches may be exponential.' });
      return { frames: F.list, def: { sections } };
    },
    predict: [
      { at: (f, i, fr) => f.meta && f.meta.level === 1 && f.meta.next !== null, once: true, pick: 'option', options: (fr, i) => { const n = fr[i].meta.next; return [...new Set([n, n + 2, Math.max(1, n - 1), 2 * n + 1])].sort((a, b) => a - b).map(String); }, ask: 'How many configurations will the next depth hold?', answer: (fr, i) => String(fr[i].meta.next), explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Some branch accepts', 'No branch accepts'], ask: 'The tree is complete up to its depth. Will some branch accept?', answer: (fr) => (fr[fr.length - 1].meta.verdict === 'accept' ? 'Some branch accepts' : 'No branch accepts'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What is the running time of a nondeterministic machine on an input?', options: ['The number of nodes in its tree', 'The length of its longest branch', 'The number of accepting branches', 'The width of the widest level'], answer: 1, why: 'Time is measured along branches: the machine runs in time t when no branch is longer than t.' },
      { q: 'When does a nondeterministic machine accept?', options: ['When most branches accept', 'When every branch accepts', 'When at least one branch accepts', 'When the first branch accepts'], answer: 2, why: 'One accepting branch is enough; rejecting means that no branch accepts.' },
      { q: 'A guess-a-bit machine for a formula with n variables makes a tree with how many leaves?', options: ['n', 'n²', '2ⁿ', 'n!'], answer: 2, why: 'Each of the n guesses doubles the branches; the depth stays n plus the time to check.' },
      { q: 'Why can a deterministic machine simulate a nondeterministic one at all?', options: ['It can explore the tree breadth first', 'It can guess as well', 'The tree is always small', 'It cannot'], answer: 0, why: 'Visiting the tree level by level finds an accepting branch if there is one; the price can be exponential time.' },
      { q: 'What does the accepting path correspond to in the language of verifiers?', options: ['The verifier', 'A certificate: the list of choices made', 'The input', 'The time bound'], answer: 1, why: 'The sequence of guesses on an accepting branch is a short certificate, and following it is a deterministic check.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // 3. P versus NP as a picture
  const PR = {
    PATH: { x: 70, y: 135, region: 'p', what: 'reachability in a graph, solved by breadth-first search' },
    RELPRIME: { x: 70, y: 175, region: 'p', what: 'whether two numbers share no factor, by Euclid\'s algorithm' },
    'CFL MEMBER': { x: 70, y: 215, region: 'p', what: 'whether a grammar derives a string, by CYK' },
    FACTOR: { x: 70, y: 345, region: 'np', what: 'whether a number has a factor below a bound; in NP, not known to be in P or NP-complete' },
    SAT: { x: 300, y: 135, region: 'npc', what: 'satisfiability of formulas, the first problem shown NP-complete' },
    CLIQUE: { x: 300, y: 195, region: 'npc', what: 'a set of k vertices all joined to each other' },
    'HAM-PATH': { x: 300, y: 255, region: 'npc', what: 'a path through every vertex once' },
    'SUBSET SUM': { x: 300, y: 315, region: 'npc', what: 'numbers that add up to a target' },
    TQBF: { x: 510, y: 175, region: 'dec', what: 'true quantified formulas, PSPACE-complete: not known to be in NP' },
    HALT: { x: 700, y: 175, region: 'undec', what: 'whether a program halts: undecidable, beyond every time bound' },
  };
  const PN = Object.keys(PR);
  T.topic({
    id: 'cx-pvsnp', family: 'cx-np', order: 30, title: 'P versus NP as a picture',
    blurb: 'Two possible worlds. If P ≠ NP, the NP-complete problems sit on the hard rim of NP, away from P. If anyone finds a polynomial algorithm for one of them, the picture collapses: P = NP.',
    inputs: [{ id: 'follow', kind: 'choice', label: 'Follow a problem', def: 'SAT', options: PN.map((p) => ({ value: p, label: p })) }],
    presets: [
      { label: 'Follow SAT', values: { follow: 'SAT' } },
      { label: 'Follow PATH (already easy)', values: { follow: 'PATH' } },
      { label: 'Follow FACTOR (in between?)', values: { follow: 'FACTOR' } },
      { label: 'Follow HALT (no time bound helps)', values: { follow: 'HALT' } },
    ],
    run(inp) {
      const fol = inp.follow;
      const F = new T.Frames([]);
      // the regions of the two worlds, by stage
      const R = {
        dec: { x: 0, y: 0, w: 620, h: 410, text: 'Decidable', cls: 'r1' },
        undec: { x: 640, y: 0, w: 150, h: 410, text: 'Undecidable', cls: 'r4' },
        np: { x: 20, y: 36, w: 440, h: 360, text: 'NP', cls: 'r0' },
        p: { x: 38, y: 74, w: 190, h: 196, text: 'P', cls: 'r2' },
        npc: { x: 262, y: 74, w: 180, h: 300, text: 'NP-complete', cls: 'r3' },
      };
      const reg = (id, extra) => Object.assign({ key: 'r:' + id, kind: 'region', rx: 16 }, R[id], extra || {});
      const pt = (name, cls) => {
        const p = PR[name];
        const hot = name === fol;
        return [
          { key: 'pt:' + name, kind: 'token', x: p.x, y: p.y, r: hot ? 8 : 6, cls: hot ? '' : cls || 'act', pick: true },
          { key: 'pl:' + name, kind: 'text', x: p.x + 14, y: p.y + 5, text: name, anchor: 'start', size: hot ? 16 : 14, cls: hot ? 'hot' : 'strong', pick: true },
        ];
      };
      const pts = (names, cls) => [].concat(...names.map((n) => pt(n, cls)));
      const inP = ['PATH', 'RELPRIME', 'CFL MEMBER'], inNPC = ['SAT', 'CLIQUE', 'HAM-PATH', 'SUBSET SUM'];
      const where = (world) => {
        const p = PR[fol];
        if (fol === 'HALT') return 'HALT is not even decidable, so no time bound applies to it in either world.';
        if (fol === 'TQBF') return world === 'B' ? 'TQBF stays outside: P = NP would not, as far as anyone knows, make PSPACE problems easy.' : 'TQBF is decidable in polynomial space but is not known to be in NP: a true formula has no known short certificate.';
        if (p.region === 'p') return fol + ' (' + p.what + ') is in P in both worlds.';
        if (world === 'B') return fol + ' would now be in P along with everything else in NP.';
        return fol + ': ' + p.what + '.';
      };
      const base = [reg('dec'), reg('undec')].concat(pts(['TQBF']), pts(['HALT'], 'bad'));
      F.add({ items: base.concat([reg('p')], pts(inP)), say: 'Start with P: the problems a deterministic machine decides in polynomial time, like PATH, RELPRIME and CFL membership. ' + (PR[fol].region === 'p' ? where('A') : 'Everything here is decidable; HALT, on the right, is not.'), hl: { cls: [0] } });
      F.add({ items: base.concat([reg('np'), reg('p')], pts(inP), pts(['FACTOR'])), say: 'Around P draw NP: problems whose yes-answers have certificates a polynomial verifier can check. P sits inside, since a solver can ignore the certificate. ' + (fol === 'FACTOR' ? where('A') : 'FACTOR is in NP; whether it is in P is unknown.'), hl: { cls: [0, 1] } });
      F.add({ items: base.concat([reg('np'), reg('p'), reg('npc')], pts(inP), pts(['FACTOR']), pts(inNPC, 'bad')), say: 'The NP-complete problems are the hardest in NP: SAT, CLIQUE, HAM-PATH, SUBSET SUM. Drawn apart from P, this is the world most people believe in: P ≠ NP. ' + (inNPC.includes(fol) ? where('A') : ''), hl: { cls: [2] } });
      // every NP problem reduces to SAT
      const arrows = (cls) => ['PATH', 'FACTOR', 'CLIQUE'].map((n) => ({ key: 'ar:' + n, kind: 'edge', from: n === 'CLIQUE' ? 'pt:CLIQUE' : { x: PR[n].x + 18 + T.geom.textWidth(n, 14, { bold: true }), y: PR[n].y }, to: 'pt:SAT', bend: n === 'CLIQUE' ? 0 : n === 'PATH' ? -26 : 20, cls: 'alt ' + (cls || '') }));
      F.add({ items: base.concat([reg('np'), reg('p'), reg('npc')], pts(inP), pts(['FACTOR']), pts(inNPC, 'bad'), arrows()), say: 'NP-complete means every problem in NP reduces to it in polynomial time. The arrows show three of these reductions into SAT; there is one from every problem in NP.', hl: { cls: [2] }, meta: { ask: true } });
      F.add({ items: base.concat([reg('np'), reg('p'), reg('npc', { cls: 'r3 hot' })], pts(inP), pts(['FACTOR']), pts(['SAT'], 'good'), pts(inNPC.slice(1), 'bad'), arrows('hot')), say: 'Now suppose someone found a polynomial algorithm for SAT. Then each NP problem could be solved by reducing it to SAT and running that algorithm: polynomial time followed by polynomial time.' });
      // the collapse: NP and the NP-complete rim fall into P
      const big = { x: 20, y: 36, w: 440, h: 360 };
      const collapsed = [reg('dec'), reg('undec'), { key: 'r:p', kind: 'region', rx: 16, x: big.x, y: big.y, w: big.w, h: big.h, text: 'P = NP', cls: 'r2 hot' }].concat(pts(inP, 'good'), pts(['FACTOR'], 'good'), pts(inNPC, 'good'), pts(['TQBF']), pts(['HALT'], 'bad'));
      F.add({ items: collapsed, exits: { 'r:np': { exit: 'into', into: 'r:p' }, 'r:npc': { exit: 'into', into: 'r:p' } }, say: 'The picture collapses: NP and P become one region, and every problem in it, CLIQUE and FACTOR included, has a polynomial algorithm. ' + where('B'), mark: 'P = NP', hl: { cls: [3] } });
      F.add({ items: collapsed, say: 'TQBF and HALT do not move: a fast SAT algorithm says nothing known about problems outside NP. Which world is real is the P versus NP question, still open.', hl: { cls: [3] } });
      return { frames: F.list, def: { sections: [
        { id: 'cls', kind: 'math', title: 'The classes', text: 'P = problems decided in polynomial time\nNP = problems verified in polynomial time\nNP-complete = in NP, and every NP problem reduces to it\nIf one NP-complete problem is in P, then P = NP' },
        { id: 'pr', kind: 'text', title: fol, text: PR[fol].what.charAt(0).toUpperCase() + PR[fol].what.slice(1) + '.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.ask, once: true, ask: 'Suppose SAT turns out to have a polynomial algorithm. Click a problem that would certainly stay where it is.', answer: () => ['pt:HALT', 'pl:HALT', 'pt:TQBF', 'pl:TQBF', 'pt:PATH', 'pl:PATH', 'pt:RELPRIME', 'pl:RELPRIME', 'pt:CFL MEMBER', 'pl:CFL MEMBER'], explain: 'Problems already in P stay in P, and problems outside NP (TQBF, HALT) are not known to move. Everything else in NP would join P.' },
    ],
    quiz: [
      { q: 'If a polynomial algorithm were found for one NP-complete problem, what would follow?', options: ['Only that problem becomes easy', 'P = NP', 'NP = PSPACE', 'HALT becomes decidable'], answer: 1, why: 'Every NP problem reduces to it in polynomial time, so all of NP would be solvable in polynomial time.' },
      { q: 'Why is P drawn inside NP?', options: ['It is a guess', 'A polynomial solver is a verifier that ignores the certificate', 'Because NP problems are easier', 'Because P is finite'], answer: 1, why: 'Every problem decided in polynomial time can be verified in polynomial time with an empty certificate.' },
      { q: 'Where does FACTOR sit, as far as anyone knows?', options: ['In P', 'NP-complete', 'In NP, not known to be in P and not believed NP-complete', 'Outside NP'], answer: 2, why: 'A factor is a short certificate, so it is in NP; no polynomial algorithm and no NP-completeness proof are known.' },
      { q: 'Would P = NP make HALT decidable?', options: ['Yes', 'No: HALT is not decidable at all, and time classes contain only decidable problems', 'Only for short programs', 'Nobody knows'], answer: 1, why: 'P and NP contain only decidable problems; their equality says nothing about HALT.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------------
  // 4. co-NP: when is the answer no easy to prove?
  const QS = {
    sat: { ask: 'Is φ satisfiable?', yesCert: 'sat', label: 'SAT' },
    taut: { ask: 'Is φ true under every assignment (a tautology)?', noCert: 'false', label: 'TAUT' },
    unsat: { ask: 'Is φ unsatisfiable?', noCert: 'sat', label: 'UNSAT' },
  };
  T.topic({
    id: 'cx-conp', family: 'cx-np', order: 40, title: 'co-NP: proving the answer is no',
    blurb: 'For SAT a yes comes with a short proof: one satisfying row. For its complement, UNSAT, and for TAUT, it is the no-answers that have one-row proofs; a yes seems to need the whole truth table.',
    inputs: [
      { id: 'q', kind: 'choice', label: 'Question', def: 'unsat', options: [{ value: 'sat', label: 'SAT: is φ satisfiable?' }, { value: 'unsat', label: 'UNSAT: is φ unsatisfiable?' }, { value: 'taut', label: 'TAUT: is φ always true?' }] },
      { id: 'f', kind: 'text', label: 'Formula φ (CNF)', def: '(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)' },
    ],
    check: (inp) => { let f; try { f = T.sat.parse(inp.f); } catch (e) { return 'Formula: ' + e.message; } if (!f.n) return 'Formula: give at least one variable'; if (f.n > 4) return 'Formula: at most 4 variables (16 rows)'; if (f.clauses.length > 6) return 'Formula: at most 6 clauses'; return null; },
    presets: [
      { label: 'UNSAT, and it is: every row checked', values: { q: 'unsat', f: '(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)' } },
      { label: 'UNSAT, but one row refutes it', values: { q: 'unsat', f: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z)' } },
      { label: 'TAUT, refuted by one row', values: { q: 'taut', f: '(x ∨ ¬y) ∧ (y ∨ z ∨ ¬x)' } },
      { label: 'TAUT, and it is (x ∨ ¬x in every clause)', values: { q: 'taut', f: '(x ∨ ¬x ∨ y) ∧ (z ∨ ¬z) ∧ (¬y ∨ y)' } },
      { label: 'SAT: one row is the proof', values: { q: 'sat', f: '(x ∨ y) ∧ (¬x ∨ z) ∧ (¬y ∨ ¬z)' } },
    ],
    counters: [{ id: 'rows', label: 'rows checked' }, { id: 'all', label: 'rows in the table' }],
    run(inp) {
      const f = T.sat.parse(inp.f), n = f.n, N = 2 ** n, Q = QS[inp.q];
      const F = new T.Frames(['rows', 'all']);
      F.set('all', N);
      const rowA = (r) => { const a = [null]; for (let v = 1; v <= n; v++) a.push(!!(r & (1 << (n - v)))); return a; };
      const val = Array.from({ length: N }, (_, r) => T.sat.evaluate(f, rowA(r)));
      const bits = (r) => rowA(r).slice(1).map((b) => (b ? 1 : 0)).join('');
      const perRow = n <= 2 ? 4 : n === 3 ? 4 : 4;
      const CW = 30 + 16 * n;
      const gx = -((perRow * (CW + 8)) / 2), gy = 150;
      const fm = (a, hot) => K.cx.formula({ f, a: a || [], x: -320, y: -20, maxW: 640, labels: true, hot: hot || [], prefix: 'fm' });
      const grid = (checked, hot) => {
        const items = [{ key: 'gr:label', kind: 'text', x: gx - 12, y: gy + 26, text: f.names.slice(1).join(' '), anchor: 'end', cls: 'mono' }];
        for (let r = 0; r < N; r++) {
          const c = r % perRow, rr = Math.floor(r / perRow);
          const done = checked.has(r);
          items.push({ key: 'gr:' + r, kind: 'cell', x: gx + c * (CW + 8), y: gy + rr * 50, w: CW, h: 40, rx: 6, text: bits(r) + (done ? (val[r] ? ' ✓' : ' ✗') : ''), cls: 'mono ' + (done ? (val[r] ? 'good' : 'bad') : '') + (hot === r ? ' hot' : ''), pick: true });
        }
        return items;
      };
      // where the answer is: yes or no, and whether a single row proves it
      const satisfiable = val.some(Boolean), allTrue = val.every(Boolean);
      const answer = inp.q === 'sat' ? satisfiable : inp.q === 'unsat' ? !satisfiable : allTrue;
      const certRow = inp.q === 'taut' ? val.findIndex((x) => !x) : val.findIndex((x) => x);
      const short = certRow >= 0 && (inp.q === 'sat' ? answer : !answer);
      const checked = new Set();
      F.add({ items: fm().items.concat(grid(checked)), say: 'The question: ' + Q.ask + ' The formula has ' + n + ' variable' + (n === 1 ? '' : 's') + ', so its truth table has ' + N + ' rows, one per assignment.', meta: { short, certRows: val.map((v, r) => r).filter((r) => (inp.q === 'taut' ? !val[r] : val[r])) } });
      if (short) {
        checked.add(certRow);
        F.count('rows');
        const kind = inp.q === 'sat' ? 'a satisfying row: the certificate for yes' : inp.q === 'unsat' ? 'a satisfying row, which shows φ is not unsatisfiable: a certificate for no' : 'a row that makes φ false, which shows it is not a tautology: a certificate for no';
        F.add({ items: fm(rowA(certRow)).items.concat(grid(checked, certRow)), say: 'A prover hands over row ' + bits(certRow) + ', ' + kind + '. Checking it takes one pass over the clauses.', hl: { q: [0] } });
        F.add({ items: fm(rowA(certRow)).items.concat(grid(checked, certRow)), say: 'Settled after 1 row of ' + N + ': the answer is ' + (answer ? 'yes' : 'no') + '. Whichever side has a short checkable proof is the easy side to certify.', mark: answer ? 'yes' : 'no', meta: { answer } });
      } else {
        const step = N > 8 ? 2 : 1;
        for (let r = 0; r < N; r += step) {
          const rows = [];
          for (let k = r; k < Math.min(N, r + step); k++) { checked.add(k); rows.push(k); F.count('rows'); }
          const last = rows[rows.length - 1];
          const bad = f.clauses.findIndex((c) => !T.sat.evalClause(c, rowA(last)));
          F.add({ items: fm(rowA(last), bad >= 0 ? [bad] : []).items.concat(grid(checked, last)), say: rows.map((k) => 'Row ' + bits(k) + ' makes φ ' + (val[k] ? 'true' : 'false') + (val[k] ? '' : ' (clause C' + (f.clauses.findIndex((c) => !T.sat.evalClause(c, rowA(k))) + 1) + ' fails)')).join('; ') + '.' + (r === 0 ? ' No single row can prove the answer here, so every row must be looked at.' : '') });
        }
        F.add({ items: fm().items.concat(grid(checked)), say: 'All ' + N + ' rows checked: the answer is ' + (answer ? 'yes' : 'no') + '. ' + (inp.q === 'sat' ? 'For a no to SAT, no short certificate is known: that is the co-NP side.' : 'This yes needed every row. Nobody knows a short certificate for unsatisfiable formulas or tautologies; if there were one, NP would equal co-NP.'), mark: answer ? 'yes' : 'no', meta: { answer } });
      }
      // the map of the two classes
      const venn = K.set.venn({ sets: [{ id: 'A', label: 'NP' }, { id: 'B', label: 'co-NP' }], members: { A: ['SAT', 'CLIQUE'], AB: ['P', 'PATH'], B: ['UNSAT', 'TAUT'] }, hot: [inp.q === 'sat' ? 'A' : 'B'], x: 0, y: 190, r: 120 }).items;
      F.add({ items: fm().items.concat(venn), say: Q.label + ' is in ' + (inp.q === 'sat' ? 'NP: its yes-instances have short certificates.' : 'co-NP: its complement is in NP, so its no-instances have short certificates.') + ' P lies in both. Whether NP = co-NP is open; it would follow from P = NP.' });
      return { frames: F.list, def: { sections: [
        { id: 'q', kind: 'math', title: 'Certificates', text: 'SAT: yes ⇐ one satisfying row (NP)\nUNSAT: no ⇐ one satisfying row (co-NP)\nTAUT: no ⇐ one falsifying row (co-NP)' },
        { id: 'f', kind: 'math', title: 'φ', text: f.clauses.map((c, i) => 'C' + (i + 1) + ' = ' + T.sat.toText({ clauses: [c], names: f.names })).join('\n') },
        { id: 'co', kind: 'text', title: 'co-NP', text: 'A language is in co-NP when its complement is in NP: every no-instance has a short certificate that a polynomial verifier accepts.' },
      ] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.short, once: true, ask: 'A single row of the table can settle this question. Click a row that would do it.', answer: (fr) => fr[0].meta.certRows.map((r) => 'gr:' + r), explain: (fr) => fr[1].say },
      { at: (f) => f.meta && f.meta.short === false, once: true, pick: 'option', options: ['Yes, one row is enough', 'No, every row must be checked'], ask: 'Can one row of the truth table prove the answer here?', answer: () => 'No, every row must be checked', explain: 'The answer here is a claim about every row, and no single row can certify it; as far as anyone knows, only checking all of them does.' },
    ],
    quiz: [
      { q: 'What is the certificate that a CNF formula is not a tautology?', options: ['A satisfying assignment', 'An assignment that makes it false', 'The whole truth table', 'There is none'], answer: 1, why: 'One falsifying row shows the formula is not always true, and checking it is fast: TAUT is in co-NP.' },
      { q: 'UNSAT is the complement of SAT. Which class is UNSAT in?', options: ['NP', 'co-NP', 'P', 'None'], answer: 1, why: 'Its complement SAT is in NP, so UNSAT is in co-NP.' },
      { q: 'Which statement is an open question?', options: ['P ⊆ NP', 'P ⊆ co-NP', 'NP = co-NP', 'SAT is in NP'], answer: 2, why: 'P is in both NP and co-NP; whether NP equals co-NP is unknown.' },
      { q: 'If P = NP, what would happen to co-NP?', options: ['Nothing known', 'co-NP = P too', 'co-NP would be empty', 'co-NP would contain HALT'], answer: 1, why: 'P is closed under complement, so P = NP gives co-NP = co-P = P = NP.' },
    ],
  });
})();
