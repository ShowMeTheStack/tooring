// Parser tests: the LR family and operator precedence, then CYK, Earley, recursive descent, PEG and LL.
// Oracles: the exact bounded language of T.grammar.language, an independent precedence-climbing parser
// for the expression grammar, and the three LALR constructions checked against each other.
import { load, rng, harness } from './load.mjs';

const T = load();
const g = T.grammar, L = T.lr, O = T.opp;
const t = harness('parsers');
const KINDS = ['lr0', 'slr', 'lalr', 'lr1'];
const key = (w) => w.join('\u0001');

// ---------- random grammars: every conflict-free table accepts exactly the language ----------
function checkTables(G, n, label) {
  const lang = new Set(g.language(G, n).map(key));
  const words = g.allWords(G.terminals, n);
  const ok = {};
  for (const k of KINDS) {
    const tab = L.buildTable(G, k, { precedence: false });
    ok[k] = tab.conflicts.length === 0;
    for (const w of words) {
      const r = L.parse(tab, w, { maxSteps: 400, trace: w.length === n });
      if (ok[k]) t.ok(r.accepted === lang.has(key(w)), label + ' ' + k + ' on ' + g.show(w) + ' expected ' + lang.has(key(w)) + '\n' + g.toString(G));
      else if (r.accepted) t.ok(lang.has(key(w)), label + ' ' + k + ' (with conflicts) accepted a non-member ' + g.show(w));
      if (r.accepted) {
        t.ok(key(g.yieldOf(r.tree)) === key(w) && g.checkTree(G, r.tree), label + ' ' + k + ' tree for ' + g.show(w));
        // every reduce step names a real handle on top of the symbol stack
        if (w.length === n) for (const s of r.trace) if (s.kind === 'reduce') {
          const p = r.trace[0] && L.augment(G).productions[s.prod];
          t.ok(s.handle.end === s.symbols.length && key(s.symbols.slice(s.handle.start)) === key(p.rhs), label + ' handle');
        }
      }
    }
    // a conflict-free table never holds two candidates in a cell
    if (ok[k]) t.ok(tab.cells.every((row) => Object.values(row).every((c) => c.length === 1)), label + ' ' + k + ' cells');
    else t.ok(tab.conflicts.every((c) => tab.cells[c.state][c.symbol].length > 1 && c.items.length >= 2), label + ' ' + k + ' conflict items');
  }
  // the hierarchy on conflict-freedom
  t.ok(!ok.lr0 || ok.slr, label + ' LR(0) ⇒ SLR');
  t.ok(!ok.slr || ok.lalr, label + ' SLR ⇒ LALR');
  t.ok(!ok.lalr || ok.lr1, label + ' LALR ⇒ LR(1)');
  const c = L.classify(G);
  const expect = ok.lr0 ? 'LR(0)' : ok.slr ? 'SLR(1)' : ok.lalr ? 'LALR(1)' : ok.lr1 ? 'LR(1)' : null;
  t.eq(c.verdict, expect, label + ' classify');
  return ok;
}

// The three ways to LALR(1) lookaheads agree, and so do their tables.
function checkLalr(G, label) {
  const lr0 = L.lr0Collection(G), m = L.lalrByMerge(G), p = L.lalrByPropagation(G), r = L.lalrByRelations(G);
  const lr1 = L.lr1Collection(G);
  t.ok(m.states.length === lr0.states.length && p.states.length === lr0.states.length, label + ' LALR state count');
  t.ok(lr1.states.length >= lr0.states.length, label + ' LR(1) has at least as many states');
  const cores = new Set(lr1.states.map((s) => s.kernel.map((i) => i.p + '.' + i.d).sort().join(' ')));
  t.ok(cores.size === lr0.states.length, label + ' LR(1) cores are the LR(0) states');
  for (const s of lr0.states) {
    const ms = m.states[s.id], ps = p.states[s.id];
    t.eq(ps.kernel.map((i) => [i.p, i.d, i.la]), ms.kernel.map((i) => [i.p, i.d, i.la]), label + ' kernel lookaheads state ' + s.id);
    t.eq(ps.items.map((i) => [i.p, i.d, i.la]), ms.items.map((i) => [i.p, i.d, i.la]), label + ' item lookaheads state ' + s.id);
    for (const it of r.states[s.id].items) {
      const q = ps.items.find((x) => x.p === it.p && x.d === it.d);
      t.eq(it.la, q.la, label + ' relations method state ' + s.id + ' item ' + L.itemText(lr0.aug, it));
    }
  }
  const a = L.buildTable(G, 'lalr', { lalr: 'merge', precedence: false }), b = L.buildTable(G, 'lalr', { precedence: false });
  t.eq(a.cells, b.cells, label + ' LALR tables');
  t.eq(a.goto, b.goto, label + ' LALR gotos');
}

function closureChecks(G, label) {
  const c0 = L.lr0Collection(G);
  for (const s of c0.states) {
    // closure is closed: every item with the dot before B brings every B-rule with the dot at the start
    const has = new Set(s.items.map((i) => i.p + '.' + i.d));
    for (const it of s.items) {
      const B = c0.aug.productions[it.p].rhs[it.d];
      if (B !== undefined && g.isN(c0.aug, B)) for (const q of g.info(c0.aug).byA.get(B)) t.ok(has.has(q.id + '.0'), label + ' closure0');
    }
    for (const [X, to] of Object.entries(s.trans)) t.eq(L.goto0(c0.aug, s.items, X), c0.states[to].kernel, label + ' goto0');
  }
  t.ok(c0.trace.filter((x) => x.kind === 'state').length === c0.states.length, label + ' one state step per state');
}

const r = rng(2024);
let tried = 0, levels = { lr0: 0, slr: 0, lalr: 0, lr1: 0 };
for (let i = 0; i < 260; i++) {
  const three = i % 5 === 4;
  const G = g.random(r, { nonterminals: 2 + r.int(2), terminals: three ? ['a', 'b', 'c'] : ['a', 'b'], maxRules: 3, maxLen: 3, eps: 0.12 });
  const ok = checkTables(G, three ? 5 : 7, 'random#' + i);
  for (const k of KINDS) if (ok[k]) levels[k]++;
  if (i % 2 === 0) checkLalr(G, 'random#' + i);
  if (i % 4 === 0) closureChecks(G, 'random#' + i);
  tried++;
}
t.ok(levels.lr1 > 20 && levels.lr0 > 3, 'random grammars cover the levels ' + JSON.stringify(levels));

// ---------- hand-made grammars with known verdicts ----------
const hand = {
  // a list of items each closed by a marker; no lookahead needed at all
  lr0: 'S -> x L y\nL -> L , i | i',
  // an optional sign before digits: LR(0) cannot decide whether to reduce the empty sign
  slr: 'N -> P d D\nP -> s | ε\nD -> D d | ε',
  // a pair of a's or a lone a, optionally followed by a closing a: SLR's FOLLOW(A) is too coarse
  lalrNotSlr: 'S -> A A | a | A A a\nA -> a',
  // two openers p and s, each followed by t and a closer; which rule reduces t depends on the opener,
  // and merging the two states that read t loses that memory
  lr1NotLalr: 'S -> p U q | p V r | s U r | s V q\nU -> t\nV -> t',
  // two ways to read a lone k that only the following symbol could tell apart, but it is the same
  rr: 'S -> U q | V q\nU -> k\nV -> k',
  // a sum with no precedence: ambiguous, so no LR table is free of conflicts
  amb: 'S -> S p S | o',
};
const verdicts = { lr0: 'LR(0)', slr: 'SLR(1)', lalrNotSlr: 'LALR(1)', lr1NotLalr: 'LR(1)', rr: null, amb: null };
for (const [name, text] of Object.entries(hand)) {
  const G = g.parse(text);
  const c = L.classify(G);
  t.eq(c.verdict, verdicts[name], 'hand ' + name + ' verdict');
  t.ok(c.reasons.length === 4 && c.trace.length >= 4, 'hand ' + name + ' reasons');
  checkTables(G, 6, 'hand ' + name);
  checkLalr(G, 'hand ' + name);
  closureChecks(G, 'hand ' + name);
}
{
  const c = L.classify(g.parse(hand.rr));
  t.ok(c.levels.lr1.conflicts.some((x) => x.type === 'reduce/reduce' && x.symbol === 'q'), 'rr: reduce/reduce on q');
  t.ok(g.ambiguity(g.parse(hand.rr), 4).ambiguous, 'rr is ambiguous');
  const a = L.classify(g.parse(hand.amb));
  t.ok(a.levels.lr1.conflicts.some((x) => x.type === 'shift/reduce' && x.symbol === 'p'), 'amb: shift/reduce on p');
  t.ok(g.ambiguity(g.parse(hand.amb), 5).ambiguous, 'amb is ambiguous');
  const s = L.classify(g.parse(hand.slr));
  t.ok(s.levels.lr0.conflicts.length > 0 && s.levels.slr.conflicts.length === 0, 'slr verdict levels');
}

// ---------- precedence and associativity on an ambiguous expression grammar ----------
const exprText = `%nonassoc '<'
%left '+' '-'
%left '*' '/'
%right NEG
%right '^'
E -> E < E | E + E | E - E | E * E | E / E | E ^ E | - E %prec NEG | ( E ) | n`;
const EG = g.parse(exprText);
// independent reference: precedence climbing
const BIN = { '<': [1, 'non'], '+': [2, 'left'], '-': [2, 'left'], '*': [3, 'left'], '/': [3, 'left'], '^': [5, 'right'] };
function climb(toks) {
  let i = 0;
  const fail = () => { throw 0; };
  function prefix() {
    const x = toks[i++];
    if (x === 'n') return 'n';
    if (x === '(') { const e = expr(0); if (toks[i++] !== ')') fail(); return e; }
    if (x === '-') return '(-' + expr(4) + ')';
    return fail();
  }
  function expr(min) {
    let left = prefix(), lastNon = false;
    for (;;) {
      const op = toks[i];
      if (!BIN[op] || BIN[op][0] < min) return left;
      if (lastNon && BIN[op][1] === 'non') fail();
      i++;
      const [p, a] = BIN[op];
      left = '(' + left + op + expr(a === 'right' ? p : p + 1) + ')';
      lastNon = a === 'non';
      if (lastNon && toks[i] === '<') fail();
    }
  }
  try { const e = expr(0); return i === toks.length ? e : null; } catch (e) { if (e === 0) return null; throw e; }
}
function render(G, tr) {
  const p = G.productions[tr.prod], k = tr.children;
  if (p.rhs.length === 1) return 'n';
  if (p.rhs[0] === '(') return render(G, k[1]);
  if (p.rhs[0] === '-') return '(-' + render(G, k[1]) + ')';
  return '(' + render(G, k[0]) + p.rhs[1] + render(G, k[2]) + ')';
}
for (const kind of ['slr', 'lalr', 'lr1']) {
  const tab = L.buildTable(EG, kind);
  t.eq(tab.conflicts.length, 0, 'expr ' + kind + ': precedence settles every conflict');
  t.ok(tab.resolutions.length > 20 && tab.resolutions.every((x) => /because/.test(x.say)), 'expr ' + kind + ' resolutions traced');
  t.ok(tab.resolutions.some((x) => x.decided === 'error' && x.symbol === '<'), 'expr ' + kind + ' nonassoc error entry');
  t.ok(tab.resolutions.some((x) => x.decided === 'shift' && x.symbol === '^'), 'expr ' + kind + ' right assoc shifts');
  const raw = L.buildTable(EG, kind, { precedence: false });
  t.ok(raw.conflicts.length === tab.resolutions.length, 'expr ' + kind + ' without precedence: the same cells are conflicts');
  const syms = ['n', '+', '-', '*', '^', '<', '(', ')'];
  const tests = g.allWords(syms, 4);
  const rr = rng(99);
  for (let k = 0; k < 2500; k++) { const len = 5 + rr.int(5); const w = []; for (let j = 0; j < len; j++) w.push(rr.int(3) ? rr.pick(['n', 'n', '-', '(', ')']) : rr.pick(syms)); tests.push(w); }
  for (const w of tests) {
    const ref = climb(w), res = L.parse(tab, w);
    t.ok(res.accepted === (ref !== null), 'expr ' + kind + ' accepts ' + w.join('') + ' iff the reference does');
    if (res.accepted && ref !== null) t.eq(render(EG, res.tree), ref, 'expr ' + kind + ' grouping of ' + w.join(''));
  }
}
{
  const tab = L.buildTable(EG, 'lalr');
  const cases = { 'n-n-n': '((n-n)-n)', 'n^n^n': '(n^(n^n))', '-n^n': '(-(n^n))', '-n*n': '((-n)*n)', 'n<n+n*n': '(n<(n+(n*n)))', 'n/(n-n)': '(n/(n-n))' };
  for (const [s, want] of Object.entries(cases)) { const res = L.parse(tab, s); t.ok(res.accepted, 'expr accepts ' + s); if (res.accepted) t.eq(render(EG, res.tree), want, 'expr groups ' + s); }
  const bad = L.parse(tab, 'n<n<n');
  t.ok(!bad.accepted && /non-associative/.test(bad.error.message), 'n<n<n rejected by %nonassoc');
  const e2 = L.parse(tab, 'n+*n');
  t.ok(!e2.accepted && e2.error.expected.includes('n') && e2.trace[e2.trace.length - 1].kind === 'error', 'error lists expected tokens');
}

// ---------- traces have the promised shape ----------
{
  const G = g.parse('%token id\nE -> E + T | T\nT -> T * F | F\nF -> ( E ) | id');
  const tab = L.buildTable(G, 'slr');
  t.eq(tab.states.length, 12, 'expression grammar: 12 LR(0) states');
  t.eq(L.classify(G).verdict, 'SLR(1)', 'expression grammar is SLR(1)');
  const res = L.parse(tab, 'id+id*id');
  t.ok(res.accepted, 'id+id*id accepted');
  t.eq(res.trace.map((s) => s.kind[0]).join(''), 'ssrrrssrrssrrra', 'driver step kinds');
  t.ok(res.trace.every((s) => typeof s.say === 'string' && s.say.length > 5 && Array.isArray(s.stack) && Array.isArray(s.input)), 'driver steps carry stack, input and say');
  for (const k of KINDS) t.ok(L.buildTable(G, k).trace.every((s) => s.kind && s.say), 'table trace ' + k);
  const p = L.lalrByPropagation(G);
  t.ok(p.trace.some((s) => s.kind === 'spontaneous') && p.trace.some((s) => s.kind === 'propagates') && p.trace.some((s) => s.kind === 'pass'), 'propagation trace kinds');
  const rel = L.lalrByRelations(G);
  t.ok(['dr', 'includes', 'lookback', 'read', 'follow', 'la'].every((k) => rel.trace.some((s) => s.kind === k)), 'relations trace kinds');
  const m = L.lalrByMerge(G);
  t.ok(m.trace.filter((s) => s.kind === 'merge').length === 12 && m.trace.some((s) => s.lr1States.length > 1), 'merge trace');
  const c1 = L.closure1(L.augment(G), [{ p: 0, d: 0, la: ['$'] }]);
  t.ok(c1.items.find((i) => i.p === 5 && i.d === 0).la.join('') === '*+$', 'closure1 lookaheads of F → • ( E )');
  t.ok(c1.trace.filter((s) => s.kind === 'closure').every((s) => /FIRST/.test(s.say)), 'closure1 explains lookaheads');
  t.eq(L.itemText(L.augment(G), { p: 1, d: 1 }), 'E → E • + T', 'item text');
  t.eq(L.actionText({ type: 'shift', state: 4 }) + L.actionText({ type: 'reduce', prod: 2 }) + L.actionText({ type: 'accept' }), 's4r2acc', 'action text');
  const big = L.parse(tab, 'id' + '+id'.repeat(40), { maxSteps: 30 });
  t.ok(!big.accepted && big.trace[big.trace.length - 1].kind === 'limit', 'step limit');
  // a capital letter quoted as a terminal survives augmentation
  const Q = g.parse("S -> 'X' S | y");
  t.ok(L.parse(L.buildTable(Q, 'lr0'), ['X', 'X', 'y']).accepted, 'quoted capital terminal');
  t.eq(L.augment(g.make('S', [['S', ["S'", 'a']], ['S', ['b']], ["S'", ['c']]])).start, "S''", 'fresh start name');
}

// ---------- operator precedence ----------
{
  const B = g.parse('B -> B v C | C\nC -> C & D | D\nD -> ~ D | ( B ) | t | f');
  const R = O.relationsFromGrammar(B);
  t.ok(R.operator.ok && R.conflicts.length === 0, 'boolean grammar is operator-precedence');
  const sorted = (a) => a.slice().sort().join(' ');
  t.eq(sorted(R.leading.B), sorted(['v', '&', '~', '(', 't', 'f']), 'LEADING(B)');
  t.eq(sorted(R.leading.D), sorted(['~', '(', 't', 'f']), 'LEADING(D)');
  t.eq(sorted(R.trailing.C), sorted(['&', '~', ')', 't', 'f']), 'TRAILING(C)');
  t.eq([R.rel['v']['&'], R.rel['&']['v'], R.rel['v']['v'], R.rel['('][')'], R.rel['$']['t'], R.rel['t']['$'], R.rel['~']['&']], ['<', '>', '>', '=', '<', '>', '>'], 'relations');
  t.ok(R.trace.some((s) => s.kind === 'leading') && R.trace.some((s) => s.kind === 'equal'), 'relations trace');
  const F = O.functions(R);
  t.ok(F.ok, 'precedence functions exist');
  for (const a of R.terminals) for (const b of R.terminals) {
    const r0 = R.rel[a][b];
    if (r0) t.ok(r0 === '<' ? F.f[a] < F.g[b] : r0 === '>' ? F.f[a] > F.g[b] : F.f[a] === F.g[b], 'f/g agree on ' + a + ' ' + b);
  }
  const lang = new Set(g.language(B, 6).map(key));
  for (const w of g.allWords(B.terminals, 5)) {
    const res = O.parse(R, w), inL = lang.has(key(w));
    t.ok(res.accepted === inL, 'opp ' + w.join('') + ' expected ' + inL);
    if (res.accepted) t.eq(key(g.yieldOf(res.tree)), key(w), 'opp yield ' + w.join(''));
    const rf = O.parse(R, w, { functions: F });
    t.ok(rf.accepted === inL, 'opp with functions ' + w.join(''));
  }
  const res = O.parse(R, 't v f & ~t');
  t.ok(res.accepted && res.tree.prod === 0 && res.tree.children[2].prod === 2, 'opp groups & under v');
  t.ok(res.trace.some((s) => s.kind === 'reduce' && s.handle) && res.trace.every((s) => s.say), 'opp trace');
  t.ok(!O.parse(R, '~').accepted, 'a lone ~ is rejected by the handle check');
  t.ok(!O.operatorCheck(g.parse('S -> A B\nA -> a\nB -> b')).ok && !O.operatorCheck(g.parse('S -> a S | ε')).ok, 'non-operator grammars detected');
  const A = g.parse('E -> E + E | E * E | n');
  const RA = O.relationsFromGrammar(A);
  t.ok(RA.conflicts.length > 0 && RA.trace.some((s) => s.kind === 'conflict'), 'ambiguous grammar: relation conflicts');
  const tab = O.fromTable(`+ * n $
+ > < < >
* > > < >
n > > . >
$ < < < .`, A);
  t.ok(tab.conflicts.length === 0 && tab.rel['+']['*'] === '<', 'relations from a table');
  const r2 = O.parse(tab, 'n+n*n+n');
  t.ok(r2.accepted, 'table parse accepts');
  const show = (x) => (x.children === null ? x.sym : x.children.length === 1 ? show(x.children[0]) : '(' + x.children.map(show).join('') + ')');
  t.eq(show(r2.tree), '((n+(n*n))+n)', 'table parse grouping');
  const F2 = O.functions(tab);
  t.ok(F2.ok && F2.f['*'] > F2.g['+'], 'functions from a table');
  const cyc = O.fromTable({ terminals: ['a', 'b', '$'], rel: { a: { b: '>', a: '<' }, b: { b: '<', a: '>' }, $: {} } });
  t.ok(!O.functions(cyc).ok, 'cyclic relations have no precedence functions');
}

// --- general and LL parsers ---
const P = T.parse, LL = T.ll, C = T.cfg;
const setEq = (a, b) => { const x = [...a].sort(), y = [...b].sort(); return JSON.stringify(x) === JSON.stringify(y); };

// ---------- CYK, Earley and recursive descent against the language, up to length 7 ----------
{
  const r = rng(9001);
  for (let k = 0; k < 120; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(4), eps: k % 3 === 0 ? 0.4 : 0.15 });
    const n = 7, lang = new Set(g.language(G, n).map(key));
    const CNF = C.toCNF(G).grammar, lr = C.leftRecursive(G).length > 0;
    for (const w of g.allWords(G.terminals, n)) {
      const want = lang.has(key(w));
      const cy = P.cyk(CNF, w);
      t.ok(cy.accepted === want, 'CYK on ' + g.show(w) + ' ' + k);
      const ea = P.earley(G, w);
      t.ok(ea.accepted === want, 'Earley on ' + g.show(w) + ' ' + k);
      if (want) {
        t.ok(g.checkTree(CNF, cy.tree) && key(g.yieldOf(cy.tree)) === key(w), 'CYK tree ' + k);
        for (const tr of ea.trees) t.ok(g.checkTree(G, tr) && key(g.yieldOf(tr)) === key(w), 'Earley tree ' + k);
        if (w.length <= 5) {
          t.eq(ea.ambiguous, g.parseTrees(G, w, 2).length > 1, 'Earley ambiguity on ' + g.show(w) + ' ' + k);
          const cnt = g.parseTrees(CNF, w, 40).length;
          if (cnt < 40) t.eq(cy.count, cnt, 'CYK counts the trees of ' + g.show(w) + ' ' + k);
        }
      }
      if (w.length <= 5 && !lr) {
        const rd = P.recursiveDescent(G, w);
        if (!rd.gaveUp) t.ok(rd.accepted === want, 'backtracking descent on ' + g.show(w) + ' ' + k);
        if (rd.accepted) t.ok(g.checkTree(G, rd.tree) && key(g.yieldOf(rd.tree)) === key(w), 'descent tree ' + k);
        const lim = P.recursiveDescent(G, w, { limited: true });
        if (lim.accepted) t.ok(want, 'limited descent only accepts members ' + k);
      }
    }
    if (lr) t.ok(P.recursiveDescent(G, ['a']).refused, 'left-recursive grammars are refused ' + k);
    // the CYK table: every source points at entries that exist
    const w = g.language(G, 6).slice(-1)[0];
    if (w && w.length) {
      const cy = P.cyk(CNF, w);
      for (let len = 2; len <= w.length; len++) for (let i = 0; i + len <= w.length; i++) for (const e of cy.cells[len][i]) for (const s of e.sources) {
        t.ok(cy.cells[s.split][i].some((x) => x.A === s.B) && cy.cells[len - s.split][i + s.split].some((x) => x.A === s.C), 'CYK provenance ' + k);
      }
      // Earley items: each scan/complete link points at an item with the dot one place earlier
      const ea = P.earley(G, w);
      ea.sets.forEach((S, j) => S.forEach((it) => it.links.forEach((l) => {
        if (l.pred) { const pr = ea.sets[l.pred[0]][l.pred[1]]; t.ok(pr.prod === it.prod && pr.dot === it.dot - 1 && pr.origin === it.origin, 'Earley link ' + k); }
        if (l.child) { const ch = ea.sets[l.child[0]][l.child[1]]; t.ok(l.child[0] === j && ch.origin === l.pred[0], 'Earley child span ' + k); }
      })));
      t.ok(P.cyk(G, w, { convert: true }).accepted, 'CYK converts on request ' + k);
    }
  }
  const G = g.parse('S -> A b\nA -> a | a a');
  t.ok(P.recursiveDescent(G, 'aab').accepted && !P.recursiveDescent(G, 'aab', { limited: true }).accepted, 'backtracking into a finished call is needed for aab');
  const rd = P.recursiveDescent(G, 'aab');
  t.ok(['call', 'try', 'match', 'mismatch', 'backtrack', 'return', 'accept'].every((k) => rd.trace.some((s) => s.kind === k)), 'descent trace kinds');
  let threw = false; try { P.cyk(G, 'ab'); } catch (e) { threw = true; }
  t.ok(threw, 'CYK refuses a grammar not in CNF unless asked to convert');
  const E = P.earley(g.parse('S -> S S | ε | a'), 'aa');
  t.ok(E.accepted && E.ambiguous, 'Earley: ε plus a cycle, still accepts and sees ambiguity');
  t.ok(P.earley(g.parse('S -> A A A\nA -> ε'), []).accepted, 'Earley: the empty word through nullable chains');
  const cy0 = P.cyk(C.toCNF(g.parse('S -> a S | ε')).grammar, []);
  t.ok(cy0.accepted, 'CYK on the empty word uses S0 → ε');
}

// ---------- FIRST and FOLLOW: worked grammars ----------
{
  const chk = (src, first, follow) => {
    const G = g.parse(src), ff = LL.firstFollow(G);
    for (const A of Object.keys(first)) t.ok(setEq(ff.first.get(A), first[A]), 'FIRST(' + A + ') in ' + src.split('\n')[0] + ': ' + [...ff.first.get(A)]);
    for (const A of Object.keys(follow)) t.ok(setEq(ff.follow.get(A), follow[A]), 'FOLLOW(' + A + ') in ' + src.split('\n')[0] + ': ' + [...ff.follow.get(A)]);
    t.ok(ff.trace.every((s) => s.say && s.kind), 'trace sentences');
    return ff;
  };
  chk('S -> A B c | d\nA -> a A | ε\nB -> b | ε', { S: ['a', 'b', 'c', 'd'], A: ['a', 'ε'], B: ['b', 'ε'] }, { S: ['$'], A: ['b', 'c'], B: ['c'] });
  chk('L -> [ M ]\nM -> I N | ε\nN -> , I N | ε\nI -> x | L', { L: ['['], M: ['x', '[', 'ε'], N: [',', 'ε'], I: ['x', '['] }, { L: ['$', ',', ']'], M: [']'], N: [']'], I: [',', ']'] });
  chk('S -> A B C\nA -> a | ε\nB -> b | ε\nC -> c | ε', { S: ['a', 'b', 'c', 'ε'], A: ['a', 'ε'] }, { A: ['b', 'c', '$'], B: ['c', '$'], C: ['$'] });
  chk('%token go stop\nRun -> Step Run | stop\nStep -> go Turn\nTurn -> l | r | ε', { Run: ['go', 'stop'], Step: ['go'], Turn: ['l', 'r', 'ε'] }, { Run: ['$'], Step: ['go', 'stop'], Turn: ['go', 'stop'] });
  const ff = chk('S -> B S x | y\nB -> ε', { S: ['y'], B: ['ε'] }, { S: ['$', 'x'], B: ['y'] });
  const fo = LL.firstOf(g.parse('S -> B S x | y\nB -> ε'), ['B', 'B', 'x'], ff);
  t.ok(setEq(fo.set, ['x']) && fo.trace.length === 3, 'FIRST of a string walks past nullable symbols');
  t.ok(setEq(LL.firstOf(g.parse('S -> B\nB -> ε'), ['B', 'B']).set, ['ε']), 'FIRST of an all-nullable string has ε');
  const rounds = LL.firstFollow(g.parse('A -> B\nB -> C\nC -> D\nD -> d')).trace.filter((s) => s.kind === 'round' && s.phase === 'first').length;
  t.ok(rounds >= 2, 'fixpoint rounds are traced (' + rounds + ')');
}

// ---------- FIRST and FOLLOW against the definitions, by searching sentential forms ----------
{
  const r = rng(9002);
  const bruteFirst = (G, A) => {
    const out = new Set(), seen = new Set(), q = [[A]];
    while (q.length && seen.size < 20000) {
      const f = q.shift();
      if (!f.length) { out.add('ε'); continue; }
      if (!g.isN(G, f[0])) { out.add(f[0]); continue; }
      for (const p of g.info(G).byA.get(f[0])) { const nf = p.rhs.concat(f.slice(1)); const kk = key(nf); if (nf.length <= 8 && !seen.has(kk)) { seen.add(kk); q.push(nf); } }
    }
    return out;
  };
  const bruteFollow = (G) => {
    const out = new Map(G.nonterminals.map((A) => [A, new Set()])), seen = new Set([G.start]), q = [[G.start]];
    while (q.length && seen.size < 30000) {
      const f = q.shift();
      f.forEach((s, i) => { if (g.isN(G, s)) { if (i === f.length - 1) out.get(s).add('$'); else if (!g.isN(G, f[i + 1])) out.get(s).add(f[i + 1]); } });
      for (const o of g.options(G, f)) { const nf = g.rewrite(G, f, o.prod, o.pos); const kk = key(nf); if (nf.length <= 9 && !seen.has(kk)) { seen.add(kk); q.push(nf); } }
    }
    return out;
  };
  for (let k = 0; k < 120; k++) {
    let G = g.random(r, { nonterminals: 1 + r.int(3), eps: 0.25, maxLen: 3 });
    const reach = C.reachable(G).set;
    G = g.derive(G, G.productions.filter((p) => reach.has(p.A)).map((p) => [p.A, p.rhs]));
    const ff = LL.firstFollow(G), bf = bruteFollow(G);
    for (const A of G.nonterminals) {
      const b = bruteFirst(G, A);
      t.ok([...b].every((x) => ff.first.get(A).has(x)), 'brute FIRST ⊆ FIRST(' + A + ') ' + k);
      t.ok(setEq(b, ff.first.get(A)), 'FIRST(' + A + ') matches the definition ' + k + '\n' + g.toString(G) + ' ' + [...b] + ' / ' + [...ff.first.get(A)]);
      if (!reach.has(A)) continue;
      t.ok(setEq(bf.get(A), ff.follow.get(A)), 'FOLLOW(' + A + ') matches the definition ' + k + '\n' + g.toString(G) + ' ' + [...bf.get(A)] + ' / ' + [...ff.follow.get(A)]);
    }
  }
}

// ---------- LL(1): tables, the predictive parser, recovery, generated code, LL(k) ----------
{
  const r = rng(9003);
  let ll1 = 0, notll1 = 0;
  for (let k = 0; ll1 < 100 && k < 5000; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(3), eps: 0.25, terminals: k % 2 ? ['a', 'b'] : ['a', 'b', 'c'] });
    const tab = LL.ll1Table(G);
    const multi = Object.values(tab.table).some((row) => Object.values(row).some((c) => c.length > 1));
    t.eq(tab.ll1, !multi, 'LL(1) iff no cell holds two rules');
    if (!tab.ll1) {
      if (notll1++ < 100) {
        t.ok(tab.conflicts.every((c) => /FIRST\/(FIRST|FOLLOW)/.test(c.type) && c.say), 'conflicts are explained');
        for (const w of g.language(G, 4)) { const res = LL.predictive(G, w, { table: tab, maxSteps: 400 }); if (res.accepted) t.ok(g.checkTree(G, res.tree), 'first-choice parse still builds a real tree'); }
        if (C.leftRecursive(G).some((x) => g.generatingSet(G).has(x.A) && C.reachable(G).set.has(x.A))) t.ok(!tab.ll1, 'useful left recursion is never LL(1)');
      }
      continue;
    }
    ll1++;
    const n = G.terminals.length > 2 ? 5 : 6, lang = new Set(g.language(G, n).map(key));
    const fn = new Function('tokens', LL.codegen(G).code + '\nreturn parse(tokens);');
    for (const w of g.allWords(G.terminals, n)) {
      const want = lang.has(key(w)), res = LL.predictive(G, w, { table: tab });
      t.ok(res.accepted === want, 'LL(1) parser on ' + g.show(w) + ' ' + k);
      let code; try { code = fn(w); } catch (e) { code = null; }
      t.ok(!!code === want, 'generated descent on ' + g.show(w) + ' ' + k);
      if (want && w.length <= 5) {
        const all = g.parseTrees(G, w, 2);
        t.ok(all.length === 1 && g.treeKey(all[0]) === g.treeKey(res.tree), 'LL(1) tree is the only tree of ' + g.show(w) + ' ' + k);
        t.ok(g.treeKey(code) === g.treeKey(res.tree), 'generated code builds the same tree ' + k);
      }
      if (w.length <= 4) {
        const rec = LL.predictive(G, w, { table: tab, recover: true });
        t.ok(rec.accepted === want && (want ? !rec.errors.length : rec.errors.length > 0), 'panic mode agrees and reports errors ' + k);
      }
    }
    const clean = C.removeUseless(G);
    if (!clean.empty) {
      t.ok(LL.strongLLk(clean.grammar, 1).ok === LL.ll1Table(clean.grammar).ll1, 'strong LL(1) = LL(1) on a clean grammar ' + k);
      t.ok(LL.strongLLk(clean.grammar, 2).ok, 'LL(1) implies strong LL(2) ' + k);
      const f1 = LL.firstK(clean.grammar, 1), ff = LL.firstFollow(clean.grammar);
      for (const A of clean.grammar.nonterminals) t.ok(setEq(f1.sets[A].map((x) => (x.length ? x[0] : 'ε')), ff.first.get(A)), 'FIRST_1 = FIRST on a clean grammar ' + k);
    }
  }
  t.ok(ll1 >= 60, 'enough LL(1) grammars (' + ll1 + ')');
  // hand cases
  const S = g.parse('S -> a b S | a c | d');
  t.ok(!LL.ll1Table(S).ll1 && LL.strongLLk(S, 2).ok, 'needs two symbols of lookahead');
  t.eq(LL.firstK(S, 2).sets.S.map(g.show), ['d', 'ab', 'ac'], 'FIRST_2');
  const D = g.parse('S -> i E t S X | o\nX -> e S | ε\nE -> b');
  const td = LL.ll1Table(D);
  t.ok(td.conflicts.length === 1 && td.conflicts[0].A === 'X' && td.conflicts[0].terminal === 'e' && td.conflicts[0].type === 'FIRST/FOLLOW', 'the optional else clause gives one FIRST/FOLLOW conflict');
  const LR = g.parse('A -> A x | y');
  t.ok(LL.ll1Table(LR).conflicts[0].type === 'FIRST/FIRST', 'left recursion gives a FIRST/FIRST conflict');
  t.ok(LL.ll1Table(C.removeLeftRecursion(LR).grammar).ll1, 'and removing it fixes that');
  // panic mode on a list grammar
  const Lg = g.parse('L -> [ M ]\nM -> I N | ε\nN -> , I N | ε\nI -> x | L');
  const bad = LL.predictive(Lg, '[x,,x]', { recover: true });
  t.ok(!bad.accepted && bad.errors.length >= 1 && bad.trace[bad.trace.length - 1].kind === 'accept', 'recovery reaches the end of [x,,x]');
  t.ok(bad.trace.some((s) => s.kind === 'sync-pop' || s.kind === 'skip' || s.kind === 'pop-terminal'), 'recovery actions traced');
  const bad2 = LL.predictive(Lg, '[x x]', { recover: true });
  t.ok(bad2.errors.length >= 1 && bad2.partialTree.sym === 'L', 'a partial tree survives errors');
  const strict = LL.predictive(Lg, '[x,,x]');
  t.ok(!strict.accepted && strict.trace[strict.trace.length - 1].kind === 'error', 'without recovery the parser stops at the first error');
  const ok = LL.predictive(Lg, '[x,[x],[]]');
  t.ok(ok.accepted && ok.trace.every((s) => Array.isArray(s.stack) && s.action && s.say), 'each step shows stack, input and action');
  const cg = LL.codegen(Lg);
  t.ok(/function parse_L\(\)/.test(cg.code) && cg.lines.some((l) => l.prod !== undefined), 'generated code names functions and marks rules');
}

// ---------- PEG and packrat ----------
{
  const peg = P.parsePEG("Sum <- Num ('+' Num)*\nNum <- [0-9]+ !'.'\n# a comment");
  t.ok(P.packrat(peg, '12+3+45').accepted && !P.packrat(peg, '12+').accepted && !P.packrat(peg, '1.5').accepted, 'a small PEG');
  const pal = g.parse('S -> a S a | b S b | a | b | ε');
  const diff = P.contrastPEG(pal, 6);
  t.ok(diff.length > 0 && diff.every((d) => d.cfg && !d.peg), 'ordered choice loses palindromes the CFG generates');
  t.ok(P.contrastPEG(g.parse('S -> a | a b'), 3).some((d) => g.show(d.word) === 'ab'), 'a | a b: the PEG commits to a');
  const lr = P.packrat(P.parsePEG("E <- E '+' 'n' / 'n'"), 'n+n');
  t.ok(lr.trace.some((s) => s.kind === 'left-recursion') && !lr.accepted, 'left recursion fails in a PEG');
  const m = P.packrat(P.parsePEG("S <- A 'x' / A 'y'\nA <- 'a' A / 'a'"), 'aaay');
  t.ok(m.accepted && m.hits > 0 && m.trace.some((s) => s.kind === 'memo'), 'the second alternative reuses memoised results');
  for (const bad of ["S <- 'a", 'S <- (a', 'S <- B', "S 'a'"]) { let th = false; try { P.parsePEG(bad); } catch (e) { th = true; } t.ok(th, 'PEG syntax error: ' + bad); }
  t.eq(P.showPEG(P.parsePEG("S <- !'a' . / &[bc] ('d' / 'e')* 'f'?").rules.get('S')), "!'a' . / &[bc] ('d' / 'e')* 'f'?", 'PEG prints back');
  // packrat against a plain (unmemoised) PEG interpreter on random grammars read as PEGs
  const naive = (peg0, w) => {
    const ev = (e, i) => {
      switch (e.t) {
        case 'lit': return e.syms.every((s, k) => w[i + k] === s) ? i + e.syms.length : -1;
        case 'seq': { let j = i; for (const x of e.items) { j = ev(x, j); if (j < 0) return -1; } return j; }
        case 'alt': for (const x of e.items) { const j = ev(x, i); if (j >= 0) return j; } return -1;
        case 'not': return ev(e.e, i) >= 0 ? -1 : i;
        case 'ref': return ev(peg0.rules.get(e.name), i);
      }
      throw new Error(e.t);
    };
    return ev(peg0.rules.get(peg0.start), 0);
  };
  const r = rng(9004);
  for (let k = 0; k < 200; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(3), eps: 0.2 });
    if (C.leftRecursive(G).length) continue;
    const peg0 = P.pegFromGrammar(G);
    for (const w of g.allWords(G.terminals, 5)) {
      let a; try { a = naive(peg0, w); } catch (e) { a = 'loop'; }
      if (a === 'loop') continue;
      const res = P.packrat(peg0, w, { full: false });
      t.eq(res.end === null ? -1 : res.end, a, 'packrat = plain PEG on ' + g.show(w) + ' ' + k);
      const calls = res.trace.filter((s) => s.kind === 'call').map((s) => s.rule + '@' + s.pos);
      t.ok(new Set(calls).size === calls.length, 'each rule runs at most once per position ' + k);
    }
  }
}

t.done();
