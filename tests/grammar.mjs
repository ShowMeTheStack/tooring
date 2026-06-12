// Grammars: the text format, the hierarchy, derivations and trees, generation, ambiguity, cleanup and
// normal forms, and regular grammars <-> NFAs. Random grammars are checked against the exact bounded
// language computed by least fixpoint (T.grammar.language).
import { load, rng, harness } from './load.mjs';

const T = load();
const g = T.grammar, c = T.cfg;
const t = harness('grammar');
const K = (w) => w.join('\u0001');
const langSet = (G, n, from) => new Set(g.language(G, n, from).map(K));
const sameSet = (a, b) => a.size === b.size && [...a].every((x) => b.has(x));
const noEps = (s) => new Set([...s].filter((x) => x !== ''));

// ---------- the text format ----------
{
  const G = g.parse('S -> aSb | ε');
  t.eq(G.nonterminals, ['S'], 'compact: nonterminals');
  t.eq(G.terminals, ['a', 'b'], 'compact: terminals');
  t.eq(G.productions.map((p) => p.rhs), [['a', 'S', 'b'], []], 'compact: right sides');
  const H = g.parse('S -> a S b\n  | eps\n# a comment\nS -> c // trailing comment');
  t.eq(H.productions.map((p) => p.rhs), [['a', 'S', 'b'], [], ['c']], 'continuation lines, eps and comments');
  const E = g.parse("%token id\nExpr -> Expr '+' Term | Term\nTerm -> Term * Fac | Fac\nFac -> ( Expr ) | id");
  t.eq(E.nonterminals, ['Expr', 'Term', 'Fac'], 'multi-letter names read whole');
  t.eq(E.terminals, ['+', '*', '(', ')', 'id'], 'quoted and %token terminals');
  t.eq(E.start, 'Expr', 'start is the first left side');
  const W = g.parse('%words\nE -> E plus T | T\nT -> num');
  t.eq(W.terminals, ['plus', 'num'], '%words: every word one symbol');
  const P = g.parse("E -> T E'\nE' -> + T E' | ε\nT -> x");
  t.eq(P.nonterminals, ['E', 'T', "E'"], 'primes are part of names');
  t.eq(P.productions[1].rhs, ['+', 'T', "E'"], 'primes in right sides');
  const A = g.parse('S ::= a S | b\nS → c');
  t.eq(A.productions.length, 3, 'all three arrow forms');
  const St = g.parse('%start B\nA -> a\nB -> A b');
  t.eq(St.start, 'B', '%start');
  const Pr = g.parse("%left '+' '-'\n%left '*'\n%right '^'\n%nonassoc '<'\nE -> E + E | E * E | E ^ E | E < E | - E %prec UMINUS | n");
  t.eq(Pr.precedence['+'], { level: 1, assoc: 'left' }, 'precedence level 1');
  t.eq(Pr.precedence['^'], { level: 3, assoc: 'right' }, 'right associativity');
  t.eq(Pr.precedence['<'].assoc, 'nonassoc', 'nonassoc');
  t.eq(Pr.productions[4].prec, 'UMINUS', '%prec on a rule');
  t.eq(Pr.productions[4].rhs, ['-', 'E'], '%prec removed from the right side');
  const U = g.parse('S -> a B C\nC B -> B C\na B -> a b');
  t.eq(U.productions[1].lhs, ['C', 'B'], 'unrestricted left side');
  t.eq(U.productions[2].lhs, ['a', 'B'], 'unrestricted left side with a terminal');
  t.ok(U.productions[1].A === null, 'non-context-free rule has no single head');
  const Q = g.parse("S -> 'A' S | ε");
  t.eq(Q.terminals, ['A'], 'a quoted capital is a terminal');
  const Dead = g.parse('S -> a B | b');
  t.eq(Dead.nonterminals, ['S', 'B'], 'a capital with no rules is a nonterminal');
  for (const [bad, why] of [['', 'empty'], ['S a b', 'no arrow'], ["S -> 'a", 'unclosed quote'], ['-> a', 'no left side'], ['%bogus x\nS -> a', 'unknown directive'], ['S -> $', 'reserved $'], ["'a' -> b", 'quoted left side']]) {
    const r = g.tryParse(bad);
    t.ok(r.grammar === null && typeof r.error === 'string', 'rejects ' + why);
  }
  t.eq(g.tryParse('S -> a\nS b').line, 2, 'error carries its line');
  t.eq(g.input(E, 'id+id * id'), ['id', '+', 'id', '*', 'id'], 'input read by longest terminal');
  t.eq(g.input(E, ['id']), ['id'], 'input arrays pass through');
}

// ---------- printing round trips ----------
{
  const r = rng(101);
  for (let k = 0; k < 300; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(4), terminals: r() < 0.3 ? ['a', 'b', 'c'] : ['a', 'b'] });
    const s = g.toString(G), H = g.parse(s);
    t.eq(g.toString(H), s, 'round trip ' + k);
    t.ok(sameSet(langSet(G, 5), langSet(H, 5)), 'round trip keeps the language ' + k);
    const C = c.toCNF(G).grammar, CS = g.toString(C);
    t.eq(g.toString(g.parse(CS)), CS, 'CNF prints and reads back ' + k);
    const N = c.toGNF(G).grammar, NS = g.toString(N);
    t.eq(g.toString(g.parse(NS)), NS, 'GNF prints and reads back ' + k);
  }
  const E = g.parse("%token id\n%left '+'\nE -> E + E %prec '+' | '(' E ')' | id | 'A'");
  t.eq(g.toString(g.parse(g.toString(E))), g.toString(E), 'tokens, precedence and quoted capitals round trip');
}

// ---------- the Chomsky hierarchy ----------
{
  const cases = [
    ['S -> a S | b A | ε\nA -> b A | a', 3, true, false],
    ['S -> S a | A b | a\nA -> A b | ε', 3, false, true],
    ['S -> a b S | c', 3, true, false],
    ['S -> a', 3, true, true],
    ['S -> a A\nA -> S b | ε', 2, false, false],             // linear, but mixed sides
    ['S -> a S b | ε', 2, false, false],
    ['S -> S S | ( S ) | ε', 2, false, false],
    ['S -> a B C | a S B C\nC B -> B C\na B -> a b\nb B -> b b\nb C -> b c\nc C -> c c', 1, false, false],
    ['S -> ε | A\nA -> a A b | a b', 2, false, false],
    ['S -> a S B | a\na B -> b', 0, false, false],
    ['S -> A B\nA B -> b', 0, false, false],
  ];
  for (const [src, level, right, left] of cases) {
    const r = g.classify(g.parse(src));
    t.eq(r.level, level, 'level of ' + src.replace(/\n/g, '; '));
    t.eq(r.rightLinear, right, 'right-linear of ' + src.replace(/\n/g, '; '));
    t.eq(r.leftLinear, left, 'left-linear of ' + src.replace(/\n/g, '; '));
    t.ok(r.trace.length === g.parse(src).productions.length + 1 && r.trace.every((s) => typeof s.say === 'string'), 'a step per rule');
  }
  t.ok(g.classify(g.parse('S -> ε | a S b')).monotone === false, 'ε-rule makes a CF grammar non-monotone unless only at the start');
  t.ok(g.classify(g.parse('S -> ε | a A\nA -> a A b | a b')).monotone === true, 'S → ε allowed when S is not on a right side');
  t.ok(g.classify(g.parse('S -> a B C\nC B -> B C')).contextSensitiveForm === false, 'CB → BC is monotone but not in αAβ → αγβ form');
  t.ok(g.classify(g.parse('S -> a B c\na B c -> a b c')).contextSensitiveForm === true, 'a B c → a b c is context-sensitive form');
}

// ---------- generation and the bounded language ----------
{
  const r = rng(202);
  let complete = 0;
  for (let k = 0; k < 150; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(3), eps: 0.1 });
    const n = 5, gen = g.generate(G, n, { budget: 4000 }), L = langSet(G, n);
    const got = new Set(gen.words.map(K));
    t.ok([...got].every((x) => L.has(x)), 'generation finds only words of the language ' + k);
    if (gen.complete) { complete++; t.ok(sameSet(got, L), 'complete generation finds them all ' + k); }
    // brute force membership: every word of the language has a tree, every other word none
    for (const w of g.allWords(G.terminals, 4)) {
      const trees = g.parseTrees(G, w, 1);
      t.eq(trees.length > 0, L.has(K(w)), 'parseTrees agrees with the fixpoint on ' + g.show(w) + ' ' + k);
      if (trees.length) { t.ok(g.checkTree(G, trees[0]), 'tree uses the rules ' + k); t.eq(g.yieldOf(trees[0]), w, 'tree yields the word ' + k); }
    }
  }
  t.ok(complete > 75, 'most bounded searches finish (' + complete + ')');
  // a monotone grammar for a^n b^n c^n (n ≥ 1): exact by form length
  const M = g.parse('S -> a S B C | a B C\nC B -> B C\na B -> a b\nb B -> b b\nb C -> b c\nc C -> c c');
  t.eq(g.classify(M).level, 1, 'swap grammar is monotone');
  const words = g.generate(M, 9, { budget: 200000 });
  t.ok(words.complete, 'monotone search is complete');
  t.eq(words.words.map(g.show), ['abc', 'aabbcc', 'aaabbbccc'], 'a^n b^n c^n up to 9');
  const U = g.parse('S -> a S X | ε\na X -> X a\nS X -> S b');
  t.ok(g.generate(U, 4, { budget: 5000 }).words.every((w) => w.every((x) => x === 'a' || x === 'b')), 'unrestricted search yields terminal words');
  t.eq(g.language(g.parse('S -> a S'), 6), [], 'no terminating derivation: ∅');
  t.eq(g.language(g.parse('S -> ε'), 3).map(g.show), ['ε'], '{ε}');
}

// ---------- derivations and trees ----------
{
  const r = rng(303);
  for (let k = 0; k < 150; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(4), eps: 0.15 });
    for (const w of g.language(G, 5).slice(0, 6)) {
      const tree = g.parseTrees(G, w, 1)[0];
      for (const order of ['leftmost', 'rightmost', 'breadth']) {
        const d = g.derivationOf(G, tree, order);
        t.eq(d.forms[d.forms.length - 1], w, order + ' derivation ends in the word');
        t.eq(d.steps.length, g.treeSize(tree) - g.yieldOf(tree).length - countLeaves(tree), order + ' one step per inner node');
        if (order === 'leftmost') t.ok(d.trace.slice(1).every((s) => s.leftmost), 'leftmost steps are leftmost');
        if (order === 'rightmost') t.ok(d.trace.slice(1).every((s) => s.rightmost), 'rightmost steps are rightmost');
        const back = g.treeOf(G, d.steps);
        t.ok(back.complete && g.treeKey(back.tree) === g.treeKey(tree), order + ' derivation gives back the tree');
        t.eq(g.replay(G, d.steps).forms, d.forms, 'replay gives the same forms');
      }
      // an arbitrary order: always the middle pending nonterminal
      const d = g.derivationOf(G, tree, (idx) => idx[Math.floor(idx.length / 2)]);
      t.ok(g.treeKey(g.treeOf(G, d.steps).tree) === g.treeKey(tree), 'arbitrary order gives the same tree');
    }
  }
  function countLeaves(tr) { return tr.children === null ? 0 : tr.children.length === 0 ? 0 : tr.children.reduce((a, ch) => a + countLeaves(ch), 0); }
  const G = g.parse('S -> a S b | ε');
  t.eq(g.options(G, ['a', 'S', 'b']), [{ prod: 0, pos: 1 }, { prod: 1, pos: 1 }], 'options lists every applicable rule');
  t.eq(g.rewrite(G, ['a', 'S', 'b'], 0, 1), ['a', 'a', 'S', 'b', 'b'], 'rewrite');
  let threw = false; try { g.rewrite(G, ['a'], 0, 0); } catch (e) { threw = true; }
  t.ok(threw, 'rewrite refuses a rule that does not apply');
  const part = g.treeOf(G, [{ prod: 0, pos: 0 }]);
  t.ok(!part.complete, 'a partial derivation gives a partial tree');
}

// ---------- ambiguity ----------
{
  const ambiguous = [
    'E -> E + E | E * E | ( E ) | n',
    'S -> i S | i S e S | x',
    'S -> a S | S a | a',
    'S -> A B | C\nA -> a\nB -> b\nC -> a b',
    'S -> S S | a',
    'S -> A | B\nA -> a A | ε\nB -> a B | ε',
    'S -> A\nA -> S | b',                      // a cycle: infinitely many trees
    'S -> a S b S | b S a S | ε',
  ];
  for (const src of ambiguous) {
    const G = g.parse(src), r = g.ambiguity(G, 6);
    t.ok(r.ambiguous, 'finds ambiguity in ' + src.replace(/\n/g, '; '));
    if (!r.ambiguous) continue;
    t.ok(g.treeKey(r.trees[0]) !== g.treeKey(r.trees[1]), 'the two trees differ');
    for (const tr of r.trees) { t.ok(g.checkTree(G, tr), 'tree uses the rules'); t.eq(g.yieldOf(tr), r.word, 'tree yields the word'); }
    t.ok(r.derivations[0].forms.map(K).join('|') !== r.derivations[1].forms.map(K).join('|'), 'two different leftmost derivations');
    t.ok(T.parse.earley(G, r.word).ambiguous, 'Earley agrees the word is ambiguous');
  }
  const unambiguous = ['S -> a S b | ε', 'S -> ( S ) S | ε', 'E -> E + T | T\nT -> T * F | F\nF -> ( E ) | n', 'S -> a S | b'];
  for (const src of unambiguous) t.ok(!g.ambiguity(g.parse(src), 7).ambiguous, 'no ambiguity in ' + src.replace(/\n/g, '; '));
  const r = rng(404);
  for (let k = 0; k < 150; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(3), eps: 0.15 });
    const a = g.ambiguity(G, 5);
    if (a.ambiguous) t.ok(g.parseTrees(G, a.word, 3).length >= 2, 'random ambiguity confirmed ' + k);
    else for (const w of g.language(G, 5)) t.ok(!T.parse.earley(G, w).ambiguous, 'random: Earley sees one tree too ' + k);
  }
}

// ---------- cleanup ----------
{
  const r = rng(505), n = 6;
  for (let k = 0; k < 250; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(5), eps: 0.2, maxRules: 3 });
    const L = langSet(G, n);
    const U = c.removeUseless(G), UG = U.grammar;
    t.ok(sameSet(langSet(UG, n), L), 'useless removal keeps the language ' + k);
    if (!U.empty) {
      const gen = g.generatingSet(UG), reach = g.reachableSet(UG);
      t.ok(UG.nonterminals.every((A) => gen.has(A) && reach.has(A)), 'every symbol left is useful ' + k);
    }
    if (U.otherOrder) t.ok(U.otherOrder.grammar.nonterminals.length >= UG.nonterminals.length, 'the wrong order never removes more ' + k);
    const nul = c.nullable(G).set;
    for (const A of G.nonterminals) t.eq(nul.has(A), langSet(G, 0, A).has(''), 'nullable(' + A + ') matches ε ∈ L(' + A + ') ' + k);
    const E = c.removeEpsilon(G);
    t.ok(sameSet(langSet(E.grammar, n), L), 'ε-removal keeps the language (ε kept by a start rule) ' + k);
    t.ok(E.grammar.productions.every((p) => p.rhs.length || (p.A === E.grammar.start && !E.grammar.productions.some((q) => q.rhs.includes(p.A)))), 'only the start may have an ε-rule ' + k);
    const E2 = c.removeEpsilon(G, { keepEmpty: false });
    t.ok(sameSet(langSet(E2.grammar, n), noEps(L)), 'ε-removal without keeping ε loses only ε ' + k);
    t.ok(E2.grammar.productions.every((p) => p.rhs.length), 'no ε-rules at all ' + k);
    const Un = c.removeUnit(G);
    t.ok(sameSet(langSet(Un.grammar, n), L), 'unit removal keeps the language ' + k);
    t.ok(Un.grammar.productions.every((p) => !(p.rhs.length === 1 && g.isN(Un.grammar, p.rhs[0]))), 'no unit rules left ' + k);
    for (const [A, B] of Un.pairs) t.ok(A === B || [...langSet(G, 4, B)].every((x) => langSet(G, 4, A).has(x)), 'unit pair (A, B) means L(B) ⊆ L(A) ' + k);
  }
  // the order matters: here reachable-first leaves B behind
  const G = g.parse('S -> a | A B\nA -> b\nB -> B c');
  const U = c.removeUseless(G);
  t.eq(U.grammar.nonterminals, ['S'], 'correct order leaves only S');
  t.eq(U.otherOrder.leftover, ['A'], 'reachable-first would have left A');
  const Empty = c.removeUseless(g.parse('S -> a S | A S\nA -> b'));
  t.ok(Empty.empty && Empty.grammar.productions.length === 0, 'a start symbol that generates nothing: ∅');
}

// ---------- normal forms ----------
{
  const r = rng(606), n = 6;
  for (let k = 0; k < 250; k++) {
    const G = g.random(r, { nonterminals: 1 + r.int(4), eps: 0.2, maxLen: 3 + r.int(2) });
    const L = langSet(G, n);
    const C = c.toCNF(G);
    t.ok(c.isCNF(C.grammar), 'CNF shape ' + k);
    t.ok(sameSet(langSet(C.grammar, n), L), 'CNF keeps the language ' + k);
    t.eq(C.stages.map((s) => s.name), ['START', 'TERM', 'BIN', 'DEL', 'UNIT', 'USELESS'], 'CNF stages in the stated order');
    t.ok(C.trace.every((s) => typeof s.say === 'string' && s.kind), 'CNF trace has sentences ' + k);
    let N;
    try { N = c.toGNF(G); } catch (e) { t.ok(/grew/.test(e.message), 'GNF only fails by size ' + k); continue; }
    t.ok(c.isGNF(N.grammar), 'GNF shape ' + k);
    t.ok(sameSet(langSet(N.grammar, n), L), 'GNF keeps the language ' + k);
    const LR = c.removeLeftRecursion(G);
    t.eq(c.leftRecursive(LR.grammar), [], 'no left recursion left ' + k);
    t.ok(sameSet(langSet(LR.grammar, n), L), 'left-recursion removal keeps the language ' + k);
    const LR2 = c.removeLeftRecursion(G, { epsFree: true });
    t.ok(sameSet(langSet(LR2.grammar, n), L) && !c.leftRecursive(LR2.grammar).length, 'ε-free variant too ' + k);
    const F = c.leftFactor(G);
    t.ok(sameSet(langSet(F.grammar, n), L), 'left factoring keeps the language ' + k);
    for (const A of F.grammar.nonterminals) {
      const firsts = g.info(F.grammar).byA.get(A).filter((p) => p.rhs.length).map((p) => p.rhs[0]);
      t.ok(new Set(firsts).size === firsts.length, 'no two alternatives share a first symbol ' + k);
    }
  }
  // hand cases
  const E = g.parse('E -> E + T | T\nT -> T * F | F\nF -> ( E ) | n');
  const R = c.removeLeftRecursion(E);
  t.eq(g.toString(R.grammar), "E -> T E'\nE' -> + T E' | ε\nT -> F T'\nT' -> * F T' | ε\nF -> ( E ) | n", 'expression grammar without left recursion');
  const ind = g.parse('A -> B a | c\nB -> A b | d');
  t.eq(c.leftRecursive(ind).map((x) => [x.A, x.immediate]), [['A', false], ['B', false]], 'indirect left recursion found');
  t.eq(c.leftRecursive(c.removeLeftRecursion(ind).grammar), [], 'indirect left recursion removed');
  const hidden = g.parse('S -> A S x | y\nA -> ε | z');
  t.eq(c.leftRecursive(hidden).map((x) => x.A), ['S'], 'left recursion hidden behind a nullable symbol');
  t.eq(c.leftRecursive(c.removeLeftRecursion(hidden).grammar), [], 'hidden left recursion removed');
  const im = c.removeImmediate(g.parse('A -> A x | A y | z | w'), 'A');
  t.eq(g.toString(im.grammar), "A -> z A' | w A'\nA' -> x A' | y A' | ε", 'immediate removal of one nonterminal');
  const lf = c.leftFactor(g.parse('S -> i E t S | i E t S e S | a\nE -> b'));
  t.eq(g.toString(lf.grammar), "S -> i E t S S' | a\nS' -> ε | e S\nE -> b", 'left factoring the conditional');
  const cnf = c.toCNF(g.parse('S -> a S b | ε'));
  t.eq(g.toString(cnf.grammar), 'S0 -> ε | T_a S1\nS -> T_a S1\nT_a -> a\nS1 -> S T_b | b\nT_b -> b', 'CNF of a^n b^n');
}

// ---------- regular grammars and NFAs ----------
{
  const r = rng(707), n = 6;
  const linear = (right) => {
    const Ns = ['S', 'A', 'B', 'C'].slice(0, 1 + r.int(4)), prods = [];
    for (const A of Ns) for (let k = 0; k < 1 + r.int(3); k++) {
      const w = Array.from({ length: r.int(3) }, () => r.pick(['a', 'b']));
      const B = r() < 0.6 ? [r.pick(Ns)] : [];
      prods.push([A, right ? w.concat(B) : B.concat(w)]);
    }
    return g.make('S', prods, { nonterminals: Ns, terminals: ['a', 'b'] });
  };
  for (let k = 0; k < 300; k++) {
    const G = linear(true), L = langSet(G, n);
    const M = c.rightLinearToNFA(G).nfa;
    for (const w of g.allWords(['a', 'b'], n)) t.eq(c.nfaAccepts(M, w), L.has(K(w)), 'right-linear → NFA on ' + g.show(w));
    if (T.FA) { const acc = T.FA.acceptor(T.FA.make(M)); for (const w of g.allWords(['a', 'b'], 5)) t.eq(acc(w.join('')), L.has(K(w)), 'the NFA also runs in the automata engine'); }
    const back = c.nfaToRightLinear(M).grammar;
    t.ok(g.classify(back).rightLinear && sameSet(langSet(back, n), L), 'NFA → right-linear keeps the language ' + k);
    const left = c.nfaToLeftLinear(M).grammar;
    t.ok(g.classify(left).leftLinear && sameSet(langSet(left, n), L), 'NFA → left-linear keeps the language ' + k);
    const H = linear(false), LH = langSet(H, n), MH = c.leftLinearToNFA(H).nfa;
    for (const w of g.allWords(['a', 'b'], 5)) t.eq(c.nfaAccepts(MH, w), LH.has(K(w)), 'left-linear → NFA on ' + g.show(w));
  }
  let threw = false; try { c.rightLinearToNFA(g.parse('S -> a S b | ε')); } catch (e) { threw = true; }
  t.ok(threw, 'a non-linear grammar is refused');
}

t.done();
