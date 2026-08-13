// Grammar cleanup and normal forms (part 3). A grammar is drawn as rows of rule chips: a chip glides when its
// rule survives, grows out of the rule it came from, and fades when it is dropped. Useless symbols get two
// status columns (generates? reachable?) and the wrong-order trap side by side; ε-removal expands each rule
// into every way of leaving its nullable symbols out; unit rules become a graph whose paths are the unit
// pairs; Chomsky and Greibach normal forms go stage by stage; left recursion is shown as a tree that leans
// left turning into one that leans right.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;
  const CF = (T.CF = T.CF || {});
  // every stage item of these topics carries the class cf, so the styles in styles-cf.css stay with them
  const topic = (t) => { const run = t.run; t.run = (inp) => CF.mark(run(inp)); return T.topic(t); };
  const Geo = T.geom;

  T.family({ id: 'cfg-clean', part: 'context-free', order: 30, title: 'Cleanup and normal forms', blurb: 'Remove what does nothing (useless symbols, ε-rules, unit rules), then put every rule in a fixed shape: Chomsky and Greibach normal forms, and no left recursion.' });

  const key = CF.ruleKey;
  const pairsOf = (G) => G.productions.map((p) => [p.A, p.rhs]);
  const mk = (G, pairs, start, extra) => T.grammar.make(start || G.start, pairs, { nonterminals: G.nonterminals.concat(extra || []), terminals: G.terminals });
  const has = (G, A, rhs) => G.productions.some((p) => p.A === A && p.rhs.join(' ') === rhs.join(' '));
  const gcheck = (o) => (v) => CF.checkGrammar(v, Object.assign({ maxRules: 14, maxN: 7 }, o || {}));

  // ---- useless symbols -----------------------------------------------------------------------------------------
  const TRAP = 'S → a | A B\nA → a\nB → b B';
  const USELESS = 'S → a S | A | C\nA → a\nB → a a\nC → a C b';
  topic({
    id: 'clean-useless', family: 'cfg-clean', order: 10, title: 'Useless symbols, and the order that matters',
    blurb: 'A symbol is useful only if it generates some terminal string and the start symbol can reach it. Remove the non-generating ones first, then the unreachable ones; the other order can leave junk behind.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: TRAP, check: gcheck() }],
    presets: [
      { label: 'The wrong-order trap', values: { g: TRAP } },
      { label: 'Some of each', values: { g: USELESS } },
      { label: 'Nothing to remove', values: { g: 'S → a S b | ε' } },
      { label: 'The empty language ∅', values: { g: 'S → a S | A S\nA → a' } },
    ],
    counters: [{ id: 'gen', label: 'generating' }, { id: 'reach', label: 'reachable' }, { id: 'rules', label: 'rules left' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const r = T.cfg.removeUseless(G);
      const F = new T.Frames(['gen', 'reach', 'rules']);
      const gen = {}, reach = {};
      const G1 = r.empty ? null : mk(G, G.productions.filter((p) => [p.A, ...p.rhs].every((s) => !CF.isN(G, s) || r.generating.includes(s))).map((p) => [p.A, p.rhs]));
      let cur = G, hot = null, drop = new Set();
      const scene = (extra) => {
        const d = CF.rules(cur, { prefix: 'g', order: G.nonterminals, keepEmpty: true, cols: [
          { head: 'generates?', text: (A) => gen[A], cls: (A) => (gen[A] === '✓' ? 'good' : gen[A] === '✗' ? 'bad' : '') },
          { head: 'reachable?', text: (A) => reach[A], cls: (A) => (reach[A] === '✓' ? 'good' : reach[A] === '✗' ? 'bad' : '') }],
          cls: (A, rhs) => (hot === key(A, rhs) ? 'hot' : drop.has(key(A, rhs)) ? 'drop' : ''), lhsCls: (A) => (gen[A] === '✗' || reach[A] === '✗' ? 'drop' : '') });
        return d.items.concat(extra ? extra(d) : []);
      };
      F.set('rules', G.productions.length);
      F.add({ items: scene(), say: 'Two questions for every nonterminal: does it generate some string of terminals, and can the start symbol ' + G.start + ' reach it? First the generating ones, in rounds: a rule whose right side is all terminals or generating symbols makes its left side generating.' });
      for (const s of r.trace) {
        if (s.kind === 'generating') { gen[s.A] = '✓'; hot = key(s.A, G.productions[s.prod].rhs); F.count('gen'); F.add({ items: scene(), say: s.say, hl: { g: [s.prod] } }); }
        else if (s.kind === 'drop' && s.phase === 'generating') {
          hot = null;
          for (const A of G.nonterminals) if (!gen[A]) gen[A] = '✗';
          drop = new Set(s.prods.map((id) => key(G.productions[id].A, G.productions[id].rhs)));
          F.add({ items: scene(), say: s.say + (s.prods.length ? ' A rule that mentions a non-generating symbol can never finish a derivation.' : ''), hl: { g: s.prods } });
          drop = new Set();
          if (G1) { cur = G1; F.set('rules', G1.productions.length); F.add({ items: scene(), say: 'What is left: ' + G1.productions.length + ' rule' + (G1.productions.length === 1 ? '' : 's') + '. Now the second question, in this smaller grammar.' }); }
        } else if (s.kind === 'empty') {
          F.add({ items: scene(), say: s.say + ' Every rule goes: no derivation from ' + G.start + ' ever ends.', mark: 'empty language' });
        } else if (s.kind === 'reach') {
          reach[s.A] = '✓'; F.count('reach');
          hot = s.prod === null ? null : key(G1.productions[s.prod].A, G1.productions[s.prod].rhs);
          F.add({ items: scene(), say: s.say });
        } else if (s.kind === 'drop' && s.phase === 'reachable') {
          hot = null;
          for (const A of G.nonterminals) if (!reach[A] && gen[A] === '✓') reach[A] = '✗';
          drop = new Set(s.prods.map((id) => key(G1.productions[id].A, G1.productions[id].rhs)));
          F.add({ items: scene(), say: s.say });
          drop = new Set(); cur = r.grammar; F.set('rules', r.grammar.productions.length);
          F.add({ items: scene(), say: 'The clean grammar: ' + r.grammar.productions.map((p) => CF.prod(r.grammar, p)).join(', ') + '. Same language, nothing idle.', meta: { clean: true } });
        } else if (s.kind === 'order') {
          const other = r.otherOrder.grammar, left = new Set(r.otherOrder.leftover);
          const extra = (d) => {
            const x = d.box.x + Math.max(d.box.w, 360) + 90;
            const o = CF.rules(other, { prefix: 'w', x, y: d.box.y + 18, title: 'the other order', lhsCls: (A) => (left.has(A) ? 'drop' : ''), cls: (A) => (left.has(A) ? 'bad' : '') });
            return o.items;
          };
          F.add({ items: scene(extra), say: s.say, mark: left.size ? 'trap' : undefined, meta: { left: [...left].map((A) => 'w:l:' + A) } });
        }
      }
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), { id: 'why', kind: 'text', title: 'Why this order', text: 'Removing non-generating symbols deletes rules, and a symbol that was reachable only through those rules becomes unreachable. Reachability must therefore be computed on what is left. The other way round, nothing that the second pass removes can make a symbol stop generating, so one round each, in this order, is enough.' }] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.left && fr[i + 1].meta.left.length, once: true, pick: 'option', options: ['The same clean grammar', 'Some useless symbol stays behind'], ask: 'What if we had removed unreachable symbols first, then non-generating ones?', answer: () => 'Some useless symbol stays behind', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i) => i === 0, once: true, pick: 'item', ask: 'Click a nonterminal that will turn out not to generate anything.', answer: (fr) => { const last = fr.filter((f) => f.items.some((it) => it.key && it.key.startsWith('g:cc:0:') && it.text === '✗')); const f = last[0]; return f ? f.items.filter((it) => it.key.startsWith('g:cc:0:') && it.text === '✗').map((it) => 'g:l:' + it.key.slice(7)) : null; }, explain: 'A nonterminal generates nothing when every one of its rules needs a symbol that generates nothing, often itself.' },
    ],
    quiz: [
      { q: 'B → b B is the only rule for B. Is B generating?', options: ['No: every derivation from B still contains B', 'Yes, it makes b', 'Only if B is reachable', 'Yes, it makes ε'], answer: 0, why: 'The rule always puts B back, so no string of terminals ever comes out.' },
      { q: 'Why find the non-generating symbols before the unreachable ones?', options: ['Deleting rules can make more symbols unreachable', 'It is faster', 'Reachability needs generating symbols', 'The order does not matter'], answer: 0, why: 'In S → a | A B, A → a, B → b B, dropping B kills S → A B and leaves A unreachable.' },
      { q: 'The start symbol does not generate. The language is…', options: ['empty, ∅', '{ε}', 'infinite', 'regular but not empty'], answer: 0, why: 'No derivation from the start ever finishes.' },
      { q: 'After removing useless symbols, the language…', options: ['is unchanged', 'shrinks', 'loses ε', 'grows'], answer: 0, why: 'A useless symbol takes part in no complete derivation, so nothing is lost.' },
    ],
  });

  // ---- ε-rules -------------------------------------------------------------------------------------------------
  const EPS1 = 'S → A b A\nA → a A | ε';
  const EPS2 = 'S → A B | a\nA → a A | ε\nB → b | ε';
  topic({
    id: 'clean-eps', family: 'cfg-clean', order: 20, title: 'Removing ε-rules: every way of leaving out',
    blurb: 'Find the nullable nonterminals, then replace each rule by all its versions with nullable symbols left in or out. Watch a rule with k nullable symbols fan out into up to 2ᵏ rules.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: EPS1, check: gcheck() }],
    presets: [
      { label: 'Two nullable A in one rule', values: { g: EPS1 } },
      { label: 'ε in the language', values: { g: EPS2 } },
      { label: 'A chain of nullables', values: { g: 'S → a B C\nB → C C | b\nC → c | ε' } },
      { label: 'Nothing nullable', values: { g: 'S → a S b | a b' } },
    ],
    counters: [{ id: 'nullable', label: 'nullable' }, { id: 'rules', label: 'rules' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const r = T.cfg.removeEpsilon(G, { keepEmpty: true });
      const F = new T.Frames(['nullable', 'rules']);
      const nul = {};
      let work = pairsOf(G);
      let hot = null, from = {}, bench = null;
      const cur = () => mk(G, work, G.start);
      const scene = () => {
        const g = cur();
        const d = CF.rules(g, { prefix: 'g', order: G.nonterminals.concat(r.grammar.nonterminals), cols: [{ head: 'nullable?', text: (A) => nul[A], cls: (A) => (nul[A] === '✓' ? 'good' : '') }], cls: (A, rhs) => (hot === key(A, rhs) ? 'hot' : from[key(A, rhs)] ? 'new' : ''), from });
        const items = d.items;
        if (bench) {
          const x0 = d.box.x + Math.max(d.box.w, 380) + 80;
          let y = d.box.y + 4;
          items.push({ key: 'b:title', kind: 'text', x: x0, y: y - 8, text: 'keep or drop', cls: 'title' });
          y += 10;
          bench.rows.forEach((row, k) => {
            let x = x0;
            row.syms.forEach((s, i) => {
              const w = Math.max(36, Geo.textWidth(s, 16, { mono: true }) + 16);
              items.push({ key: 'b:' + k + ':' + i, kind: 'cell', x, y, w, h: 36, text: s, cls: 'mono ' + (CF.isN(G, s) ? 'nt' : 't') + (row.out.has(i) ? ' gone' : bench.pos.includes(i) ? ' act' : '') });
              x += w;
            });
            if (!row.syms.length) { items.push({ key: 'b:' + k + ':e', kind: 'cell', x, y, w: 40, h: 36, text: 'ε', cls: 'mono empty' }); x += 40; }
            items.push({ key: 'b:' + k + ':v', kind: 'text', x: x + 14, y: y + 23, text: row.note, cls: row.ok ? 'good' : 'bad' });
            y += 44;
          });
        }
        return items;
      };
      F.set('rules', G.productions.length);
      F.add({ items: scene(), say: 'A nonterminal is nullable when it can derive ε. Find them in rounds: an ε-rule makes its left side nullable, and so does a rule whose right side is all nullable.' });
      for (const s of r.trace) {
        if (s.kind === 'nullable') { nul[s.A] = '✓'; hot = key(s.A, G.productions[s.prod].rhs); F.count('nullable'); F.add({ items: scene(), say: s.say, hl: { g: [s.prod] } }); }
        else if (s.kind === 'round' && !s.added.length) { hot = null; F.add({ items: scene(), say: s.say + ' Now rewrite the rules one at a time.', meta: { nul: s.set.length } }); }
        else if (s.kind === 'expand') {
          const p = G.productions[s.prod];
          const pos = s.nullablePositions, rows = [];
          const seen = new Set();
          for (let mask = 0; mask < 1 << pos.length; mask++) {
            const out = new Set(pos.filter((_, j) => mask & (1 << j)));
            const rhs = p.rhs.filter((_, i) => !out.has(i));
            const kk = rhs.join(' ');
            const note = !rhs.length ? 'all gone: ε, dropped' : rhs.length === 1 && rhs[0] === p.A ? p.A + ' → ' + p.A + ' says nothing' : seen.has(kk) ? 'a duplicate' : '→ ' + p.A + ' → ' + CF.rhs(G, rhs);
            const ok = rhs.length && !(rhs.length === 1 && rhs[0] === p.A) && !seen.has(kk);
            seen.add(kk);
            rows.push({ syms: p.rhs, out, ok, note });
          }
          bench = { pos, rows };
          hot = key(p.A, p.rhs);
          F.add({ items: scene(), say: CF.prod(G, p) + ' has ' + pos.length + ' nullable position' + (pos.length === 1 ? '' : 's') + ', so ' + (1 << pos.length) + ' ways to keep or drop them. Struck-out symbols are the ones left out this time.', hl: { g: [s.prod] }, meta: { k: pos.length, kept: s.variants.length } });
          // replace the rule by its variants
          const i = work.findIndex((x) => x[0] === p.A && x[1].join(' ') === p.rhs.join(' '));
          from = {};
          for (const v of s.variants) if (v.join(' ') !== p.rhs.join(' ')) from[key(p.A, v)] = 'g:c:' + key(p.A, p.rhs);
          work.splice(i, 1, ...s.variants.map((v) => [p.A, v]));
          work = work.filter((x, j) => work.findIndex((y) => y[0] === x[0] && y[1].join(' ') === x[1].join(' ')) === j);
          hot = null; F.set('rules', work.length);
          F.add({ items: scene(), say: s.say, hl: { g: [s.prod] } });
          from = {}; bench = null;
        } else if (s.kind === 'drop') {
          const p = G.productions[s.prod];
          hot = key(p.A, p.rhs);
          F.add({ items: scene(), say: s.say + ' Every use of it is already covered by a version that leaves ' + p.A + ' out.' });
          work = work.filter((x) => !(x[0] === p.A && !x[1].length)); hot = null; F.set('rules', work.length);
        } else if (s.kind === 'start' || s.kind === 'lose') {
          work = pairsOf(r.grammar); F.set('rules', work.length);
          F.add({ items: scene(), say: s.say });
        }
      }
      work = pairsOf(r.grammar); bench = null; hot = null; F.set('rules', work.length);
      const g2 = r.grammar;
      F.add({ items: CF.rules(g2, { prefix: 'g', order: G.nonterminals.concat(g2.nonterminals), cols: [{ head: 'nullable?', text: (A) => nul[A], cls: (A) => (nul[A] === '✓' ? 'good' : '') }] }).items, say: 'Done: ' + g2.productions.length + ' rules, ' + (r.emptyInLanguage ? 'and ε only from the start symbol, the one place it is allowed.' : 'and no ε-rules at all. The language is the same, since ε was never in it.') });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), CF.gsec(g2, 'g2', 'Without ε-rules')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.k !== undefined && f.meta.k >= 2, once: true, pick: 'option', options: ['1', '2', '3', '4'], ask: 'How many new rules will this one rule become (after dropping ε and duplicates)?', answer: (fr, i) => String(fr[i].meta.kept), explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.nul !== undefined, once: true, pick: 'option', options: ['0', '1', '2', '3'], ask: 'How many nonterminals did the rounds find nullable?', answer: (fr, i) => String(Math.min(3, fr[i].meta.nul)), explain: (fr, i) => fr[i].say },
    ],
    quiz: [
      { q: 'In B → C C | b, C → c | ε, is B nullable?', options: ['Yes: B → C C and C is nullable', 'No, B has no ε-rule', 'Only if b is nullable', 'Only in the second round'], answer: 0, why: 'A rule whose right side is all nullable makes its left side nullable, without an ε-rule of its own.' },
      { q: 'A rule has 3 nullable symbols. At most how many versions does it get?', options: ['8', '3', '6', '4'], answer: 0, why: 'Each nullable occurrence is kept or dropped: 2³ = 8 (minus the all-dropped one if it is ε).' },
      { q: 'S is nullable and appears on a right side. How is ε kept in the language?', options: ['A new start S0 → S | ε', 'Keep S → ε', 'It cannot be kept', 'Add ε to every rule'], answer: 0, why: 'Only a start symbol that never appears on a right side may have an ε-rule.' },
      { q: 'Why drop a version like A → A?', options: ['It changes nothing and only makes cycles', 'It is not context-free', 'It makes the grammar ambiguous only', 'It removes ε'], answer: 0, why: 'A → A rewrites A into itself: no new words, only loops.' },
    ],
  });

  // ---- unit rules ----------------------------------------------------------------------------------------------
  const UNIT1 = 'E → E + T | T\nT → T * F | F\nF → ( E ) | x';
  const UNIT2 = 'S → A | a S\nA → B | b\nB → S | c';
  topic({
    id: 'clean-unit', family: 'cfg-clean', order: 30, title: 'Unit rules and unit pairs',
    blurb: 'A unit rule A → B only renames. Draw the unit rules as a graph: every path A ⇒* B is a unit pair, and A simply takes over B\'s real rules.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: UNIT1, check: gcheck() }],
    presets: [
      { label: 'An expression grammar', values: { g: UNIT1 } },
      { label: 'A unit cycle', values: { g: UNIT2 } },
      { label: 'No unit rules', values: { g: 'S → a S b | a b' } },
    ],
    counters: [{ id: 'pairs', label: 'unit pairs' }, { id: 'rules', label: 'rules' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const r = T.cfg.removeUnit(G);
      const F = new T.Frames(['pairs', 'rules']);
      const units = G.productions.filter((p) => p.rhs.length === 1 && CF.isN(G, p.rhs[0]));
      const m = { kind: 'pda', states: G.nonterminals.slice(), start: G.start, accept: [], trans: units.map((p) => ({ from: p.A, to: p.rhs[0], label: '' })) };
      const pos = K.graph.layout(m, { gapX: 120, gapY: 100 }).pos;
      let pairs = G.nonterminals.map((A) => [A, A]);
      let work = pairsOf(G), from = {}, hotE = [], hotS = [], dropU = false;
      const scene = (lit) => {
        const g = K.graph.draw(m, { pos, hideStart: true, taken: hotE, hot: hotS, prefix: 'u' });
        const items = g.items;
        const gb = g.box;
        // the unit pairs found so far, as chips under the graph
        let x = gb.x, y = gb.y + gb.h + 50;
        items.push({ key: 'p:title', kind: 'text', x, y: y - 12, text: 'unit pairs', cls: 'title' });
        pairs.forEach(([A, B]) => {
          const t = '(' + A + ', ' + B + ')';
          const w = Geo.textWidth(t, 15, { mono: true }) + 20;
          if (x + w > gb.x + Math.max(gb.w, 260)) { x = gb.x; y += 44; }
          items.push({ key: 'p:' + A + ',' + B, kind: 'cell', x, y, w, h: 36, text: t, cls: 'mono chip' + (lit && lit[0] === A && lit[1] === B ? ' hot' : A === B ? ' read' : '') });
          x += w + 8;
        });
        const rx = gb.x + Math.max(gb.w, 260) + 90;
        const d = CF.rules(mk(G, work), { prefix: 'g', x: rx, y: gb.y, order: G.nonterminals, from, cls: (A, rhs) => (from[key(A, rhs)] ? 'new' : dropU && rhs.length === 1 && CF.isN(G, rhs[0]) ? 'drop' : '') });
        return items.concat(d.items);
      };
      F.set('rules', G.productions.length);
      F.add({ items: scene(), say: units.length ? 'The unit rules, ' + units.map((p) => CF.prod(G, p)).join(', ') + ', drawn as arrows between nonterminals. Every (A, A) is a unit pair to begin with.' : 'This grammar has no unit rules: the graph has no arrows, and only the trivial pairs (A, A) exist.' });
      for (const s of r.trace) {
        if (s.kind === 'pair') {
          pairs.push([s.A, s.B]); F.count('pairs');
          const via = G.productions[s.via];
          hotE = [via.A + '>' + via.rhs[0]]; hotS = [s.A, s.B];
          F.add({ items: scene([s.A, s.B]), say: s.say + ' Following arrows from ' + s.A + ' reaches ' + s.B + '.', hl: { g: [s.via] }, meta: { pairs: pairs.length } });
        } else if (s.kind === 'copy') {
          hotE = []; hotS = [s.A, s.B];
          from = {};
          for (const rhs of s.rules) if (!has(mk(G, work), s.A, rhs)) { from[key(s.A, rhs)] = 'g:c:' + key(s.B, rhs); work.push([s.A, rhs]); }
          F.set('rules', work.length);
          F.add({ items: scene(), say: s.say });
          from = {};
        } else if (s.kind === 'drop') {
          hotS = []; hotE = [];
          if (s.prods.length) { dropU = true; F.add({ items: scene(), say: s.say + ' Each one is now redundant: whatever it led to was copied up.', hl: { g: s.prods } }); dropU = false; }
        }
      }
      work = pairsOf(r.grammar); F.set('rules', work.length);
      F.add({ items: scene(), say: 'No unit rules are left: ' + r.grammar.productions.length + ' rules, the same language, and every step of a derivation now adds a terminal or makes the form longer.' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), CF.gsec(r.grammar, 'g2', 'Without unit rules')] } };
    },
    predict: [
      { at: (f, i, fr) => i === 0 && fr.some((x) => x.meta && x.meta.pairs), once: true, pick: 'option', options: ['1', '2', '3', '4', '5', '6'], ask: 'How many non-trivial unit pairs (A, B) with A ≠ B will there be?', answer: (fr) => { const n = fr.filter((x) => x.meta && x.meta.pairs).length; return String(Math.min(6, n)); }, explain: 'Each pair is a path of unit arrows; a cycle makes every member reach every other.' },
    ],
    quiz: [
      { q: 'E → T, T → F are unit rules. Which unit pairs start at E?', options: ['(E, E), (E, T), (E, F)', 'only (E, T)', '(E, F) only', 'none'], answer: 0, why: 'Unit pairs follow paths: E reaches T directly and F through T.' },
      { q: 'After the pair (E, F) is found, what does E get?', options: ['Copies of F\'s non-unit rules', 'The rule E → F', 'Nothing', 'F\'s unit rules'], answer: 0, why: 'E could reach F by renaming, so E may use F\'s real rules directly.' },
      { q: 'A cycle S → A, A → B, B → S makes…', options: ['all of S, A, B unit pairs of each other', 'the grammar invalid', 'no pairs', 'an ε-rule'], answer: 0, why: 'Around a cycle every nonterminal reaches every other.' },
      { q: 'Why remove ε-rules before unit rules in the CNF recipe?', options: ['Removing ε-rules can create new unit rules', 'It is alphabetical', 'Unit removal creates ε-rules', 'It does not matter'], answer: 0, why: 'A → B C with C nullable gives A → B.' },
    ],
  });

  // ---- Chomsky normal form -------------------------------------------------------------------------------------
  const STAGES = ['START', 'TERM', 'BIN', 'DEL', 'UNIT', 'USELESS'];
  const STAGE_SAY = {
    START: 'START: a new start symbol, so the start never appears on a right side.',
    TERM: 'TERM: inside a right side of two or more symbols, each terminal gets a nonterminal of its own.',
    BIN: 'BIN: a right side longer than two is split into a chain of pairs.',
    DEL: 'DEL: remove ε-rules, keeping every way of leaving nullable symbols out.',
    UNIT: 'UNIT: remove unit rules, copying the rules they led to.',
    USELESS: 'Finally drop anything useless the earlier stages left behind.',
  };
  const CNF1 = 'S → a S b | A\nA → c A | ε';
  topic({
    id: 'cnf', family: 'cfg-clean', order: 40, title: 'Chomsky normal form, stage by stage',
    blurb: 'START, TERM, BIN, DEL, UNIT: five small rewrites, each keeping the language, after which every rule is A → B C or A → a.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: CNF1, check: gcheck({ maxRules: 9, maxN: 5 }) }],
    presets: [
      { label: 'aⁿcᵐbⁿ', values: { g: CNF1 } },
      { label: 'Expressions', values: { g: 'E → E + T | T\nT → ( E ) | x' } },
      { label: 'Long rule', values: { g: 'S → a B c D | b\nB → b\nD → d' } },
      { label: 'Already in CNF', values: { g: 'S → A B | a\nA → a\nB → b' } },
    ],
    check: (inp) => { const G = CF.grammar(inp.g); try { if (T.cfg.toCNF(G).grammar.productions.length > 30) return 'Grammar: its normal form would have more than 30 rules; try a smaller grammar'; } catch (e) { return 'Grammar: ' + e.message; } return null; },
    counters: [{ id: 'rules', label: 'rules' }, { id: 'nts', label: 'nonterminals' }, { id: 'bad', label: 'rules not yet in CNF' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const res = T.cfg.toCNF(G);
      const F = new T.Frames(['rules', 'nts', 'bad']);
      const okRule = (g, p) => (p.rhs.length === 2 && p.rhs.every((s) => CF.isN(g, s)) && !p.rhs.includes(g.start)) || (p.rhs.length === 1 && !CF.isN(g, p.rhs[0])) || (p.rhs.length === 0 && p.A === g.start);
      const order = [];
      const addOrder = (g) => { for (const A of g.nonterminals) if (!order.includes(A)) order.push(A); };
      addOrder(G);
      const scene = (g, k, o) => {
        o = o || {};
        const items = [];
        let x = 0;
        STAGES.forEach((s, i) => {
          const w = Geo.textWidth(s, 13, { bold: true }) + 28;
          items.push({ key: 'st:' + s, kind: 'cell', x, y: 0, w, h: 32, text: s, cls: 'stage' + (i === k ? ' hot' : i < k ? ' done' : '') });
          x += w + 8;
        });
        addOrder(g);
        const d = CF.rules(g, { prefix: 'g', y: 64, order: order.filter((A) => g.nonterminals.includes(A)), maxW: 640, from: o.from, cls: (A, rhs) => (o.lit && o.lit.has(key(A, rhs)) ? 'hot' : o.from && o.from[key(A, rhs)] ? 'new' : o.mark && !okRule(g, { A, rhs }) ? 'lead-n' : '') });
        return items.concat(d.items);
      };
      const stat = (g) => F.set('rules', g.productions.length).set('nts', g.nonterminals.length).set('bad', g.productions.filter((p) => !okRule(g, p)).length);
      stat(G);
      F.add({ items: scene(G, -1, { mark: true }), say: 'The goal: every rule is A → B C (two nonterminals, neither the start) or A → a, with S → ε allowed only for the start. Dashed chips are the rules not in that shape yet: ' + F.counts.bad + '.' });
      let prev = G;
      res.stages.forEach((st, k) => {
        const g = st.grammar;
        const before = CF.ruleSet(prev), after = CF.ruleSet(g);
        const gone = new Set([...before].filter((x) => !after.has(x)));
        const born = [...after].filter((x) => !before.has(x));
        const from = {};
        for (const b of born) { const A = b.split('→')[0]; const src = [...gone].find((x) => x.split('→')[0] === A); from[b] = src ? 'g:c:' + src : 'g:l:' + A; }
        if (gone.size) F.add({ items: scene(prev, k, { lit: gone }), say: STAGE_SAY[st.name] + ' The lit rules are about to change.', meta: { stage: st.name, unit: st.name === 'UNIT' ? [...gone].map((x) => 'g:c:' + x) : null, bin: st.name === 'BIN' ? g.nonterminals.length - prev.nonterminals.length : null } });
        const says = st.trace.filter((s) => !['phase', 'round', 'nullable', 'pair', 'generating', 'reach'].includes(s.kind)).map((s) => s.say);
        stat(g);
        F.add({ items: scene(g, k, { from, mark: true }), say: (gone.size ? '' : STAGE_SAY[st.name] + ' ') + (says.slice(0, 3).join(' ') || 'Nothing changes.') + (says.length > 3 ? ' (and ' + (says.length - 3) + ' more like it)' : '') + ' Now ' + F.counts.bad + ' rule' + (F.counts.bad === 1 ? '' : 's') + ' still out of shape.', hl: { cnf: [] } });
        prev = g;
      });
      F.add({ items: scene(res.grammar, STAGES.length), say: res.trace[res.trace.length - 1].say + ' ' + G.productions.length + ' rules became ' + res.grammar.productions.length + '. Every parse tree is now binary, which is what CYK and the pumping lemma need.', mark: 'CNF' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), CF.gsec(res.grammar, 'cnf', 'Chomsky normal form')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.unit && f.meta.unit.length, once: true, pick: 'item', ask: 'UNIT is next. Click a rule it will remove.', answer: (fr, i) => fr[i].meta.unit, explain: (fr, i) => fr[i + 1].say },
      { at: (f) => f.meta && f.meta.bin !== null && f.meta.bin !== undefined, once: true, pick: 'option', options: ['0', '1', '2', '3'], ask: 'How many new nonterminals will BIN add?', answer: (fr, i) => String(Math.min(3, fr[i].meta.bin)), explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Which rule is in Chomsky normal form?', options: ['A → B C', 'A → a B', 'A → B', 'A → a b'], answer: 0, why: 'Only A → B C and A → a (and S → ε for the start).' },
      { q: 'BIN splits A → X Y Z into…', options: ['A → X A1, A1 → Y Z', 'A → X Y, A → Z', 'A → X, A → Y Z', 'A → X Y Z stays'], answer: 0, why: 'A chain of fresh nonterminals, two symbols per rule.' },
      { q: 'Why is DEL done after BIN?', options: ['So leaving out nullable symbols does not multiply long rules', 'Because DEL needs short rules to work at all', 'It must come first', 'Alphabetical order'], answer: 0, why: 'A rule of length k with k nullable symbols has 2ᵏ versions; on pairs that is at most 4.' },
      { q: 'A CNF parse tree of a word of length n ≥ 1 has how many internal nodes?', options: ['2n − 1', 'n', 'n²', '2n + 1'], answer: 0, why: 'n − 1 binary nodes plus n nodes A → a.' },
      { q: 'Why add a new start symbol first?', options: ['So the start is never on a right side, and S → ε can stay if ε is in the language', 'To make the grammar unambiguous', 'To remove left recursion', 'It is not needed'], answer: 0, why: 'S → ε is only harmless when S cannot appear inside a derivation.' },
    ],
  });

  // ---- Greibach normal form ------------------------------------------------------------------------------------
  /** Greibach normal form, step by step, keeping a snapshot of all rules after each step */
  function gnfSteps(G0) {
    const snaps = [];
    const e = T.cfg.removeEpsilon(G0, { keepEmpty: false }), u = T.cfg.removeUnit(e.grammar), c = T.cfg.removeUseless(u.grammar);
    const H = c.grammar;
    const order = H.nonterminals.slice(), N = new Set(order), used = new Set(H.nonterminals.concat(H.terminals));
    const rules = new Map(order.map((A) => [A, H.productions.filter((p) => p.A === A).map((p) => p.rhs.slice())]));
    const dd = (rs) => { const s = new Set(); return rs.filter((r) => { const k = r.join(' '); if (s.has(k)) return false; s.add(k); return true; }); };
    const snap = (kind, A, say) => snaps.push({ kind, A, say, rules: new Map([...rules].map(([k, v]) => [k, v.map((r) => r.slice())])) });
    snap('prepare', null, 'First clean up: no ε-rules, no unit rules, no useless symbols. Then number the nonterminals ' + order.map((A, i) => A + '=' + (i + 1)).join(', ') + '. The plan: make every rule start with a terminal or a higher-numbered nonterminal, then substitute back from the top.');
    const fresh = (A) => { for (const c2 of [A + "'", A + "''"]) if (!used.has(c2)) { used.add(c2); return c2; } let i = 1; while (used.has(A + i)) i++; used.add(A + i); return A + i; };
    for (let i = 0; i < order.length; i++) {
      const Ai = order[i];
      for (let j = 0; j < i; j++) {
        const Aj = order[j], next = []; let did = false;
        for (const r of rules.get(Ai)) { if (r[0] === Aj) { did = true; for (const d of rules.get(Aj)) next.push(d.concat(r.slice(1))); } else next.push(r); }
        if (did) { rules.set(Ai, dd(next)); snap('substitute', Ai, Ai + ' had a rule starting with the lower ' + Aj + ': replace that ' + Aj + ' by each of its right sides.'); }
      }
      const alphas = rules.get(Ai).filter((r) => r[0] === Ai).map((r) => r.slice(1)), betas = rules.get(Ai).filter((r) => r[0] !== Ai);
      if (alphas.length) {
        const B = fresh(Ai); N.add(B);
        rules.set(Ai, dd(betas.flatMap((b) => [b, b.concat([B])])));
        rules.set(B, dd(alphas.flatMap((a) => [a, a.concat([B])])));
        snap('immediate', Ai, Ai + ' → ' + Ai + ' … is left-recursive: write ' + Ai + ' → β | β ' + B + ' and ' + B + ' → α | α ' + B + ', so the repetition grows on the right instead.');
      }
    }
    const lead = (A) => rules.get(A).every((r) => !N.has(r[0]));
    const sub = (A) => { const next = []; let did = false; for (const r of rules.get(A)) { if (N.has(r[0])) { did = true; for (const d of rules.get(r[0])) next.push(d.concat(r.slice(1))); } else next.push(r); } if (did) { rules.set(A, dd(next)); snap('back', A, 'Substitute back into ' + A + ': the nonterminal it started with already starts with a terminal, so put its right sides in front.'); } };
    for (let i = order.length - 1; i >= 0; i--) sub(order[i]);
    for (const B of [...N].filter((x) => !order.includes(x))) { let g = 0; while (!lead(B) && g++ < 20) sub(B); }
    const tn = new Map();
    for (const [A, rs] of rules) rules.set(A, rs.map((r) => r.map((s, i) => { if (i === 0 || N.has(s)) return s; if (!tn.has(s)) { let X = 'T_' + s; if (!/^[a-z0-9]+$/.test(s) || used.has(X)) X = fresh('T'); used.add(X); tn.set(s, X); } return tn.get(s); })));
    for (const [t, X] of tn) { rules.set(X, [[t]]); N.add(X); }
    if (tn.size) snap('term', null, 'Last, a terminal after the first position gets a nonterminal of its own: ' + [...tn].map(([t, X]) => X + ' → ' + t).join(', ') + '.');
    return { snaps, emptyIn: e.emptyInLanguage, N: [...N] };
  }
  const GNF1 = 'S → A B | b\nA → S a | a\nB → b';
  topic({
    id: 'gnf', family: 'cfg-clean', order: 50, title: 'Greibach normal form',
    blurb: 'Every rule should start with a terminal: A → a B₁ … Bₖ. Order the nonterminals, push every rule to start higher up, turn left recursion around, then substitute back from the top.',
    inputs: [{ id: 'g', kind: 'grammar', label: 'Grammar', def: GNF1, check: gcheck({ maxRules: 8, maxN: 4 }) }],
    presets: [
      { label: 'Indirect left recursion', values: { g: GNF1 } },
      { label: 'Immediate left recursion', values: { g: 'S → S a | b' } },
      { label: 'aⁿbⁿ', values: { g: 'S → a S b | a b' } },
    ],
    check: (inp) => { try { const s = gnfSteps(CF.grammar(inp.g)); const n = [...s.snaps[s.snaps.length - 1].rules.values()].reduce((a, r) => a + r.length, 0); if (n > 26) return 'Grammar: its Greibach form has ' + n + ' rules; try a smaller grammar'; if (n === 0) return 'Grammar: the language is empty or only ε, nothing to convert'; } catch (e) { return 'Grammar: ' + e.message; } return null; },
    counters: [{ id: 'rules', label: 'rules' }, { id: 'good', label: 'start with a terminal' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const S = gnfSteps(G);
      const F = new T.Frames(['rules', 'good']);
      const Nset = new Set(S.N);
      const gOf = (m) => T.grammar.make(G.start, [...m].flatMap(([A, rs]) => rs.map((r) => [A, r])), { nonterminals: S.N.concat(G.nonterminals), terminals: G.terminals });
      let prevSet = new Set();
      const order = [];
      S.snaps.forEach((sn, k) => {
        const g = gOf(sn.rules);
        for (const A of sn.rules.keys()) if (!order.includes(A)) order.push(A);
        const now = CF.ruleSet(g);
        const from = {};
        if (k) for (const x of now) if (!prevSet.has(x)) from[x] = 'g:l:' + x.split('→')[0];
        const d = CF.rules(g, { prefix: 'g', order, maxW: 620, from, lhsCls: (A) => (A === sn.A ? 'hot' : ''), cls: (A, rhs) => (Nset.has(rhs[0]) ? 'lead-n' : 'lead-t') + (from[key(A, rhs)] ? ' new' : '') });
        const all = g.productions.length, good = g.productions.filter((p) => !Nset.has(p.rhs[0])).length;
        F.set('rules', all).set('good', good);
        F.add({ items: d.items, say: sn.say + ' ' + good + ' of ' + all + ' rules start with a terminal (solid chips; dashed ones start with a nonterminal).', meta: { left: all - good, keys: k === 0 ? g.productions.filter((p) => Nset.has(p.rhs[0])).map((p) => 'g:c:' + key(p.A, p.rhs)) : null } });
        prevSet = now;
      });
      const fin = gOf(S.snaps[S.snaps.length - 1].rules);
      F.add({ items: CF.rules(fin, { prefix: 'g', order, maxW: 620, cls: () => 'lead-t' }).items, say: 'Greibach normal form: every rule is a terminal followed only by nonterminals' + (S.emptyIn ? ' (ε was in the language and needs a separate start rule S → ε)' : '') + '. A derivation now produces exactly one terminal per step, so a word of length n takes n steps, and a top-down parser reading one symbol per step never loops.', mark: 'GNF' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Grammar'), CF.gsec(fin, 'gnf', 'Greibach normal form')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.keys && f.meta.keys.length, once: true, pick: 'item', ask: 'Click a rule that does not yet start with a terminal.', answer: (fr, i) => fr[i].meta.keys, explain: 'Those are the dashed chips; substitution and the left-recursion turn fix them.' },
    ],
    quiz: [
      { q: 'Which rule is in Greibach normal form?', options: ['A → a B C', 'A → B a', 'A → B C', 'A → a b'], answer: 0, why: 'A terminal first, then nonterminals only.' },
      { q: 'In GNF, how many steps derive a word of length 5?', options: ['5', '4', '9', 'It depends'], answer: 0, why: 'Each step adds exactly one terminal.' },
      { q: 'S → S a | b becomes…', options: ['S → b | b S\', S\' → a | a S\'', 'S → a S | b', 'S → b a', 'It cannot be converted'], answer: 0, why: 'The left-recursive repetition of a is moved into a right-recursive S\'.' },
      { q: 'Why order the nonterminals A₁ … Aₙ first?', options: ['Rules Aᵢ → Aⱼ … with j > i can be fixed by substituting back from the top', 'To make the grammar smaller', 'To remove ε', 'It is arbitrary and unneeded'], answer: 0, why: 'Aₙ\'s rules all start with terminals, then Aₙ₋₁, and so on down.' },
    ],
  });

  // ---- left recursion ------------------------------------------------------------------------------------------
  const LR1 = 'E → E + n | n';
  const LR2 = 'S → A a | b\nA → S c | d';
  topic({
    id: 'left-rec', family: 'cfg-clean', order: 60, title: 'Removing left recursion: the tree turns around',
    blurb: 'A → A α | β grows its trees down the left side, which sends a top-down parser into an endless loop. A → β A\', A\' → α A\' | ε makes the same words with trees that grow down the right.',
    inputs: [
      { id: 'g', kind: 'grammar', label: 'Grammar', def: LR1, check: gcheck({ maxRules: 8, maxN: 4 }) },
      { id: 'w', kind: 'string', label: 'Word to draw', def: 'n+n+n', max: 7 },
    ],
    presets: [
      { label: 'Sums: n+n+n', values: { g: LR1, w: 'n+n+n' } },
      { label: 'Two kinds of repetition', values: { g: 'A → A x | A y | z', w: 'zxyx' } },
      { label: 'Indirect: S ⇒ A a ⇒ S c a', values: { g: LR2, w: 'bcaca' } },
    ],
    check: (inp) => { const G = CF.grammar(inp.g); const e = CF.checkWord(G, inp.w); if (e) return e; if (!T.grammar.parseTrees(G, CF.word(G, inp.w), 1).length) return 'Word: ' + inp.w + ' is not in the language'; if (!T.cfg.leftRecursive(G).length) return 'Grammar: no nonterminal is left-recursive here'; return null; },
    counters: [{ id: 'depth', label: 'left spine' }, { id: 'rules', label: 'rules' }],
    run(inp) {
      const G = CF.grammar(inp.g);
      const res = T.cfg.removeLeftRecursion(G);
      const H = res.grammar;
      const w = CF.word(G, inp.w);
      const t1 = T.grammar.parseTrees(G, w, 1)[0], t2 = T.grammar.parseTrees(H, w, 1)[0];
      const F = new T.Frames(['depth', 'rules']);
      const spine = (t, side) => { const ids = []; let n = t, id = 'r'; while (n && n.children && n.children.length) { ids.push(id); const i = side === 'l' ? 0 : n.children.length - 1; id += '.' + i; n = n.children[i]; } return ids; };
      const lsp = spine(t1, 'l'), rsp = spine(t2, 'r');
      const order = H.nonterminals.slice();
      const rulesAt = (g, o) => CF.rules(g, Object.assign({ prefix: 'g', order }, o));
      const r0 = rulesAt(G, { cls: (A, rhs) => (rhs[0] === A ? 'hot' : '') });
      const top = r0.box.h + 70;
      const treeL = (lit) => { const d = K.tree.draw(CF.kitTree(G, t1, { cls: (n, id) => (lit && lsp.includes(id) ? 'pv' : '') }), { prefix: 'A', y: top, yield: true, yieldLabel: 'before', gapX: 14 }); return d; };
      const tl = treeL(false);
      const treeR = (lit) => K.tree.draw(CF.kitTree(H, t2, { cls: (n, id) => (lit && rsp.includes(id) ? 'px' : '') }), { prefix: 'B', y: top, x: 0, yield: true, yieldLabel: 'after', gapX: 14 });
      const probe = treeR(false);
      const dx = tl.box.x + tl.box.w + 90 - probe.box.x;
      const tr = (lit) => K.tree.draw(CF.kitTree(H, t2, { cls: (n, id) => (lit && rsp.includes(id) ? 'px' : '') }), { prefix: 'B', y: top, x: dx, yield: true, yieldLabel: 'after', gapX: 14 });
      const lr = T.cfg.leftRecursive(G);
      F.set('rules', G.productions.length);
      F.add({ items: r0.items, say: 'Left-recursive: ' + lr.map((x) => x.A + (x.immediate ? ' (directly: a rule ' + x.A + ' → ' + x.A + ' …)' : ' (through other nonterminals)')).join(', ') + '. A parser that expands ' + lr[0].A + ' by trying its first symbol would expand ' + lr[0].A + ' again before reading anything: forever.' });
      F.set('depth', lsp.length);
      F.add({ items: r0.items.concat(treeL(true).items), say: 'The tree of ' + CF.show(w) + ' grows down its left side (orange): each repetition adds a level on the left, ' + lsp.length + ' levels here.', meta: { side: 'Right' } });
      for (const s of res.trace) {
        if (s.kind === 'immediate' || s.kind === 'substitute' || s.kind === 'prepare') {
          F.add({ items: r0.items.concat(treeL(true).items), say: s.say });
        }
      }
      const prev = CF.ruleSet(G), from = {};
      for (const x of CF.ruleSet(H)) if (!prev.has(x)) from[x] = 'g:l:' + x.split('→')[0].replace(/'+$|\d+$/, '');
      const r1 = rulesAt(H, { from, cls: (A, rhs) => (from[key(A, rhs)] ? 'new' : '') });
      F.set('rules', H.productions.length);
      F.add({ items: r1.items.concat(treeL(true).items), say: 'The new grammar: ' + H.productions.map((p) => CF.prod(H, p)).join(', ') + '. It starts with what used to end the recursion, then repeats the tails with a new nonterminal that calls itself on the right.' });
      F.set('depth', rsp.length);
      F.add({ items: r1.items.concat(treeL(true).items, tr(true).items), say: 'The same word in the new grammar: the tree now grows down its right side (blue), and every rule starts with something other than its own left side. Same words, a different shape, and a top-down parser can read it.', mark: 'no left recursion' });
      return { frames: F.list, def: { sections: [CF.gsec(G, 'g', 'Before'), CF.gsec(H, 'h', 'After')] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.side, once: true, pick: 'option', options: ['Left', 'Right', 'Neither: it becomes flat'], ask: 'After the rewrite, which side will the tree of the same word grow down?', answer: (fr, i) => fr[i].meta.side, explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'A → A α | β generates…', options: ['β α*', 'α* β', 'α β*', 'only β'], answer: 0, why: 'One β at the left end, then any number of α.' },
      { q: 'Its replacement without left recursion is…', options: ['A → β A\', A\' → α A\' | ε', 'A → α A | β', 'A → β | α', 'A → A β'], answer: 0, why: 'Start with β, then repeat α on the right.' },
      { q: 'Why does left recursion trouble a top-down parser?', options: ['Expanding A puts A first again without reading input: an endless loop', 'It makes the grammar ambiguous', 'It removes words', 'It needs ε-rules'], answer: 0, why: 'The parser never gets to compare a terminal with the input.' },
      { q: 'What does the rewrite change about E → E - T style trees?', options: ['They lean right, so the grouping must be recovered by the parser\'s actions', 'Nothing', 'They lose the - signs', 'They become ambiguous'], answer: 0, why: 'The words are the same but the tree shape is different; left associativity now has to be rebuilt when evaluating.' },
    ],
  });
})();
