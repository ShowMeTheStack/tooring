// Strings: symbols in a row that slide together (concatenation), swap ends (reversal), and are cut into
// prefixes and suffixes; and Σ*, every string over an alphabet, unfolding as a tree level by level and
// numbered in shortlex order, which lists them all.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit, F = T.Found, Geo = T.geom;

  T.family({ id: 'found-strings', part: 'foundations', order: 80, title: 'Alphabets and strings', blurb: 'An alphabet is a finite set of symbols, a string is a finite row of them, and ε is the string with none. Σ* collects every string, and shortlex order lists it.' });

  const show = F.show;
  const CW = 46, CH = 44;
  /** A row of symbol cells; keys say where each symbol came from, so a symbol that moves glides */
  const row = (syms, x0, y0, opts) => {
    opts = opts || {};
    const items = [];
    if (!syms.length) items.push({ key: opts.epsKey || ('eps:' + x0 + ':' + y0), kind: 'cell', x: x0, y: y0, w: CW, h: CH, text: 'ε', cls: 'mono empty', size: 17 });
    syms.forEach((s, i) => items.push(Object.assign({ key: s.key, kind: 'cell', x: x0 + i * CW, y: y0, w: CW, h: CH, text: s.c, cls: 'mono ' + (s.cls || ''), size: 18 }, s.extra || {})));
    return items;
  };
  const label = (key, x, y, text, cls) => ({ key, kind: 'text', x, y, text, anchor: 'end', cls: cls || 'strong', size: 16 });

  const OPS = {
    concat: { label: 'concatenation uv' },
    reverse: { label: 'reverse uᴿ' },
    prefixes: { label: 'prefixes of u' },
    suffixes: { label: 'suffixes of u' },
    power: { label: 'powers u⁰, u¹, u², u³' },
    revcat: { label: '(uv)ᴿ = vᴿuᴿ' },
  };
  T.topic({
    id: 'string-ops', family: 'found-strings', order: 10, title: 'Operations on strings',
    blurb: 'Concatenate two strings, reverse one, list its prefixes and suffixes, raise it to a power. Every symbol is a tile you can follow, and ε, the empty string, behaves exactly as it should.',
    inputs: [
      { id: 'u', kind: 'string', label: 'u', def: 'abb', max: 6 },
      { id: 'v', kind: 'string', label: 'v', def: 'ca', max: 5 },
      { id: 'op', kind: 'choice', label: 'Operation', def: 'concat', options: Object.entries(OPS).map(([value, o]) => ({ value, label: o.label })) },
    ],
    presets: [
      { label: 'Concatenate abb and ca', values: { u: 'abb', v: 'ca', op: 'concat' } },
      { label: 'Concatenate with ε', values: { u: 'ab', v: '', op: 'concat' } },
      { label: 'Reverse 10110', values: { u: '10110', v: '', op: 'reverse' } },
      { label: 'Prefixes of abca', values: { u: 'abca', v: '', op: 'prefixes' } },
      { label: 'Suffixes of abca', values: { u: 'abca', v: '', op: 'suffixes' } },
      { label: 'Powers of ab', values: { u: 'ab', v: '', op: 'power' } },
      { label: '(uv)ᴿ = vᴿuᴿ', values: { u: 'ab', v: 'cde', op: 'revcat' } },
    ],
    counters: [{ id: 'len', label: 'length of the result' }, { id: 'made', label: 'strings made' }],
    run(inp) {
      const u = [...inp.u], v = [...inp.v], op = inp.op;
      const F2 = new T.Frames(['len', 'made']);
      const U = u.map((c, i) => ({ c, key: 'u:' + i, cls: 'part-x' }));
      const V = v.map((c, i) => ({ c, key: 'v:' + i, cls: 'part-z' }));
      const su = show(inp.u), sv = show(inp.v);
      const bracket = (key, from, to, y, text, cls) => ({ key, kind: 'bracket', x1: from * CW, x2: Math.max(from + 1, to) * CW, y, side: 'below', text, cls: cls || '' });
      let def = [];
      if (op === 'concat') {
        def = ['u = ' + su + ',  |u| = ' + u.length, 'v = ' + sv + ',  |v| = ' + v.length, 'uv: the symbols of u, then those of v', '|uv| = |u| + |v|,  uε = εu = u'];
        F2.add({ items: row(U, 0, 0, { epsKey: 'eu' }).concat(row(V, 0, 90, { epsKey: 'ev' }), [label('lu', -14, 28, 'u'), label('lv', -14, 118, 'v')]), say: 'u = ' + su + ' has ' + u.length + ' symbol' + (u.length === 1 ? '' : 's') + ' and v = ' + sv + ' has ' + v.length + '.', hl: { def: ['0', '1'] }, meta: { len: u.length + v.length } });
        F2.set('len', u.length + v.length).count('made');
        const items = row(U.concat(V), 0, 0, { epsKey: 'eu' }).concat([label('lu', -14, 28, 'uv')]);
        if (u.length) items.push(bracket('bu', 0, u.length, CH + 8, 'u', 'x'));
        if (v.length) items.push(bracket('bv', u.length, u.length + v.length, CH + 8, 'v', 'z'));
        F2.add({ items, say: 'uv = ' + show(inp.u + inp.v) + ': v slides in after u. Its length is ' + u.length + ' + ' + v.length + ' = ' + (u.length + v.length) + '.' + (!v.length || !u.length ? ' Concatenating with ε changes nothing: ε is the identity for concatenation.' : ' Order matters: vu = ' + show(inp.v + inp.u) + (inp.v + inp.u === inp.u + inp.v ? ', the same here, by luck.' : ' is a different string.')), hl: { def: ['2', '3'] }, mark: 'uv' });
      } else if (op === 'reverse' || op === 'revcat') {
        const W = op === 'revcat' ? U.concat(V) : U;
        const n = W.length;
        def = op === 'revcat' ? ['u = ' + su + ', v = ' + sv, 'wᴿ: the symbols of w in the opposite order', '(uv)ᴿ = vᴿ uᴿ', 'reversing twice gives back w'] : ['u = ' + su, 'uᴿ: the symbols of u in the opposite order', 'εᴿ = ε, (uᴿ)ᴿ = u', 'u is a palindrome when uᴿ = u'];
        const at = W.map((_, i) => i);
        const scene = (hot) => row(at.map((p, i) => ({ c: W[p].c, key: W[p].key, cls: W[p].cls + (hot && hot.includes(i) ? ' hot' : '') })), 0, 0, { epsKey: 'eu' }).concat([label('lu', -14, 28, op === 'revcat' ? 'uv' : 'u')]);
        F2.set('len', n);
        F2.add({ items: scene(), say: op === 'revcat' ? 'Start from uv = ' + show(inp.u + inp.v) + '. Reverse the whole string, swapping the two ends and working inwards.' : 'u = ' + su + '. To reverse it, swap the two ends and work inwards.', hl: { def: ['0', '1'] }, meta: { len: n } });
        if (!n) F2.add({ items: scene(), say: 'The empty string has nothing to swap: εᴿ = ε.', hl: { def: ['2'] } });
        for (let i = 0; i < Math.floor(n / 2); i++) {
          const j = n - 1 - i;
          [at[i], at[j]] = [at[j], at[i]];
          F2.add({ items: scene([i, j]), say: 'Swap places ' + (i + 1) + ' and ' + (j + 1) + ': ' + W[at[j]].c + ' and ' + W[at[i]].c + ' trade places.' + (W[at[i]].c === W[at[j]].c ? ' They are the same symbol, so the string looks unchanged.' : ''), hl: { def: ['1'] } });
        }
        const res = at.map((p) => W[p].c).join('');
        F2.count('made');
        const items = scene();
        if (op === 'revcat' && n) { if (v.length) items.push(bracket('bv', 0, v.length, CH + 8, 'vᴿ', 'z')); if (u.length) items.push(bracket('bu', v.length, n, CH + 8, 'uᴿ', 'x')); }
        F2.add({ items, say: op === 'revcat' ? '(uv)ᴿ = ' + show(res) + '. The colours show it: v\'s symbols now come first, reversed, then u\'s, reversed. So (uv)ᴿ = vᴿ uᴿ.' : 'uᴿ = ' + show(res) + '.' + (res === inp.u ? ' It reads the same both ways: ' + su + ' is a palindrome.' : ' Reversing again would give back ' + su + '.'), hl: { def: op === 'revcat' ? ['2'] : [res === inp.u ? '3' : '2'] }, mark: 'reversed' });
      } else if (op === 'prefixes' || op === 'suffixes') {
        const pre = op === 'prefixes', n = u.length;
        def = pre ? ['u = ' + su, 'x is a prefix of u when u = xy for some y', '|u| + 1 prefixes, from ε to u itself', 'proper prefix: not u itself'] : ['u = ' + su, 'y is a suffix of u when u = xy for some x', '|u| + 1 suffixes, from u itself to ε', 'proper suffix: not u itself'];
        const top = row(U, 0, 0, { epsKey: 'eu' }).concat([label('lu', -14, 28, 'u')]);
        const rows = [];
        F2.add({ items: top, say: 'u = ' + su + ' has ' + n + ' symbol' + (n === 1 ? '' : 's') + '. ' + (pre ? 'A prefix is what you can read from the start before stopping.' : 'A suffix is what is left after cutting some symbols off the front.'), hl: { def: ['0', '1'] }, meta: { count: n + 1 } });
        for (let k = 0; k <= n; k++) {
          const len = pre ? k : n - k;
          const from = pre ? 0 : k;
          const syms = u.slice(from, from + len).map((c, j) => ({ c, key: 'p:' + k + ':' + j, cls: 'part-x', extra: { enter: 'from', src: 'u:' + (from + j) } }));
          const y = 70 + k * (CH + 10);
          rows.push(...row(syms, from * CW, y, { epsKey: 'pe:' + k }), label('pl:' + k, -14, y + 28, '|' + len + '|', 'title'));
          F2.count('made').set('len', len);
          const s = show(u.slice(from, from + len).join(''));
          F2.add({ items: top.concat(rows), say: (pre ? 'Prefix of length ' + len + ': ' : 'Cut ' + k + ' symbol' + (k === 1 ? '' : 's') + ' off the front: ') + s + '.' + (len === 0 ? ' ε is a ' + (pre ? 'prefix' : 'suffix') + ' of every string.' : len === n ? ' u is a ' + (pre ? 'prefix' : 'suffix') + ' of itself (not a proper one).' : ''), hl: { def: ['1'] } });
        }
        F2.add({ items: top.concat(rows), say: su + ' has ' + (n + 1) + ' ' + (pre ? 'prefixes' : 'suffixes') + ', one for each place to cut, including both ends; ' + n + ' of them are proper.', hl: { def: ['2', '3'] }, mark: 'all' });
      } else {
        def = ['u = ' + su, 'u⁰ = ε', 'uᵏ⁺¹ = uᵏ u', '|uᵏ| = k · |u|'];
        F2.add({ items: row(U, 0, 0, { epsKey: 'eu' }).concat([label('lu', -14, 28, 'u')]), say: 'u = ' + su + '. Powers are repeated concatenation.', hl: { def: ['0'] }, meta: { len: 3 * u.length } });
        for (let k = 0; k <= 3; k++) {
          const syms = [];
          for (let c = 0; c < k; c++) u.forEach((ch, j) => syms.push({ c: ch, key: 'w:' + c + ':' + j, cls: c % 2 ? 'part-z' : 'part-x', extra: { enter: 'from', src: c ? 'w:' + (c - 1) + ':' + j : 'u:' + j } }));
          const y = 80 + k * (CH + 14);
          const prev = [];
          for (let kk = 0; kk < k; kk++) {
            const ss = [];
            for (let c = 0; c < kk; c++) u.forEach((ch, j) => ss.push({ c: ch, key: 'r' + kk + ':' + c + ':' + j, cls: c % 2 ? 'part-z' : 'part-x' }));
            prev.push(...row(ss, 0, 80 + kk * (CH + 14), { epsKey: 'pe:' + kk }), label('pl:' + kk, -14, 80 + kk * (CH + 14) + 28, 'u' + '⁰¹²³'[kk]));
          }
          F2.set('len', k * u.length).count('made');
          F2.add({ items: row(U, 0, 0, { epsKey: 'eu' }).concat([label('lu', -14, 28, 'u')], prev, row(syms.map((s, i) => Object.assign({}, s, { key: 'r' + k + ':' + s.key.slice(2) })), 0, y, { epsKey: 'pe:' + k }), [label('pl:' + k, -14, y + 28, 'u' + '⁰¹²³'[k])]), say: k === 0 ? 'u⁰ = ε: zero copies of u is the empty string, whatever u is.' : 'u' + '⁰¹²³'[k] + ' = ' + show(inp.u.repeat(k)) + ': ' + k + ' cop' + (k === 1 ? 'y' : 'ies') + ' of u, length ' + k + ' · ' + u.length + ' = ' + k * u.length + '.', hl: { def: [k === 0 ? '1' : '2'] } });
        }
        F2.list[F2.list.length - 1].mark = 'powers';
      }
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: OPS[op].label, text: def.join('\n') }] } };
    },
    predict: [
      { at: (f, i, fr, inp) => i === 0 && (inp.op === 'prefixes' || inp.op === 'suffixes'), pick: 'option', options: (fr, i, inp) => [...new Set([inp.u.length - 1, inp.u.length, inp.u.length + 1, 2 * inp.u.length].filter((x) => x >= 0))].map(String), ask: 'How many ' + 'of them will u have, counting ε and u itself?', answer: (fr) => String(fr[0].meta.count), explain: (fr) => fr[fr.length - 1].say },
      { at: (f, i, fr, inp) => i === 0 && (inp.op === 'concat' || inp.op === 'power' || inp.op === 'reverse' || inp.op === 'revcat'), pick: 'option', options: (fr) => [...new Set([fr[0].meta.len, fr[0].meta.len + 1, Math.max(0, fr[0].meta.len - 1), fr[0].meta.len * 2])].sort((a, b) => a - b).map(String), ask: (fr, i, inp) => 'How long will ' + (inp.op === 'power' ? 'u³' : inp.op === 'concat' ? 'uv' : inp.op === 'revcat' ? '(uv)ᴿ' : 'uᴿ') + ' be?', answer: (fr) => String(fr[0].meta.len), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'What is |ε|, and what is uε?', options: ['1, and u', '0, and u', '0, and ε', 'Undefined'], answer: 1, why: 'ε has no symbols, and adding nothing to u leaves u.' },
      { q: 'How many prefixes does a string of length 5 have?', options: ['4', '5', '6', '10'], answer: 2, why: 'Cut after 0, 1, …, 5 symbols: six prefixes, from ε to the string itself.' },
      { q: 'Which is (abc)ᴿ · (de)ᴿ?', options: ['(abcde)ᴿ', '(deabc)ᴿ', 'cbade', 'edcba'], answer: 1, why: '(xy)ᴿ = yᴿxᴿ, so (de · abc)ᴿ = (abc)ᴿ(de)ᴿ = cbaed.' },
      { q: 'Is concatenation commutative?', options: ['Yes', 'No: ab · c = abc but c · ab = cab'], answer: 1, why: 'It is associative, and ε is its identity, but order matters.' },
    ],
  });

  // ---------------------------------------------------------------------------------------------------
  // Σ* as an unfolding tree, numbered in shortlex order
  // ---------------------------------------------------------------------------------------------------
  T.topic({
    id: 'sigma-star', family: 'found-strings', order: 20, title: 'Σ*: every string, in shortlex order',
    blurb: 'Start from ε and give every string one child per symbol. Level n holds the strings of length n. Number them level by level, alphabetically within a level: every string gets a number.',
    inputs: [
      { id: 'sigma', kind: 'list', label: 'Alphabet Σ', def: ['a', 'b'], max: 3, check: (v) => (v.some((x) => [...x].length !== 1) ? 'Alphabet Σ: one symbol each' : new Set(v).size !== v.length ? 'Alphabet Σ: a symbol is listed twice' : null) },
      { id: 'n', kind: 'number', label: 'Longest length shown', def: 3, min: 0, max: 4 },
    ],
    check: (inp) => (Number(F.countUpTo(inp.sigma.length, inp.n)) > 31 ? 'Too many strings to draw (' + F.countUpTo(inp.sigma.length, inp.n) + '); at most 31, so use a shorter length or a smaller alphabet' : null),
    presets: [
      { label: '{a, b} up to length 3', values: { sigma: ['a', 'b'], n: 3 } },
      { label: '{0, 1, 2} up to length 2', values: { sigma: ['0', '1', '2'], n: 2 } },
      { label: 'One symbol: a chain', values: { sigma: ['a'], n: 4 } },
      { label: 'The empty alphabet: Σ* = {ε}', values: { sigma: [], n: 2 } },
    ],
    counters: [{ id: 'strings', label: 'strings drawn' }, { id: 'numbered', label: 'numbered' }],
    run(inp) {
      const S = inp.sigma, N = inp.n;
      const all = F.sigmaStar(S, N);
      const F2 = new T.Frames(['strings', 'numbered']);
      const num = new Map(all.map((w, i) => [w, i]));
      const build = (maxLvl, numbered, hot) => {
        const mk = (w) => {
          const node = { id: w === '' ? 'eps' : w, label: numbered.has(w) ? show(w) + ' #' + num.get(w) : show(w) + '\u2007'.repeat(String(num.get(w)).length + 1), mono: true, cls: (numbered.has(w) ? 'good' : '') + (hot === w ? ' hot' : '') };
          if ([...w].length < maxLvl) node.children = S.map((a) => mk(w + a));
          return node;
        };
        return K.tree.draw(mk(''), { prefix: 'ss', gapX: S.length === 3 ? 10 : 16, gapY: 86 }).items;
      };
      const numbered = new Set();
      F2.add({ items: build(0, numbered), say: 'Σ = ' + (S.length ? '{' + S.join(', ') + '}' : '∅') + '. The root is ε, the empty string: every string starts here.', hl: { def: ['0'] } });
      numbered.add(''); F2.set('strings', 1).set('numbered', 1);
      F2.add({ items: build(0, numbered, ''), say: 'ε is number 0: the only string of length 0.', hl: { def: ['1'] } });
      if (!S.length) {
        F2.add({ items: build(0, numbered), say: 'With no symbols there is nothing to add to ε, so the tree stops here: over the empty alphabet, Σ* = {ε}, one string.', hl: { def: ['2'] }, mark: 'done' });
      }
      const perNode = all.length <= 15;
      for (let L = 1; S.length && L <= N; L++) {
        const lvl = all.filter((w) => [...w].length === L);
        F2.set('strings', all.filter((w) => [...w].length <= L).length);
        F2.add({ items: build(L, numbered), say: 'Level ' + L + ': each string of length ' + (L - 1) + ' gets one child per symbol, giving ' + S.length + '^' + L + ' = ' + lvl.length + ' strings of length ' + L + '.', hl: { def: ['2'] }, meta: L === 2 || (L === 1 && N === 1) ? { first: 'ss:n:' + lvl[0] } : {} });
        if (perNode) for (const w of lvl) { numbered.add(w); F2.count('numbered'); F2.add({ items: build(L, numbered, w), say: show(w) + ' is number ' + num.get(w) + '.', hl: { def: ['1'] } }); }
        else { lvl.forEach((w) => numbered.add(w)); F2.count('numbered', lvl.length); F2.add({ items: build(L, numbered), say: 'Number level ' + L + ' left to right: ' + show(lvl[0]) + ' is #' + num.get(lvl[0]) + ', up to ' + show(lvl[lvl.length - 1]) + ' as #' + num.get(lvl[lvl.length - 1]) + '.', hl: { def: ['1'] } }); }
      }
      if (S.length) {
        const ex = all[all.length - 1];
        F2.add({ items: build(N, numbered), say: 'Every level is finite, so the numbering finishes each level and moves on: each string gets a number, and Σ* is countable. (' + show(ex) + ' is #' + F.indexOfString(S, ex) + '.) In dictionary order, ' + (S.length > 1 ? S[0] + ', ' + S[0] + S[0] + ', ' + S[0] + S[0] + S[0] + ', … would go on for ever and ' + S[1] + ' would never get a number.' : 'with one symbol the two orders agree.'), hl: { def: ['3'] }, mark: 'countable' });
      }
      return { frames: F2.list, def: { sections: [{ id: 'def', kind: 'math', title: 'Shortlex order', text: ['Σ* = all finite strings over Σ, ε included', 'shortlex: shorter first, then alphabetical', 'level n has |Σ|ⁿ strings', 'each string has a finite position: Σ* is countable'].join('\n') }] } };
    },
    predict: [
      { at: (f) => f.meta && f.meta.first, once: true, pick: 'item', ask: 'Which string of this new level comes first in shortlex order? Click it.', answer: (fr, i) => fr[i].meta.first, explain: (fr, i) => fr[i + 1].say },
    ],
    quiz: [
      { q: 'Over Σ = {a, b}, which comes first in shortlex order: b or aa?', options: ['b', 'aa'], answer: 0, why: 'Shorter strings come first; b has length 1.' },
      { q: 'How many strings of length 3 are there over {a, b, c}?', options: ['3', '9', '27', '40'], answer: 2, why: '3 choices for each of 3 places: 3³ = 27.' },
      { q: 'Why not list Σ* in dictionary order?', options: ['It is slower', 'a, aa, aaa, … never ends, so b would never get a number', 'Dictionary order is not defined on strings'], answer: 1, why: 'A listing must reach each string after finitely many steps.' },
      { q: 'What is Σ* when Σ = ∅?', options: ['∅', '{ε}', 'Undefined'], answer: 1, why: 'The empty string uses no symbols, so it exists over any alphabet.' },
    ],
  });
})();
