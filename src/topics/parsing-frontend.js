// A tiny front end for a little language of assignments: the lexer, one DFA built from a regular expression
// per kind of token, cuts the source text into tokens by longest match; then an LALR(1) parser with
// precedence declarations builds the tree bottom up over those tokens. Source text at the bottom, tokens
// bracketed above it, the tree growing above the tokens.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const K = T.Kit;

  T.family({ id: 'front-end', part: 'parsing', order: 70, title: 'A tiny front end', blurb: 'From source text to tokens to a tree: a lexer built from regular expressions feeding an LR parser.' });

  const RULES = [
    { name: 'id', regex: '[a-z]+' }, { name: 'num', regex: '[0-9]+' },
    { name: '=', regex: '=' }, { name: '+', regex: '\\+' }, { name: '*', regex: '\\*' },
    { name: '(', regex: '\\(' }, { name: ')', regex: '\\)' }, { name: ';', regex: ';' },
    { name: 'space', regex: '\\ ', skip: true },
  ];
  const GRAMMAR = '%token id num\n%left +\n%left *\nP → S | P S\nS → id = E ;\nE → E + E | E * E | ( E ) | id | num';
  const CW = 46;

  T.topic({
    id: 'front-end', family: 'front-end', order: 10, title: 'Source text to tokens to tree',
    blurb: 'The lexer reads characters and groups them into tokens, always taking the longest match; the parser reads tokens and groups them into phrases, reducing handles. Two levels, two kinds of machine: a DFA and an LR automaton.',
    inputs: [{ id: 'src', kind: 'text', label: 'Program (assignments like x = 2 * (y + 1);)', def: 'x = 12 + y*3;' }],
    presets: [
      { label: 'Precedence: x = 12 + y*3;', values: { src: 'x = 12 + y*3;' } },
      { label: 'Brackets: v=(a+b)*2;', values: { src: 'v=(a+b)*2;' } },
      { label: 'Two statements: a=1; b=a;', values: { src: 'a=1; b=a;' } },
      { label: 'A lexical error: x = 3 # 4;', values: { src: 'x = 3 # 4;' } },
      { label: 'A syntax error: x = 3 + ;', values: { src: 'x = 3 + ;' } },
    ],
    check: (inp) => { const s = String(inp.src || ''); if (!s.trim()) return 'Program: write at least one assignment'; if ([...s].length > 18) return 'Program: at most 18 characters, so the picture stays readable'; if (/[\t\n]/.test(s)) return 'Program: one line, please'; return null; },
    counters: [{ id: 'tokens', label: 'tokens' }, { id: 'shifts', label: 'shifts' }, { id: 'reduces', label: 'reductions' }],
    run(inp) {
      const src = [...String(inp.src)];
      const lex = T.Lexer.build(RULES), lx = lex.tokenize(src.join(''));
      const G = T.PX.G(GRAMMAR), table = T.lr.buildTable(G, 'lalr', { precedence: true }), aug = table.aug;
      const F = new T.Frames(['tokens', 'shifts', 'reduces']);
      const toks = lx.tokens, x0 = 0;
      const spanX = (t) => x0 + ((t.start + t.end) / 2) * CW;
      const xAt = (i) => (i < toks.length ? spanX(toks[i]) : x0 + src.length * CW + 40);
      const r = toks.length ? T.lr.parse(table, toks.map((t) => t.name)) : null;
      // forest snapshots over the token row
      let nodes = [], seq = 0;
      const snaps = [];
      if (r) for (const st of r.trace) {
        const shifted = toks.length - (st.input.length - 1);
        snaps.push({ st, roots: nodes.slice(), shifted });
        if (st.kind === 'shift') nodes.push({ id: 't' + shifted, label: toks[shifted].text, at: shifted, cls: 'term' });
        else if (st.kind === 'reduce') { const q = aug.productions[st.prod], k = q.rhs.length; nodes.push({ id: 'n' + seq++, label: q.A, cls: 'nt', children: nodes.splice(nodes.length - k, k) }); }
      }
      const depth = (n) => (n.children ? 1 + Math.max(...n.children.map(depth)) : 0);
      const H = Math.max(2, ...nodes.map(depth));
      const leafY = -70, gy = 54;
      const lexed = [];
      const scene = (o) => {
        o = o || {};
        const items = [];
        src.forEach((c, i) => items.push({ key: 'fe:c' + i, kind: 'cell', x: x0 + i * CW, y: 0, w: CW - 2, h: 42, text: c === ' ' ? '·' : c, cls: 'mono' + (c === ' ' ? ' empty' : '') + (o.scan && i >= o.scan[0] && i < o.scan[1] ? (i < o.scan[2] ? ' hot' : ' act') : '') + (o.bad === i ? ' bad' : ''), pick: true }));
        items.push({ key: 'fe:lab', kind: 'text', x: x0 - 14, y: 26, text: 'source', anchor: 'end', cls: 'title' });
        lexed.forEach((t) => items.push({ key: 'fe:br' + t.start, kind: 'bracket', x1: x0 + t.start * CW, x2: x0 + t.end * CW - 2, y: -6, side: 'above', text: t.name === 'id' || t.name === 'num' ? t.name : '', cls: t.skip ? '' : 'x' }));
        const s = o.snap;
        const placed = s ? s.roots : [];
        const shifted = s ? s.shifted : 0;
        const pending = lexed.filter((t) => !t.skip).map((t, i) => ({ id: 't' + i, label: t.text, at: i, cls: 'term pending' })).slice(shifted);
        if (placed.length || pending.length) items.push(...T.PX.forest({ prefix: 'ft', roots: placed.concat(pending), y: leafY, gy, xAt, hot: o.hot || [] }).items);
        return items;
      };
      F.add({ items: scene({}), say: 'The source is just characters: ' + JSON.stringify(src.join('')) + '. The lexer\'s DFA has ' + lex.dfa.states.length + ' states, built from one regular expression per kind of token: names [a-z]+, numbers [0-9]+, the symbols = + * ( ) ; and spaces to skip.' });
      // the lexer, token by token
      for (const st of lx.trace) {
        if (st.kind === 'error') {
          F.add({ items: scene({ bad: st.pos }), say: 'Lexical error: no token can start with ' + st.ch + ' (position ' + (st.pos + 1) + '). The lexer reports it and skips that one character.', mark: 'lexical error', meta: { kind: 'lex-error' } });
          continue;
        }
        lexed.push({ name: st.name, text: st.text, start: st.start, end: st.end, skip: st.kind === 'skip' });
        if (st.kind === 'token') F.count('tokens');
        F.add({ items: scene({ scan: [st.start, Math.max(st.scanned, st.end), st.end] }), say: st.kind === 'skip' ? 'A space: matched and skipped; the parser never sees it.' : 'Token ' + st.name + ' "' + st.text + '"' + (st.end - st.start > 1 ? ': the DFA keeps going while it can, so ' + st.text + ' is one token, not ' + (st.end - st.start) + ' (longest match).' : '.') + (st.scanned > st.end ? ' It looked one character further, found no longer token, and backed up.' : ''), meta: { kind: 'lex', name: st.name } });
      }
      if (!toks.length) { F.add({ items: scene({}), say: 'No tokens at all: there is nothing for the parser to read.', mark: 'rejected' }); return { frames: F.list }; }
      F.add({ items: scene({ snap: { roots: [], shifted: 0 } }), say: 'The lexer is done: ' + toks.length + ' tokens, ' + toks.map((t) => t.name).join(' ') + '. Now the LALR(1) parser reads token names, not characters; the text of each id and num rides along to the tree.' });
      for (const s of snaps) {
        const st = s.st;
        if (st.kind === 'start') continue;
        if (st.kind === 'shift') { F.count('shifts'); F.add({ items: scene({ snap: s, hot: ['t' + s.shifted] }), say: 'Shift ' + st.symbol + (st.symbol === 'id' || st.symbol === 'num' ? ' (' + toks[s.shifted].text + ')' : '') + ': state ' + st.to + '.', meta: { kind: 'shift' } }); continue; }
        if (st.kind === 'reduce') { F.count('reduces'); const q = aug.productions[st.prod]; F.add({ items: scene({ snap: snaps[snaps.indexOf(s) + 1] || s, hot: ['n' + (F.counts.reduces - 1)] }), say: 'Reduce by ' + T.grammar.showProd(aug, q) + (q.rhs.length === 3 && (q.rhs[1] === '+' || q.rhs[1] === '*') ? (st.symbol === '*' ? '' : '') : '') + '.' + (q.rhs[1] === '*' ? ' * binds tighter than +, so this product is finished first.' : ''), hl: { g: [st.prod - 1] }, meta: { kind: 'reduce' } }); continue; }
        if (st.kind === 'accept') { F.add({ items: scene({ snap: s, hot: s.roots.map((n) => n.id) }), say: 'Accept: the whole program reduced to P.' + (lx.errors.length ? ' (The lexer did report ' + lx.errors.length + ' error' + (lx.errors.length > 1 ? 's' : '') + ', so the program is still wrong.)' : ' The tree is what a compiler\'s later phases work on.'), mark: lx.errors.length ? 'errors' : 'accepted', meta: { yes: !lx.errors.length } }); continue; }
        if (st.kind === 'error') F.add({ items: scene({ snap: s }), say: 'Syntax error at ' + (st.symbol === '$' ? 'the end' : st.symbol) + ': ' + st.say.replace(/^Error: /, '') + ' The tokens were all fine; it is their order that is wrong.', mark: 'syntax error', meta: { yes: false } });
      }
      return { frames: F.list, def: { sections: [
        { id: 'lex', kind: 'math', title: 'Tokens (first listed wins a tie)', text: RULES.map((x) => (x.skip ? 'skip  ' : '') + x.name + '  =  ' + x.regex.replace(/\\(.)/g, '$1').replace(/^ $/, '␣')).join('\n') },
        T.PX.gdef(G, { title: 'Grammar (with %left + below %left *)' }),
      ] } };
    },
    predict: [
      { at: (f, i, fr) => fr[i + 1] && fr[i + 1].meta && fr[i + 1].meta.kind === 'lex' && fr[i + 1].meta.name === 'num', once: true, pick: 'option', options: ['id', 'num', '=', 'an error'], ask: 'What kind of token comes next?', answer: () => 'num', explain: (fr, i) => fr[i + 1].say },
      { at: (f, i, fr) => i === fr.length - 2, once: true, pick: 'option', options: ['Accept', 'Reject'], ask: 'Will the program be accepted?', answer: (fr) => (fr[fr.length - 1].meta && fr[fr.length - 1].meta.yes ? 'Accept' : 'Reject'), explain: (fr) => fr[fr.length - 1].say },
    ],
    quiz: [
      { q: 'Why does the lexer read "12" as one num token and not two?', options: ['Numbers are special', 'Longest match: it keeps going while a longer token is possible', 'The parser asks it to', 'Spaces separate tokens'], answer: 1, why: 'At each position the lexer takes the longest prefix any token rule matches.' },
      { q: 'Which level notices x = 3 + ; is wrong?', options: ['The lexer', 'The parser', 'Both', 'Neither'], answer: 1, why: 'Every token is fine; their order breaks the grammar.' },
      { q: 'Which level notices x = 3 # 4; is wrong?', options: ['The lexer', 'The parser', 'Neither', 'Only the tree'], answer: 0, why: 'No token can begin with #.' },
      { q: 'Why split the front end into a lexer and a parser?', options: ['Tradition only', 'Tokens are regular and need only a DFA; nesting needs a context-free parser, and the parser gets far fewer symbols to read', 'Parsers cannot read characters', 'To allow ambiguity'], answer: 1, why: 'Each part uses the simplest machine that does its job.' },
    ],
  });
})();
