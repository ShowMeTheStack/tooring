// The sandbox: build any finite automaton, PDA, Turing machine, grammar or regular expression, run it on
// a string step by step, test it against a list of strings, and convert it (subset construction,
// minimisation, to a regex, to Chomsky normal form, to a PDA ...) with the core engines. What is built is
// kept in this browser and can be shared as a link (#sandbox=code).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const store = T.UI.storage;
  const SB = (T.Sandbox = {});

  const KINDS = [['fa', 'Finite automaton'], ['pda', 'PDA'], ['tm', 'Turing machine'], ['grammar', 'Grammar'], ['regex', 'Regex'], ['ram', 'Registers'], ['counter', 'Counters'], ['rec', 'Recursive functions'], ['lambda', 'λ-terms']];
  // the other models of computation: a program in a text box, run step by step with the core engines
  const MODEL = new Set(['ram', 'counter', 'rec', 'lambda']);
  const MODEL_HELP = {
    ram: 'One instruction per line: inc r1, dec r1, jz r1 label, jmp label, halt; label: before an instruction. The input gives r1, r2, ... (or r3=5); the answer is r0.',
    counter: 'One state per line: q: inc A next, q: dec A next ifzero, q: halt. The input sets counters like A=3 B=0.',
    rec: 'One definition per line, name = expression, from Z, S, P(i,n), composition C(f; g, h) and recursion R(f, g); the library (add, mul, ...) is there. The input is the function and its arguments, like add 2 3.',
    lambda: 'A λ-term (\\ also works for λ); numerals 0, 1, 2 ... and names like ADD, TRUE are defined. It is reduced leftmost outermost to normal form.',
  };
  const EXAMPLES = {
    fa: [
      ['Ends in ab (an NFA)', 'start p\naccept r\np -a,b-> p\np -a-> q\nq -b-> r', 'ab\naab\n-ba\n-ε\nbbab'],
      ['Even number of a\'s (a DFA)', 'start e\naccept e\ne -a-> o\no -a-> e\ne -b-> e\no -b-> o', 'ε\naa\n-a\nbab\n-abbb'],
      ['ε-moves: a* then b*', 'start s\naccept s t\ns -a-> s\ns -ε-> t\nt -b-> t', 'ε\naab\n-ba\nbbb'],
    ],
    pda: [
      ['aⁿbⁿ, n ≥ 1', 'start p\nstack-start Z\naccept f\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> d, ε\nd, b, A -> d, ε\nd, ε, Z -> f, Z', 'ab\naabb\n-aab\n-ε\n-ba'],
      ['Even palindromes over {x, y}', 'start push\nstack-start Z\naccept done\npush, x, ε -> push, X\npush, y, ε -> push, Y\npush, ε, ε -> pop, ε\npop, x, X -> pop, ε\npop, y, Y -> pop, ε\npop, ε, Z -> done, Z', 'ε\nxx\nxyyx\n-xy\n-xyx'],
    ],
    tm: [
      ['Add one in binary', 'start: right\naccept: done\nright, 0 -> right, 0, R\nright, 1 -> right, 1, R\nright, _ -> carry, _, L\ncarry, 1 -> carry, 0, L\ncarry, 0 -> done, 1, S\ncarry, _ -> done, 1, S', '0\n1\n1011\n111'],
      ['Equal 0s and 1s, 0s first', 'start: s\naccept: yes\ns, 0 -> r, X, R\ns, Y -> chk, Y, R\ns, _ -> yes, _, S\nr, 0 -> r, 0, R\nr, Y -> r, Y, R\nr, 1 -> l, Y, L\nl, 0 -> l, 0, L\nl, Y -> l, Y, L\nl, X -> s, X, R\nchk, Y -> chk, Y, R\nchk, _ -> yes, _, S', 'ε\n01\n0011\n-001\n-10'],
    ],
    grammar: [
      ['Balanced brackets', 'S → ( S ) S | ε', 'ε\n()\n(())()\n-(()\n-)('],
      ['Arithmetic', 'E → E + T | T\nT → T * F | F\nF → ( E ) | x', 'x\nx+x*x\n(x+x)*x\n-x+\n-(x'],
    ],
    ram: [['Add r1 and r2', 'loop1: jz r1 next\n  dec r1\n  inc r0\n  jmp loop1\nnext: jz r2 done\n  dec r2\n  inc r0\n  jmp next\ndone: halt', '2 3']],
    counter: [['Double A into B', 'd: dec A d1 m\nd1: inc B d2\nd2: inc B d\nm: dec B m1 h\nm1: inc A m\nh: halt', 'A=3']],
    rec: [['Addition by recursion', 'plus = R(P(1,1), C(S; P(3,3)))', 'plus 2 3']],
    lambda: [['Two plus one', 'ADD 2 1', '']],
    regex: [
      ['Contains bb', '(a|b)*bb(a|b)*', 'bb\nabba\n-abab\n-ε'],
      ['Binary numbers with no leading zero', '0|1(0|1)*', '0\n10\n1101\n-01\n-ε'],
    ],
  };

  SB.open = function (app, main, arg) {
    const saved = store.get('sandbox', null);
    const st = Object.assign({ kind: 'fa', texts: {}, tests: {}, input: {}, tmView: 'diagram', pos: {} }, saved || {});
    for (const [k] of KINDS) { if (st.texts[k] === undefined) st.texts[k] = EXAMPLES[k][0][1]; if (st.tests[k] === undefined) st.tests[k] = EXAMPLES[k][0][2]; if (st.input[k] === undefined) st.input[k] = st.tests[k].split('\n')[0].replace(/^[+-]/, '').replace(/^ε$/, ''); }
    const page = { player: null, editor: null, history: [] };
    const save = () => store.set('sandbox', st);
    const root = h('div.sandbox', { id: 'sandbox' });
    main.appendChild(root);

    // ---- head ----
    const seg = h('div.seg', { role: 'tablist', id: 'sbKinds' });
    for (const [k, label] of KINDS) {
      const b = h('button', { type: 'button', dataset: { kind: k }, role: 'tab' }, label);
      b.addEventListener('click', () => { if (st.kind !== k) { st.kind = k; save(); draw(); } });
      seg.appendChild(b);
    }
    const ex = h('button.btn', { type: 'button', id: 'sbExamples' }, icon('book'), 'Examples');
    ex.addEventListener('click', () => {
      const r = ex.getBoundingClientRect();
      T.UI.showMenu(EXAMPLES[st.kind].map(([label, text, tests]) => ({ label, action: () => { remember(); st.texts[st.kind] = text; st.tests[st.kind] = tests; st.input[st.kind] = tests.split('\n')[0].replace(/^[+-]/, '').replace(/^ε$/, ''); delete st.pos[st.kind]; save(); draw(); } })), r.left, r.bottom + 4, { anchor: ex, keyboard: true });
    });
    const share = h('button.btn', { type: 'button', id: 'sbShare' }, icon('link'), 'Share');
    share.addEventListener('click', () => T.Share.pack({ kind: st.kind, text: st.texts[st.kind], tests: st.tests[st.kind], pos: st.pos[st.kind] || null }).then((code) => T.Share.copy(location.href.replace(/#.*$/, '') + '#sandbox=' + code, 'A link to this ' + KINDS.find((k) => k[0] === st.kind)[1].toLowerCase() + ' is copied.')));
    const back = h('button.btn', { type: 'button', id: 'sbBack', title: 'Back to what you had before the last conversion or example' }, icon('undo'), 'Back');
    back.addEventListener('click', () => { const p = page.history.pop(); if (!p) return; st.kind = p.kind; st.texts[p.kind] = p.text; save(); draw(); });
    root.appendChild(h('div.sb-head', h('div', h('div.crumbs', 'Tooring'), h('h1', 'Sandbox')), h('div.sb-actions', seg, ex, back, share)));
    const grid = h('div.sb');
    root.appendChild(grid);
    const remember = () => { page.history.push({ kind: st.kind, text: st.texts[st.kind] }); back.disabled = false; };

    function draw() {
      back.disabled = !page.history.length;
      for (const b of seg.children) b.classList.toggle('on', b.dataset.kind === st.kind);
      if (page.player) { page.player.dispose(); page.player = null; }
      grid.innerHTML = '';
      const k = st.kind;
      // ---- the editor ----
      const edCard = h('div.card.sb-pane', { id: 'sbEditor' });
      const machine = k === 'fa' || k === 'pda' || k === 'tm';
      const model = MODEL.has(k);
      const title = h('h3', machine ? 'Draw the machine' : k === 'grammar' ? 'Write the grammar' : model ? (k === 'lambda' ? 'Write the term' : 'Write the program') : 'Write the expression');
      edCard.appendChild(title);
      const host = h('div');
      edCard.appendChild(host);
      if (k === 'tm') {
        const v = h('div.seg', { id: 'sbTmView', style: { marginBottom: '8px' } });
        for (const [id, label] of [['diagram', 'Diagram'], ['table', 'Table']]) { const b = h('button', { type: 'button', class: st.tmView === id ? 'on' : '' }, label); b.addEventListener('click', () => { st.tmView = id; save(); draw(); }); v.appendChild(b); }
        title.after(v);
      }
      const onText = (text) => { st.texts[k] = text; save(); refreshConvert(); };
      if (machine && !(k === 'tm' && st.tmView === 'table')) {
        page.editor = new T.DiagramEditor(host, { text: st.texts[k], kind: k === 'fa' ? 'nfa' : k, onChange: (text, m) => { st.pos[k] = m.pos; onText(text); } });
        if (st.pos[k]) { page.editor.m.pos = Object.assign({}, page.editor.m.pos, st.pos[k]); page.editor.view = null; page.editor.render(); }
      } else if (k === 'tm') page.editor = new T.TMTableEditor(host, { text: st.texts[k], onChange: onText });
      else if (model) {
        const ta = h('textarea.mono.prog-answer', { id: 'sbProgram', spellcheck: 'false', wrap: 'off', 'aria-label': 'The program' });
        ta.value = st.texts[k];
        ta.addEventListener('input', () => onText(ta.value));
        host.append(h('p.muted', { style: { fontSize: '13px', margin: '0 0 6px' } }, MODEL_HELP[k]), ta);
        requestAnimationFrame(() => T.UI.autosize(ta, 460));
        page.editor = { getText: () => ta.value };
      } else if (k === 'grammar') page.editor = new T.GrammarEditor(host, { text: st.texts[k], onChange: onText });
      else page.editor = new T.RegexInput(host, { value: st.texts[k], onChange: onText });
      // ---- run ----
      const runCard = h('div.card.sb-pane', { id: 'sbRunCard' });
      const inp = h('input', { type: 'text', id: 'sbInput', value: st.input[k] || '', placeholder: model ? { ram: 'r1, r2, ... like 2 3', counter: 'like A=3 B=0', rec: 'like add 2 3', lambda: '(not used)' }[k] : 'ε (empty)', spellcheck: 'false', 'aria-label': model ? 'Input' : 'Input string' });
      const go = h('button.btn.primary', { type: 'button', id: 'sbRun' }, icon('run'), 'Run');
      const verdict = h('span.verdict.wait', { id: 'sbVerdict' }, 'not run');
      const pbox = h('div', { id: 'sbPlayer' });
      const run = () => {
        const w = inp.value.trim() === 'ε' ? '' : inp.value.trim();
        st.input[k] = w; save();
        const src = { kind: k === 'fa' ? 'nfa' : k, text: st.texts[k] };
        if (model) {
          if (page.player) page.player.dispose();
          pbox.innerHTML = '';
          let res = null;
          try { res = T.Sim.model(k, st.texts[k], inp.value); } catch (e) { res = { frames: [{ items: [], say: 'This cannot run yet: ' + e.message }], verdict: 'error', note: '' }; }
          verdict.className = 'verdict ' + (res.verdict === 'error' || res.verdict === 'no halt' ? 'no' : 'yes');
          verdict.textContent = res.verdict + (res.note ? ' · ' + res.note : '');
          const topic = { id: 'sandbox-run', title: 'Run', inputs: [], camera: 'fit-all', run: () => res.frames };
          page.player = new T.Player(app, pbox, { topic, embed: true, side: false, idp: 'sb-' });
          return;
        }
        const a = T.Sim.accepts(src, w);
        verdict.className = 'verdict ' + (a.accepted === true ? 'yes' : a.accepted === false ? 'no' : 'wait');
        verdict.textContent = a.accepted === true ? 'accepted' : a.accepted === false ? 'rejected' : (a.note || 'no answer');
        if (page.player) page.player.dispose();
        pbox.innerHTML = '';
        const pos = machine && page.editor && page.editor.m ? page.editor.m.pos : null;
        const topic = { id: 'sandbox-run', title: 'Run', inputs: [], camera: 'fit-all', run: () => { try { return T.Sim.frames(src, w, pos); } catch (e) { return [{ items: [], say: 'This cannot run yet: ' + e.message }]; } } };
        page.player = new T.Player(app, pbox, { topic, embed: true, side: false, idp: 'sb-' });
      };
      go.addEventListener('click', run);
      inp.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); run(); } });
      runCard.append(h('h3', 'Run it'), h('div.sb-run', inp, go, verdict), pbox);
      // ---- tests ----
      const testCard = h('div.card.sb-pane.sb-tests', { id: 'sbTests' });
      const ta = h('textarea', { id: 'sbTestList', spellcheck: 'false', 'aria-label': 'Strings to test, one per line' });
      ta.value = st.tests[k] || '';
      requestAnimationFrame(() => T.UI.autosize(ta, 300));
      ta.addEventListener('input', () => { st.tests[k] = ta.value; save(); });
      const out = h('div', { id: 'sbTestOut' });
      const test = h('button.btn', { type: 'button', id: 'sbTestAll' }, icon('test'), 'Test all');
      test.addEventListener('click', () => {
        const src = { kind: k === 'fa' ? 'nfa' : k, text: st.texts[k] };
        const rows = ta.value.split('\n').map((l) => l.trim()).filter((l) => l !== '');
        const tbl = h('table.sb-results', h('tr', h('th', 'string'), h('th', 'result'), h('th', 'expected')));
        let bad = 0;
        for (const l of rows) {
          const exp = l[0] === '+' ? true : l[0] === '-' ? false : null;
          let w = exp === null ? l : l.slice(1).trim();
          if (w === 'ε') w = '';
          const a = T.Sim.accepts(src, w);
          const mism = exp !== null && a.accepted !== null && a.accepted !== exp;
          if (mism) bad++;
          const tr = h('tr' + (mism ? '.mismatch' : ''), h('td', w === '' ? 'ε' : w), h('td', { class: a.accepted === true ? 'yes' : a.accepted === false ? 'no' : '' }, a.accepted === true ? 'accept' : a.accepted === false ? 'reject' : a.note || '?'), h('td', exp === null ? '' : exp ? 'accept' : 'reject'));
          tr.addEventListener('click', () => { inp.value = w; run(); });
          tr.style.cursor = 'pointer';
          tbl.appendChild(tr);
        }
        out.innerHTML = '';
        out.append(tbl, h('p.muted', { style: { fontSize: '13px', margin: '6px 0 0' } }, rows.length + ' strings' + (bad ? ', ' + bad + ' not as expected' : '') + '. Click a row to run it.'));
      });
      testCard.append(h('h3', 'Test strings'), h('p.muted', { style: { fontSize: '13px', margin: '0 0 6px' } }, 'One per line; ε for the empty string; start a line with + or − to say what you expect.'), ta, h('div.sb-actions', test), out);
      // ---- convert ----
      const conv = h('div.card.sb-pane', { id: 'sbConvert' });
      const convBtns = h('div.sb-actions');
      conv.append(h('h3', 'Convert'), convBtns);
      function refreshConvert() {
        convBtns.innerHTML = '';
        const list = T.Sim.conversions(k === 'fa' ? 'nfa' : k);
        if (!list.length) convBtns.appendChild(h('span.muted', 'Nothing to convert a Turing machine into here.'));
        for (const c of list) {
          const b = h('button.btn.small', { type: 'button', dataset: { conv: c.id }, disabled: !c.ready(), title: c.ready() ? '' : 'Needs an engine that is not loaded' }, icon('convert'), c.label);
          b.addEventListener('click', () => {
            let res;
            try { res = c.run(st.texts[k]); } catch (e) { T.UI.toast('Could not convert: ' + e.message, 'err', 5000); return; }
            remember();
            const to = c.to === 'dfa' || c.to === 'nfa' ? 'fa' : c.to;
            st.kind = to; st.texts[to] = res; delete st.pos[to]; save();
            draw();
            T.UI.toast(c.label + ': done. Back returns to what you had.', 'ok');
          });
          convBtns.appendChild(b);
        }
      }
      refreshConvert();
      if (model) { testCard.style.display = 'none'; conv.style.display = 'none'; }
      grid.append(h('div', edCard, conv), h('div', runCard, testCard));
      grid.lastChild.style.display = grid.firstChild.style.display = 'flex';
      grid.lastChild.style.flexDirection = grid.firstChild.style.flexDirection = 'column';
      grid.lastChild.style.gap = grid.firstChild.style.gap = '14px';
      grid.lastChild.style.minWidth = grid.firstChild.style.minWidth = '0';
      run();
      page.run = run;
    }

    if (arg && arg.startsWith('=')) {
      T.Share.unpack(arg.slice(1)).then((d) => {
        if (!d || !d.kind) throw new Error('This share code holds nothing for the sandbox.');
        st.kind = d.kind; st.texts[d.kind] = d.text; if (d.tests) st.tests[d.kind] = d.tests; if (d.pos) st.pos[d.kind] = d.pos; else delete st.pos[d.kind];
        save(); draw();
        history.replaceState(null, '', '#sandbox');
      }).catch((e) => { T.UI.toast(e.message, 'err', 5000); draw(); });
    } else draw();
    page.dispose = () => { if (page.player) page.player.dispose(); };
    return page;
  };
})();
