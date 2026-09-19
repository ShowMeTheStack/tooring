// Lessons, exercises and tours. #learn lists the chapters of every part with their lessons and exercises
// (and progress); #lesson=id reads a lesson, whose blocks may hold a live topic player, a machine to run, or
// an editor with strings to test; #exercise=id sets an exercise with the editor its answer needs, checks
// the answer with T.Check, and gives hints one at a time; #tour=id starts a guided tour.
//
// Lesson blocks (a lesson's blocks: [...]):
//   'text' or {p}            a paragraph, with `code`, **bold**, *italic* and [links](#topic=dfa-run)
//   {h}                      a heading                {list: [..]}, {steps: [..]}   bullets, numbered steps
//   {tip}, {warn}            a note, a warning        {def: 'term', text}          a definition
//   {math: 'lines'}          formal text, monospaced  {code, lang: 'grammar'|'machine'|'regex'}
//   {table: [[head..], [row..]], caption}            {svg: '<svg..>', caption}     a figure
//   {predict: {q, options, answer, explain}}         a question to answer before reading on
//   {topic: id, input: {..}, frame: n, inputs: true, caption}  a live player of a topic (no side panel;
//                                                    inputs: true shows its inputs and examples too)
//   {relation: {domain: 'a b c', pairs: '(a, b), (b, c)', props: [..]}, caption}  a relation to edit, drawn
//                                                    as a graph and a matrix with its properties checked
//   {sandbox: {kind: 'fa'|'pda'|'tm'|'grammar'|'regex', text, input}, caption}
//                                                    a machine (or grammar, or expression) to run on strings
//   {editor: {kind: 'dfa'|'nfa'|'pda'|'tm'|'grammar'|'regex', text, tests: 'ab\n-ba'}, caption}
//                                                    an editor with a list of strings to test (- = reject)
//   {exercise: id}, {lesson: id}                      a card leading to it
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const store = T.UI.storage;
  const C = () => T.Content;
  const inline = (t) => T.UI.inline(t);
  const LEVEL = ['', 'easy', 'medium', 'hard'];

  // ---- progress, kept in this browser --------------------------------------------------------------------
  const prog = () => Object.assign({ read: {}, solved: {}, hints: {}, drafts: {}, tours: {} }, store.get('learn', {}));
  const saveProg = (p) => store.set('learn', p);
  const mark = (kind, id) => { const p = prog(); p[kind][id] = Date.now(); saveProg(p); };

  const L = (T.Learn = {
    isDone(type, id) { const p = prog(); return type === 'lesson' ? !!p.read[id] : type === 'exercise' ? !!p.solved[id] : false; },
    progress: prog,
    open(app, main, hash, opts) {
      if (hash.startsWith('lesson=')) return lessonPage(app, main, hash.slice(7), opts || {});
      if (hash.startsWith('exercise=')) return exercisePage(app, main, hash.slice(9), opts || {});
      if (hash.startsWith('tour=')) { const id = hash.slice(5); setTimeout(() => T.Tour.start(id), 0); return listPage(app, main); }
      return listPage(app, main);
    },
  });

  // ---- the list --------------------------------------------------------------------------------------------
  function listPage(app, main) {
    document.title = 'Learn · Tooring';
    const p = prog();
    const box = h('div.home.learn', { id: 'learnView' });
    box.append(h('div.crumbs', 'Tooring'), h('h1.page-title', 'Learn'));
    const chs = C() ? C().chapters.filter((c) => c.lessons.length || c.exercises.length) : [];
    const total = (k) => chs.reduce((n, c) => n + c[k].length, 0);
    const nl = total('lessons'), nx = total('exercises');
    const rd = chs.reduce((n, c) => n + c.lessons.filter((id) => p.read[id]).length, 0), sv = chs.reduce((n, c) => n + c.exercises.filter((id) => p.solved[id]).length, 0);
    if (!chs.length) {
      box.appendChild(h('p.lead', 'Lessons explain each idea with figures that run, and exercises are checked the moment you answer.'));
      box.appendChild(T.UI.empty('learn', 'Lessons and exercises are on their way', 'They are being written. Meanwhile every topic in the catalogue runs and explains itself step by step, and the sandbox runs any machine you build.', [{ label: 'Browse the topics', icon: 'library', primary: true, action: () => { location.hash = ''; } }, { label: 'Open the sandbox', icon: 'sandbox', action: () => { location.hash = 'sandbox'; } }]));
      main.appendChild(box);
      return { dispose() {} };
    }
    box.appendChild(h('p.lead', 'Lessons explain each idea with figures that run; exercises are checked the moment you answer, with hints when you are stuck. Your progress stays in this browser.'));
    box.appendChild(h('div.learn-sum', h('div', h('b', rd + ' of ' + nl), ' lessons read'), h('div.fc-bar', h('i', { style: { width: (nl ? Math.round((100 * rd) / nl) : 0) + '%' } })), h('div', h('b', sv + ' of ' + nx), ' exercises solved'), h('div.fc-bar', h('i', { style: { width: (nx ? Math.round((100 * sv) / nx) : 0) + '%' } }))));
    if (C().tours.size) {
      const tours = h('div.tour-list');
      for (const t of C().tours.values()) { const b = h('button.chip', { type: 'button', dataset: { tour: t.id } }, icon('flag'), t.title, p.tours[t.id] ? ' ✓' : ''); b.addEventListener('click', () => T.Tour.start(t.id)); tours.appendChild(b); }
      box.append(h('h2.sub-title', 'Guided tours'), tours);
    }
    for (const part of T.parts) {
      const mine = chs.filter((c) => c.part === part.id);
      if (!mine.length) continue;
      const sec = h('section.part', h('div.part-head', h('span.num', String(part.n)), h('h2', part.title)));
      const grid = h('div.chap-grid');
      for (const ch of mine) {
        const card = h('div.card.chap-card', { dataset: { chapter: ch.id } }, h('h3', ch.title), ch.blurb ? h('p.muted', ch.blurb) : null);
        const list = h('ul.chap-items');
        for (const id of ch.lessons) { const l = C().lessons.get(id); list.appendChild(h('li' + (p.read[id] ? '.done' : ''), h('a', { href: '#lesson=' + id }, icon('book'), h('span', l.title)), l.minutes ? h('span.meta', l.minutes + ' min') : null, p.read[id] ? h('span.ok', { title: 'Read' }, '✓') : null)); }
        for (const id of ch.exercises) { const x = C().exercises.get(id); list.appendChild(h('li' + (p.solved[id] ? '.done' : ''), h('a', { href: '#exercise=' + id }, icon('build'), h('span', x.title)), h('span.meta', { title: LEVEL[x.level || 1] }, '●'.repeat(x.level || 1)), p.solved[id] ? h('span.ok', { title: 'Solved' }, '✓') : null)); }
        card.appendChild(list);
        grid.appendChild(card);
      }
      sec.appendChild(grid);
      box.appendChild(sec);
    }
    main.appendChild(box);
    return { dispose() {} };
  }

  const crumbs = (x) => { const ch = C().chapterOf(x); const part = ch && T.partOf(ch.part); return h('div.crumbs', h('a', { href: '#learn' }, 'Learn'), part ? ' › Part ' + part.n + ': ' + part.title : '', ch ? ' › ' + ch.title : ''); };
  const missing = (what, id) => (main) => { main.appendChild(h('div.home', T.UI.empty('book', 'There is no ' + what + ' called "' + id + '"', 'It may have been renamed or removed.', [{ label: 'All lessons and exercises', icon: 'learn', primary: true, action: () => { location.hash = 'learn'; } }]))); return { dispose() {} }; };

  // ---- a lesson -------------------------------------------------------------------------------------------
  function lessonPage(app, main, id, opts) {
    const l = C() && C().lessons.get(id);
    if (!l) return missing('lesson', id)(main);
    document.title = l.title + ' · Learn · Tooring';
    const page = { players: [], editors: [], player: null, dispose() { for (const p of page.players) p.dispose(); } };
    const box = h('article.lesson', { id: 'lessonView', dataset: { lesson: id } });
    box.append(crumbs(l), h('h1.page-title', l.title), h('div.ls-meta', l.minutes ? h('span', icon('history'), l.minutes + ' minutes') : null, l.sample ? h('span.sample-tag', 'Sample') : null));
    if (l.summary) box.appendChild(h('p.lead', inline(l.summary)));
    (l.blocks || []).forEach((b, i) => { const el = block(app, b, page, 'b' + i + '-'); if (el) box.appendChild(el); });
    // previous / done
    const ch = C().chapterOf(l), ids = ch ? ch.lessons : [], k = ids.indexOf(id);
    const nav = h('div.ls-nav');
    if (!opts.inCourse) {
      nav.appendChild(k > 0 ? h('a.btn', { href: '#lesson=' + ids[k - 1] }, icon('stepBack'), 'Previous lesson') : h('span'));
      const done = h('button.btn.primary', { type: 'button', id: 'lessonDone' }, icon('check'), k + 1 < ids.length ? 'Done, next lesson' : 'Done');
      done.addEventListener('click', () => { mark('read', id); location.hash = k + 1 < ids.length ? 'lesson=' + ids[k + 1] : ch && ch.exercises.length ? 'exercise=' + ch.exercises[0] : 'learn'; });
      nav.appendChild(done);
    } else {
      const done = h('button.btn', { type: 'button', id: 'lessonDone' }, icon('check'), prog().read[id] ? 'Read ✓' : 'Mark as read');
      done.addEventListener('click', () => { mark('read', id); done.textContent = 'Read ✓'; });
      nav.appendChild(done);
    }
    box.appendChild(nav);
    main.appendChild(box);
    for (const p of page.players) p.redraw();
    page.player = page.players[0] || null;
    // the keyboard drives the player last pointed at or focused
    box.addEventListener('pointerover', (e) => { const p = page.players.find((x) => x.root.contains(e.target)); if (p) page.player = p; });
    box.addEventListener('focusin', (e) => { const p = page.players.find((x) => x.root.contains(e.target)); if (p) page.player = p; });
    T.UI.fitTables(box);
    return page;
  }

  /** One block of a lesson as an element */
  function block(app, b, page, idp) {
    if (typeof b === 'string') return paras(b);
    if (b.p) return paras(b.p);
    if (b.h) return h('h2.ls-h', b.h);
    if (b.list) return h('ul.ls-list', b.list.map((x) => h('li', inline(x))));
    if (b.steps) return h('ol.ls-steps', b.steps.map((x) => h('li', inline(x))));
    if (b.tip) return h('div.ls-note.tip', icon('hint'), h('div', inline(b.tip)));
    if (b.warn) return h('div.ls-note.warn', icon('warn'), h('div', inline(b.warn)));
    if (b.def) return h('div.ls-def', h('b', b.def), ' ', h('span', inline(b.text || '')));
    if (b.math !== undefined) return h('div.ls-math', ...String(b.math).split('\n').map((x) => h('div', x)));
    if (b.code !== undefined) return h('pre.ls-code', b.lang === 'grammar' && T.highlightGrammarLine ? { html: String(b.code).split('\n').map((x) => T.highlightGrammarLine(x)).join('\n') } : b.lang === 'regex' && T.highlightRegex ? { html: T.highlightRegex(b.code) } : String(b.code));
    if (b.table) {
      const head = h('thead', h('tr', b.table[0].map((x) => h('th', inline(String(x))))));
      const body = h('tbody', b.table.slice(1).map((r) => h('tr', r.map((x) => h('td', inline(String(x)))))));
      return figure(h('div.fit-table', h('table.ls-table', head, body)), b.caption);
    }
    if (b.svg) { const d = h('div.ls-svg'); d.innerHTML = b.svg; return figure(d, b.caption); }
    if (b.predict) return predictBlock(b.predict);
    if (b.topic) return topicBlock(app, b, page, idp);
    if (b.relation) return figure(relationBox(b.relation), b.caption, 'relation');
    if (b.sandbox) return figure(runBox(app, page, Object.assign({ idp }, b.sandbox)), b.caption, 'sandbox');
    if (b.editor) return figure(editorBox(app, page, Object.assign({ idp }, b.editor)), b.caption, 'editor');
    if (b.exercise) { const x = C().exercises.get(b.exercise); return x ? linkCard('#exercise=' + x.id, 'build', 'Exercise', x.title, (x.level ? LEVEL[x.level] : '') + (prog().solved[x.id] ? ' · solved ✓' : '')) : null; }
    if (b.lesson) { const x = C().lessons.get(b.lesson); return x ? linkCard('#lesson=' + x.id, 'book', 'Lesson', x.title, x.minutes ? x.minutes + ' min' : '') : null; }
    return null;
  }
  /** Text with blank lines between paragraphs and single line breaks kept */
  function paras(text) {
    const ps = String(text).split(/\n\s*\n/).map((t) => t.trim()).filter(Boolean).map((t) => h('p', ...t.split('\n').map((line, i) => [i ? h('br') : null, inline(line)])));
    return ps.length === 1 ? ps[0] : h('div.ls-paras', ...ps);
  }
  const figure = (el, caption, cls) => h('figure.ls-fig' + (cls ? '.' + cls : ''), el, caption ? h('figcaption', inline(caption)) : null);
  const linkCard = (href, ic, kind, title, meta) => h('a.ls-link', { href }, h('span.tc-icon', icon(ic)), h('span', h('span.kind', kind), h('b', title), meta ? h('span.meta', meta) : null), h('span.go', '→'));
  function predictBlock(q) {
    const box = h('div.ls-predict', h('div.lp-q', icon('help'), h('div', h('b', 'Before reading on: '), inline(q.q))));
    const opts = h('div.lp-opts'), res = h('div.lp-res', { 'aria-live': 'polite' });
    q.options.forEach((o, i) => {
      const b = h('button.quiz-opt', { type: 'button' }, inline(o));
      b.addEventListener('click', () => {
        [...opts.children].forEach((c, k) => { c.disabled = true; c.classList.toggle('right', k === q.answer); c.classList.toggle('wrong', k === i && i !== q.answer); });
        res.innerHTML = '';
        res.appendChild(h('div.' + (i === q.answer ? 'lp-ok' : 'lp-no'), h('b', i === q.answer ? 'Right. ' : 'Not quite. '), inline(q.explain || '')));
      });
      opts.appendChild(b);
    });
    box.append(opts, res);
    return box;
  }
  function topicBlock(app, b, page, idp) {
    const t = T.byId(b.topic);
    if (!t) return figure(T.UI.empty('watch', 'A figure is missing here', 'It shows the topic "' + b.topic + '", which is not in this build.'), b.caption);
    const host = h('div.ls-player');
    let input = T.inputOf(t, Object.assign(T.inputOf(t), b.input || {}));
    if (T.checkInput(t, input)) input = T.inputOf(t);
    const p = new T.Player(app, host, { topic: t, input, embed: true, side: false, counters: true, inputs: !!b.inputs, idp: 'ls' + idp });
    if (b.frame) p.go(b.frame, true);
    page.players.push(p);
    const open = h('a.btn.small', { href: '#topic=' + t.id, title: 'Open this topic on its own page, with its definition and inputs' }, 'Open the topic');
    return figure(h('div', host, h('div.ls-fig-tools', h('span.muted', t.title), open)), b.caption, 'topic');
  }

  // ---- a relation to type and see ------------------------------------------------------------------------------
  /**
   * {relation: {domain: 'a b c' (or a list), pairs: '(a, b), (b, c)', props: ['reflexive', ...]}}: the pairs
   * are typed in set notation and drawn as a graph and as a matrix, with its properties checked as it changes.
   */
  const PROPS = { reflexive: 'isReflexive', irreflexive: 'isIrreflexive', symmetric: 'isSymmetric', antisymmetric: 'isAntisymmetric', transitive: 'isTransitive', equivalence: 'isEquivalence', 'partial order': 'isPartialOrder' };
  function relationBox(o) {
    const F = T.Found;
    const dom = h('input.mono', { type: 'text', value: Array.isArray(o.domain) ? o.domain.join(' ') : o.domain || '', 'aria-label': 'The set', spellcheck: 'false' });
    const pairs = h('input.mono', { type: 'text', value: o.pairs || '', 'aria-label': 'The pairs of the relation', spellcheck: 'false', placeholder: '(a, b), (b, c)' });
    const err = h('div.err', { role: 'alert' });
    const art = h('div.rel-art');
    const mat = h('div.fit-table.rel-matrix');
    const props = h('div.rel-props', { 'aria-live': 'polite' });
    const stage = new T.Stage(art, { label: 'The relation as a graph' });
    const draw = () => {
      err.textContent = '';
      const D = dom.value.split(/[\s,{}]+/).filter(Boolean);
      const r = pairs.value.trim() ? T.Check.parseValue(pairs.value, { topSet: true }) : { v: { t: 'set', items: [] } };
      if (r.error) { err.textContent = r.error; return; }
      const R = [], seen = new Set();
      for (const p of r.v.items) {
        if (p.t !== 'tuple' || p.items.length !== 2 || p.items.some((x) => x.t !== 'atom')) { err.textContent = 'Each element of a relation is a pair, like (a, b) or a-b.'; return; }
        const [x, y] = p.items.map((q) => q.v);
        if (!D.includes(x) || !D.includes(y)) { err.textContent = (D.includes(x) ? y : x) + ' is not in the set {' + D.join(', ') + '}.'; return; }
        if (!seen.has(x + '\u0000' + y)) { seen.add(x + '\u0000' + y); R.push([x, y]); }
      }
      // the graph: the elements round a circle, an arrow per pair, loops for (x, x)
      const n = Math.max(1, D.length), rad = 60 + 18 * n, pos = {};
      D.forEach((x, k) => { const a = -Math.PI / 2 + (2 * Math.PI * k) / n; pos[x] = { x: Math.round(rad * Math.cos(a)), y: Math.round(rad * Math.sin(a)) }; });
      const m = { kind: 'nfa', states: D, start: null, accept: [], trans: R.map(([x, y]) => ({ from: x, to: y, label: '' })) };
      try { const g = T.Kit.graph.draw(m, { pos, noStart: true }); stage.show({ items: g.items.filter((it) => !/start/.test(it.key)).map((it) => (it.kind === 'edge' ? Object.assign({}, it, { label: '', lx: undefined, ly: undefined }) : it)) }, { duration: 250 }); } catch (e) { stage.show({ items: [] }); }
      // the matrix
      const has = new Set(R.map(([x, y]) => x + '\u0000' + y));
      mat.innerHTML = '';
      mat.appendChild(h('table.ls-table.rel-table', h('thead', h('tr', h('th', 'R'), ...D.map((y) => h('th', y)))), h('tbody', ...D.map((x) => h('tr', h('th', x), ...D.map((y) => h('td' + (has.has(x + '\u0000' + y) ? '.on' : ''), has.has(x + '\u0000' + y) ? '1' : '0')))))));
      // the properties
      props.innerHTML = '';
      const why = F.rel.why(D, R);
      for (const p of o.props || ['reflexive', 'symmetric', 'antisymmetric', 'transitive', 'equivalence']) {
        const fn = F.rel[PROPS[p]];
        if (!fn) continue;
        const yes = fn(D, R);
        const w = !yes && why.find((x) => x.prop === p);
        props.appendChild(h('span.rel-prop' + (yes ? '.yes' : '.no'), { title: w ? w.say : '' }, (yes ? '✓ ' : '✗ ') + p));
      }
      const notes = why.filter((x) => (o.props || ['reflexive', 'symmetric', 'transitive']).includes(x.prop));
      if (notes.length) props.appendChild(h('div.rel-why', ...notes.map((x) => h('div', x.say))));
      T.UI.fitTables(mat.parentElement || mat);
    };
    const redraw = T.UI.debounce(draw, 150);
    dom.addEventListener('input', redraw); pairs.addEventListener('input', redraw);
    const box = h('div.rel-box', h('div.rel-inputs', h('label', h('span', 'Set'), dom), h('label.grow', h('span', 'Pairs'), pairs)), err, h('div.rel-views', art, mat), props);
    requestAnimationFrame(draw);
    return box;
  }

  // ---- running what is in a lesson or an exercise ------------------------------------------------------------
  const simKind = (k) => (k === 'fa' || k === 'dfa' ? 'nfa' : k);
  const sbKind = (k) => (k === 'dfa' || k === 'nfa' ? 'fa' : k);
  /**
   * A string to run a machine (or grammar or expression) on: the verdict, and the run as a little player.
   * o: {kind, text | getText(), input, idp, summary: false}
   */
  function runBox(app, page, o) {
    const get = () => (o.getText ? o.getText() : o.text);
    const box = h('div.run-box');
    if (o.text !== undefined && o.summary !== false) {
      const k = simKind(o.kind);
      const s = k === 'grammar' ? T.grammarSummary(o.text) : k === 'regex' ? { kind: 'Expression', facts: [o.text] } : T.machineSummary(o.text);
      const code = h('pre.ls-code.run-code', o.text);
      const tog = h('button.btn.small.ghost', { type: 'button', 'aria-expanded': 'false' }, 'Text ▾');
      tog.addEventListener('click', () => { const on = box.classList.toggle('show-code'); tog.setAttribute('aria-expanded', String(on)); });
      const toSb = h('button.btn.small', { type: 'button', title: 'Open this in the sandbox to change it' }, icon('sandbox'), 'Open in the sandbox');
      toSb.addEventListener('click', () => T.Share.pack({ kind: sbKind(o.kind), text: get(), tests: o.tests || '' }).then((code) => { location.hash = 'sandbox=' + code; }));
      box.appendChild(h('div.run-head', h('span.model-kind', s.kind), h('span.model-facts', ...s.facts.slice(0, 4).map((f) => h('span', f))), h('span.grow'), tog, toSb));
      box.appendChild(code);
    }
    const inp = h('input.mono', { type: 'text', value: o.input || '', placeholder: 'ε (empty)', spellcheck: 'false', 'aria-label': 'A string to run' });
    const go = h('button.btn.small.primary', { type: 'button' }, icon('run'), 'Run');
    const verdict = h('span.verdict.wait', 'not run');
    const host = h('div.run-player');
    let player = null;
    const run = () => {
      const w = inp.value.trim() === 'ε' ? '' : inp.value.trim();
      const src = { kind: simKind(o.kind), text: get() };
      const a = T.Sim.accepts(src, w);
      verdict.className = 'verdict ' + (a.accepted === true ? 'yes' : a.accepted === false ? 'no' : 'wait');
      verdict.textContent = a.accepted === true ? 'accepted' : a.accepted === false ? 'rejected' : (a.note || 'no answer');
      if (player) { player.dispose(); page.players.splice(page.players.indexOf(player), 1); }
      host.innerHTML = '';
      const topic = { id: 'run', title: 'Run', inputs: [], camera: 'fit-all', run: () => { try { return T.Sim.frames(src, w); } catch (e) { return [{ items: [], say: 'This cannot run yet: ' + e.message }]; } } };
      player = new T.Player(app, host, { topic, embed: true, side: false, idp: 'run' + (o.idp || '') });
      page.players.push(player);
      page.player = player;
    };
    go.addEventListener('click', run);
    inp.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); run(); } });
    box.append(h('div.sb-run', h('label.run-label', 'Input'), inp, go, verdict), host);
    if (o.autorun !== false) run();
    return box;
  }
  /** An editor (diagram, grammar or expression) with strings to test against it */
  function editorBox(app, page, o) {
    const box = h('div.ed-box');
    const host = h('div');
    box.appendChild(host);
    const ed = makeEditor(host, o.kind, o.text, () => {});
    if (o.idp) host.querySelectorAll('[id]').forEach((e) => { e.id = 'ls' + o.idp + e.id; });
    page.editors.push(ed);
    box.appendChild(testBench(() => ({ kind: simKind(o.kind), text: ed.get() }), o.tests || ''));
    return box;
  }
  /** Make the right editor for a kind: {get(), set(text), root, ed} */
  function makeEditor(host, kind, text, onChange) {
    if (kind === 'grammar') { const ed = new T.GrammarEditor(host, { text: text || '', onChange }); return { get: () => ed.getText(), ed }; }
    if (kind === 'regex') { const ed = new T.RegexInput(host, { value: text || '', onChange }); return { get: () => ed.value(), ed }; }
    const ed = new T.DiagramEditor(host, { text: text || (kind === 'tm' ? 'start: q0\naccept: qa' : 'start q0'), kind: kind === 'fa' ? 'nfa' : kind, onChange: (t) => onChange(t) });
    return { get: () => ed.getText(), ed };
  }
  function testBench(src, tests) {
    const ta = h('textarea.mono', { spellcheck: 'false', rows: String(Math.min(8, Math.max(3, String(tests).split('\n').length))), 'aria-label': 'Strings to test, one per line' });
    ta.value = tests;
    requestAnimationFrame(() => T.UI.autosize(ta, 240));
    const out = h('div.bench-out', { 'aria-live': 'polite' });
    const test = h('button.btn.small', { type: 'button' }, icon('test'), 'Test');
    test.addEventListener('click', () => {
      const rows = ta.value.split('\n').map((l) => l.trim()).filter(Boolean);
      const tbl = h('table.sb-results', h('tr', h('th', 'string'), h('th', 'result'), h('th', 'expected')));
      let bad = 0;
      for (const l of rows) {
        const exp = l[0] === '+' ? true : l[0] === '-' || l[0] === '−' ? false : null;
        let w = exp === null ? l : l.slice(1).trim();
        if (w === 'ε') w = '';
        const a = T.Sim.accepts(src(), w);
        const mism = exp !== null && a.accepted !== null && a.accepted !== exp;
        if (mism) bad++;
        tbl.appendChild(h('tr' + (mism ? '.mismatch' : ''), h('td', w === '' ? 'ε' : w), h('td', { class: a.accepted === true ? 'yes' : a.accepted === false ? 'no' : '' }, a.accepted === true ? 'accept' : a.accepted === false ? 'reject' : a.note || '?'), h('td', exp === null ? '' : exp ? 'accept' : 'reject')));
      }
      out.innerHTML = '';
      out.append(tbl, h('p.muted', rows.length + ' strings' + (bad ? ', ' + bad + ' not as expected.' : ', all as expected.')));
    });
    return h('div.bench', h('div.bench-head', h('b', 'Strings to test'), h('span.muted', 'one per line; − in front for one that should be rejected'), test), ta, out);
  }

  // ---- an exercise -------------------------------------------------------------------------------------------
  function exercisePage(app, main, id, opts) {
    const x = C() && C().exercises.get(id);
    if (!x) return missing('exercise', id)(main);
    document.title = x.title + ' · Exercise · Tooring';
    const page = { players: [], editors: [], player: null, dispose() { for (const p of page.players) p.dispose(); } };
    const p0 = prog();
    const box = h('article.lesson.exercise', { id: 'exerciseView', dataset: { exercise: id, kind: x.kind } });
    box.append(crumbs(x), h('h1.page-title', x.title), h('div.ls-meta', h('span.level', { title: 'Level' }, '●'.repeat(x.level || 1) + ' ' + LEVEL[x.level || 1]), p0.solved[id] ? h('span.solved', icon('check'), 'Solved') : null, x.sample ? h('span.sample-tag', 'Sample') : null));
    for (const b of [].concat(x.text || [])) { const el = block(app, b, page, 'x-'); if (el) box.appendChild(el); }
    const answerHost = h('div.answer', { id: 'answer' });
    box.appendChild(answerHost);
    const A = answerUI(app, page, x, answerHost, p0.drafts[id]);
    const saveDraft = T.UI.debounce(() => { const p = prog(); try { p.drafts[id] = A.get(); saveProg(p); } catch (e) { /* not ready */ } }, 400);
    answerHost.addEventListener('input', saveDraft);
    answerHost.addEventListener('click', saveDraft);
    // check, hints, result
    const result = h('div.ex-result', { id: 'exResult', 'aria-live': 'polite' });
    const hintBox = h('div.hints', { id: 'hints' });
    const check = h('button.btn.primary', { type: 'button', id: 'btnCheck' }, icon('check'), 'Check my answer');
    const hintBtn = h('button.btn', { type: 'button', id: 'btnHint' }, icon('hint'), 'A hint');
    const hints = x.hints || [];
    const showHints = () => {
      const n = prog().hints[id] || 0;
      hintBox.innerHTML = '';
      for (let i = 0; i < Math.min(n, hints.length); i++) hintBox.appendChild(h('div.ls-note.tip.hint' + (i === hints.length - 1 ? '.worked' : ''), icon(i === hints.length - 1 ? 'book' : 'hint'), h('div', h('b', i === hints.length - 1 ? 'Worked answer. ' : 'Hint ' + (i + 1) + '. '), inline(hints[i]))));
      hintBtn.disabled = n >= hints.length;
      hintBtn.lastChild.textContent = n >= hints.length ? 'No more hints' : n === hints.length - 1 ? 'Show the worked answer' : n ? 'Another hint' : 'A hint';
      hintBtn.style.display = hints.length ? '' : 'none';
    };
    hintBtn.addEventListener('click', async () => {
      const p = prog(), n = p.hints[id] || 0;
      if (n === hints.length - 1 && !(await T.UI.confirm('Show the worked answer?', 'You learn more by trying first. Show it anyway?', 'Show it', 'Keep trying'))) return;
      p.hints[id] = n + 1; saveProg(p); showHints();
    });
    check.addEventListener('click', () => {
      let a;
      try { a = A.get(); } catch (e) { a = undefined; }
      const r = T.Check.answer(x, a);
      if (A.mark) A.mark(r);
      result.innerHTML = '';
      result.className = 'ex-result ' + (r.ok ? 'ok' : 'bad');
      // the heading already says Correct or Not yet: drop a checker's own "Right." or "Not quite."
      const msg = String(r.message || '').replace(r.ok ? /^Right\.\s*/ : /^Not quite(?:\.|:)?\s*/, '').replace(/^./, (c) => c.toUpperCase());
      result.appendChild(h('div.ex-v', icon(r.ok ? 'check' : 'x'), h('b', r.ok ? 'Correct.' : 'Not yet.'), ' ', h('span', msg)));
      for (const d of r.details || []) result.appendChild(h('div.ex-d', inline(d)));
      if (r.counterexample !== undefined && A.tryString) {
        const b = h('button.btn.small', { type: 'button', id: 'btnTryCounter' }, icon('run'), 'Run your answer on ' + r.counterexample);
        b.addEventListener('click', () => A.tryString(r.counterexample === 'ε' ? '' : r.counterexample));
        result.appendChild(b);
      }
      if (r.ok) {
        mark('solved', id);
        const ch = C().chapterOf(x), ids = ch ? ch.exercises : [], k = ids.indexOf(id);
        if (!opts.inCourse && k + 1 < ids.length) result.appendChild(h('a.btn.small.primary', { href: '#exercise=' + ids[k + 1], id: 'btnNextEx' }, 'Next exercise', icon('stepOver')));
      }
    });
    box.appendChild(h('div.ex-tools', check, hintBtn, h('a.btn.ghost', { href: '#learn' }, 'All exercises')));
    box.append(result, hintBox);
    showHints();
    main.appendChild(box);
    for (const p of page.players) p.redraw();
    page.player = page.players[0] || null;
    T.UI.fitTables(box);
    page.check = () => check.click();
    page.answer = A;
    return page;
  }

  /** The answer area for an exercise's kind: {get() -> answer, mark(result), tryString(w)} */
  function answerUI(app, page, x, host, draft) {
    const K = T.Check;
    if (x.kind === 'program' || (x.kind === 'machine' && x.machine === 'tm' && (x.format === 'text' || x.format === 'macro' || (x.tapes || 1) > 1))) {
      const ta = programArea(typeof draft === 'string' ? draft : x.start || '', x.placeholder || (x.kind === 'program' ? 'Write the program here' : 'Write the machine here'));
      const sigma = K.alphabet(x.alphabet);
      if (sigma) host.appendChild(h('p.muted.ans-note', 'Alphabet: {' + sigma.join(', ') + '}' + (x.tapes > 1 ? ' · ' + x.tapes + ' tapes' : '')));
      host.appendChild(ta);
      requestAnimationFrame(() => T.UI.autosize(ta, 520));
      return { get: () => ta.value };
    }
    if (x.kind === 'transducer') return transducerUI(x, host, typeof draft === 'string' ? draft : x.start || (x.machine === 'mealy' ? 'mealy\nstart q0\n' : 'moore\nstart q0\nout q0 = ε\n'));
    if (x.kind === 'machine' || x.kind === 'regex' || x.kind === 'grammar') {
      const kind = x.kind === 'machine' ? x.machine : x.kind;
      const ed = makeEditor(host, kind, typeof draft === 'string' ? draft : x.start || '', () => {});
      page.editors.push(ed);
      const sigma = K.alphabet(x.alphabet);
      if (sigma) host.prepend(h('p.muted.ans-note', 'Alphabet: {' + sigma.join(', ') + '}' + (x.maxStates ? ' · at most ' + x.maxStates + ' states' : '') + (x.maxSize ? ' · at most ' + x.maxSize + ' parts' : '')));
      const rb = h('div.ans-try');
      host.appendChild(h('details.try', h('summary', 'Try your answer on a string'), rb));
      const box = runBox(app, page, { kind: kind, getText: () => ed.get(), input: '', idp: 'ans', summary: false, autorun: false });
      rb.appendChild(box);
      return { get: () => ed.get(), tryString(w) { const d = host.querySelector('details.try'); d.open = true; const i = box.querySelector('input'); i.value = w === '' ? 'ε' : w; box.querySelector('.btn.primary').click(); d.scrollIntoView({ block: 'nearest' }); } };
    }
    if (x.kind === 'table') {
      const S = K.tableSpec(x);
      const inputs = {};
      const tbl = h('table.fill-table', h('thead', h('tr', h('th', S.corner || ''), ...S.cols.map((c) => h('th', c)))));
      const body = h('tbody');
      S.rows.forEach((r, ri) => {
        const tr = h('tr', h('th', r));
        S.cols.forEach((c, ci) => {
          const key = S.cell(ri, ci);
          if (key === null) { tr.appendChild(h('td.none')); return; }
          const i = h('input.mono', { type: 'text', 'aria-label': (x.table === 'cyk' ? r + ', from ' + c + ' (position ' + (ci + 1) + ')' : r + (S.cols.length > 1 ? ', ' + c : '')), spellcheck: 'false', autocomplete: 'off', placeholder: S.kind === 'set' ? '∅' : '–' });
          if (draft && draft[key] !== undefined) i.value = draft[key];
          inputs[key] = i;
          tr.appendChild(h('td', i));
        });
        body.appendChild(tr);
      });
      tbl.appendChild(body);
      if (x.show) host.appendChild(subjectOf(x.show));
      else if (S.grammar) host.appendChild(h('div.gram.ans-gram', ...T.grammar.toString(S.grammar).split('\n').map((l) => h('div.rule', { html: T.highlightGrammarLine ? T.highlightGrammarLine(l, S.grammar.nonterminals) : l }))));
      if (x.table === 'cyk') host.appendChild(h('p.muted.ans-note', 'The word is ' + (x.word || '') + '. Each cell holds the nonterminals that derive the piece of the word starting under its column, as long as its row says.'));
      host.appendChild(h('div.fit-table.ans-table', tbl));
      host.appendChild(h('p.muted.ans-note', S.kind === 'set' ? 'Write a set as a, b, ε; leave a cell empty for ∅.' : S.kind === 'rhs' ? 'Write the right side of the rule, like a S b or ε; leave the cell empty when there is none.' : ''));
      return { get: () => Object.fromEntries(Object.entries(inputs).map(([k, i]) => [k, i.value])), mark(r) { for (const [k, i] of Object.entries(inputs)) { i.classList.toggle('right', !!(r.cells && r.cells[k])); i.classList.toggle('wrong', !!(r.cells && !r.cells[k])); } } };
    }
    if (x.kind === 'choice') {
      const many = Array.isArray(x.answer);
      const chosen = new Set([].concat(draft === undefined || draft === null ? [] : draft));
      const opts = h('div.choices', { role: many ? 'group' : 'radiogroup' });
      x.options.forEach((o, i) => {
        const b = h('button.quiz-opt.choice', { type: 'button', role: many ? 'checkbox' : 'radio', 'aria-checked': String(chosen.has(i)), dataset: { i: String(i) } }, h('span.box'), h('span', inline(o)));
        b.addEventListener('click', () => {
          if (!many) chosen.clear();
          if (chosen.has(i) && many) chosen.delete(i); else chosen.add(i);
          for (const c of opts.children) { const on = chosen.has(+c.dataset.i); c.setAttribute('aria-checked', String(on)); c.classList.toggle('on', on); c.classList.remove('right', 'wrong'); }
        });
        b.classList.toggle('on', chosen.has(i));
        opts.appendChild(b);
      });
      if (many) host.appendChild(h('p.muted.ans-note', 'Choose all that apply.'));
      host.appendChild(opts);
      return { get: () => (many ? [...chosen].sort() : chosen.size ? [...chosen][0] : null), mark(r) { for (const c of opts.children) { const i = +c.dataset.i; c.classList.toggle('right', r.ok && chosen.has(i)); c.classList.toggle('wrong', !r.ok && chosen.has(i) && !many); } } };
    }
    if (x.kind === 'string' || x.kind === 'number' || x.kind === 'set') {
      const i = h('input' + (x.kind !== 'number' ? '.mono' : ''), { type: 'text', id: 'ansText', 'aria-label': 'Your answer', placeholder: x.placeholder || (x.kind === 'number' ? 'a number' : x.kind === 'set' ? 'like {a, b}, (1, 2) or {{a, b}, {c}}' : x.set ? '{a, b}' : 'ε for the empty string'), spellcheck: 'false', autocomplete: 'off', inputmode: x.kind === 'number' ? 'decimal' : null });
      if (draft !== undefined && draft !== null) i.value = draft;
      i.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); document.getElementById('btnCheck').click(); } });
      host.appendChild(h('label.ans-line', h('span', 'Your answer'), i));
      return { get: () => i.value };
    }
    if (x.kind === 'pumping') return pumpUI(x, host);
    host.appendChild(h('p.muted', 'This kind of exercise (' + x.kind + ') has no answer area yet.'));
    return { get: () => null };
  }

  /** What a table is about, shown above it: {grammar} (coloured), {machine} (drawn) or {regex} */
  function subjectOf(show) {
    if (show.grammar !== undefined) {
      let nts = null;
      try { nts = T.grammar.parse(show.grammar).nonterminals; } catch (e) { nts = null; }
      return h('div.gram.ans-gram', ...String(show.grammar).split('\n').map((l) => h('div.rule', { html: T.highlightGrammarLine ? T.highlightGrammarLine(l, nts) : l })));
    }
    if (show.regex !== undefined) return h('pre.ls-code.ans-gram', T.highlightRegex ? { html: T.highlightRegex(show.regex) } : String(show.regex));
    if (show.machine !== undefined) {
      const box = h('div.ans-machine');
      const s = T.machineSummary(show.machine);
      box.appendChild(h('div.run-head', h('span.model-kind', s.kind), h('span.model-facts', ...s.facts.map((f) => h('span', f)))));
      const art = h('div.rel-art');
      box.appendChild(art);
      requestAnimationFrame(() => { try { const m = T.Machine.parse(show.machine); const st = new T.Stage(art, { label: 'The machine' }); st.show({ items: T.Kit.graph.draw(m, { pos: T.Kit.graph.layout(m).pos }).items }, { duration: 0 }); } catch (e) { art.remove(); } });
      return box;
    }
    return h('div');
  }

  /** A text box for programs: monospaced, keeps every space and line, Tab indents */
  function programArea(text, placeholder) {
    const ta = h('textarea.mono.prog-answer', { id: 'ansProgram', spellcheck: 'false', autocomplete: 'off', 'aria-label': 'Your answer', placeholder, rows: '8', wrap: 'off' });
    ta.value = text;
    ta.addEventListener('keydown', (e) => { if (e.key === 'Tab' && !e.shiftKey) { e.preventDefault(); document.execCommand('insertText', false, '  '); } });
    return ta;
  }
  /** A Moore or Mealy machine as text, drawn as it is typed, with a string to try */
  function transducerUI(x, host, text) {
    const K = T.Check;
    const ta = programArea(text, 'moore\nstart q0\nq0 -a-> q1\nout q1 = 1');
    const err = h('div.err', { role: 'alert' });
    const art = h('div.rel-art.trans-art');
    const stage = new T.Stage(art, { label: 'The machine' });
    const draw = () => {
      const r = K.parseTransducer(ta.value);
      err.textContent = r.errors[0] || '';
      if (r.errors.length && !r.m.states.length) return;
      const m = r.m, name = (q) => (m.type === 'moore' ? q + '/' + (m.out[q] === undefined || m.out[q] === '' ? 'ε' : m.out[q]) : q);
      const merged = new Map();
      for (const t of m.trans) { const k = t.from + '>' + t.to; const l = m.type === 'mealy' ? t.sym + '/' + (t.out === '' ? 'ε' : t.out) : t.sym; merged.set(k, merged.has(k) ? merged.get(k) + ', ' + l : l); }
      const d = { kind: 'dfa', states: m.states.map(name), start: name(m.start), accept: [], trans: [...merged].map(([k, l]) => { const [a, b] = k.split('>'); return { from: name(a), to: name(b), label: l }; }) };
      try { stage.show({ items: T.Kit.graph.draw(d, { pos: T.Kit.graph.layout(d).pos }).items }, { duration: 200 }); } catch (e) { /* half typed */ }
    };
    ta.addEventListener('input', T.UI.debounce(draw, 200));
    const inp = h('input.mono', { type: 'text', 'aria-label': 'An input to try', placeholder: 'an input string', spellcheck: 'false' });
    const out = h('span.verdict.wait', 'output');
    const go = h('button.btn.small', { type: 'button' }, icon('run'), 'Try');
    go.addEventListener('click', () => { const r = K.parseTransducer(ta.value); if (r.errors.length) { out.textContent = r.errors[0]; return; } const o = K.runTransducer(r.m, inp.value.trim()); out.className = 'verdict ' + (o.complete ? 'yes' : 'no'); out.textContent = o.complete ? 'output ' + K.show(o.output) : 'stuck'; });
    host.append(h('p.muted.ans-note', 'One line per move: q0 -a-> q1 (Moore) or q0 -a/1-> q1 (Mealy); out q0 = 1 gives a Moore state its output; the first line says moore or mealy.'), h('div.trans-grid', ta, art), err, h('div.sb-run', inp, go, out));
    requestAnimationFrame(() => { T.UI.autosize(ta, 420); draw(); });
    return { get: () => ta.value, tryString(w) { inp.value = w; go.click(); } };
  }

  /** The pumping game, move by move: the computer's p, your s, its split, your i */
  function pumpUI(x, host) {
    let G = T.Check.pumpGame(x);
    const lang = G.lang;
    const state = { s: null, i: null };
    const log = h('ol.pump-log', { 'aria-live': 'polite' });
    const sIn = h('input.mono', { type: 'text', id: 'pumpS', 'aria-label': 'Your string s', spellcheck: 'false', autocomplete: 'off', placeholder: 'a string of the language, at least ' + G.p + ' long' });
    const sGo = h('button.btn.small.primary', { type: 'button', id: 'pumpSGo' }, 'Play s');
    const iIn = h('input', { type: 'number', id: 'pumpI', min: '0', value: '0', 'aria-label': 'Your i' });
    const iGo = h('button.btn.small.primary', { type: 'button', id: 'pumpIGo' }, 'Pump');
    const again = h('button.btn.small', { type: 'button', id: 'pumpAgain' }, icon('restart'), 'Play again');
    const splitEl = h('div.pump-split');
    const iRow = h('div.pump-row.hidden', h('label', h('span', 'Your i'), iIn), iGo);
    const say = (t, cls) => log.appendChild(h('li' + (cls ? '.' + cls : ''), t));
    const reset = () => { G = T.Check.pumpGame(x); state.s = state.i = null; log.innerHTML = ''; splitEl.innerHTML = ''; iRow.classList.add('hidden'); sIn.disabled = sGo.disabled = false; say('The computer claims ' + (lang.notation || lang.name) + ' is ' + (x.cf ? 'context-free' : 'regular') + ', with pumping length p = ' + G.p + '.'); };
    sGo.addEventListener('click', () => {
      const s = sIn.value.trim() === 'ε' ? '' : sIn.value.trim();
      const r = G.word(s);
      if (!r.ok) { say(r.say, 'bad'); return; }
      state.s = s;
      sIn.disabled = sGo.disabled = true;
      say('You choose s = ' + (s || 'ε') + '.');
      const sp = G.split();
      say('The computer splits it: ' + sp.parts.map(([k, v]) => k + ' = ' + (v || 'ε')).join(', ') + '.');
      splitEl.innerHTML = '';
      for (const [k, v] of sp.parts) splitEl.appendChild(h('span.part.p-' + k, h('b', k), h('span.mono', v || 'ε')));
      iRow.classList.remove('hidden');
      iIn.focus();
    });
    iGo.addEventListener('click', () => {
      const i = +iIn.value;
      if (!Number.isInteger(i) || i < 0) { say('i is a whole number, 0 or more.', 'bad'); return; }
      const r = G.pump(i);
      state.i = i;
      say(r.say, r.win ? 'good' : 'bad');
      iGo.disabled = true;
    });
    again.addEventListener('click', () => { iGo.disabled = false; reset(); });
    sIn.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); sGo.click(); } });
    iIn.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); iGo.click(); } });
    host.append(h('div.pump', h('div.pump-row', h('label', h('span', 'Your string s'), sIn), sGo, again), splitEl, iRow, log));
    reset();
    return { get: () => ({ s: state.s, i: state.i }) };
  }

  // ---- guided tours -------------------------------------------------------------------------------------------
  T.Tour = {
    active: null,
    start(id) {
      const t = C() && C().tours.get(id);
      if (!t) { T.UI.toast('There is no tour called ' + id + '.', 'err'); return; }
      this.close();
      this.active = { t, i: 0 };
      this.show();
    },
    close() {
      if (this.box) this.box.remove();
      this.box = null;
      document.querySelectorAll('.tour-hi').forEach((e) => e.classList.remove('tour-hi'));
      document.removeEventListener('keydown', this.onKey, true);
      this.active = null;
    },
    onRoute() { /* a tour that changes the route waits for the page in show() */ },
    async show() {
      const a = this.active;
      if (!a) return;
      const st = a.t.steps[a.i];
      if (st.route !== undefined && location.hash.replace(/^#/, '') !== st.route) { location.hash = st.route; await new Promise((r) => setTimeout(r, 120)); }
      if (st.before) { try { st.before(T.app); } catch (e) { /* the step still shows */ } }
      let target = null;
      for (let k = 0; k < 30 && st.target && !(target = document.querySelector(st.target)); k++) await new Promise((r) => setTimeout(r, 60));
      if (this.active !== a) return;
      if (this.box) this.box.remove();
      document.querySelectorAll('.tour-hi').forEach((e) => e.classList.remove('tour-hi'));
      if (target) { target.classList.add('tour-hi'); target.scrollIntoView({ block: 'nearest', behavior: 'smooth' }); }
      const last = a.i === a.t.steps.length - 1;
      const back = h('button.btn.small', { type: 'button', id: 'tourBack', disabled: a.i === 0 }, 'Back');
      const next = h('button.btn.small.primary', { type: 'button', id: 'tourNext' }, last ? 'Finish' : 'Next');
      const close = h('button.icon-btn.tour-x', { type: 'button', id: 'tourClose', 'aria-label': 'Close the tour' }, icon('x'));
      back.addEventListener('click', () => { a.i--; this.show(); });
      next.addEventListener('click', () => { if (last) { const p = prog(); p.tours[a.t.id] = Date.now(); saveProg(p); this.close(); T.UI.toast('Tour finished.', 'ok', 2000); } else { a.i++; this.show(); } });
      close.addEventListener('click', () => this.close());
      this.box = h('div.tour', { role: 'dialog', 'aria-label': a.t.title, id: 'tourBox' },
        h('div.tour-k', a.t.title + ' · ' + (a.i + 1) + ' of ' + a.t.steps.length), close,
        h('div.tour-t', inline(st.text)), h('div.tour-b', back, next));
      document.body.appendChild(this.box);
      this.place(target);
      this.onKey = this.onKey || ((e) => { if (!this.active || T.UI.anyModalOpen()) return; if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); this.close(); } });
      document.addEventListener('keydown', this.onKey, true);
      setTimeout(() => next.focus(), 30);
    },
    place(target) {
      const b = this.box, bw = b.offsetWidth, bh = b.offsetHeight, W = innerWidth, H = innerHeight;
      let x, y;
      if (target) {
        const r = target.getBoundingClientRect();
        x = Math.min(W - bw - 12, Math.max(12, r.left));
        y = r.bottom + 12;
        if (y + bh > H - 12) y = r.top - bh - 12;
        if (y < 12) y = Math.max(12, Math.min(H - bh - 12, r.top + 12));
      } else { x = (W - bw) / 2; y = (H - bh) / 2; }
      b.style.left = Math.round(x) + 'px'; b.style.top = Math.round(y) + 'px';
    },
  };
})();
