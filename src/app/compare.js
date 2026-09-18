// Compare: two runs side by side, stepping together. Either one topic on two inputs (a string that is
// accepted beside one that is not, a short carry beside a long one) or two topics on their own inputs
// (a topic may name its partner with compareWith). One set of controls drives both; each side keeps its
// narration and counters, so where they part ways and how much work each does is plain to see.
// #compare chooses, #compare=a,b shows topics a and b (a,a for one topic on two inputs).
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const store = T.UI.storage;

  /** Pairs worth comparing: every topic's compareWith, and topics with two or more presets (two inputs) */
  function pairs() {
    const out = [], seen = new Set();
    for (const t of T.topics) {
      const o = t.compareWith && T.byId(t.compareWith);
      if (!o) continue;
      const k = [t.id, o.id].sort().join(',');
      if (seen.has(k)) continue;
      seen.add(k);
      out.push([t, o]);
    }
    return out;
  }
  const differs = (a, b) => JSON.stringify(a) !== JSON.stringify(b);
  /** A second input for the same topic: the first preset that differs from the first input */
  function otherInput(t, input) {
    for (const p of t.presets || []) { const v = T.inputOf(t, Object.assign({}, T.inputOf(t), p.values)); if (differs(v, input) && !T.checkInput(t, v)) return v; }
    return input;
  }

  /** One side: a small input bar and an embedded player with no controls of its own */
  class Side {
    constructor(app, el, t, input, tag) {
      this.app = app; this.t = t; this.el = el; this.tag = tag; this.input = input;
      const head = h('div.cmp-head', h('span.cmp-tag', tag), h('div.cmp-title', h('h3', t.title), h('a', { href: '#topic=' + t.id }, 'Open on its own')));
      this.bar = h('div.cmp-inputs');
      this.err = h('div.err', { role: 'alert' });
      this.host = h('div.cmp-player');
      el.append(head, this.bar, this.err, this.host);
      this.buildInputs();
      this.run();
    }
    buildInputs() {
      const t = this.t, bar = this.bar;
      bar.innerHTML = '';
      this.fields = {};
      const id = (x) => 'cmp' + this.tag + '-' + x;
      for (const inp of t.inputs || []) {
        if (inp.kind === 'hidden') continue;
        const v = this.input[inp.id];
        let f;
        if (inp.kind === 'machine' || inp.kind === 'grammar') {
          const s = inp.kind === 'machine' ? T.machineSummary(v) : T.grammarSummary(v);
          const ed = h('button.btn.small', { type: 'button', id: id('edit-' + inp.id) }, icon('edit'), 'Edit');
          ed.addEventListener('click', () => {
            const done = (text) => { if (text === null || text === undefined) return; this.input = Object.assign({}, this.input, { [inp.id]: text }); this.apply(); };
            if (inp.kind === 'machine' && T.editMachine) T.editMachine(String(this.input[inp.id]), { kind: inp.machine }).then(done);
            else if (T.editGrammar) T.editGrammar(String(this.input[inp.id])).then(done);
          });
          bar.appendChild(h('div.cmp-model', h('span.model-kind', s.kind), h('span.cmp-facts', s.facts.slice(0, 3).join(' · ')), ed));
          continue;
        }
        if (inp.kind === 'choice') f = h('select', { id: id(inp.id), 'aria-label': inp.label }, ...(inp.options || []).map((o) => h('option', { value: o.value, selected: o.value === v }, o.label)));
        else f = h('input', { type: inp.kind === 'number' ? 'number' : 'text', id: id(inp.id), 'aria-label': inp.label, value: T.showInput(inp, v), spellcheck: 'false', placeholder: inp.kind === 'string' ? 'ε (empty)' : '', class: inp.kind === 'number' ? '' : 'mono' });
        f.addEventListener('keydown', (e) => { if (e.key === 'Enter') { e.preventDefault(); this.apply(); } });
        if (inp.kind === 'choice') f.addEventListener('change', () => this.apply());
        this.fields[inp.id] = { inp, f };
        bar.appendChild(h('label', h('span', inp.label), f));
      }
      if (Object.keys(this.fields).length) { const go = h('button.btn.small.primary', { type: 'button', id: id('run') }, icon('run'), 'Run'); go.addEventListener('click', () => this.apply()); bar.appendChild(go); }
      if ((t.presets || []).length) {
        const sel = h('select.cmp-presets', { id: id('preset'), 'aria-label': 'Examples' }, h('option', { value: '' }, 'Examples…'), ...t.presets.map((p, i) => h('option', { value: String(i) }, p.label)));
        sel.addEventListener('change', () => { if (sel.value === '') return; this.input = T.inputOf(t, Object.assign({}, T.inputOf(t), t.presets[+sel.value].values)); this.buildInputs(); this.run(); this.onChange && this.onChange(); });
        bar.appendChild(sel);
      }
    }
    apply() {
      const next = Object.assign({}, this.input);
      for (const [k, { inp, f }] of Object.entries(this.fields)) next[k] = T.parseInput(inp, f.value);
      const e = T.checkInput(this.t, next);
      this.err.textContent = e || '';
      if (e) return;
      this.input = next;
      this.buildInputs();
      this.run();
      if (this.onChange) this.onChange();
    }
    run() {
      if (this.player) this.player.dispose();
      this.host.innerHTML = '';
      this.player = new T.Player(this.app, this.host, { topic: this.t, input: this.input, embed: true, side: false, bare: true, counters: true, idp: 'cmp' + this.tag + '-' });
    }
    get frames() { return this.player.frames; }
    get i() { return this.player.i; }
    get done() { return this.player.i >= this.player.frames.length - 1; }
    go(i, instant) { this.player.go(i, instant); }
  }

  T.Compare = {
    pairs,
    open(app, main, arg) {
      const ids = (arg || '').replace(/^=/, '').split(',').filter(Boolean);
      const a = T.byId(ids[0]), b = T.byId(ids[1] || ids[0]);
      if (!a || !b) return this.chooser(app, main, a);
      return this.view(app, main, a, b);
    },
    chooser(app, main, first) {
      document.title = 'Compare · Tooring';
      const box = h('div.home.compare-pick', { id: 'compareChooser' });
      box.append(h('div.crumbs', 'Tooring'), h('h1.page-title', 'Compare'), h('p.lead', 'Run two things side by side, step for step: one topic on two inputs, or two topics that do the same job in different ways. One set of controls moves both.'));
      const grid = h('div.fam-grid');
      const card = (title, sub, hash) => { const c = h('button.fam-card.plain', { type: 'button' }, h('div.fc-body', h('h3', title), h('p', sub))); c.addEventListener('click', () => { location.hash = hash; }); return c; };
      for (const [x, y] of pairs()) grid.appendChild(card(x.title + ' and ' + y.title, (T.familyOf(x) || {}).title || '', 'compare=' + x.id + ',' + y.id));
      // a few topics on two of their own inputs
      const two = T.topics.filter((t) => (t.presets || []).length >= 2).slice(0, 9);
      for (const t of two) grid.appendChild(card(t.title, 'Two inputs side by side: ' + t.presets[0].label + ', and ' + t.presets[1].label + '.', 'compare=' + t.id + ',' + t.id));
      if (grid.children.length) box.appendChild(grid);
      else box.appendChild(T.UI.empty('compare', 'Nothing to compare yet', 'When topics are here, any one of them can be run on two inputs side by side.'));
      if (T.topics.length) {
        const opt = (sel) => T.topics.map((t) => h('option', { value: t.id, selected: sel && sel.id === t.id }, ((T.familyOf(t) || {}).title || '') + ': ' + t.title));
        const s1 = h('select', { id: 'cmpA', 'aria-label': 'First topic' }, ...opt(first));
        const s2 = h('select', { id: 'cmpB', 'aria-label': 'Second topic' }, ...opt(first));
        const go = h('button.btn.primary', { type: 'button', id: 'cmpGo' }, icon('compare'), 'Compare');
        go.addEventListener('click', () => { location.hash = 'compare=' + s1.value + ',' + s2.value; });
        box.append(h('h2.sub-title', 'Or pick any two'), h('p.muted', 'Pick the same topic twice to give it two inputs.'), h('div.cmp-pick', s1, s2, go));
      }
      main.appendChild(box);
      return { dispose() {} };
    },
    view(app, main, a, b) {
      const same = a === b;
      document.title = (same ? a.title + ': two inputs' : a.title + ' and ' + b.title) + ' · Compare · Tooring';
      const root = h('div.compare', { id: 'compareView' });
      const ia = (() => { const v = T.inputOf(a, store.get('in:' + a.id, null)); return T.checkInput(a, v) ? T.inputOf(a) : v; })();
      let ib = same ? otherInput(a, ia) : (() => { const v = T.inputOf(b, store.get('in:' + b.id, null)); return T.checkInput(b, v) ? T.inputOf(b) : v; })();
      const swap = h('button.btn.small', { type: 'button', id: 'cmpSwap', title: 'Swap the two sides' }, icon('convert'), 'Swap');
      const other = h('a.btn.small', { href: '#compare=' + a.id }, 'Pick others');
      root.appendChild(h('div.t-head', h('div', h('div.crumbs', h('a', { href: '#compare' }, 'Compare')), h('h1', same ? a.title + ': two inputs' : a.title + ' and ' + b.title),
        h('p', same ? 'The same topic on two inputs. Change either side\'s input and run it; both step together.' : 'Two topics, each on its own input, stepping together.')), h('div.t-actions', swap, other)));
      // one set of controls for both
      let playing = false, timer = null;
      const playBtn = h('button.icon-btn.play', { type: 'button', id: 'cmpPlay', 'aria-label': 'Play', title: 'Play both (Space)' }, icon('run'));
      const pos = h('span.pos', { id: 'cmpPos' });
      const speed = h('input', { type: 'range', min: '0', max: String(T.SPEEDS.length - 1), value: String(app.settings.speed), 'aria-label': 'Speed', id: 'cmpSpeed' });
      speed.addEventListener('input', () => { app.settings.speed = +speed.value; app.saveSettings(); });
      const grid = h('div.cmp-grid');
      const L = h('div.card.cmp-side', { id: 'cmpLeft' }), R = h('div.card.cmp-side', { id: 'cmpRight' });
      grid.append(L, R);
      const ib2 = (id, ic, title, fn) => { const x = h('button.icon-btn', { type: 'button', id, title, 'aria-label': title }, icon(ic)); x.addEventListener('click', () => { pause(); fn(); }); return x; };
      const bar = h('div.card.controls.cmp-controls', ib2('cmpFirst', 'restart', 'Both from the start (Home)', () => goAll(0)), ib2('cmpBack', 'stepBack', 'Step back (←)', () => step(-1)), playBtn, ib2('cmpFwd', 'stepOver', 'Next step (→)', () => step(1)), pos, h('label.speed', h('span', 'Speed'), speed));
      root.append(bar, grid);
      main.appendChild(root);
      const left = new Side(app, L, a, ia, 'A'), right = new Side(app, R, b, ib, 'B');
      const n = () => Math.max(left.frames.length, right.frames.length);
      const status = () => { pos.textContent = 'A ' + (left.i + 1) + '/' + left.frames.length + ' · B ' + (right.i + 1) + '/' + right.frames.length; };
      // both sides move by the same number of steps; a side that has finished stays on its last frame
      const goAll = (i, instant) => { left.go(Math.min(i, left.frames.length - 1), instant); right.go(Math.min(i, right.frames.length - 1), instant); k = i; status(); };
      let k = 0;
      const step = (d) => goAll(Math.max(0, Math.min(n() - 1, k + d)));
      const setPlay = (on) => { playing = on; playBtn.innerHTML = ''; playBtn.appendChild(icon(on ? 'pause' : 'run')); playBtn.setAttribute('aria-label', on ? 'Pause' : 'Play'); };
      const pause = () => { setPlay(false); clearTimeout(timer); };
      const tick = () => {
        clearTimeout(timer);
        if (!playing || !root.isConnected) return;
        if (k >= n() - 1) { pause(); return; }
        timer = setTimeout(() => { step(1); tick(); }, T.SPEEDS[app.settings.speed]);
      };
      const play = () => { if (k >= n() - 1) goAll(0, true); setPlay(true); tick(); };
      playBtn.addEventListener('click', () => (playing ? pause() : play()));
      left.onChange = right.onChange = () => { pause(); goAll(0, true); };
      swap.addEventListener('click', () => { if (!same) location.hash = 'compare=' + b.id + ',' + a.id; else { const x = left.input; left.input = right.input; right.input = x; left.buildInputs(); right.buildInputs(); left.run(); right.run(); goAll(0, true); } });
      goAll(0, true);
      // what the keyboard drives
      const facade = {
        get frames() { return { length: n() }; },
        get i() { return k; },
        get stage() { return left.player.stage; },
        toggle: () => (playing ? pause() : play()), play, pause, step: (d) => { pause(); step(d); }, go: (i, instant) => goAll(i, instant),
        fit: () => { left.player.stage.fit(); right.player.stage.fit(); },
        redraw: () => { left.player.redraw(); right.player.redraw(); },
        speedEl: speed, sides: [left, right],
      };
      return { player: facade, left, right, dispose() { pause(); left.player.dispose(); right.player.dispose(); } };
    },
  };
})();
