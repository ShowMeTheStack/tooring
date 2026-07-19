// The topic player: the inputs and presets, the stage with its narration and controls (play, pause, step,
// scrub, speed, zoom, keyboard), the definition panel (the formal definition or table, with what the step
// uses lit), the list of steps, the counters, predictions on the way and the quiz at the end.
// On a phone the stage comes first with the narration under it, the inputs follow, and the definition
// and steps open in a drawer from the bottom.
// Other pages embed the same player (opts.embed): the sandbox, the kit gallery, lessons, Compare.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const store = T.UI.storage;
  const SPEEDS = [1800, 1250, 880, 620, 420, 260];
  T.SPEEDS = SPEEDS;
  const KIND_NAME = { dfa: 'DFA', nfa: 'NFA', pda: 'PDA', tm: 'Turing machine' };

  /** A one-line summary of a machine's text: {kind, title, facts: [..], error} */
  T.machineSummary = function (text) {
    try {
      const m = T.Machine.parse(text);
      const fa = m.kind === 'dfa' || m.kind === 'nfa';
      const eps = fa && T.Machine.moves(m).some((v) => v.sym === '');
      const moves = fa ? T.Machine.moves(m).length : m.trans.length;
      const sigma = T.Machine.alphabet(m);
      const facts = [m.states.length + ' state' + (m.states.length === 1 ? '' : 's'), moves + ' ' + (fa ? 'move' : 'rule') + (moves === 1 ? '' : 's'), 'start ' + m.start];
      if (m.accept.length) facts.push('accept ' + m.accept.join(' '));
      if (sigma.length && sigma.length <= 6) facts.push('Σ = {' + sigma.join(', ') + '}');
      return { kind: eps ? 'ε-NFA' : KIND_NAME[m.kind] || m.kind, facts };
    } catch (e) {
      // a form the diagram reader does not know (several tapes, a nondeterministic machine): count its rules
      const lines = String(text || '').split('\n').map((l) => l.trim()).filter((l) => l && !/^(#|\/\/)/.test(l));
      const rules = lines.filter((l) => /->|→/.test(l)).length;
      const start = (lines.find((l) => /^start\b/i.test(l)) || '').replace(/^start:?\s*/i, '');
      return { kind: 'Machine', facts: [rules + ' rule' + (rules === 1 ? '' : 's')].concat(start ? ['start ' + start] : []) };
    }
  };
  /** The same for a grammar */
  T.grammarSummary = function (text) {
    const r = T.readGrammar ? T.readGrammar(text) : { ok: false };
    if (!r.ok) return { kind: 'Grammar', facts: [String(text || '').split('\n').filter((l) => l.trim()).length + ' lines'], error: r.error };
    return { kind: 'Grammar', facts: [r.nonterminals.length + ' nonterminal' + (r.nonterminals.length === 1 ? '' : 's'), r.rules + ' rule' + (r.rules === 1 ? '' : 's'), 'start ' + r.start, r.terminals.length && r.terminals.length <= 6 ? 'terminals ' + r.terminals.join(' ') : null].filter(Boolean) };
  };

  class Player {
    /**
     * opts: {topic, input, embed (no head, inputs or quiz), side: false (no side panel), bare (no controls:
     * Compare drives it), counters: true (counters under the narration), idp (id prefix), onFrame(i)}
     */
    constructor(app, main, opts) {
      this.app = app;
      this.t = opts.topic;
      this.f = T.familyOf(this.t);
      this.opts = opts;
      this.input = opts.input || T.inputOf(this.t);
      this.i = 0;
      this.frames = [];
      this.playing = false;
      this.timer = null;
      this.answered = new Set();
      this.root = h('div.topic' + (opts.embed ? '.embed' : ''), { dataset: { topic: this.t.id } });
      main.appendChild(this.root);
      this.build();
      // embedded players are many to a page: their element ids get a prefix
      if (opts.idp) this.root.querySelectorAll('[id]').forEach((e) => { if (!e.closest('svg')) e.id = opts.idp + e.id; });
      this.run();
      this.onResize = T.UI.debounce(() => { if (this.disposed) return; if (this.tabBody) T.UI.fitTables(this.tabBody); this.stage.applyView(); if (this.frames[this.i] && this.frames[this.i].narrowView) this.go(this.i, true); }, 120);
      window.addEventListener('resize', this.onResize);
    }
    dispose() { this.pause(); this.disposed = true; window.removeEventListener('resize', this.onResize); }

    // ---- layout -------------------------------------------------------------------------------------
    build() {
      const t = this.t;
      if (!this.opts.embed) {
        const part = T.topicPart(t);
        const quiz = h('button.btn', { type: 'button', id: 'btnQuiz', disabled: !(t.quiz && t.quiz.length), title: 'Questions on this topic (Q)' }, icon('check'), h('span.lbl', 'Quiz'));
        quiz.addEventListener('click', () => this.quiz());
        const cmp = h('button.btn', { type: 'button', id: 'btnCompare', title: 'Run this topic side by side with another input or another topic' }, icon('compare'), h('span.lbl', 'Compare'));
        cmp.addEventListener('click', () => { location.hash = 'compare=' + t.id + ',' + (t.compareWith && T.byId(t.compareWith) ? t.compareWith : t.id); });
        const share = h('button.btn', { type: 'button', id: 'btnShare', title: 'Copy a link to this topic with this input' }, icon('link'), h('span.lbl', 'Share'));
        share.addEventListener('click', () => this.share());
        const crumbs = h('div.crumbs', part ? h('a', { href: '#part=' + part.id }, 'Part ' + part.n + ': ' + part.title) : null, this.f ? ' › ' + this.f.title : '');
        this.root.appendChild(h('div.t-head', h('div', crumbs, h('h1', t.title), h('p', t.blurb || '')), h('div.t-actions', quiz, cmp, share)));
        this.inputsEl = h('div.inputs', { id: 'inputs' });
        this.root.appendChild(this.inputsEl);
        this.buildInputs();
      } else if (this.opts.inputs && (t.inputs || []).length) {
        // an embedded player may show its inputs too (a lesson that wants the reader to try things)
        this.inputsEl = h('div.inputs.embed-inputs', { id: 'inputs' });
        this.root.appendChild(this.inputsEl);
        this.buildInputs();
      }
      this.stageWrap = h('div.stage-wrap', { id: this.opts.embed ? 'sbStage' : 'stageWrap' });
      this.stage = new T.Stage(this.stageWrap, { label: t.title, reserveRight: 52 });
      this.stage.onPick = (key) => this.pick(key);
      this.stage.enableZoom();
      const zb = (id, ic, title, fn) => { const b = h('button.icon-btn.zbtn', { type: 'button', id, 'aria-label': title, title }, icon(ic)); b.addEventListener('click', fn); return b; };
      const zIn = zb('btnZoomIn', 'zoomIn', 'Zoom in (+)', () => this.stage.setZoom(this.stage.zoom * 1.4, true));
      const zOut = zb('btnZoomOut', 'zoomOut', 'Zoom out (−)', () => this.stage.setZoom(this.stage.zoom / 1.4, true));
      const zFit = zb('btnZoomFit', 'fit', 'Fit to the stage (F)', () => this.stage.fit());
      this.stage.onZoom = (z) => { zOut.disabled = z <= 1; zFit.disabled = z <= 1; this.stageWrap.classList.toggle('zoomed', z > 1); };
      this.stage.onZoom(1);
      const zFull = zb('btnFull', 'max', 'The stage alone, on the whole screen (Shift+F)', () => this.fullscreen());
      this.zFull = zFull;
      this.stageWrap.appendChild(h('div.zoom', zIn, zOut, zFit, zFull));
      this.sayEl = h('div.say', { id: this.opts.embed ? 'sbSay' : 'say', 'aria-live': 'polite' });
      this.playBtn = h('button.icon-btn.play', { type: 'button', id: 'btnPlay', 'aria-label': 'Play', title: 'Play (Space)' }, icon('run'));
      this.playBtn.addEventListener('click', () => this.toggle());
      const ib = (id, ic, title, fn) => { const b = h('button.icon-btn', { type: 'button', id, 'aria-label': title, title }, icon(ic)); b.addEventListener('click', fn); return b; };
      this.backBtn = ib('btnBack', 'stepBack', 'Step back (←)', () => this.step(-1));
      this.fwdBtn = ib('btnFwd', 'stepOver', 'Next step (→)', () => this.step(1));
      const first = ib('btnFirst', 'restart', 'From the start (Home)', () => { this.pause(); this.go(0); });
      this.range = h('input', { type: 'range', min: '0', max: '0', value: '0', id: 'timeline', 'aria-label': 'Timeline' });
      this.range.addEventListener('input', () => { this.pause(); this.go(+this.range.value, true); });
      this.marks = h('div.marks');
      this.speedEl = h('input', { type: 'range', min: '0', max: String(SPEEDS.length - 1), value: String(this.app.settings.speed), id: 'speed', 'aria-label': 'Speed' });
      this.speedEl.addEventListener('input', () => { this.app.settings.speed = +this.speedEl.value; this.app.saveSettings(); });
      this.posEl = h('span.pos', { id: 'pos' });
      const big = ib('btnBig', 'full', 'A bigger stage (B)', () => this.bigger());
      // on a phone the definition and steps live in a drawer that this opens
      const drawerBtn = this.opts.side === false ? null : h('button.btn.small.drawer-btn', { type: 'button', id: 'btnDrawer', 'aria-expanded': 'false', 'aria-controls': 'sidePanel', title: 'The definition and the steps (D)' }, icon('drawer'), 'Definition');
      if (drawerBtn) drawerBtn.addEventListener('click', () => this.drawer());
      this.drawerBtn = drawerBtn;
      const controls = h('div.controls', first, this.backBtn, this.playBtn, this.fwdBtn, h('div.timeline', this.range, this.marks), this.posEl, h('label.speed', h('span', 'Speed'), this.speedEl), big, drawerBtn);
      const stageCard = h('div.card.stage-card', this.stageWrap, this.sayEl, this.opts.bare ? null : controls);
      if (this.opts.counters) { this.countersEl = h('div.counters.inline', { id: 'counters' }); stageCard.appendChild(this.countersEl); }
      if (this.opts.side === false) { this.root.appendChild(stageCard); this.tabs = {}; return; }
      this.tabs = {};
      const tabBar = h('div.tabs', { role: 'tablist', 'aria-label': 'Panels' });
      this.tabBody = h('div.tab-body', { id: 'tabBody', role: 'tabpanel' });
      for (const [k, label] of [['def', 'Definition'], ['steps', 'Steps']]) {
        const b = h('button', { type: 'button', role: 'tab', id: 'tab-' + k, 'aria-selected': 'false' }, label);
        b.addEventListener('click', () => this.showTab(k));
        b.addEventListener('keydown', (e) => { if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') { e.preventDefault(); e.stopPropagation(); const n = k === 'def' ? 'steps' : 'def'; this.showTab(n); this.tabs[n].focus(); } });
        tabBar.appendChild(b);
        this.tabs[k] = b;
      }
      const close = h('button.icon-btn.drawer-close', { type: 'button', id: 'btnDrawerClose', 'aria-label': 'Close the panel', title: 'Close (Esc)' }, icon('x'));
      close.addEventListener('click', () => this.drawer(false));
      tabBar.appendChild(close);
      this.countersEl = h('div.counters', { id: 'counters' });
      this.sideCard = h('div.card.side-card', { id: 'sidePanel' }, tabBar, this.tabBody, this.countersEl);
      this.scrim = h('div.drawer-scrim', { 'aria-hidden': 'true' });
      this.scrim.addEventListener('click', () => this.drawer(false));
      this.root.appendChild(h('div.work', stageCard, this.sideCard, this.scrim));
      this.tab = store.get('tab', 'def');
    }
    bigger() { this.stageWrap.classList.toggle('big'); this.redraw(); }
    /** The stage card alone over the whole window (Esc or the button again to leave) */
    fullscreen(on) {
      const card = this.stageWrap.closest('.stage-card');
      on = on === undefined ? !card.classList.contains('fullscreen') : !!on;
      card.classList.toggle('fullscreen', on);
      document.body.classList.toggle('stage-full', on);
      this.zFull.innerHTML = ''; this.zFull.appendChild(icon(on ? 'min' : 'max'));
      this.zFull.setAttribute('aria-label', on ? 'Leave the full-screen stage' : 'The stage alone, on the whole screen');
      this.zFull.setAttribute('aria-pressed', String(on));
      this.redraw();
    }
    /** Open or close the phone drawer (toggle when open is not given) */
    drawer(open) {
      if (!this.sideCard) return;
      const on = open === undefined ? !this.root.classList.contains('drawer-open') : !!open;
      this.root.classList.toggle('drawer-open', on);
      if (this.drawerBtn) this.drawerBtn.setAttribute('aria-expanded', String(on));
      if (on) { T.UI.fitTables(this.tabBody); const f = this.tabs[this.tab]; if (f) setTimeout(() => f.focus(), 30); } else if (this.drawerBtn && this.drawerBtn.offsetParent) this.drawerBtn.focus();
    }

    // ---- inputs ----------------------------------------------------------------------------------------
    buildInputs() {
      const t = this.t, el = this.inputsEl;
      el.innerHTML = '';
      this.fields = {};
      for (const inp of t.inputs || []) {
        if (inp.kind === 'hidden') continue;
        const v = this.input[inp.id];
        let field;
        const id = 'in-' + inp.id;
        if (inp.kind === 'machine' || inp.kind === 'grammar') { el.appendChild(this.modelField(inp, v)); continue; }
        if (inp.kind === 'choice') field = h('select', { id, 'aria-label': inp.label }, ...(inp.options || []).map((o) => h('option', { value: o.value, selected: o.value === v }, o.label)));
        else if (inp.kind === 'number') field = h('input', { type: 'number', value: String(v), id, 'aria-label': inp.label, style: { width: '96px' }, min: inp.min, max: inp.max });
        else if (inp.kind === 'program') {
          // several lines of text with no drawing editor (a program, a machine with directives): Ctrl+Enter runs
          field = h('textarea.mono.prog-text', { id, 'aria-label': inp.label, spellcheck: 'false', rows: String(Math.min(17, Math.max(3, String(v || '').split('\n').length + 1))) });
          field.value = String(v || '');
        } else {
          field = h('input', { type: 'text', value: T.showInput(inp, v), id, 'aria-label': inp.label, spellcheck: 'false', placeholder: inp.kind === 'string' ? 'ε (empty)' : inp.kind === 'list' ? 'a, ab, ε' : '', style: inp.kind === 'regex' ? { minWidth: '200px' } : null });
          if (inp.kind === 'string' || inp.kind === 'regex' || inp.kind === 'list') field.classList.add('mono');
        }
        field.addEventListener('keydown', (e) => { if (e.key === 'Enter' && (field.tagName !== 'TEXTAREA' || e.ctrlKey || e.metaKey)) { e.preventDefault(); this.apply(); } });
        this.fields[inp.id] = { inp, field };
        el.appendChild(h('label' + (inp.kind === 'program' ? '.wide' : ''), inp.label, field));
        if (inp.kind === 'program') T.UI.autosize(field, 380);
      }
      const go = h('button.btn.primary', { type: 'button', id: 'btnRun' }, icon('run'), 'Run');
      go.addEventListener('click', () => this.apply());
      if ((t.inputs || []).length) el.appendChild(go);
      if (t.presets && t.presets.length) {
        const ps = h('div.presets', { role: 'group', 'aria-label': 'Examples' });
        for (const p of t.presets) {
          const on = Object.entries(p.values || {}).every(([k, val]) => JSON.stringify(this.input[k]) === JSON.stringify(val));
          const c = h('button.chip' + (on ? '.on' : ''), { type: 'button', 'aria-pressed': String(on) }, p.label);
          c.addEventListener('click', () => { this.input = T.inputOf(t, Object.assign({}, T.inputOf(t), p.values)); this.buildInputs(); this.run(); });
          ps.appendChild(c);
        }
        el.appendChild(ps);
        T.UI.scrollRow(ps);
      }
      this.errEl = h('div.err', { id: 'inputErr', role: 'alert' });
      el.appendChild(this.errEl);
      if (!(t.inputs || []).length && !(t.presets || []).length) el.style.display = 'none';
    }
    /**
     * A machine or grammar input: a compact card with its name and what it has (kind, states, start,
     * accepting states), an Edit button that opens the diagram or grammar editor, and the text itself
     * behind a toggle, sized to its lines when opened.
     */
    modelField(inp, v) {
      const machine = inp.kind === 'machine';
      const id = 'in-' + inp.id;
      const ta = h('textarea.model-text', { id, 'aria-label': inp.label + ' as text', spellcheck: 'false', rows: '4' });
      ta.value = String(v || '');
      const kindEl = h('span.model-kind'), nameEl = h('b.model-name'), factsEl = h('div.model-facts');
      const preset = () => (this.t.presets || []).find((p) => p.values && p.values[inp.id] !== undefined && String(p.values[inp.id]).trim() === ta.value.trim());
      const nameOf = () => {
        const named = /^\s*name:?\s+(.+)$/im.exec(ta.value);
        if (named) return named[1].trim();
        const p = preset();
        if (p) return p.label.replace(/:\s*[^:]*$/, '').trim() || p.label;
        const d = typeof inp.def === 'function' ? inp.def() : inp.def;
        return String(d || '').trim() === ta.value.trim() ? (machine ? 'The example machine' : 'The example grammar') : (machine ? 'Your machine' : 'Your grammar');
      };
      const refresh = () => {
        const s = machine ? T.machineSummary(ta.value) : T.grammarSummary(ta.value);
        kindEl.textContent = s.kind;
        nameEl.textContent = nameOf();
        factsEl.innerHTML = '';
        for (const f of s.facts) factsEl.appendChild(h('span', f));
        if (box.classList.contains('open')) T.UI.autosize(ta, 320);
      };
      const ed = h('button.btn', { type: 'button', id: 'btnEdit-' + inp.id, title: machine ? 'Draw and edit the machine' : 'Edit the grammar' }, icon('edit'), machine ? 'Edit machine' : 'Edit grammar');
      ed.addEventListener('click', () => this.openEditor(inp, ta, refresh));
      const textBtn = h('button.btn.small.ghost', { type: 'button', id: 'btnText-' + inp.id, 'aria-expanded': 'false', 'aria-controls': id, title: 'Show the ' + (machine ? 'machine' : 'grammar') + ' as text' }, h('span', 'Text'), h('span.caret', '▾'));
      const box = h('div.model-in', { id: 'model-' + inp.id, dataset: { kind: inp.kind } });
      textBtn.addEventListener('click', () => {
        const on = !box.classList.contains('open');
        box.classList.toggle('open', on);
        textBtn.setAttribute('aria-expanded', String(on));
        if (on) { T.UI.autosize(ta, 320); setTimeout(() => ta.focus(), 20); }
      });
      ta.addEventListener('input', T.UI.debounce(refresh, 150));
      ta.addEventListener('keydown', (e) => { if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); this.apply(); } });
      box.append(h('div.model-head', h('div.model-icon', icon(machine ? 'machine' : 'grammar')), h('div.model-sum', h('div.model-line', kindEl, nameEl), factsEl), h('div.model-acts', ed, textBtn)),
        h('div.model-body', ta, h('div.model-hint', 'Edit the text, then Run (Ctrl+Enter). ', h('a', { href: '#sandbox' }, 'The sandbox'), ' explains the format.')));
      this.fields[inp.id] = { inp, field: ta, refresh };
      refresh();
      return h('div.in-model', h('span.in-label', inp.label), box);
    }
    openEditor(inp, field, refresh) {
      const done = (text) => { if (text === null || text === undefined) return; field.value = text; if (refresh) refresh(); this.apply(); };
      if (inp.kind === 'machine' && T.editMachine) T.editMachine(field.value, { kind: inp.machine }).then(done);
      if (inp.kind === 'grammar' && T.editGrammar) T.editGrammar(field.value).then(done);
    }
    /** Read the fields, check them and run again */
    apply() {
      const next = Object.assign({}, this.input);
      for (const [id, { inp, field }] of Object.entries(this.fields || {})) next[id] = T.parseInput(inp, field.value);
      const e = T.checkInput(this.t, next);
      this.errEl.textContent = e || '';
      if (e) return false;
      this.input = next;
      if (!this.opts.embed) store.set('in:' + this.t.id, next);
      this.run();
      if (this.inputsEl) for (const c of this.inputsEl.querySelectorAll('.presets .chip')) c.classList.remove('on');
      return true;
    }

    // ---- running ---------------------------------------------------------------------------------------
    run() {
      this.pause();
      const res = T.run(this.t, this.input);
      this.res = res;
      this.frames = res.frames.length ? res.frames : [{ items: [], say: 'Nothing happens with this input.' }];
      this.answered = new Set();
      this.stage.clear();
      this.range.max = String(this.frames.length - 1);
      this.marks.innerHTML = '';
      this.frames.forEach((f, i) => {
        if (f.predict || f.mark) {
          const m = h('i' + (f.predict ? '.q' : ''), { title: f.mark || 'Predict' });
          m.style.left = (this.frames.length > 1 ? (i / (this.frames.length - 1)) * 100 : 0) + '%';
          this.marks.appendChild(m);
        }
      });
      this.i = 0;
      this.go(0, true);
      if (this.tabBody) this.showTab(this.tab);
    }
    showTab(k) {
      if (!this.tabBody) return;
      this.tab = k;
      store.set('tab', k);
      for (const [key, b] of Object.entries(this.tabs)) { b.classList.toggle('on', key === k); b.setAttribute('aria-selected', String(key === k)); b.tabIndex = key === k ? 0 : -1; }
      this.tabBody.setAttribute('aria-labelledby', (this.opts.idp || '') + 'tab-' + k);
      this.tabBody.innerHTML = '';
      if (k === 'def') this.tabBody.appendChild(this.defView());
      else this.tabBody.appendChild(this.stepsView());
      T.UI.fitTables(this.tabBody);
    }
    /** The formal definition, tables and grammar of what is running, with this step's part lit */
    defView() {
      const box = h('div.defn', { id: 'defView' });
      const d = this.res && this.res.def;
      if (!d || !(d.sections || []).length) { box.appendChild(T.UI.empty('book', 'No definition here', 'This picture explains itself step by step: follow the narration under the stage, or open Steps for the whole story.')); return box; }
      const fr = this.frames[this.i] || {};
      const hl = fr.hl || {};
      for (const s of d.sections || []) {
        if (s.title) box.appendChild(h('h4', s.title));
        const lit = [].concat(hl[s.id] || []).map(String);
        if (s.kind === 'table') box.appendChild(T.Kit.table.html(Object.assign({}, s, { hl: lit })));
        else if (s.kind === 'grammar') {
          const g = h('div.gram');
          (s.rules || []).forEach((r, i) => g.appendChild(h('div.rule' + (lit.includes(String(i)) ? '.hl' : ''), { html: T.highlightGrammarLine ? T.highlightGrammarLine(r, s.nonterminals) : r })));
          box.appendChild(g);
        } else if (s.kind === 'math') box.appendChild(h('div.math', ...String(s.text).split('\n').map((l, i) => h('div' + (lit.includes(String(i)) ? '.hlline' : ''), l))));
        else box.appendChild(h('p', s.text || ''));
      }
      // keep the lit row in view
      requestAnimationFrame(() => { const el = box.querySelector('tr.hl, td.hl, .rule.hl'); if (el && this.tabBody && this.tabBody.offsetParent) { const r = el.getBoundingClientRect(), b = this.tabBody.getBoundingClientRect(); if (r.top < b.top || r.bottom > b.bottom) el.scrollIntoView({ block: 'nearest' }); } });
      return box;
    }
    stepsView() {
      const box = h('ol.steps', { id: 'stepsView' });
      this.frames.forEach((f, i) => {
        const li = h('li' + (i === this.i ? '.on' : ''), h('button', { type: 'button', 'aria-current': i === this.i ? 'step' : null }, f.say || '(no narration)'));
        li.firstChild.addEventListener('click', () => { this.pause(); this.go(i); });
        box.appendChild(li);
      });
      requestAnimationFrame(() => { const on = box.querySelector('li.on'); if (on && this.tabBody && this.tabBody.offsetParent) { const r = on.getBoundingClientRect(), b = this.tabBody.getBoundingClientRect(); if (r.top < b.top || r.bottom > b.bottom) on.scrollIntoView({ block: 'nearest' }); } });
      return box;
    }

    // ---- moving through the frames -----------------------------------------------------------------------
    go(i, instant) {
      i = Math.max(0, Math.min(this.frames.length - 1, i));
      const back = i < this.i;
      this.i = i;
      const fr = this.frames[i];
      const dur = instant ? 0 : Math.min(SPEEDS[this.app.settings.speed] * 0.72, 700) * (back ? 0.7 : 1);
      this.stage.show(fr, { duration: dur });
      this.range.value = String(i);
      this.posEl.textContent = (i + 1) + ' / ' + this.frames.length;
      this.sayEl.innerHTML = '';
      this.sayEl.appendChild(h('span.step', i === 0 ? 'Start' : i === this.frames.length - 1 ? 'Finished' : 'Step ' + i));
      this.sayEl.appendChild(document.createTextNode(fr.say || ''));
      this.renderCounters(fr);
      if (this.tabBody) this.showTab(this.tab);
      this.backBtn.disabled = i === 0;
      this.fwdBtn.disabled = i === this.frames.length - 1;
      this.clearPredict();
      if (i === this.frames.length - 1 && this.res && this.res.ok && !this.opts.embed) this.app.markDone(this.t);
      if (this.opts.onFrame) this.opts.onFrame(i, fr);
    }
    renderCounters(fr) {
      if (!this.countersEl) return;
      const c = fr.counters || {};
      const prev = this.i > 0 ? this.frames[this.i - 1].counters || {} : {};
      const list = (this.res && this.res.counters && this.res.counters.length ? this.res.counters : Object.keys(c).map((k) => ({ id: k, label: k }))).map((x) => (typeof x === 'string' ? { id: x, label: x } : x));
      this.countersEl.innerHTML = '';
      for (const k of list) this.countersEl.appendChild(h('div.counter' + (c[k.id] !== prev[k.id] && this.i > 0 ? '.bump' : ''), { dataset: { counter: k.id } }, h('b', String(c[k.id] === undefined ? 0 : c[k.id])), h('span', k.label)));
    }
    step(d) {
      this.pause();
      if (d > 0 && this.pendingPredict()) return;
      this.go(this.i + d);
    }
    toggle() { if (this.playing) this.pause(); else this.play(); }
    play() {
      if (this.i >= this.frames.length - 1) this.go(0, true);
      this.playing = true;
      this.playBtn.innerHTML = ''; this.playBtn.appendChild(icon('pause')); this.playBtn.setAttribute('aria-label', 'Pause');
      this.tick();
    }
    pause() {
      this.playing = false;
      clearTimeout(this.timer);
      if (this.playBtn) { this.playBtn.innerHTML = ''; this.playBtn.appendChild(icon('run')); this.playBtn.setAttribute('aria-label', 'Play'); }
    }
    tick() {
      clearTimeout(this.timer);
      if (!this.playing || this.disposed) return;
      if (this.i >= this.frames.length - 1) { this.pause(); return; }
      if (this.pendingPredict()) { this.pause(); return; }
      this.timer = setTimeout(() => { if (!this.playing) return; this.go(this.i + 1); this.tick(); }, SPEEDS[this.app.settings.speed] * (this.frames[this.i].slow ? 1.6 : 1));
    }
    redraw() { this.stage.view = null; this.go(this.i, true); }
    fit() { this.stage.fit(); }

    // ---- predictions -----------------------------------------------------------------------------------
    pendingPredict() {
      const fr = this.frames[this.i];
      if (!fr.predict || !this.app.settings.predict || this.answered.has(this.i)) return false;
      this.showPredict(fr.predict);
      return true;
    }
    showPredict(p) {
      this.clearPredict();
      const box = h('div.predict', { id: 'predict', role: 'dialog', 'aria-label': 'Predict' });
      box.append(h('h4', 'Predict'), h('p', p.ask));
      const skip = h('button.btn.skip', { type: 'button', id: 'predictSkip' }, 'Show me');
      skip.addEventListener('click', () => this.reveal(null));
      if (p.pick === 'option' && p.options) {
        const opts = h('div.opts');
        for (const o of p.options) { const b = h('button.chip', { type: 'button' }, String(o)); b.addEventListener('click', () => this.reveal(String(o))); opts.appendChild(b); }
        opts.appendChild(skip);
        box.appendChild(opts);
      } else {
        this.stageWrap.classList.add('picking');
        box.appendChild(h('div.opts', h('span.muted', 'Click it on the picture.'), skip));
      }
      this.predictBox = box;
      this.predictQ = p;
      this.sayEl.after(box);
      const f = box.querySelector('button');
      if (f && document.activeElement && this.root.contains(document.activeElement)) f.focus();
    }
    pick(key) { if (!this.predictQ || this.predictQ.pick === 'option') return; this.reveal(key); }
    reveal(given) {
      const p = this.predictQ;
      if (!p) return;
      this.answered.add(this.i);
      this.stageWrap.classList.remove('picking');
      const answers = [].concat(p.answer).map(String);
      const right = given !== null && answers.includes(String(given));
      const box = this.predictBox;
      box.querySelectorAll('.opts').forEach((o) => o.remove());
      box.appendChild(h('div.res' + (given === null ? '' : right ? '.good' : '.bad'), given === null ? '' : right ? 'Right.' : 'Not quite.'));
      if (p.explain) box.appendChild(h('p', { style: { marginTop: '4px' } }, p.explain));
      const go = h('button.btn.primary', { type: 'button', id: 'predictGo' }, 'See it happen');
      go.addEventListener('click', () => { this.clearPredict(); this.go(this.i + 1); });
      box.appendChild(go);
      this.predictQ = null;
      go.focus();
    }
    clearPredict() { if (this.predictBox) { this.predictBox.remove(); this.predictBox = null; } this.predictQ = null; if (this.stageWrap) this.stageWrap.classList.remove('picking'); }

    // ---- quiz and sharing --------------------------------------------------------------------------------
    quiz() {
      const t = this.t;
      if (!(t.quiz && t.quiz.length)) return;
      const box = h('div');
      let score = 0, answered = 0;
      const sc = h('p.muted', { id: 'quizScore' });
      for (const q of t.quiz || []) {
        const qb = h('div.quiz-q', h('h4', q.q));
        const why = h('div.quiz-why');
        q.options.forEach((o, k) => {
          const b = h('button.quiz-opt', { type: 'button' }, o);
          b.addEventListener('click', () => {
            if (qb.dataset.done) return;
            qb.dataset.done = '1';
            answered++;
            if (k === q.answer) { score++; b.classList.add('right'); } else { b.classList.add('wrong'); qb.querySelectorAll('.quiz-opt')[q.answer].classList.add('right'); }
            why.textContent = q.why || '';
            sc.textContent = score + ' of ' + answered + ' right so far';
          });
          qb.appendChild(b);
        });
        qb.appendChild(why);
        box.appendChild(qb);
      }
      box.appendChild(sc);
      T.UI.modal({ title: 'Quiz: ' + t.title, body: box, wide: true, buttons: [{ label: 'Close', value: true, primary: true }] });
    }
    share() {
      const q = Object.entries(this.input).map(([k, v]) => k + '=' + encodeURIComponent(JSON.stringify(v))).join('&');
      const url = location.href.replace(/#.*$/, '') + '#topic=' + this.t.id + (q ? '?' + q : '');
      T.Share.copy(url, 'A link to this topic with this input is copied.');
    }
  }

  T.Player = Player;
})();
