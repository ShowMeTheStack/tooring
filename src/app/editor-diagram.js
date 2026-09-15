// The state-diagram editor: draw a DFA, NFA, PDA or Turing machine.
//   click empty space (or double-click)    add a state
//   drag a state                           move it
//   shift-drag from a state to another     add a transition (to itself for a loop); the arrow tool does the
//   (or the arrow tool: click, then click) same with two clicks, for touch screens
//   double-click a state / a label         rename the state / edit the label
//   Start, Accepting, Delete               act on the selected state or transition (keys S, A, Delete)
//   undo, redo, auto layout                (Ctrl+Z, Ctrl+Shift+Z, L)
// The text pane beside it holds the same machine as text and is kept in sync both ways.
// API: new T.DiagramEditor(el, {text, kind, onChange(text, machine)}) with getText(), setText(text),
// machine(), select(id), layout(), undo(), redo(), destroy(); and T.editMachine(text, {kind}) -> Promise
// of the edited text (or null), in a dialog.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const M = T.Machine, KG = T.Kit.graph;
  const DEFAULT_LABEL = { dfa: 'a', nfa: 'a', pda: 'a, Z → A Z', tm: 'a → a, R' };
  const HINT = { dfa: 'symbols, like a, b', nfa: 'symbols, like a, b (ε for an empty move)', pda: 'read, pop → push; one per line', tm: 'read → write, move; one per line' };

  class DiagramEditor {
    constructor(el, opts) {
      this.el = el;
      this.opts = opts || {};
      this.m = { kind: this.opts.kind || 'nfa', states: [], start: null, accept: [], trans: [], pos: {} };
      this.undoStack = []; this.redoStack = [];
      this.sel = null;           // {type: 'state', q} | {type: 'edge', from, to}
      this.tool = 'select';
      this.build();
      this.quiet = true;
      this.setText(this.opts.text || '', true);
      this.quiet = false;
    }

    // ---- layout of the editor --------------------------------------------------------------------------
    build() {
      const tb = (id, ic, title, fn, label) => { const b = h('button.btn.small', { type: 'button', id: 'ed-' + id, title }, icon(ic), label || null); b.addEventListener('click', fn); return b; };
      this.btnArrow = tb('arrow', 'cursor', 'Arrow tool: click a state, then another, to add a transition (or shift-drag)', () => this.setTool(this.tool === 'arrow' ? 'select' : 'arrow'), 'Arrow');
      this.btnStart = tb('start', 'run', 'Make the selected state the start state (S)', () => this.toggleStart(), 'Start');
      this.btnAccept = tb('accept', 'check', 'Make the selected state accepting, or not (A)', () => this.toggleAccept(), 'Accepting');
      this.btnDel = tb('delete', 'trash', 'Delete the selection (Delete)', () => this.deleteSel(), 'Delete');
      this.btnUndo = tb('undo', 'undo', 'Undo (Ctrl+Z)', () => this.undo());
      this.btnRedo = tb('redo', 'redo', 'Redo (Ctrl+Shift+Z)', () => this.redo());
      const lay = tb('layout', 'layout', 'Lay the states out again (L)', () => this.layout(), 'Layout');
      const fit = tb('fit', 'fit', 'Fit the drawing to the box', () => { this.view = null; this.render(); });
      this.tools = h('div.ed-tools', this.btnArrow, h('span.sep'), this.btnStart, this.btnAccept, this.btnDel, h('span.sep'), this.btnUndo, this.btnRedo, h('span.sep'), lay, fit);
      this.canvasWrap = h('div.ed-canvas-wrap', { id: 'edCanvas' });
      this.stage = new T.Stage(this.canvasWrap, { label: 'Machine editor' });
      this.svg = this.stage.root;
      this.svg.classList.add('ed-canvas');
      this.svg.setAttribute('tabindex', '0');
      this.ghost = document.createElementNS('http://www.w3.org/2000/svg', 'path');
      this.ghost.setAttribute('class', 'ed-ghost');
      this.svg.appendChild(this.ghost);
      this.hint = h('div.ed-hint', 'Click to add a state · drag to move · shift-drag between states for a transition · double-click to rename or relabel');
      this.canvasWrap.appendChild(this.hint);
      this.text = h('textarea', { id: 'edText', spellcheck: 'false', 'aria-label': 'The machine as text' });
      this.err = h('div.ed-err', { id: 'edErr' });
      this.text.addEventListener('input', () => { clearTimeout(this.textTimer); this.textTimer = setTimeout(() => this.fromText(), 250); });
      const side = h('div.ed-side', h('div.muted', { style: { fontSize: '13px' } }, 'The same machine as text: edit either side.'), this.text, this.err);
      const left = h('div.card', { style: { display: 'flex', flexDirection: 'column', minWidth: 0 } }, this.tools, this.canvasWrap);
      this.root = h('div.ed', left, side);
      this.el.appendChild(this.root);
      this.bindPointer();
      this.svg.addEventListener('keydown', (e) => this.onKey(e));
    }
    setTool(t) { this.tool = t; this.btnArrow.classList.toggle('primary', t === 'arrow'); this.pendingFrom = null; this.render(); }

    // ---- the model ---------------------------------------------------------------------------------------
    snapshot() { return JSON.stringify(this.m); }
    push() { this.undoStack.push(this.snapshot()); if (this.undoStack.length > 200) this.undoStack.shift(); this.redoStack = []; }
    undo() { if (!this.undoStack.length) return; this.redoStack.push(this.snapshot()); this.m = JSON.parse(this.undoStack.pop()); this.sel = null; this.changed(true); }
    redo() { if (!this.redoStack.length) return; this.undoStack.push(this.snapshot()); this.m = JSON.parse(this.redoStack.pop()); this.sel = null; this.changed(true); }
    machine() { return JSON.parse(this.snapshot()); }
    getText() { return M.format(this.m); }
    /** Replace the machine with text; states it already had keep their places */
    setText(text, initial) {
      let m;
      try { m = M.parse(text || 'start q0'); } catch (e) { this.err.textContent = e.message; this.text.value = text; return false; }
      if (!initial) this.push();
      const old = this.m.pos || {};
      m.pos = {};
      for (const q of m.states) if (old[q]) m.pos[q] = old[q];
      for (const q of m.states) if (m.pos[q] === undefined && text && /^at /m.test(text)) { /* positions came with the text */ }
      this.m = m;
      if (this.opts.kind && (m.kind === 'dfa' || m.kind === 'nfa') && (this.opts.kind === 'dfa' || this.opts.kind === 'nfa')) this.m.kind = M.isDeterministic(m) ? 'dfa' : 'nfa';
      this.place();
      this.err.textContent = '';
      this.changed(false, true);
      return true;
    }
    /** Positions for states that have none, keeping the others */
    place() {
      const missing = this.m.states.filter((q) => !this.m.pos[q]);
      if (!missing.length) return;
      const lay = KG.layout(this.m, { fixed: this.m.pos }).pos;
      for (const q of missing) this.m.pos[q] = { x: Math.round(lay[q].x), y: Math.round(lay[q].y) };
    }
    layout() { this.push(); this.m.pos = {}; this.m.pos = KG.layout(Object.assign({}, this.m, { pos: {} })).pos; this.view = null; this.changed(true); }
    fromText() {
      const t = this.text.value;
      let m;
      try { m = M.parse(t); } catch (e) { this.err.textContent = e.message; return; }
      this.err.textContent = '';
      this.push();
      const pos = this.m.pos;
      this.m = m;
      this.m.pos = {};
      for (const q of m.states) if (pos[q]) this.m.pos[q] = pos[q];
      this.place();
      this.changed(false, true);
    }
    /** Something changed: redraw, rewrite the text (unless it is being typed), tell the owner */
    changed(byUser, fromText) {
      this.render();
      // a finite automaton is a DFA exactly when it is deterministic
      if (this.m.kind === 'dfa' || this.m.kind === 'nfa') this.m.kind = M.isDeterministic(this.m) ? 'dfa' : 'nfa';
      if (!fromText && document.activeElement !== this.text) this.text.value = this.getText();
      else if (fromText && document.activeElement !== this.text) this.text.value = this.getText();
      // the text pane grows with the machine, so none of it hides below the box
      if (!this.fitText) this.fitText = T.UI.autosize(this.text, 360); else this.fitText();
      this.btnUndo.disabled = !this.undoStack.length; this.btnRedo.disabled = !this.redoStack.length;
      const st = this.sel && this.sel.type === 'state';
      this.btnStart.disabled = !st; this.btnAccept.disabled = !st || this.m.kind === 'pda' && this.m.acceptBy === 'empty';
      this.btnDel.disabled = !this.sel;
      if (this.opts.onChange && !this.quiet) this.opts.onChange(this.getText(), this.machine());
      void byUser;
    }

    // ---- drawing -------------------------------------------------------------------------------------------
    render() {
      const m = this.m;
      const cls = {};
      if (this.sel && this.sel.type === 'state') cls[this.sel.q] = 'sel';
      if (this.pendingFrom) cls[this.pendingFrom] = 'sel';
      const edgeCls = {};
      if (this.sel && this.sel.type === 'edge') edgeCls[this.sel.from + '>' + this.sel.to] = 'sel';
      const d = KG.draw(m, { pos: m.pos, cls, edgeCls, prefix: 'ed' });
      // keep the camera still while editing; it grows to take in states moved outside it
      const b = T.stageBounds(d.items, { margin: 60, minW: 560, minH: 360 }) || { x: -280, y: -180, w: 560, h: 360 };
      if (!this.view) this.view = b;
      else if (!this.dragging) {
        const v = this.view;
        if (b.x < v.x || b.y < v.y || b.x + b.w > v.x + v.w || b.y + b.h > v.y + v.h) this.view = T.geom.union([v, b]);
      }
      this.stage.show({ items: d.items, view: this.view }, { instant: true });
      // a wide invisible stroke on each edge, so it is easy to click
      for (const g of this.svg.querySelectorAll('.it-edge')) {
        let hit = g.querySelector('.edge-hit');
        if (!hit) { hit = document.createElementNS('http://www.w3.org/2000/svg', 'path'); hit.setAttribute('class', 'edge-hit'); hit.setAttribute('data-audit', 'ignore'); g.insertBefore(hit, g.firstChild); }
        hit.setAttribute('d', g.querySelector('.edge-path').getAttribute('d'));
      }
      this.svg.querySelectorAll('.it-state').forEach((g) => g.classList.toggle('sel', !!cls[g.dataset.key.slice(5)]));
      this.svg.querySelectorAll('.it-edge').forEach((g) => g.classList.toggle('sel', !!edgeCls[g.dataset.key.slice(5)]));
    }
    toWorld(e) {
      const pt = this.svg.createSVGPoint(); pt.x = e.clientX; pt.y = e.clientY;
      const p = pt.matrixTransform(this.svg.getScreenCTM().inverse());
      return { x: p.x, y: p.y };
    }
    stateAt(e) { const g = e.target.closest && e.target.closest('.it-state'); return g ? g.dataset.key.slice(5) : null; }
    edgeAt(e) { const g = e.target.closest && e.target.closest('.it-edge'); if (!g || g.dataset.key === 'ed:start') return null; const k = g.dataset.key.slice(5); const i = k.indexOf('>'); return { from: k.slice(0, i), to: k.slice(i + 1) }; }

    // ---- pointer ----------------------------------------------------------------------------------------------
    bindPointer() {
      const svg = this.svg;
      let drag = null;
      svg.addEventListener('pointerdown', (e) => {
        if (e.button !== 0) return;
        svg.focus({ preventScroll: true });
        this.closeInline();
        const q = this.stateAt(e), w = this.toWorld(e);
        if (q && (e.shiftKey || this.tool === 'arrow')) {
          if (this.tool === 'arrow' && !e.shiftKey && this.pendingFrom) { this.addEdge(this.pendingFrom, q); this.pendingFrom = null; return; }
          drag = { mode: 'link', from: q, start: w, moved: false };
          try { svg.setPointerCapture(e.pointerId); } catch (x) { /* gone */ }
          return;
        }
        if (q) { drag = { mode: 'move', q, start: w, orig: Object.assign({}, this.m.pos[q]), moved: false }; try { svg.setPointerCapture(e.pointerId); } catch (x) { /* gone */ } this.select({ type: 'state', q }); return; }
        const ed = this.edgeAt(e);
        if (ed) { this.select(Object.assign({ type: 'edge' }, ed)); return; }
        drag = { mode: 'empty', start: w, moved: false };
      });
      svg.addEventListener('pointermove', (e) => {
        if (!drag) return;
        const w = this.toWorld(e);
        if (!drag.moved && Math.hypot(w.x - drag.start.x, w.y - drag.start.y) < 4) return;
        drag.moved = true;
        if (drag.mode === 'move') {
          if (!drag.pushed) { this.push(); drag.pushed = true; this.dragging = true; }
          this.m.pos[drag.q] = { x: Math.round(drag.orig.x + w.x - drag.start.x), y: Math.round(drag.orig.y + w.y - drag.start.y) };
          this.render();
        } else if (drag.mode === 'link') {
          const p = this.m.pos[drag.from];
          this.ghost.setAttribute('d', `M${p.x},${p.y} L${w.x},${w.y}`);
        }
      });
      const up = (e) => {
        if (!drag) return;
        const d = drag; drag = null;
        this.ghost.setAttribute('d', '');
        if (d.mode === 'move') { this.dragging = false; if (d.moved) this.changed(true); return; }
        if (d.mode === 'link') {
          const el = document.elementFromPoint(e.clientX, e.clientY);
          const g = el && el.closest && el.closest('.it-state');
          const to = g ? g.dataset.key.slice(5) : null;
          if (!d.moved && this.tool === 'arrow') { this.pendingFrom = d.from; this.render(); return; }
          if (to) this.addEdge(d.from, to);
          return;
        }
        if (d.mode === 'empty' && !d.moved) {
          if (this.sel || this.pendingFrom) { this.sel = null; this.pendingFrom = null; this.changed(false); return; }
          this.addState(d.start);
        }
      };
      svg.addEventListener('pointerup', up);
      svg.addEventListener('pointercancel', () => { drag = null; this.dragging = false; this.ghost.setAttribute('d', ''); });
      svg.addEventListener('dblclick', (e0) => {
        // pointer capture makes the svg the target: find what is really under the pointer
        const e = { target: document.elementFromPoint(e0.clientX, e0.clientY) || e0.target };
        const q = this.stateAt(e);
        if (q) { this.renameState(q); return; }
        const ed = this.edgeAt(e) || this.labelAt(e);
        if (ed) { this.editLabel(ed.from, ed.to); return; }
      });
    }
    labelAt(e) { const t = e.target.closest && e.target.closest('.edge-label'); return t ? this.edgeAt({ target: t }) : null; }
    select(s) { this.sel = s; this.changed(false); }
    onKey(e) {
      if (e.target !== this.svg) return;
      const k = e.key, mod = e.ctrlKey || e.metaKey;
      if (mod && (k === 'z' || k === 'Z')) { e.preventDefault(); if (e.shiftKey) this.redo(); else this.undo(); return; }
      if (mod && (k === 'y')) { e.preventDefault(); this.redo(); return; }
      if (mod) return;
      if (k === 'Delete' || k === 'Backspace') { e.preventDefault(); this.deleteSel(); }
      else if (k === 's' || k === 'S') { e.preventDefault(); this.toggleStart(); }
      else if (k === 'a' || k === 'A') { e.preventDefault(); this.toggleAccept(); }
      else if (k === 'l' || k === 'L') { e.preventDefault(); this.layout(); }
      else if (k === 'Escape') { this.sel = null; this.pendingFrom = null; this.setTool('select'); this.changed(false); }
      else if (k === 'Enter' && this.sel) { e.preventDefault(); if (this.sel.type === 'state') this.renameState(this.sel.q); else this.editLabel(this.sel.from, this.sel.to); }
      e.stopPropagation();
    }

    // ---- edits -------------------------------------------------------------------------------------------------
    freshName() { let i = 0; while (this.m.states.includes('q' + i)) i++; return 'q' + i; }
    addState(at) {
      this.push();
      const q = this.freshName();
      this.m.states.push(q);
      this.m.pos[q] = { x: Math.round(at.x), y: Math.round(at.y) };
      if (!this.m.start) this.m.start = q;
      this.sel = { type: 'state', q };
      this.changed(true);
      return q;
    }
    addEdge(from, to) {
      const exists = this.m.trans.some((t) => t.from === from && t.to === to);
      this.sel = { type: 'edge', from, to };
      if (exists) { this.changed(false); this.editLabel(from, to); return; }
      this.push();
      this.m.trans.push({ from, to, label: DEFAULT_LABEL[this.m.kind] || 'a' });
      this.changed(true);
      this.editLabel(from, to, true);
    }
    toggleStart() { if (!this.sel || this.sel.type !== 'state') return; this.push(); this.m.start = this.sel.q; this.changed(true); }
    toggleAccept() {
      if (!this.sel || this.sel.type !== 'state') return;
      this.push();
      const q = this.sel.q, i = this.m.accept.indexOf(q);
      if (i < 0) this.m.accept.push(q); else this.m.accept.splice(i, 1);
      this.changed(true);
    }
    deleteSel() {
      const s = this.sel;
      if (!s) return;
      this.push();
      if (s.type === 'state') {
        this.m.states = this.m.states.filter((q) => q !== s.q);
        this.m.trans = this.m.trans.filter((t) => t.from !== s.q && t.to !== s.q);
        this.m.accept = this.m.accept.filter((q) => q !== s.q);
        delete this.m.pos[s.q];
        if (this.m.start === s.q) this.m.start = this.m.states[0] || null;
      } else this.m.trans = this.m.trans.filter((t) => !(t.from === s.from && t.to === s.to));
      this.sel = null;
      this.changed(true);
    }
    /** An input laid over the drawing, at a point in drawing units */
    inline(at, value, multi, onDone, placeholder) {
      this.closeInline();
      const r = this.svg.getBoundingClientRect(), wr = this.canvasWrap.getBoundingClientRect();
      const ctm = this.svg.getScreenCTM();
      const sx = ctm.a * at.x + ctm.e - wr.left, sy = ctm.d * at.y + ctm.f - wr.top;
      const inp = h(multi ? 'textarea.ed-inline' : 'input.ed-inline', { type: 'text', id: 'edInline', spellcheck: 'false', placeholder: placeholder || '', rows: multi ? String(Math.max(2, value.split('\n').length)) : null });
      inp.value = value;
      inp.style.left = Math.max(4, Math.min(r.width - 210, sx - 100)) + 'px';
      inp.style.top = Math.max(4, sy - 18) + 'px';
      inp.style.width = '200px';
      let done = false;
      const finish = (ok) => { if (done) return; done = true; inp.remove(); this.inlineEl = null; if (ok) onDone(inp.value); this.svg.focus({ preventScroll: true }); };
      inp.addEventListener('keydown', (e) => {
        e.stopPropagation();
        if (e.key === 'Enter' && !(multi && e.shiftKey)) { e.preventDefault(); finish(true); }
        if (e.key === 'Escape') { e.preventDefault(); finish(false); }
      });
      inp.addEventListener('blur', () => finish(true));
      this.canvasWrap.appendChild(inp);
      this.inlineEl = inp;
      setTimeout(() => { inp.focus(); inp.select(); }, 0);
      return inp;
    }
    closeInline() { if (this.inlineEl) this.inlineEl.blur(); }
    renameState(q) {
      this.inline(this.m.pos[q], q, false, (v) => {
        v = v.trim();
        if (!v || v === q) return;
        if (!/^[^\s:]+$/.test(v) || (/,/.test(v) && (this.m.kind === 'pda' || this.m.kind === 'tm'))) { T.UI.toast('A state name has no spaces or colons' + (this.m.kind === 'pda' || this.m.kind === 'tm' ? ' or commas' : '') + '.', 'err'); return; }
        if (this.m.states.includes(v)) { T.UI.toast('There is already a state ' + v + '.', 'err'); return; }
        this.push();
        const ren = (x) => (x === q ? v : x);
        this.m.states = this.m.states.map(ren);
        this.m.accept = this.m.accept.map(ren);
        this.m.start = ren(this.m.start);
        this.m.trans = this.m.trans.map((t) => Object.assign(t, { from: ren(t.from), to: ren(t.to) }));
        this.m.pos[v] = this.m.pos[q]; delete this.m.pos[q];
        this.sel = { type: 'state', q: v };
        this.changed(true);
      });
    }
    /** Edit the label of the edge from → to: all its rules at once (a finite automaton's symbols, or one rule per line) */
    editLabel(from, to, fresh) {
      const fa = this.m.kind === 'dfa' || this.m.kind === 'nfa';
      const rules = this.m.trans.filter((t) => t.from === from && t.to === to);
      const cur = fa ? KG.edges({ kind: this.m.kind, trans: rules }).map((e) => e.label).join(', ') : rules.map((t) => t.label).join('\n');
      const r = KG.route(this.m, this.m.pos, Object.fromEntries(this.m.states.map((q) => [q, KG.shape(q)])), {}).find((x) => x.from === from && x.to === to);
      const at = r ? { x: r.lx, y: r.ly } : this.m.pos[from];
      this.inline(at, cur, !fa, (v) => {
        const lines = fa ? [v] : v.split('\n').map((x) => x.trim()).filter(Boolean);
        try {
          if (!fa) for (const l of lines) (this.m.kind === 'pda' ? M.pdaLabel : M.tmLabel)(l);
          if (fa && !M.symbols(v).length) throw new Error('give at least one symbol');
        } catch (e) { T.UI.toast(e.message, 'err'); if (fresh) { this.m.trans = this.m.trans.filter((t) => !(t.from === from && t.to === to)); this.changed(true); } return; }
        if (!fresh) this.push();
        const keep = this.m.trans.filter((t) => !(t.from === from && t.to === to));
        const idx = this.m.trans.findIndex((t) => t.from === from && t.to === to);
        const add = lines.filter((l) => l !== '').map((l) => ({ from, to, label: fa ? M.symbols(l).map((x) => (x === '' ? 'ε' : x)).join(', ') : l }));
        keep.splice(idx < 0 ? keep.length : Math.min(idx, keep.length), 0, ...add);
        this.m.trans = keep;
        this.changed(true);
      }, HINT[this.m.kind]);
    }
    destroy() { this.closeInline(); this.root.remove(); }
  }
  T.DiagramEditor = DiagramEditor;

  /** Edit machine text in a dialog with the diagram editor: resolves with the new text, or null */
  T.editMachine = function (text, opts) {
    const box = h('div', { style: { minHeight: '460px' } });
    let ed = null;
    return T.UI.modal({
      title: 'Edit the machine', body: box, cls: 'huge',
      buttons: [{ label: 'Cancel', value: null }, { label: 'Use this machine', value: () => ed.getText(), primary: true }],
      cancelValue: null, dismissable: false,
      onOpen: () => { ed = new DiagramEditor(box, { text, kind: opts && opts.kind }); },
    });
  };
})();
