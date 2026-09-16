// The Turing-machine table editor: a row per state and a column per tape symbol; each cell holds what
// the machine does there, as "write, move, next" (like 1, R, q2), or nothing for "halt". States and
// symbols can be added, the start and accepting states chosen. Kept in sync with the machine text.
// API: new T.TMTableEditor(el, {text, onChange(text)}) with getText(), setText(text), destroy().
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const M = T.Machine;
  const shown = (s) => (s === '⊔' ? '_' : s);

  class TMTableEditor {
    constructor(el, opts) {
      this.opts = opts || {};
      this.root = h('div.tm-ed');
      el.appendChild(this.root);
      this.setText(this.opts.text || 'start: q0\naccept: qa\nq0, _ -> qa, _, S');
    }
    setText(text) {
      let m;
      try { m = M.parse(text); } catch (e) { this.root.innerHTML = ''; this.root.appendChild(h('div.ed-err', e.message)); return; }
      if (m.kind !== 'tm' && m.trans.length) { this.root.innerHTML = ''; this.root.appendChild(h('div.ed-err', 'This is not a Turing machine.')); return; }
      m.kind = 'tm';
      this.m = m;
      const syms = new Set(['⊔']);
      for (const t of m.trans) { const l = M.tmLabel(t.label); syms.add(l.read); syms.add(l.write); }
      this.syms = [...syms].sort((a, b) => (a === '⊔') - (b === '⊔') || a.localeCompare(b));
      this.render();
    }
    getText() { return M.format(this.m); }
    cell(q, a) {
      const t = this.m.trans.find((x) => x.from === q && M.tmLabel(x.label).read === a);
      if (!t) return '';
      const l = M.tmLabel(t.label);
      return shown(l.write) + ', ' + l.move + ', ' + t.to;
    }
    render() {
      const m = this.m;
      this.root.innerHTML = '';
      const head = h('tr', h('th', 'state'), ...this.syms.map((a) => h('th', { title: a === '⊔' ? 'the blank' : '' }, shown(a))), h('th', 'accepting'));
      const body = h('tbody');
      m.states.forEach((q) => {
        const tr = h('tr', h('th', (q === m.start ? '→ ' : '') + q));
        for (const a of this.syms) {
          const inp = h('input', { type: 'text', value: this.cell(q, a), placeholder: 'halt', spellcheck: 'false', 'aria-label': q + ' reading ' + shown(a), dataset: { q, a } });
          inp.addEventListener('change', () => this.edit(q, a, inp));
          tr.appendChild(h('td', inp));
        }
        const acc = h('input', { type: 'checkbox', checked: m.accept.includes(q), 'aria-label': q + ' accepts' });
        acc.addEventListener('change', () => { m.accept = acc.checked ? m.accept.concat([q]) : m.accept.filter((x) => x !== q); this.emit(); });
        tr.appendChild(h('td', acc));
        body.appendChild(tr);
      });
      const addQ = h('button.btn.small', { type: 'button', id: 'tmAddState' }, icon('plus'), 'State');
      addQ.addEventListener('click', () => { let i = 0; while (m.states.includes('q' + i)) i++; m.states.push('q' + i); this.render(); this.emit(); });
      const addS = h('button.btn.small', { type: 'button', id: 'tmAddSym' }, icon('plus'), 'Symbol');
      addS.addEventListener('click', () => T.UI.prompt('A new tape symbol', 'Symbol', '', { hint: 'One character, like x or #.' }).then((v) => { v = (v || '').trim(); if (!v || this.syms.includes(v) || v === '_') return; this.syms.splice(this.syms.length - 1, 0, v); this.render(); }));
      const start = h('select', { id: 'tmStart', 'aria-label': 'Start state' }, ...m.states.map((q) => h('option', { value: q, selected: q === m.start }, q)));
      start.addEventListener('change', () => { m.start = start.value; this.render(); this.emit(); });
      this.err = h('div.ed-err', { id: 'tmErr' });
      this.root.append(h('div.sb-actions', h('label', { style: { display: 'flex', gap: '6px', alignItems: 'center', fontWeight: 600 } }, 'Start', start), addQ, addS, h('span.muted', { style: { fontSize: '13px' } }, 'Each cell: write, move, next state. Empty means halt.')),
        h('div.tm-wrap', h('table.tm-table', { id: 'tmTable' }, h('thead', head), body)), this.err);
    }
    edit(q, a, inp) {
      const v = inp.value.trim();
      const m = this.m;
      const rest = m.trans.filter((x) => !(x.from === q && M.tmLabel(x.label).read === a));
      if (!v) { m.trans = rest; inp.classList.remove('bad'); this.err.textContent = ''; this.emit(); return; }
      const p = v.split(/\s*,\s*|\s+/);
      if (p.length !== 3 || !/^[LRS]$/i.test(p[1])) { inp.classList.add('bad'); this.err.textContent = q + ' reading ' + shown(a) + ': write "symbol, move, next state", like 1, R, q2'; return; }
      inp.classList.remove('bad'); this.err.textContent = '';
      const w = p[0] === '_' ? '⊔' : p[0];
      if (!m.states.includes(p[2])) m.states.push(p[2]);
      rest.push({ from: q, to: p[2], label: a + ' → ' + w + ', ' + p[1].toUpperCase() });
      m.trans = rest;
      if (!this.syms.includes(w)) { this.syms.splice(this.syms.length - 1, 0, w); this.render(); }
      if (!this.root.querySelector('tr th') || ![...this.root.querySelectorAll('tbody th')].some((th) => th.textContent.endsWith(p[2]))) this.render();
      this.emit();
    }
    emit() { if (this.opts.onChange) this.opts.onChange(this.getText()); }
    destroy() { this.root.remove(); }
  }
  T.TMTableEditor = TMTableEditor;
})();
