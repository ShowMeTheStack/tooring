// The grammar editor: a text area with the grammar coloured as it is typed (nonterminals, terminals,
// arrows, ε, comments), and a line under it saying what the grammar has, or what is wrong with it.
// API: new T.GrammarEditor(el, {text, onChange(text, grammar)}) with getText(), setText(text), grammar(),
// destroy(); T.highlightGrammarLine(line, nonterminals) -> HTML; T.editGrammar(text) -> Promise of text.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h } = T.UI;
  const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

  /** Parse with the grammar engine when it is loaded, else with the small reader: {ok, nonterminals, terminals, rules, start, error} */
  T.readGrammar = function (text) {
    try {
      if (T.grammar && T.grammar.tryParse) {
        const r = T.grammar.tryParse(text);
        if (r.error) return { ok: false, error: typeof r.error === 'string' ? r.error : r.error.message || String(r.error) };
        const G = r.grammar;
        return { ok: true, G, start: G.start, nonterminals: G.nonterminals, terminals: G.terminals, rules: G.productions.length };
      }
      const g = T.GrammarText.parse(text);
      return { ok: true, start: g.start, nonterminals: g.nonterminals, terminals: g.terminals, rules: g.rules.length };
    } catch (e) { return { ok: false, error: e.message }; }
  };

  /** One line of a grammar as coloured HTML; nonterminals: the known ones (else capitals and left sides) */
  T.highlightGrammarLine = function (line, nts) {
    const nt = new Set(nts || []);
    const m = /^\s*#/.test(line) ? ['', '', '', '', line] : /^(\s*)(.*?)(\s*)((?:^|\s)\/\/.*)?$/.exec(line);
    let body = m[2];
    const com = m[4] ? '<span class="k-com">' + esc(m[4]) + '</span>' : '';
    if (/^%/.test(body)) return m[1] + '<span class="k-kw">' + esc(body) + '</span>' + m[3] + com;
    const arrow = /(→|->|::=)/.exec(body);
    const isNT = (w) => nt.has(w) || (!nts && /^[A-Z][A-Za-z0-9_']*$|^<.*>$/.test(w));
    const sym = (w) => (w === 'ε' || w === 'eps' || w === 'epsilon' ? '<span class="k-eps">' + esc(w) + '</span>' : isNT(w) ? '<span class="k-nt">' + esc(w) + '</span>' : '<span class="k-t">' + esc(w) + '</span>');
    // a right side: words split by spaces; a word that is not a known name is cut into characters
    const side = (s) => s.split(/(\s+|\|)/).map((tok) => {
      if (tok === '|') return '<span class="k-op">|</span>';
      if (!tok || /^\s+$/.test(tok)) return tok;
      if (/^'.*'$|^".*"$/.test(tok) || isNT(tok) || tok === 'ε' || tok === 'eps') return sym(tok);
      // longest known names first, else one character at a time
      let out = '', i = 0;
      const names = [...nt].sort((a, b) => b.length - a.length);
      while (i < tok.length) {
        const n = names.find((x) => tok.startsWith(x, i));
        if (n) { out += sym(n); i += n.length; } else { out += sym(tok[i]); i++; }
      }
      return out;
    }).join('');
    if (!arrow) body = /^\s*\|/.test(body) ? side(body) : esc(body);
    else body = side(body.slice(0, arrow.index)) + '<span class="k-op">' + esc(arrow[1]) + '</span>' + side(body.slice(arrow.index + arrow[1].length));
    return m[1] + body + m[3] + com;
  };

  class GrammarEditor {
    constructor(el, opts) {
      this.opts = opts || {};
      this.hl = h('pre.ed-hl', { 'aria-hidden': 'true' });
      this.ta = h('textarea', { id: 'gramText', spellcheck: 'false', 'aria-label': 'Grammar', rows: '8' });
      this.info = h('div.gram-info', { id: 'gramInfo' });
      this.root = h('div', h('div.gram-ed', this.hl, this.ta), this.info);
      el.appendChild(this.root);
      this.ta.value = this.opts.text || '';
      this.ta.addEventListener('input', () => this.refresh(true));
      this.ta.addEventListener('scroll', () => { this.hl.scrollTop = this.ta.scrollTop; });
      // typing -> is turned into an arrow, and a tab key inserts spaces
      this.ta.addEventListener('keydown', (e) => {
        if (e.key === 'Tab') { e.preventDefault(); document.execCommand('insertText', false, '  '); }
      });
      this.refresh(false);
    }
    refresh(user) {
      const text = this.ta.value;
      if (!this.fitText) this.fitText = T.UI.autosize(this.ta, 420); else this.fitText();
      const r = T.readGrammar(text);
      this.res = r;
      this.hl.innerHTML = text.split('\n').map((l) => T.highlightGrammarLine(l, r.ok ? r.nonterminals : null)).join('\n') + '\n';
      this.info.innerHTML = '';
      if (!text.trim()) this.info.append('Write one rule per line, like S → a S b | ε.');
      else if (r.ok) this.info.append('Start ', h('b', r.start), ' · nonterminals ', h('b', r.nonterminals.join(', ')), ' · terminals ', h('b', r.terminals.join(', ') || 'none'), ' · ' + r.rules + ' rule' + (r.rules === 1 ? '' : 's'));
      else this.info.appendChild(h('span', { style: { color: 'var(--bad)' } }, r.error));
      if (user && this.opts.onChange) this.opts.onChange(text, r);
    }
    getText() { return this.ta.value; }
    setText(t) { this.ta.value = t; this.refresh(false); }
    grammar() { return this.res; }
    destroy() { this.root.remove(); }
  }
  T.GrammarEditor = GrammarEditor;

  T.editGrammar = function (text) {
    const box = h('div');
    let ed = null;
    return T.UI.modal({
      title: 'Edit the grammar', body: box, wide: true,
      buttons: [{ label: 'Cancel', value: null }, { label: 'Use this grammar', value: () => ed.getText(), primary: true }],
      cancelValue: null,
      onOpen: () => { ed = new GrammarEditor(box, { text }); ed.ta.focus(); },
    });
  };
})();
