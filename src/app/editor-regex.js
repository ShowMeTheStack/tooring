// The regular-expression input: the expression is checked as it is typed (with the place of a mistake),
// coloured (operators, ε and ∅, symbols) and shown back as the engine reads it, with its size and
// alphabet. Syntax: | for union, juxtaposition for concatenation, * + ? for repetition, ( ) for grouping,
// ε and ∅ (eps and empty also work).
// API: new T.RegexInput(el, {value, onChange(value, ok)}) with value(), setValue(v), ok(), destroy().
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h } = T.UI;
  const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;');

  /** Colour an expression as HTML */
  T.highlightRegex = function (s) {
    return [...String(s)].map((c) => (/[|*+?()]/.test(c) ? '<span class="k-op">' + esc(c) + '</span>' : c === 'ε' || c === '∅' ? '<span class="k-eps">' + c + '</span>' : /\s/.test(c) ? c : '<span class="k-t">' + esc(c) + '</span>')).join('');
  };
  /** Check an expression: {ok, error, pos, shown, size, alphabet} */
  T.checkRegex = function (s) {
    if (T.RE && T.RE.check) {
      const r = T.RE.check(s);
      if (!r.ok) return { ok: false, error: r.error, pos: r.pos };
      try { const ast = T.RE.parse(s); return { ok: true, shown: T.RE.show(ast), size: T.RE.size(ast), alphabet: T.RE.alphabet(ast) }; } catch (e) { return { ok: true }; }
    }
    // without the engine: balanced brackets and no operator out of place
    let d = 0;
    for (let i = 0; i < s.length; i++) {
      const c = s[i];
      if (c === '(') d++;
      if (c === ')' && --d < 0) return { ok: false, error: 'a ) with no ( before it', pos: i };
      if (/[*+?]/.test(c) && (i === 0 || /[|(]/.test(s[i - 1]))) return { ok: false, error: c + ' needs something before it to repeat', pos: i };
    }
    return d ? { ok: false, error: 'a ( is never closed', pos: s.length } : { ok: true };
  };

  class RegexInput {
    constructor(el, opts) {
      this.opts = opts || {};
      this.inp = h('input', { type: 'text', id: 'rxInput', spellcheck: 'false', autocomplete: 'off', 'aria-label': 'Regular expression', placeholder: 'like (a|b)*abb' });
      this.inp.value = this.opts.value || '';
      const ins = (t) => { const b = h('button.btn.small', { type: 'button', title: 'Insert ' + t }, t); b.addEventListener('click', () => { this.inp.focus(); document.execCommand('insertText', false, t); }); return b; };
      this.tokens = h('div.rx-tokens', { id: 'rxShow' });
      this.msg = h('div.gram-info', { id: 'rxInfo' });
      this.root = h('div', h('div.rx-box', this.inp, ins('ε'), ins('∅'), ins('|'), ins('*')), this.tokens, this.msg);
      el.appendChild(this.root);
      this.inp.addEventListener('input', () => this.refresh(true));
      this.refresh(false);
    }
    refresh(user) {
      const v = this.inp.value;
      const r = T.checkRegex(v);
      this.r = r;
      this.tokens.innerHTML = v ? T.highlightRegex(v) : '';
      if (!r.ok && r.pos !== undefined) {
        const i = Math.min(r.pos, v.length);
        this.tokens.innerHTML = T.highlightRegex(v.slice(0, i)) + '<span class="k-err">' + (esc(v.slice(i, i + 1)) || '&nbsp;') + '</span>' + T.highlightRegex(v.slice(i + 1));
      }
      this.msg.innerHTML = '';
      if (!v) this.msg.append('| is union, writing side by side is concatenation, * + ? repeat, ε is the empty string and ∅ the empty language.');
      else if (r.ok) this.msg.append('Read as ', h('b', r.shown || v), r.size ? ' · ' + r.size + ' operators and symbols' : '', ...(r.alphabet ? [' · alphabet ', h('b', '{' + r.alphabet.join(', ') + '}')] : []));
      else this.msg.appendChild(h('span', { style: { color: 'var(--bad)' } }, r.error));
      this.inp.classList.toggle('bad', !r.ok);
      if (user && this.opts.onChange) this.opts.onChange(v, r.ok);
    }
    value() { return this.inp.value; }
    setValue(v) { this.inp.value = v; this.refresh(false); }
    ok() { return this.r.ok; }
    destroy() { this.root.remove(); }
  }
  T.RegexInput = RegexInput;
})();
