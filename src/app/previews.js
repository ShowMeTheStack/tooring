// Small drawings for the catalogue cards: one per kind of picture (a state diagram, a tape, a stack, a
// parse tree, a table, sets, dominoes, tiles, a gadget graph ...). A family may name its drawing with
// preview: 'tape'; otherwise one is chosen from its title, id and part. They are decorations, drawn with
// the theme's colours, and marked for the diagram checker to skip.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const P = (T.Previews = {});
  const st = (x, y, r, cls) => `<circle cx="${x}" cy="${y}" r="${r || 9}" class="pv-node ${cls || ''}"/>`;
  const ar = (d, cls) => `<path d="${d}" class="pv-edge ${cls || ''}"/>`;
  const box = (x, y, w, hh, cls) => `<rect x="${x}" y="${y}" width="${w}" height="${hh}" rx="2.5" class="pv-cell ${cls || ''}"/>`;
  const DRAW = {
    states: () => st(22, 34, 9, 'on') + st(62, 20) + st(102, 34) + st(102, 34, 6, 'ring') + ar('M31 30 L53 23') + ar('M71 23 L93 30', 'hot') + ar('M95 42 Q62 62 30 42') + ar('M6 34 H13'),
    nfa: () => st(20, 34, 9, 'on') + st(60, 16, 9, 'on') + st(60, 52, 9, 'on') + st(102, 34) + st(102, 34, 6, 'ring') + ar('M28 29 L52 19') + ar('M28 39 L52 49') + ar('M69 19 L94 30', 'hot') + ar('M69 49 L94 38'),
    tape: () => [0, 1, 2, 3, 4, 5].map((i) => box(8 + i * 18, 18, 18, 18, i === 2 ? 'on' : '')).join('') + '<path d="M44 46 l7 -8 l7 8 z" class="pv-head"/>' + ar('M80 52 h24', 'hot'),
    stack: () => [0, 1, 2, 3].map((i) => box(44, 12 + i * 11, 36, 11, i === 0 ? 'on' : '')).join('') + ar('M14 20 H38', 'hot') + ar('M86 20 H110'),
    tree: () => ar('M62 14 L36 32') + ar('M62 14 L88 32') + ar('M36 32 L24 52') + ar('M36 32 L48 52') + ar('M88 32 L88 52') + st(62, 14, 7, 'on') + st(36, 32, 7) + st(88, 32, 7) + st(24, 52, 5, 'leaf') + st(48, 52, 5, 'leaf') + st(88, 52, 5, 'leaf'),
    table: () => { let s = ''; for (let r = 0; r < 4; r++) for (let c = 0; c < 5; c++) s += box(12 + c * 20, 6 + r * 13, 20, 13, (r === 0 || c === 0) ? 'head' : r === 2 && c === 3 ? 'on' : ''); return s; },
    triangle: () => { let s = ''; for (let r = 0; r < 4; r++) for (let c = 0; c < 4 - r; c++) s += box(22 + c * 20 + r * 10, 50 - r * 13, 20, 13, r === 3 ? 'on' : ''); return s; },
    sets: () => '<ellipse cx="46" cy="34" rx="28" ry="20" class="pv-set a"/><ellipse cx="78" cy="34" rx="28" ry="20" class="pv-set b"/>' + st(40, 32, 3, 'dot') + st(62, 36, 3, 'dot on') + st(88, 30, 3, 'dot'),
    dominoes: () => [0, 1, 2].map((i) => `<rect x="${12 + i * 36}" y="12" width="30" height="40" rx="4" class="pv-dom${i === 1 ? ' on' : ''}"/><path d="M${12 + i * 36} 32 h30" class="pv-mid"/>`).join(''),
    tiles: () => { let s = ''; for (let r = 0; r < 2; r++) for (let c = 0; c < 4; c++) { const x = 18 + c * 22, y = 12 + r * 22; s += `<path d="M${x} ${y} h22 l-11 11 z" class="pv-t t${(r + c) % 3}"/><path d="M${x} ${y + 22} h22 l-11 -11 z" class="pv-t t${(r + c + 1) % 3}"/><rect x="${x}" y="${y}" width="22" height="22" class="pv-tile"/>`; } return s; },
    gadget: () => ar('M20 18 L48 46') + ar('M48 46 L76 18') + ar('M76 18 L104 46') + ar('M20 18 H76') + ar('M48 46 H104', 'hot') + st(20, 18, 6) + st(48, 46, 6, 'on') + st(76, 18, 6) + st(104, 46, 6, 'on'),
    string: () => [0, 1, 2, 3, 4].map((i) => box(14 + i * 19, 22, 19, 19, i < 2 ? 'read' : i === 2 ? 'on' : '')).join('') + '<path d="M52 50 l7 -7 l7 7 z" class="pv-head"/>',
    pump: () => [0, 1, 2, 3, 4, 5].map((i) => box(8 + i * 18, 22, 18, 18, i === 2 || i === 3 ? 'pump' : '')).join('') + ar('M44 14 Q62 2 80 14', 'hot'),
    diagonal: () => { let s = ''; for (let r = 0; r < 4; r++) for (let c = 0; c < 4; c++) s += box(28 + c * 17, 6 + r * 13, 17, 13, r === c ? 'on' : ''); return s; },
    classes: () => '<ellipse cx="62" cy="36" rx="54" ry="26" class="pv-set b"/><ellipse cx="54" cy="38" rx="34" ry="18" class="pv-set a"/><ellipse cx="46" cy="40" rx="16" ry="9" class="pv-set c"/>',
    clock: () => '<circle cx="62" cy="32" r="22" class="pv-set a"/>' + ar('M62 32 V16', 'hot') + ar('M62 32 L76 38') + st(62, 32, 3, 'dot on'),
  };
  /** The drawing for a family: {preview} if it names one, else a guess from its words, else its part's */
  P.kindFor = function (f) {
    if (f.preview && DRAW[f.preview]) return f.preview;
    const s = (f.id + ' ' + f.title).toLowerCase();
    const rules = [
      [/pump/, 'pump'], [/cyk|earley|triangle/, 'triangle'], [/ll\(|first|follow|lr|slr|lalr|table|parse table|shift/, 'table'], [/pda|push|stack/, 'stack'],
      [/turing|tape|tm\b|machine|beaver|register|counter/, 'tape'], [/grammar|cfg|deriv|tree|ambig|normal form|cnf/, 'tree'], [/nfa|subset|nondet/, 'nfa'],
      [/dfa|automat|regular|minim|regex|express/, 'states'], [/pcp|domino|post/, 'dominoes'], [/til/, 'tiles'], [/diagonal|halt|countab/, 'diagonal'],
      [/sat|clique|cover|reduc|gadget|colour|color|np\b|graph/, 'gadget'], [/class|hierarch|map/, 'classes'], [/space|time|step|complex/, 'clock'],
      [/set|relation|function|closure|equivalence|partition/, 'sets'], [/string|language|alphabet/, 'string'],
    ];
    for (const [re, k] of rules) if (re.test(s)) return k;
    return { foundations: 'sets', regular: 'states', 'context-free': 'tree', parsing: 'table', turing: 'tape', computability: 'diagonal', complexity: 'gadget' }[f.part] || 'states';
  };
  P.svg = function (kind) {
    const s = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    s.setAttribute('viewBox', '0 0 124 64');
    s.setAttribute('class', 'pv pv-' + kind);
    s.setAttribute('aria-hidden', 'true');
    s.dataset.audit = 'ignore';
    s.innerHTML = (DRAW[kind] || DRAW.states)();
    return s;
  };
  P.kinds = Object.keys(DRAW);

  // ---- live thumbnails: the family's own first topic, drawn by the stage at card size ---------------------------
  // A card shows its drawing at once; when it scrolls into view, the family's first topic runs once (cached)
  // and a frame from the middle of it replaces the drawing. Work is done a card at a time, between frames,
  // so scrolling stays smooth.
  const cache = new Map();
  let queue = [], busy = false, observer = null;
  function frameFor(f) {
    if (cache.has(f.id)) return cache.get(f.id);
    let fr = null;
    try {
      const t = T.topics.find((x) => x.family === f.id && !x.noPreview);
      const r = t && T.run(t, T.inputOf(t));
      if (r && r.ok && r.frames.length) {
        const pick = f.previewFrame !== undefined ? f.previewFrame : t.previewFrame !== undefined ? t.previewFrame : Math.floor((r.frames.length - 1) * 0.6);
        const src = r.frames[Math.max(0, Math.min(r.frames.length - 1, pick))];
        // the camera hugs the drawing itself, not the topic's own (roomier) view, so the card is filled
        const u = src.items.length && T.stageBounds(src.items, { margin: 0, minW: 1, minH: 1 });
        if (u) { const m = Math.max(u.w, u.h) * 0.04 + 2; fr = { items: src.items, view: { x: u.x - m, y: u.y - m, w: u.w + 2 * m, h: u.h + 2 * m } }; }
      }
    } catch (e) { fr = null; }
    cache.set(f.id, fr);
    return fr;
  }
  function drain() {
    if (busy) return;
    busy = true;
    const next = () => {
      const job = queue.shift();
      if (!job) { busy = false; return; }
      if (job.el.isConnected && !job.el.dataset.live) {
        const fr = frameFor(job.f);
        if (fr) {
          job.el.dataset.live = '1';
          const holder = document.createElement('div');
          holder.className = 'fc-live';
          const st = new T.Stage(holder, { label: '' });
          st.root.dataset.audit = 'ignore';
          st.root.setAttribute('aria-hidden', 'true');
          job.el.innerHTML = '';
          job.el.appendChild(holder);
          st.show(fr, { duration: 0 });
        }
      }
      (window.requestIdleCallback || ((fn) => setTimeout(fn, 16)))(next);
    };
    next();
  }
  /** Ask for a live thumbnail of family f in the element el (a card's art box), when it comes into view */
  P.live = function (el, f) {
    if (typeof IntersectionObserver === 'undefined' || f.preview === 'static') return;
    if (!observer) {
      observer = new IntersectionObserver((entries) => {
        for (const e of entries) if (e.isIntersecting) { observer.unobserve(e.target); queue.push(e.target._pv); }
        drain();
      }, { rootMargin: '200px 0px' });
    }
    el._pv = { el, f };
    observer.observe(el);
  };
})();
