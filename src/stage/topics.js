// Parts, families and topics. A part is one of the seven chapters of the catalogue; a family is a group of
// topics on one idea (DFAs, CYK, Turing machines); a topic is one picture with its own inputs and presets,
// a scene for every step with narration, predictions to make on the way and a quiz at the end.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  /** The seven parts, in teaching order */
  T.parts = [
    { id: 'foundations', n: 1, title: 'Foundations', blurb: 'Sets, relations and functions, countable and uncountable, proofs by induction, pigeonhole and diagonalisation, and strings and languages.' },
    { id: 'regular', n: 2, title: 'Finite automata and regular languages', blurb: 'DFAs and NFAs, subset construction, regular expressions, the pumping lemma, Myhill–Nerode and minimisation.' },
    { id: 'context-free', n: 3, title: 'Context-free languages', blurb: 'Grammars and parse trees, ambiguity, normal forms, pushdown automata and the CF pumping lemma.' },
    { id: 'parsing', n: 4, title: 'Parsing', blurb: 'Top down and bottom up: FIRST and FOLLOW, LL(1), shift-reduce, the LR family, CYK and Earley.' },
    { id: 'turing', n: 5, title: 'Turing machines and other models', blurb: 'Tapes and heads, many tapes, nondeterminism, enumerators, register machines, recursive functions and the universal machine.' },
    { id: 'computability', n: 6, title: 'Decidability and computability', blurb: 'Decidable problems, the halting problem, reductions, Rice\'s theorem, PCP and tilings.' },
    { id: 'complexity', n: 7, title: 'Complexity', blurb: 'P and NP, certificates, SAT and reductions as gadgets, Cook–Levin, space and the class map.' },
  ];
  T.partOf = (id) => T.parts.find((p) => p.id === id) || null;
  T.families = [];
  T.topics = [];

  const partRank = (id) => { const i = T.parts.findIndex((p) => p.id === id); return i < 0 ? 99 : i; };
  /** family: {id, part, title, blurb, order} */
  T.family = function (f) {
    if (T.families.some((x) => x.id === f.id)) return T.families.find((x) => x.id === f.id);
    T.families.push(f);
    T.families.sort((a, b) => partRank(a.part) - partRank(b.part) || (a.order || 0) - (b.order || 0));
    return f;
  };
  /**
   * topic: {id, family, title, blurb, order,
   *   inputs: [{id, kind: 'string'|'machine'|'grammar'|'regex'|'choice'|'number'|'list'|'text', label, def,
   *             options: [{value, label}] (choice), min, max (number; length for string and list),
   *             alphabet (string: allowed symbols), machine: 'dfa'|'nfa'|'pda'|'tm' (machine), check(v, input)}],
   *   presets: [{label, values}],
   *   run(input) -> [frame] or {frames, def, counters},
   *   counters: [{id, label}], predict: [...], quiz: [{q, options, answer, why}], camera: 'fit-all'|'follow'}
   * A frame is {items: [stage items], say: 'narration', hl: [ids lit in the definition panel],
   *   counters: {id: n}, predict: {ask, options, answer, explain, pick: 'option'|'item'}, mark, slow, view}.
   */
  T.topic = function (t) {
    if (T.topics.some((x) => x.id === t.id)) throw new Error('two topics with id ' + t.id);
    T.topics.push(t);
    const order = (x) => (x.order === undefined ? 500 : x.order);
    const n = T.topics.map((x, k) => [x, k]);
    const fr = (x) => { const f = T.families.find((y) => y.id === x.family); return f ? partRank(f.part) * 1000 + (f.order || 0) : 99999; };
    n.sort((a, b) => fr(a[0]) - fr(b[0]) || order(a[0]) - order(b[0]) || a[1] - b[1]);
    T.topics.length = 0;
    for (const [x] of n) T.topics.push(x);
    return t;
  };
  T.byId = (id) => T.topics.find((t) => t.id === id) || null;
  T.familyOf = (t) => T.families.find((f) => f.id === t.family) || null;
  T.topicPart = (t) => { const f = T.familyOf(t); return f ? T.partOf(f.part) : null; };

  /** The value of each input: the one given, or its default */
  T.inputOf = function (t, given) {
    const o = {};
    for (const i of t.inputs || []) o[i.id] = given && given[i.id] !== undefined ? given[i.id] : (typeof i.def === 'function' ? i.def() : i.def);
    return o;
  };
  /** Read a field's text into a value of the input's kind */
  T.parseInput = function (inp, text) {
    switch (inp.kind) {
      case 'number': return text === '' ? NaN : Number(text);
      case 'list': return String(text).split(/[\s,]+/).filter(Boolean).map((x) => (x === 'ε' || x === 'eps' ? '' : x));
      case 'string': return String(text).replace(/\s+/g, '') === 'ε' ? '' : String(text).replace(/\s+/g, inp.spaces ? ' ' : '');
      default: return String(text);
    }
  };
  T.showInput = function (inp, v) {
    if (inp.kind === 'list') return (v || []).map((x) => (x === '' ? 'ε' : x)).join(', ');
    return v === undefined || v === null ? '' : String(v);
  };
  /** Check an input against the topic's limits: an error message, or null */
  T.checkInput = function (t, input) {
    for (const i of t.inputs || []) {
      const v = input[i.id];
      const L = i.label || i.id;
      if (i.kind === 'number') {
        if (!Number.isFinite(v) || (i.integer !== false && !Number.isInteger(v))) return L + ': a whole number';
        if (i.min !== undefined && v < i.min) return L + ': at least ' + i.min;
        if (i.max !== undefined && v > i.max) return L + ': at most ' + i.max;
      }
      if (i.kind === 'string') {
        if (typeof v !== 'string') return L + ': a string';
        if (i.alphabet) { const bad = [...v].find((c) => !i.alphabet.includes(c)); if (bad !== undefined) return L + ': "' + bad + '" is not in the alphabet {' + [...i.alphabet].join(', ') + '}'; }
        if (i.max !== undefined && [...v].length > i.max) return L + ': at most ' + i.max + ' symbols, so the picture stays readable';
        if (i.min !== undefined && [...v].length < i.min) return L + ': at least ' + i.min + ' symbols';
      }
      if (i.kind === 'list') {
        if (!Array.isArray(v)) return L + ': a list';
        if (i.max !== undefined && v.length > i.max) return L + ': at most ' + i.max + ' items';
        if (i.min !== undefined && v.length < i.min) return L + ': at least ' + i.min + ' item' + (i.min === 1 ? '' : 's');
      }
      if (i.kind === 'choice' && i.options && !i.options.some((o) => o.value === v)) return L + ': choose one of the options';
      if (i.kind === 'machine' && T.Machine) { try { T.Machine.parse(v); } catch (e) { return L + ': ' + e.message; } }
      if (i.check) { let e; try { e = i.check(v, input); } catch (x) { e = x.message; } if (e) return e; }
    }
    if (t.check) return t.check(input);
    return null;
  };

  /** A helper for building a topic's frames: keeps the running counters and stamps them on each frame */
  class Frames {
    constructor(counters) { this.list = []; this.counts = {}; for (const c of counters || []) this.counts[typeof c === 'string' ? c : c.id] = 0; }
    count(id, n) { this.counts[id] = (this.counts[id] || 0) + (n === undefined ? 1 : n); return this; }
    set(id, n) { this.counts[id] = n; return this; }
    add(frame) { frame.counters = Object.assign({}, this.counts, frame.counters || {}); this.list.push(frame); return frame; }
    get length() { return this.list.length; }
    last() { return this.list[this.list.length - 1]; }
  }
  T.Frames = Frames;

  /** Run a topic with an input: frames (each drawable on the stage), the definition panel and the counters */
  T.run = function (t, input) {
    let out;
    try { out = t.run(input); } catch (e) { return { ok: false, error: e.message || String(e), frames: [{ items: [], say: 'This could not be run: ' + (e.message || e) }], stack: e.stack }; }
    if (Array.isArray(out)) out = { frames: out };
    out = out || { frames: [] };
    const frames = (out.frames || []).filter(Boolean);
    for (const f of frames) { if (!f.items) f.items = []; if (f.items.some((x) => !x)) f.items = f.items.filter(Boolean); }
    // one camera for the whole run, so nothing jumps: the box around every frame (a frame may set its own)
    if (t.camera !== 'follow') {
      let box = null;
      for (const f of frames) { const b = T.stageBounds(f.items, t.cameraOpts); if (b) box = box ? T.geom.union([box, b]) : b; }
      if (box) for (const f of frames) if (!f.view) f.view = box;
    }
    // predictions declared on the topic: find the frames they ask at
    // a prediction that cannot be worked out is reported (tools/check-topics.mjs fails on it), not dropped quietly
    const predictErrors = [];
    for (const p of t.predict || []) {
      for (let i = 0; i < frames.length - 1; i++) {
        if (frames[i].predict) continue;
        let hit = false;
        try { hit = p.at(frames[i], i, frames, input); } catch (e) { hit = false; predictErrors.push('prediction ' + (t.predict.indexOf(p) + 1) + ': at() fails at frame ' + i + ': ' + (e.message || e)); }
        if (!hit) continue;
        let q = null;
        try {
          q = { ask: typeof p.ask === 'function' ? p.ask(frames, i, input) : p.ask, answer: typeof p.answer === 'function' ? p.answer(frames, i, input) : p.answer, options: p.options ? (typeof p.options === 'function' ? p.options(frames, i, input) : p.options) : null, explain: p.explain ? (typeof p.explain === 'function' ? p.explain(frames, i, input) : p.explain) : null, pick: p.pick || (p.options ? 'option' : 'item') };
        } catch (e) { q = null; predictErrors.push('prediction ' + (t.predict.indexOf(p) + 1) + ' at frame ' + i + ': ' + (e.message || e)); }
        if (!q || q.answer === null || q.answer === undefined) continue;
        frames[i].predict = q;
        if (p.once) break;
      }
    }
    return { ok: true, frames, def: out.def || (t.def ? t.def(input) : null), counters: out.counters || t.counters || [], result: out.result, predictErrors };
  };
})();
