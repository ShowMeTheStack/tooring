// The content registry: chapters, lessons, exercises, tours and courses. Content files (src/content/*.js)
// load before the app and call these to register what they hold; the lesson, exercise, tour and course
// views read it back. Nothing here touches the page, so tools/check-content.mjs can load it in node.
//
//   T.Content.chapter({id, part, n, title, blurb})                 part: one of T.parts' ids; n orders chapters
//   T.Content.lesson({id, chapter, title, minutes, summary, blocks: [...]})   blocks: see src/app/lessons.js
//   T.Content.exercise({id, chapter, title, level: 1..3, kind, text, hints: [3], solution, wrong: [...], ...})
//                                                                  kinds and their fields: src/app/check-basic.js
//   T.Content.tour({id, title, blurb, steps: [{route, target, text, before(app)}]})
//   T.Content.course({id, title, blurb, steps: ['topic-id' | {topic, note} | {lesson} | {exercise}]})
// Anything marked sample: true is a placeholder for the content still to be written.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  if (T.Content) return;
  const C = (T.Content = { chapters: [], lessons: new Map(), exercises: new Map(), tours: new Map(), courses: new Map(), errors: [] });
  const fail = (msg) => { C.errors.push(msg); };
  const need = (o, what, ...keys) => { for (const k of keys) if (o[k] === undefined || o[k] === null || o[k] === '') { fail(what + ' ' + (o.id || '?') + ' has no ' + k); return false; } return true; };

  C.chapter = function (ch) {
    if (!need(ch, 'chapter', 'id', 'part', 'title')) return null;
    const old = C.chapters.find((x) => x.id === ch.id);
    if (old) { Object.assign(old, ch); return old; }
    const c = Object.assign({ n: C.chapters.length + 1, lessons: [], exercises: [] }, ch);
    C.chapters.push(c);
    // parts in teaching order, then the chapter's number
    const rank = (x) => { const i = (T.parts || []).findIndex((p) => p.id === x.part); return (i < 0 ? 99 : i) * 1000 + (x.n || 0); };
    C.chapters.sort((a, b) => rank(a) - rank(b));
    return c;
  };
  const add = (map, listKey, what) => (x) => {
    if (!need(x, what, 'id', 'chapter', 'title')) return null;
    if (map.has(x.id)) fail('two ' + what + 's with id ' + x.id);
    map.set(x.id, x);
    const ch = C.chapters.find((c) => c.id === x.chapter);
    if (!ch) fail(what + ' ' + x.id + ' names an unknown chapter ' + x.chapter);
    else if (!ch[listKey].includes(x.id)) ch[listKey].push(x.id);
    return x;
  };
  C.lesson = add(C.lessons, 'lessons', 'lesson');
  C.exercise = add(C.exercises, 'exercises', 'exercise');
  C.tour = (t) => { if (need(t, 'tour', 'id', 'title', 'steps')) C.tours.set(t.id, t); return t; };
  C.course = (c) => { if (need(c, 'course', 'id', 'title', 'steps')) C.courses.set(c.id, c); return c; };

  C.chapterOf = (x) => C.chapters.find((c) => c.id === (x && x.chapter)) || null;
  /** A course step in one shape: {type: 'topic'|'lesson'|'exercise', id, note} */
  C.stepOf = (s) => (typeof s === 'string' ? { type: 'topic', id: s, note: '' } : s.topic ? { type: 'topic', id: s.topic, note: s.note || '' } : s.lesson ? { type: 'lesson', id: s.lesson, note: s.note || '' } : { type: 'exercise', id: s.exercise, note: s.note || '' });
  C.stepExists = (st) => (st.type === 'topic' ? !!(T.byId && T.byId(st.id)) : st.type === 'lesson' ? C.lessons.has(st.id) : C.exercises.has(st.id));
})();
