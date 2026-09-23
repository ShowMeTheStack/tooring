// Check the content: node tools/check-content.mjs [id or chapter fragment] [--verbose]
// Every exercise: its solution passes its own checker, every one of its wrong answers fails, it has three
// hints, and when it gives both a reference (ref) and a membership test (member) the two agree on every
// short string. Every lesson block names things that exist (topics, exercises, lessons), its sandbox and
// editor blocks hold text that parses, every course step and tour step is complete. Samples (sample: true)
// that name topics not in this build are reported but do not fail.
import { files } from '../tests/load.mjs';
import { readFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import vm from 'node:vm';

// every file on its own, so a topic being written elsewhere that does not load yet only costs its topics
const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const ctx = vm.createContext({ console, setTimeout, clearTimeout, TextEncoder, TextDecoder });
for (const f of files(['core', 'stage', 'topics', 'content'])) {
  try { vm.runInContext(readFileSync(join(root, 'src', f), 'utf8'), ctx, { filename: f }); }
  catch (e) { if (f.startsWith('topics/')) console.log('WARN ' + f + ' does not load: ' + e.message); else throw e; }
}
const T = vm.runInContext('globalThis.Tooring', ctx);
const C = T.Content, K = T.Check;
const only = process.argv.slice(2).filter((a) => !a.startsWith('--'))[0];
const verbose = process.argv.includes('--verbose');
const want = (x) => !only || x.id.includes(only) || String(x.chapter || '').includes(only);
let ok = 0, bad = 0, warn = 0, answers = 0;
const report = (what, id, why, isWarn) => {
  if (!why.length) { ok++; if (verbose) console.log('ok   ' + what + ' ' + id); return; }
  if (isWarn) { warn++; console.log('WARN ' + what + ' ' + id + '\n    ' + why.join('\n    ')); return; }
  bad++; console.log('FAIL ' + what + ' ' + id + '\n    ' + why.join('\n    '));
};
for (const e of C.errors) { if (only && !e.includes(only)) continue; bad++; console.log('FAIL registry: ' + e); }

// ---- exercises ----------------------------------------------------------------------------------------------
const t0 = Date.now();
for (const x of C.exercises.values()) {
  if (!want(x)) continue;
  const why = [];
  if (!K.kinds[x.kind]) why.push('unknown kind ' + x.kind);
  else {
    if (x.solution === undefined) why.push('no solution');
    else { answers++; const r = K.answer(x, x.solution); if (!r.ok) why.push('the solution fails: ' + r.message); else if (verbose) console.log('     ' + x.id + ' solution: ' + r.message); }
    if (!x.wrong || !x.wrong.length) why.push('no wrong answers to try');
    for (const w of x.wrong || []) { answers++; const r = K.answer(x, w); if (r.ok) why.push('a wrong answer passes: ' + JSON.stringify(w).slice(0, 120)); else if (verbose) console.log('     ' + x.id + ' wrong: ' + r.message); }
    // a reference and a membership test must describe the same language
    if (x.member && x.ref !== undefined && (x.kind === 'machine' || x.kind === 'regex' || x.kind === 'grammar')) {
      try {
        const R = K.lang.ref(x, x.kind);
        const M = K.lang.member(x.member, R.alphabet);
        const c = K.compare(M, R, { maxLen: 8, cap: 1200 });
        if (!c.equal) why.push('ref and member disagree on ' + K.showWord(c.counterexample));
      } catch (e) { why.push('the reference cannot be read: ' + e.message); }
    }
    if (x.kind === 'table') { try { K.tableSpec(x); } catch (e) { why.push('the table cannot be built: ' + e.message); } }
    if (x.kind === 'choice' && [].concat(x.answer).some((i) => !(i >= 0 && i < (x.options || []).length))) why.push('the answer is not one of the options');
  }
  if (!x.text) why.push('no text');
  if (!x.hints || x.hints.length < 3) why.push('three hints are needed (the last a worked answer)');
  report('exercise', x.id, why);
}

// ---- lessons -------------------------------------------------------------------------------------------------
const parses = (kind, text) => {
  if (kind === 'grammar') { T.grammar.parse(text); return; }
  if (kind === 'regex') { const c = T.RE.check(text); if (!c.ok) throw new Error(c.error); return; }
  T.Machine.parse(text);
};
for (const l of C.lessons.values()) {
  if (!want(l)) continue;
  const why = [], warns = [];
  if (!l.blocks || !l.blocks.length) why.push('no blocks');
  (l.blocks || []).forEach((b, i) => {
    const at = 'block ' + (i + 1) + ': ';
    if (typeof b === 'string') return;
    if (b.topic && !T.byId(b.topic)) (l.sample ? warns : why).push(at + 'no topic ' + b.topic);
    if (b.topic && T.byId(b.topic) && b.input) { const t = T.byId(b.topic); const e = T.checkInput(t, T.inputOf(t, Object.assign(T.inputOf(t), b.input))); if (e) why.push(at + 'the input is refused: ' + e); }
    if (b.exercise && !C.exercises.has(b.exercise)) why.push(at + 'no exercise ' + b.exercise);
    if (b.lesson && !C.lessons.has(b.lesson)) why.push(at + 'no lesson ' + b.lesson);
    for (const k of ['sandbox', 'editor']) if (b[k]) { try { parses(b[k].kind === 'fa' ? 'nfa' : b[k].kind, b[k].text); } catch (e) { why.push(at + k + ' text does not parse: ' + e.message); } }
    if (b.relation) { const r = T.Check.parseValue(b.relation.pairs || '∅', { topSet: true }); if (r.error) why.push(at + 'relation pairs: ' + r.error); }
    if (b.predict && !(b.predict.answer >= 0 && b.predict.answer < (b.predict.options || []).length)) why.push(at + 'the prediction\'s answer is not an option');
  });
  report('lesson', l.id, why);
  if (warns.length) report('lesson', l.id, warns, true);
}
// ---- courses and tours ------------------------------------------------------------------------------------------
for (const c of C.courses.values()) {
  if (!want(c)) continue;
  const why = [], warns = [];
  for (const s of c.steps) { const st = C.stepOf(s); if (!C.stepExists(st)) (c.sample && st.type === 'topic' ? warns : why).push('no ' + st.type + ' ' + st.id); }
  report('course', c.id, why);
  if (warns.length) report('course', c.id, warns, true);
}
for (const t of C.tours.values()) {
  if (!want(t)) continue;
  const why = [];
  t.steps.forEach((s, i) => { if (!s.text) why.push('step ' + (i + 1) + ' has no text'); });
  if (t.steps[0] && t.steps[0].route === undefined) why.push('the first step needs a route, so the tour starts in the right place');
  report('tour', t.id, why);
}
console.log(ok + ' ok, ' + bad + ' with problems, ' + warn + ' warnings (' + C.exercises.size + ' exercises, ' + answers + ' answers checked in ' + ((Date.now() - t0) / 1000).toFixed(1) + 's; ' + C.lessons.size + ' lessons, ' + C.courses.size + ' courses, ' + C.tours.size + ' tours)');
if (bad) process.exitCode = 1;
