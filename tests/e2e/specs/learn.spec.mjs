// Lessons, exercises (every answer kind is checked), hints, progress, tours and courses, on the real
// content of src/content: each test uses a lesson or an exercise of the kind it checks.
export default (t) => {
  t.test('the Learn page lists chapters with lessons and exercises', async (p) => {
    await p.route('learn');
    await p.wait("!!document.getElementById('learnView')");
    p.assert.ok((await p.count('.chap-card')) >= 1);
    p.assert.ok(await p.exists('.chap-items a[href="#lesson=reg-dfa-read"]'));
    p.assert.ok(await p.exists('.tour-list .chip'));
  }, { fresh: true });
  t.test('a lesson embeds a live player, a run box and a prediction', async (p) => {
    await p.route('lesson=reg-dfa-read');
    await p.wait("!!document.getElementById('lessonView')");
    p.assert.ok((await p.count('#lessonView .ls-player .stage-svg')) >= 1);
    p.assert.ok((await p.count('#lessonView .run-box .verdict.yes, #lessonView .run-box .verdict.no')) >= 1);
    await p.click('.ls-predict .quiz-opt');
    p.assert.ok(await p.exists('.ls-predict .lp-res b'));
    // the keyboard drives the embedded player
    await p.ev("document.querySelector('#lessonView .ls-player').dispatchEvent(new PointerEvent('pointerover', { bubbles: true }))");
    await p.key('ArrowRight');
    p.assert.equal(await p.ev('Tooring.app.page.player.i'), 1);
  });
  t.test('a lesson editor tests strings', async (p) => {
    await p.route('lesson=cf-l-design');
    await p.wait("!!document.querySelector('.bench .btn')");
    await p.click('.bench .btn');
    p.assert.ok((await p.count('.bench-out tr')) >= 4);
    p.assert.match(await p.text('.bench-out p'), /all as expected/);
  });
  t.test('finishing a lesson marks it read', async (p) => {
    await p.route('lesson=tur-l-tape');
    await p.wait("!!document.getElementById('lessonDone')");
    await p.click('#lessonDone');
    await p.sleep(200);
    p.assert.ok(await p.ev("Tooring.Learn.isDone('lesson', 'tur-l-tape')"));
  });
  const ex = async (p, id) => { await p.route('exercise=' + id); await p.wait("!!document.getElementById('btnCheck')"); };
  const verdict = (p) => p.ev("document.getElementById('exResult').className");
  t.test('a multiple-choice exercise is checked', async (p) => {
    await ex(p, 'found-ex-powerset-empty');
    await p.click('.choices .quiz-opt[data-i="0"]');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /bad/);
    await p.click('.choices .quiz-opt[data-i="1"]');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
    p.assert.ok(await p.ev("Tooring.Learn.isDone('exercise', 'found-ex-powerset-empty')"));
  });
  t.test('a string answer and a number answer are checked', async (p) => {
    await ex(p, 'reg-ex-mealy-output');
    await p.setValue('#ansText', '10110');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /bad/);
    await p.setValue('#ansText', '010110');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
    await ex(p, 'found-ex-powerset-size');
    await p.setValue('#ansText', '31');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /bad/);
    await p.setValue('#ansText', '32');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
  });
  t.test('a DFA built in the editor is checked by equivalence, with a counterexample to run', async (p) => {
    await ex(p, 'reg-ex-dfa-ends-a');
    const set = (text) => p.ev(`(() => { const e = Tooring.app.page.answer; const ta = document.querySelector('#answer .ed-side textarea'); ta.value = ${JSON.stringify(text)}; ta.dispatchEvent(new Event('input', { bubbles: true })); })()`);
    await set('start n\naccept n\nn -a-> y\nn -b-> n\ny -a-> y\ny -b-> n');
    await p.sleep(400);
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /bad/);
    p.assert.match(await p.text('#exResult'), /accept/);
    p.assert.ok(await p.exists('#btnTryCounter'));
    await set('start n\naccept y\nn -a-> y\nn -b-> n\ny -a-> y\ny -b-> n');
    await p.sleep(400);
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
  });
  t.test('a table is filled and checked cell by cell', async (p) => {
    await ex(p, 'parse-ex-first-2');
    const inputs = await p.count('.fill-table input');
    p.assert.equal(inputs, 3);
    await p.ev("const v = ['{', 'k, ε', '&']; document.querySelectorAll('.fill-table input').forEach((i, k) => { i.value = v[k]; })");
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /bad/);
    p.assert.equal(await p.count('.fill-table input.wrong'), 1);
    await p.ev("document.querySelectorAll('.fill-table input')[2].value = 'ε, &'");
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
  });
  t.test('the pumping game is played move by move and checked', async (p) => {
    await ex(p, 'reg-ex-pump-pal');
    await p.setValue('#pumpS', 'aaaabaaaa');
    await p.click('#pumpSGo');
    p.assert.ok((await p.count('.pump-split .part')) === 3);
    await p.setValue('#pumpI', '0');
    await p.click('#pumpIGo');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
  });
  t.test('hints come one at a time and are remembered', async (p) => {
    await ex(p, 'found-ex-both-ends');
    await p.click('#btnHint');
    p.assert.equal(await p.count('#hints .hint'), 1);
    await p.click('#btnHint');
    p.assert.equal(await p.count('#hints .hint'), 2);
    await p.ev("location.hash = 'learn'"); await p.sleep(150);
    await ex(p, 'found-ex-both-ends');
    p.assert.equal(await p.count('#hints .hint'), 2);
  });
  t.test('a tour walks through the player', async (p) => {
    await p.ev("Tooring.Tour.start('reg-tour')");
    await p.wait("!!document.getElementById('tourBox')", 5000);
    await p.wait("!!document.querySelector('#main.tour-hi')", 5000);
    await p.click('#tourNext');
    await p.wait("!!document.querySelector('#stageWrap.tour-hi') && !!Tooring.app.player", 5000);
    p.assert.match(await p.text('#tourBox'), /2 of/);
    await p.click('#tourNext');
    await p.wait("!!document.querySelector('#btnPlay.tour-hi')", 5000);
    await p.key('Escape');
    p.assert.equal(await p.exists('#tourBox'), false);
  });
  t.test('a course lists its steps and leads through them with a strip', async (p) => {
    await p.route('courses');
    await p.wait("!!document.querySelector('.course-card')");
    await p.click('.course-card[data-course="tur-course"]');
    await p.wait("!!document.getElementById('courseStart')");
    p.assert.ok((await p.count('.course-steps li')) >= 3);
    await p.click('#courseStart');
    await p.wait("!!document.getElementById('courseStrip') && !!Tooring.app.player");
    p.assert.match(await p.text('#courseStrip'), /step 1 of/);
    await p.click('#courseNext');
    await p.wait("!!document.getElementById('lessonView') && !!document.getElementById('courseStrip')");
    p.assert.match(await p.text('#courseStrip'), /step 2 of/);
  });
  t.test('a set answer is read in any notation and compared as a set', async (p) => {
    await ex(p, 'found-ex-equiv-closure');
    await p.setValue('#ansText', '{1, 4, 6}, {2, 5}');
    await p.click('#btnCheck');
    p.assert.match(await p.text('#exResult'), /missing/);
    await p.setValue('#ansText', '{{3},{5,2},{6,4,1},{1,6,4}}');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
    await p.setValue('#ansText', '{1, 4, 6');
    await p.click('#btnCheck');
    p.assert.match(await p.text('#exResult'), /never closed/);
  });
  t.test('a relation block draws the pairs and checks properties live', async (p) => {
    await p.route('lesson=found-l-relations');
    await p.wait("!!document.querySelector('.rel-prop')");
    p.assert.ok(await p.exists('.rel-prop.yes'));
    p.assert.match(await p.text('#lessonView'), /ordered pairs/);
    p.assert.ok((await p.count('#lessonView p br')) >= 1, 'a single line break is kept');
    await p.ev("(() => { const i = document.querySelectorAll('.rel-inputs input')[1]; i.value += ', (q, r)'; i.dispatchEvent(new Event('input', { bubbles: true })); })()");
    await p.sleep(400);
    p.assert.match(await p.text('.rel-props'), /✗ transitive|✗ symmetric/);
    p.assert.equal(await p.count('.rel-table td.on'), 6);
  });
  t.test('a Mealy machine is typed, drawn and checked with a counterexample', async (p) => {
    await ex(p, 'reg-ex-mealy-build');
    const set = (v) => p.ev(`(() => { const t = document.getElementById('ansProgram'); t.value = ${JSON.stringify('x')}.replace('x', ${JSON.stringify(v)}); t.dispatchEvent(new Event('input', { bubbles: true })); })()`);
    await set('mealy\nstart A\nA -a/1-> A\nA -b/0-> B\nB -a/0-> A\nB -b/1-> B');
    await p.sleep(400);
    p.assert.ok((await p.count('.trans-art [data-key]')) >= 3, 'drawn');
    await p.click('#btnCheck');
    p.assert.match(await p.text('#exResult'), /On a your machine outputs 1/);
    await set('mealy\nstart s\ns -a/0-> A\ns -b/0-> B\nA -a/1-> A\nA -b/0-> B\nB -a/0-> A\nB -b/1-> B');
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
  });
  t.test('a program answer keeps its lines and is tested', async (p) => {
    await ex(p, 'tur-x-ram-add');
    p.assert.match(await p.ev("document.getElementById('ansProgram').value"), /\n  \n/, 'the empty line of the start text is kept');
    await p.click('#btnCheck');
    p.assert.match(await p.text('#exResult'), /r1 = 1, r2 = 0/);
    await p.ev(`(() => { const t = document.getElementById('ansProgram'); t.value = t.value.replace('\\n  \\n', '\\n  inc r0\\n'); t.dispatchEvent(new Event('input', { bubbles: true })); })()`);
    await p.click('#btnCheck');
    p.assert.match(await verdict(p), /ok/);
  });
};
