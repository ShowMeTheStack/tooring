// The topic player: stepping, playing, scrubbing, inputs and presets, the panels, predictions and the quiz.
export default (t) => {
  t.test('a topic opens with its first frame drawn and narrated', async (p) => {
    await p.open('dfa-run');
    p.assert.ok((await p.frames()) > 3);
    p.assert.equal(await p.at(), 0);
    p.assert.match(await p.say(), /starts in s/);
    p.assert.ok((await p.stageKeys()).includes('g:s:s'));
  }, { fresh: true });
  t.test('the arrow keys step forwards and back', async (p) => {
    await p.open('dfa-run');
    await p.key('ArrowRight'); await p.key('ArrowRight');
    p.assert.equal(await p.at(), 2);
    await p.key('ArrowLeft');
    p.assert.equal(await p.at(), 1);
    await p.key('End');
    p.assert.equal(await p.at(), (await p.frames()) - 1);
    await p.key('Home');
    p.assert.equal(await p.at(), 0);
  });
  t.test('the step buttons move and disable at the ends', async (p) => {
    await p.open('dfa-run');
    p.assert.ok(await p.ev("document.getElementById('btnBack').disabled"));
    await p.click('#btnFwd');
    p.assert.equal(await p.at(), 1);
    await p.toEnd();
    p.assert.ok(await p.ev("document.getElementById('btnFwd').disabled"));
  });
  t.test('play runs to the end and pause stops it', async (p) => {
    await p.open('dfa-run');
    await p.ev('Tooring.app.settings.speed = 5');
    await p.click('#btnPlay');
    p.assert.ok(await p.playing());
    await p.wait('Tooring.app.player.i === Tooring.app.player.frames.length - 1', 8000);
    await p.wait('!Tooring.app.player.playing', 3000);
    await p.key(' ');
    p.assert.ok(await p.playing());
    await p.key(' ');
    p.assert.equal(await p.playing(), false);
  });
  t.test('the timeline scrubs to any frame', async (p) => {
    await p.open('cyk-fill');
    await p.ev("const r = document.getElementById('timeline'); r.value = '7'; r.dispatchEvent(new Event('input'))");
    p.assert.equal(await p.at(), 7);
    p.assert.match(await p.text('#pos'), /^8 \//);
  });
  t.test('the active state moves as symbols are read', async (p) => {
    await p.open('dfa-run', { w: 'ab' });
    await p.go(1);
    p.assert.equal(await p.ev("document.querySelector('#stageWrap .it-state.active').dataset.key"), 'g:s:A');
    await p.go(2);
    p.assert.ok(await p.exists('#stageWrap .it-edge.taken[data-key="g:e:A>B"]'));
    await p.go(3);
    p.assert.ok(await p.exists('#stageWrap .it-state.good[data-key="g:s:B"]'));
  });
  t.test('a preset changes the input and runs again', async (p) => {
    await p.open('dfa-run');
    await p.click('.presets .chip', 'Binary multiples of 3');
    await p.sleep(100);
    p.assert.equal(await p.ev("document.getElementById('in-w').value"), '1001');
    p.assert.ok((await p.stageKeys()).includes('g:s:r0'));
  });
  t.test('a string outside the alphabet is refused with a message', async (p) => {
    await p.open('dfa-run');
    await p.setInput('w', 'abc');
    await p.runInput();
    p.assert.match(await p.inputError(), /not in the machine's alphabet/);
    await p.setInput('w', 'ab');
    await p.runInput();
    p.assert.equal(await p.inputError(), '');
  });
  t.test('an input can be given in the link', async (p) => {
    await p.open('dfa-run', { w: 'bab' });
    p.assert.equal(await p.ev("document.getElementById('in-w').value"), 'bab');
  });
  t.test('the definition panel lights the move being made', async (p) => {
    await p.open('dfa-run', { w: 'ab' });
    await p.click('#tab-def');
    await p.go(1);
    p.assert.equal(await p.ev("document.querySelector('#defView td.hl').dataset.rc"), '0,0');
  });
  t.test('the steps tab lists the narration and jumps to a step', async (p) => {
    await p.open('tm-run');
    await p.click('#tab-steps');
    p.assert.equal(await p.count('#stepsView li'), await p.frames());
    await p.click('#stepsView li:nth-child(4) button');
    p.assert.equal(await p.at(), 3);
    await p.click('#tab-def');
  });
  t.test('the counters count', async (p) => {
    await p.open('tm-run');
    await p.toEnd();
    p.assert.ok(+(await p.ev("document.querySelector('[data-counter=steps] b').innerText")) > 3);
  });
  t.test('the tape head moves and carries the state name', async (p) => {
    await p.open('tm-run');
    await p.go(1);
    const a = await p.ev("document.querySelector('#stageWrap [data-key=\"t:head\"] text').textContent");
    p.assert.equal(a, 'right');
  });
  t.test('CYK draws provenance arrows', async (p) => {
    await p.open('cyk-fill');
    await p.go(8);
    p.assert.ok((await p.count('#stageWrap .it-edge.prov')) >= 2);
  });
  t.test('zoom buttons zoom in, out and back to fit', async (p) => {
    await p.open('dfa-run');
    await p.click('#btnZoomIn');
    p.assert.ok(await p.ev('Tooring.app.player.stage.zoom > 1'));
    await p.click('#btnZoomFit');
    p.assert.equal(await p.ev('Tooring.app.player.stage.zoom'), 1);
  });
  t.test('a prediction stops playback and is answered by clicking a state', async (p) => {
    await p.ev('Tooring.app.settings.predict = true');
    await p.open('dfa-run', { w: 'ab' });
    await p.click('#btnFwd');
    await p.wait("!!document.getElementById('predict')");
    p.assert.equal(await p.at(), 0);
    const [x, y] = await p.center('#stageWrap [data-key="g:s:A"] .st-shape');
    await p.clickAt(x, y);
    await p.wait("/Right/.test(document.getElementById('predict').innerText)");
    await p.click('#predictGo');
    p.assert.equal(await p.at(), 1);
    await p.ev('Tooring.app.settings.predict = false');
  });
  t.test('the quiz checks answers', async (p) => {
    await p.open('cyk-fill');
    await p.click('#btnQuiz');
    await p.waitModal();
    p.assert.ok((await p.count('.quiz-q')) >= 3);
    await p.click('.quiz-q .quiz-opt');
    p.assert.match(await p.text('#quizScore'), /of 1 right/);
    await p.closeModals();
  });
  t.test('a topic seen to the end is ticked in the catalogue', async (p) => {
    await p.open('tm-run');
    await p.toEnd();
    p.assert.ok(await p.exists('#side .cat-topic[data-topic="tm-run"] .done'));
  });
  t.test('the Edit machine button opens the diagram editor', async (p) => {
    await p.open('dfa-run');
    await p.click('#btnEdit-m');
    p.assert.equal(await p.waitModal(), 'Edit the machine');
    p.assert.ok((await p.count('.modal [data-key^="ed:s:"]')) >= 4);
    await p.modalButton('Cancel');
  });
};
