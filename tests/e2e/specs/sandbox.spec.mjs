// The sandbox: running, testing lists of strings, converting, sharing and remembering.
export default (t) => {
  t.beforeEach(async (p) => { await p.route('sandbox'); await p.wait('!!(Tooring.app.page && Tooring.app.page.player)'); });
  t.test('running a string gives a verdict and a run to step through', async (p) => {
    await p.click('[data-kind="fa"]');
    await p.ev("document.getElementById('sbInput').value = 'aab'");
    await p.click('#sbRun');
    await p.sleep(150);
    p.assert.equal(await p.text('#sbVerdict'), 'accepted');
    p.assert.ok(await p.ev('Tooring.app.page.player.frames.length') === 4);
    await p.ev("document.getElementById('sbInput').value = 'ba'");
    await p.click('#sbRun');
    p.assert.equal(await p.text('#sbVerdict'), 'rejected');
  }, { fresh: true });
  t.test('testing a list marks what is not as expected', async (p) => {
    await p.setValue('#sbTestList', 'ab\n-ab\nbb');
    await p.click('#sbTestAll');
    p.assert.equal(await p.count('#sbTestOut tr.mismatch'), 1);
    p.assert.equal(await p.count('#sbTestOut tr'), 4);
  });
  t.test('a PDA, a Turing machine, a grammar and a regex each run', async (p) => {
    for (const [k, w, v] of [['pda', 'aabb', 'accepted'], ['tm', '11', 'accepted'], ['grammar', '(())', 'accepted'], ['regex', 'abba', 'accepted']]) {
      await p.click('[data-kind="' + k + '"]');
      await p.ev(`document.getElementById('sbInput').value = '${w}'`);
      await p.click('#sbRun');
      await p.sleep(150);
      p.assert.equal(await p.text('#sbVerdict'), v, k);
      p.assert.ok(await p.ev('Tooring.app.page.player.frames.length') >= 2, k);
    }
  });
  t.test('subset construction turns the NFA into a DFA, and Back returns', async (p) => {
    await p.click('[data-kind="fa"]');
    await p.click('#sbExamples'); await p.click('.menu-pop .menu-item', 'Ends in ab');
    await p.click('[data-conv="subset"]');
    await p.sleep(150);
    p.assert.equal((await p.edMachine()).kind, 'dfa');
    p.assert.ok((await p.edMachine()).states.some((q) => q.includes(',')));
    await p.click('#sbBack');
    await p.sleep(100);
    p.assert.equal((await p.edMachine()).kind, 'nfa');
  });
  t.test('a grammar converts to Chomsky normal form', async (p) => {
    await p.click('[data-kind="grammar"]');
    await p.click('[data-conv="cnf"]');
    await p.sleep(150);
    p.assert.match(await p.ev("document.getElementById('gramText').value"), /→|->/);
  });
  t.test('what is built is remembered after a reload', async (p) => {
    await p.click('[data-kind="regex"]');
    await p.setValue('#rxInput', 'a*b');
    await p.reload();
    await p.route('sandbox');
    await p.wait("!!document.getElementById('rxInput')");
    p.assert.equal(await p.ev("document.getElementById('rxInput').value"), 'a*b');
  });
  t.test('a share link carries the machine', async (p) => {
    await p.click('[data-kind="fa"]');
    const code = await p.ev("Tooring.Share.pack({ kind: 'fa', text: 'start x\\naccept y\\nx -k-> y', tests: 'k' })");
    await p.route('sandbox=' + code);
    await p.wait("!!document.querySelector('#edCanvas [data-key=\"ed:s:y\"]')", 5000);
    p.assert.match(await p.ev("document.getElementById('edText').value"), /x -k-> y/);
  });
  t.test('the sandbox runs register machines, counter machines, recursive functions and λ-terms', async (p) => {
    await p.route('sandbox');
    await p.wait('!!(Tooring.app.page && Tooring.app.page.player)');
    for (const [k, re] of [['ram', /r0 = 5/], ['counter', /halts/], ['rec', /= 5/], ['lambda', /normal|3/]]) {
      await p.click('#sbKinds [data-kind=' + k + ']');
      await p.wait('!!document.getElementById("sbProgram")');
      await p.click('#sbRun');
      p.assert.match(await p.text('#sbVerdict'), re, k);
      p.assert.ok(await p.ev('Tooring.app.page.player.frames.length') >= 2, k + ' runs step by step');
    }
    await p.click('#sbKinds [data-kind=fa]');
  });
};
