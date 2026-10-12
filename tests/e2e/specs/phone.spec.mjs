// Phones: the menu, the player and the sandbox at 390 × 844, with touch.
export default (t) => {
  t.test('the home page fits a phone', async (p) => {
    p.assert.ok(await p.noHScroll());
    p.assert.ok(await p.visible('#btnMenu'));
    p.assert.equal(await p.visible('#side'), false);
  }, { fresh: { width: 390, height: 844, mobile: true, touch: true } });
  t.test('the menu button opens the catalogue and a topic closes it', async (p) => {
    await p.click('#btnMenu');
    await p.sleep(300);
    p.assert.ok(await p.visible('#side'));
    await p.ev("document.querySelectorAll('#side .cat-fam:not(.open) > button').forEach(b => b.click())");
    await p.click('#side .cat-topic[data-topic="dfa-run"]');
    await p.wait('!!Tooring.app.player');
    await p.sleep(300);
    p.assert.equal(await p.ev("document.getElementById('app').classList.contains('menu-open')"), false);
  });
  t.test('a topic plays on a phone without sideways scrolling', async (p) => {
    await p.open('tm-run');
    p.assert.ok(await p.noHScroll());
    p.assert.ok(await p.visible('#stageWrap'));
    await p.tap('#btnFwd');
    p.assert.equal(await p.at(), 1);
    const r = await p.rect('#stageWrap');
    p.assert.ok(r.w <= 390 && r.w > 300);
  });
  t.test('the sandbox works on a phone', async (p) => {
    await p.route('sandbox');
    await p.wait('!!(Tooring.app.page && Tooring.app.page.player)');
    p.assert.ok(await p.noHScroll());
    p.assert.ok(await p.visible('#edCanvas'));
    await p.tap('#sbRun');
    p.assert.ok((await p.text('#sbVerdict')).length > 0);
  });
};
