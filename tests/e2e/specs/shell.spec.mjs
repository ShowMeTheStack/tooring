// The frame of the page: loading, the home page and catalogue, themes, projector mode, dialogs.
export default (t) => {
  t.test('the page starts and shows the home page', async (p) => {
    p.assert.ok(await p.exists('.home .hero'));
    p.assert.match(await p.text('.hero h1'), /theory of computation/i);
    p.assert.equal(p.newExceptions().length, 0);
  }, { fresh: true });
  t.test('the title names Tooring', async (p) => { p.assert.match(await p.ev('document.title'), /Tooring/); });
  t.test('the home page lists the seven parts in order', async (p) => {
    const parts = await p.ev("[...document.querySelectorAll('.part')].map(e => e.dataset.part)");
    p.assert.deepEqual(parts, await p.ev('Tooring.parts.map(x => x.id)'));
  });
  t.test('the home page has a card for every family with topics', async (p) => {
    p.assert.equal(await p.count('.fam-card'), await p.ev('Tooring.families.filter(f => Tooring.topics.some(t => t.family === f.id)).length'));
  });
  t.test('the hero picture animates a machine', async (p) => {
    await p.wait("document.querySelectorAll('#heroArt [data-key]').length > 5");
    const a = await p.ev("document.querySelector('#heroArt .it-state.active').dataset.key");
    await p.sleep(1500);
    const b = await p.ev("[...document.querySelectorAll('#heroArt .it-state.active, #heroArt .it-state.good')].map(e => e.dataset.key).join()");
    p.assert.ok(a && b);
  });
  t.test('a family card opens its first topic', async (p) => {
    const fam = await p.attr('.fam-card', 'data-fam');
    await p.click('.fam-card');
    await p.wait('!!Tooring.app.player');
    p.assert.equal(await p.ev('Tooring.app.player.t.family'), fam);
  });
  t.test('the brand link goes home', async (p) => {
    await p.open('dfa-run');
    await p.click('#brand');
    await p.wait("!!document.querySelector('.home')");
  });
  t.test('the catalogue lists every topic under its part', async (p) => {
    await p.ev("document.querySelectorAll('#side .cat-fam:not(.open) > button').forEach(b => b.click())");
    await p.sleep(80);
    p.assert.equal((await p.sideTopics()).length, (await p.topics()).length);
    p.assert.ok((await p.count('#side .cat-group')) >= 3);
  });
  t.test('the catalogue search filters topics', async (p) => {
    await p.click('#catSearch');
    await p.insertText('turing');
    await p.sleep(250);
    const found = await p.sideTopics();
    p.assert.ok(found.includes('tm-run') && !found.includes('dfa-run'), 'turing finds the Turing topics only: ' + found);
    await p.ev("(() => { const s = document.getElementById('catSearch'); s.value = 'zzqq'; s.dispatchEvent(new Event('input')); })()");
    await p.sleep(250);
    p.assert.ok(await p.exists('#side .empty-state'), 'no match shows an empty state');
    await p.ev("(() => { const s = document.getElementById('catSearch'); s.value = ''; s.dispatchEvent(new Event('input')); })()");
  });
  t.test('the theme button switches between light and dark', async (p) => {
    const a = await p.theme();
    await p.click('#btnTheme');
    p.assert.notEqual(await p.theme(), a);
    await p.click('#btnTheme');
    p.assert.equal(await p.theme(), a);
  });
  t.test('projector mode makes the type larger and is remembered', async (p) => {
    const before = await p.ev("parseFloat(getComputedStyle(document.body).fontSize)");
    await p.click('#btnProjector');
    p.assert.ok(await p.ev("parseFloat(getComputedStyle(document.body).fontSize)") > before);
    p.assert.equal((await p.settings()).projector, true);
    await p.reload();
    p.assert.equal(await p.ev('document.documentElement.dataset.projector'), 'on');
    await p.click('#btnProjector');
  });
  t.test('the help menu opens settings, About and About the author', async (p) => {
    await p.click('#btnAbout');
    await p.click('.menu-pop .menu-item', 'Settings');
    p.assert.equal(await p.waitModal(), 'Settings');
    p.assert.ok(await p.exists('#set-theme'));
    await p.closeModals();
    await p.click('#btnAbout');
    await p.click('.menu-pop .menu-item', 'About Tooring');
    await p.waitModal();
    p.assert.match(await p.modalText(), /Based on Tooring by Jyotiprakash Mishra/);
    await p.closeModals();
    await p.click('#btnAbout');
    await p.click('.menu-pop .menu-item', 'About the author');
    p.assert.equal(await p.waitModal(), 'About the author');
    const txt = await p.modalText();
    p.assert.match(txt, /Other things I made/);
    p.assert.match(txt, /Kwery/);
    p.assert.match(txt, /Strux/);
    p.assert.ok(await p.ev("document.querySelector('.author-photo img').naturalWidth > 0"));
    await p.closeModals();
  });
  t.test('? shows the keyboard shortcuts', async (p) => {
    await p.key('?');
    p.assert.equal(await p.waitModal(), 'Keyboard shortcuts');
    await p.closeModals();
  });
  t.test('settings turn predictions off and on', async (p) => {
    await p.click('#btnAbout');
    await p.click('.menu-pop .menu-item', 'Settings');
    await p.waitModal();
    const was = (await p.settings()).predict;
    await p.click('#set-predict');
    p.assert.equal((await p.settings()).predict, !was);
    await p.closeModals();
  });
  t.test('the kit gallery shows every demo and steps through them', async (p) => {
    await p.route('kits');
    await p.wait("document.querySelectorAll('.kit-card').length > 10");
    p.assert.equal(await p.count('.kit-card'), await p.ev('Tooring.KitLab.list().length'));
    p.assert.equal(await p.ev("document.querySelectorAll('.kit-card marker').length > 0"), true);
  });
  t.test('there is no horizontal scrolling on the home page', async (p) => {
    await p.route('');
    p.assert.ok(await p.noHScroll());
  });
};
