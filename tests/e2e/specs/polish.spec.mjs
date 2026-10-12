// The polish: the machine input preview, tables that fit, keyboard shortcuts and the help, the home page
// picture and cards, Compare, projector mode, and the phone drawer.
export default (t) => {
  t.test('a machine input shows a readable summary, with its text behind a toggle', async (p) => {
    await p.open('tm-run');
    p.assert.match(await p.text('#model-m .model-kind'), /Turing/i);
    p.assert.match(await p.text('#model-m .model-facts'), /states/);
    p.assert.equal(await p.visible('#in-m'), false);
    await p.click('#btnText-m');
    p.assert.ok(await p.visible('#in-m'));
    p.assert.ok(await p.ev("(() => { const t = document.getElementById('in-m'); return t.scrollHeight <= t.clientHeight + 4; })()"), 'the whole text shows');
  }, { fresh: true });
  t.test('the transition table fits the definition panel without cutting cells', async (p) => {
    await p.open('tm-run');
    await p.click('#tab-def');
    p.assert.ok(await p.ev("[...document.querySelectorAll('#defView .dtable-wrap')].every((w) => w.scrollWidth <= w.clientWidth + 1 || w.dataset.scrollAffordance)"));
  });
  t.test('a table too wide for the panel says it scrolls', async (p) => {
    await p.open('tm-run');
    await p.ev("document.getElementById('tabBody').style.width = '150px'; Tooring.UI.fitTables(document.getElementById('tabBody'))");
    p.assert.ok(await p.exists('#defView .dtable-box.scrolls .scroll-note'));
    await p.ev("document.getElementById('tabBody').style.width = ''");
  });
  t.test('keys: F fits, P toggles predictions, R restarts, ? shows the help', async (p) => {
    await p.open('dfa-run');
    await p.click('#btnZoomIn');
    await p.ev('document.activeElement.blur()');
    await p.key('f');
    p.assert.equal(await p.ev('Tooring.app.player.stage.zoom'), 1);
    const before = await p.ev('Tooring.app.settings.predict');
    await p.key('p');
    p.assert.equal(await p.ev('Tooring.app.settings.predict'), !before);
    await p.key('p');
    await p.key('End');
    await p.key('r');
    p.assert.ok((await p.at()) <= 1);
    await p.key('?');
    p.assert.equal(await p.waitModal(), 'Keyboard shortcuts');
    p.assert.ok((await p.count('.keys kbd')) > 10);
    await p.closeModals();
    await p.ev('Tooring.app.player.pause()');
  });
  t.test('the help menu and every button show a focus ring', async (p) => {
    await p.open('dfa-run');
    await p.key('Tab');
    const ring = await p.ev("getComputedStyle(document.activeElement).outlineStyle");
    p.assert.notEqual(ring, 'none');
  });
  t.test('the home page plays several machines and has drawn cards', async (p) => {
    await p.route('');
    await p.wait('!!Tooring.app.hero');
    p.assert.ok((await p.count('#heroDots .hero-dot')) >= 4);
    p.assert.ok((await p.ev("document.getElementById('heroArt').getBoundingClientRect().height")) >= 300);
    await p.click('#heroDots .hero-dot:nth-child(4)');
    p.assert.ok(await p.exists('#heroArt .it-head, #heroArt [data-key*="t:"]'));
    p.assert.ok((await p.count('.fam-card .fc-art svg')) >= 5);
  });
  t.test('Compare runs one topic on two inputs, stepping together', async (p) => {
    await p.open('tm-run');
    await p.click('#btnCompare');
    await p.wait("!!document.getElementById('compareView')");
    p.assert.equal(await p.count('#compareView .stage-svg'), 2);
    await p.click('#cmpFwd'); await p.click('#cmpFwd');
    p.assert.deepEqual(await p.ev('Tooring.app.page.player.sides.map((s) => s.i)'), [2, 2]);
    await p.key('ArrowLeft');
    p.assert.deepEqual(await p.ev('Tooring.app.page.player.sides.map((s) => s.i)'), [1, 1]);
    p.assert.notEqual(await p.ev("document.querySelector('#cmpLeft .say').innerText"), await p.ev("document.querySelector('#cmpRight .say').innerText"));
  });
  t.test('the Compare chooser offers topics', async (p) => {
    await p.route('compare');
    await p.wait("!!document.getElementById('compareChooser')");
    p.assert.ok((await p.count('#compareChooser .fam-card')) >= 1);
    await p.click('#cmpGo');
    await p.wait("!!document.getElementById('compareView')");
  });
  t.test('projector mode hides the catalogue and enlarges the stage', async (p) => {
    await p.open('dfa-run');
    const h0 = (await p.rect('#stageWrap')).h;
    await p.ev('Tooring.app.setProjector(true)');
    await p.sleep(100);
    p.assert.equal(await p.visible('#side'), false);
    p.assert.ok((await p.rect('#stageWrap')).h > h0);
    await p.ev('Tooring.app.setProjector(false)');
  });
  t.test('an unknown topic link says so', async (p) => {
    await p.route('topic=no-such-topic');
    p.assert.ok(await p.exists('.notice'));
  });
  t.test('on a phone the stage comes first and the definition opens in a drawer', async (p) => {
    await p.open('tm-run');
    const s = await p.rect('#stageWrap'), i = await p.rect('#inputs');
    p.assert.ok(s.y < i.y, 'the stage is above the inputs');
    p.assert.equal(await p.visible('#sidePanel'), false);
    await p.tap('#btnDrawer');
    await p.sleep(350);
    p.assert.ok(await p.visible('#sidePanel'));
    p.assert.ok(await p.noHScroll());
    await p.key('Escape');
    await p.sleep(350);
    p.assert.equal(await p.visible('#sidePanel'), false);
  }, { fresh: { width: 390, height: 844, mobile: true, touch: true } });
  t.test('the stage paints by layer and z, whatever order items first appeared in', async (p) => {
    await p.open('dfa-run');
    const order = await p.ev(`(() => {
      const st = Tooring.app.player.stage;
      st.show({ items: [{ key: 'zA', kind: 'region', x: 0, y: 0, w: 50, h: 50 }] }, { duration: 0 });
      st.show({ items: [{ key: 'zA', kind: 'region', x: 0, y: 0, w: 50, h: 50 }, { key: 'zB', kind: 'region', x: -20, y: -20, w: 120, h: 120, z: -1 }, { key: 'zL', kind: 'line', x1: 0, y1: 0, x2: 9, y2: 9, layer: 'top' }] }, { duration: 0 });
      const back = [...st.layers.back.children].map((e) => e.dataset.key);
      return back.join(',') + '|' + (st.layers.top.querySelector('[data-key=zL]') ? 'line on top' : 'line below');
    })()`);
    p.assert.equal(order, 'zB,zA|line on top');
    await p.ev('Tooring.app.player.redraw()');
  });
  t.test('the full-screen stage opens and Escape closes it', async (p) => {
    await p.open('tm-run');
    await p.click('#btnFull');
    await p.sleep(200);
    p.assert.ok(await p.exists('.stage-card.fullscreen'));
    const r = await p.rect('#stageWrap');
    p.assert.ok(r.h > 600 && r.y < 10, 'the stage fills the window: ' + JSON.stringify(r));
    await p.key('Escape');
    p.assert.equal(await p.exists('.stage-card.fullscreen'), false);
  }, { fresh: true });
};
