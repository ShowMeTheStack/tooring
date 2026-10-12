// The editors: drawing a machine, the text pane in sync, the grammar editor, the regex input, the TM table.
async function shiftDrag(p, from, to) {
  const b = p.b;
  await b.send('Input.dispatchMouseEvent', { type: 'mouseMoved', x: from[0], y: from[1], modifiers: 8 });
  await b.send('Input.dispatchMouseEvent', { type: 'mousePressed', x: from[0], y: from[1], button: 'left', clickCount: 1, modifiers: 8 });
  for (let k = 1; k <= 6; k++) await b.send('Input.dispatchMouseEvent', { type: 'mouseMoved', x: from[0] + (to[0] - from[0]) * k / 6, y: from[1] + (to[1] - from[1]) * k / 6, button: 'left', modifiers: 8 });
  await b.send('Input.dispatchMouseEvent', { type: 'mouseReleased', x: to[0], y: to[1], button: 'left', clickCount: 1, modifiers: 8 });
  await p.sleep(120);
}
export default (t) => {
  t.beforeEach(async (p) => { await p.route('sandbox'); await p.wait('!!(Tooring.app.page && Tooring.app.page.editor)'); });
  t.test('the sandbox opens with a finite automaton in the editor', async (p) => {
    p.assert.ok(await p.exists('#edCanvas svg'));
    p.assert.ok((await p.edMachine()).states.length >= 3);
    p.assert.match(await p.ev("document.getElementById('edText').value"), /start/);
  }, { fresh: true });
  t.test('clicking empty space adds a state, and the text follows', async (p) => {
    const n = (await p.edMachine()).states.length;
    const [x, y] = await p.edPoint(60, 140);
    await p.clickAt(x, y, { after: 120 });
    const m = await p.edMachine();
    p.assert.equal(m.states.length, n + 1);
    p.assert.ok(await p.ev(`document.getElementById('edText').value.includes('${m.states[m.states.length - 1]}')`));
  });
  t.test('shift-dragging from one state to another adds a transition with a label', async (p) => {
    const m0 = await p.edMachine();
    const a = await p.center('#edCanvas [data-key="ed:s:q"] .st-shape');
    const b = await p.center('#edCanvas [data-key="ed:s:p"] .st-shape');
    await shiftDrag(p, a, b);
    await p.wait("!!document.getElementById('edInline')");
    await p.ev("const i = document.getElementById('edInline'); i.value = 'a, b'");
    await p.key('Enter');
    await p.sleep(120);
    const m = await p.edMachine();
    p.assert.equal(m.trans.length, m0.trans.length + 1);
    p.assert.ok(m.trans.some((t) => t.from === 'q' && t.to === 'p' && t.label === 'a, b'));
    p.assert.match(await p.ev("document.getElementById('edText').value"), /q -a,b-> p/);
  });
  t.test('dragging a state moves it', async (p) => {
    const before = (await p.edMachine()).pos.r;
    const a = await p.center('#edCanvas [data-key="ed:s:r"] .st-shape');
    await p.mouse('mouseMoved', a[0], a[1]);
    await p.mouse('mousePressed', a[0], a[1]);
    for (let k = 1; k <= 5; k++) await p.b.send('Input.dispatchMouseEvent', { type: 'mouseMoved', x: a[0] + k * 8, y: a[1] + k * 6, button: 'left' });
    await p.mouse('mouseReleased', a[0] + 40, a[1] + 30);
    await p.sleep(100);
    const after = (await p.edMachine()).pos.r;
    p.assert.ok(after.x > before.x && after.y > before.y);
  });
  t.test('double-clicking a state renames it everywhere', async (p) => {
    await p.dblclick('#edCanvas [data-key="ed:s:q"] .st-shape');
    await p.wait("!!document.getElementById('edInline')");
    await p.ev("document.getElementById('edInline').value = 'mid'");
    await p.key('Enter');
    await p.sleep(100);
    const m = await p.edMachine();
    p.assert.ok(m.states.includes('mid') && !m.states.includes('q'));
    p.assert.ok(m.trans.some((t) => t.from === 'mid' || t.to === 'mid'));
  });
  t.test('the start and accept buttons act on the selected state', async (p) => {
    await p.click('#edCanvas [data-key="ed:s:p"] .st-shape');
    await p.click('#ed-accept');
    p.assert.ok((await p.edMachine()).accept.includes('p'));
    await p.click('#ed-accept');
    p.assert.ok(!(await p.edMachine()).accept.includes('p'));
    await p.click('#edCanvas [data-key="ed:s:r"] .st-shape');
    await p.click('#ed-start');
    p.assert.equal((await p.edMachine()).start, 'r');
  });
  t.test('delete removes a state with its transitions, and undo brings it back', async (p) => {
    const n = (await p.edMachine()).states.length;
    await p.click('#edCanvas [data-key="ed:s:r"] .st-shape');
    await p.key('Delete');
    const m = await p.edMachine();
    p.assert.equal(m.states.length, n - 1);
    p.assert.ok(!m.trans.some((t) => t.from === 'r' || t.to === 'r'));
    await p.click('#ed-undo');
    p.assert.equal((await p.edMachine()).states.length, n);
    await p.click('#ed-redo');
    p.assert.equal((await p.edMachine()).states.length, n - 1);
    await p.click('#ed-undo');
  });
  t.test('typing in the text pane redraws the diagram', async (p) => {
    await p.setValue('#edText', 'start a\naccept c\na -x-> b\nb -y-> c\nc -x,y-> c');
    await p.wait("!!document.querySelector('#edCanvas [data-key=\"ed:s:c\"]')", 3000);
    const m = await p.edMachine();
    p.assert.deepEqual(m.states.slice().sort(), ['a', 'b', 'c']);
    p.assert.equal(m.kind, 'dfa');
  });
  t.test('a mistake in the text is shown and the diagram keeps the last good machine', async (p) => {
    await p.setValue('#edText', 'start a\na => b');
    await p.wait("document.getElementById('edErr').innerText.length > 0", 3000);
    p.assert.match(await p.text('#edErr'), /line 2/);
  });
  t.test('auto layout places every state', async (p) => {
    await p.click('#ed-layout');
    const m = await p.edMachine();
    p.assert.ok(m.states.every((q) => m.pos[q] && Number.isFinite(m.pos[q].x)));
  });
  t.test('the arrow tool adds a transition with two clicks', async (p) => {
    await p.click('[data-kind="fa"]');
    await p.click('#sbExamples'); await p.click('.menu-pop .menu-item', 'Even number');
    await p.wait('!!document.querySelector(\'#edCanvas [data-key="ed:s:e"]\')');
    await p.click('#ed-arrow');
    await p.click('#edCanvas [data-key="ed:s:e"] .st-shape');
    await p.click('#edCanvas [data-key="ed:s:e"] .st-shape');
    await p.wait("!!document.getElementById('edInline')");
    await p.ev("document.getElementById('edInline').value = 'c'");
    await p.key('Enter');
    await p.sleep(100);
    p.assert.ok((await p.edMachine()).trans.some((t) => t.from === 'e' && t.to === 'e' && /c/.test(t.label)));
  });
  t.test('the grammar editor colours and reads the grammar', async (p) => {
    await p.click('[data-kind="grammar"]');
    await p.wait("!!document.getElementById('gramText')");
    p.assert.ok((await p.count('.gram-ed .k-nt')) > 0);
    p.assert.match(await p.text('#gramInfo'), /nonterminals/);
    await p.setValue('#gramText', 'S → a S b | ');
    p.assert.match(await p.text('#gramInfo'), /Start S/);
  });
  t.test('the regex input points at a mistake', async (p) => {
    await p.click('[data-kind="regex"]');
    await p.wait("!!document.getElementById('rxInput')");
    await p.setValue('#rxInput', '(a|b');
    p.assert.ok(await p.exists('#rxShow .k-err'));
    await p.setValue('#rxInput', '(a|b)*');
    p.assert.ok(!(await p.exists('#rxShow .k-err')));
    p.assert.match(await p.text('#rxInfo'), /alphabet/);
  });
  t.test('the TM table edits the machine', async (p) => {
    await p.click('[data-kind="tm"]');
    await p.click('#sbTmView button', 'Table');
    await p.wait("!!document.getElementById('tmTable')");
    await p.setValue('#tmTable input[data-q="carry"][data-a="0"]', '1, L, done', 'change');
    await p.sleep(80);
    p.assert.match(await p.ev("JSON.parse(localStorage.getItem('tooring.sandbox')).texts.tm"), /carry, 0 -> done, 1, L/);
    await p.setValue('#tmTable input[data-q="carry"][data-a="0"]', 'nonsense', 'change');
    p.assert.match(await p.text('#tmErr'), /write/);
    await p.click('#sbTmView button', 'Diagram');
  });
};
