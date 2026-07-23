// Checks every picture and the page around it: node tools/check-diagrams.mjs [--no-build] [--shots DIR]
// [--all-shots] [--wide-only] [--all] [--verbose] [--only topics|kits|home|sandbox|learn|compare|courses] [filter...]
// Every topic with its default input and every preset, at its first, last and two middle frames, audited as a
// whole player page: the stage SVG, and the HTML around it (the inputs, the narration, the definition panel
// and its tables, the counters). Once per run also the Steps tab, and on a phone the definition drawer.
// Also every frame of every kit demo, every scene of the home page picture and the home page itself, the
// sandbox's kinds, the Learn list and every lesson and exercise, Compare and the courses. Each is drawn in
// the built page at 1440×900 and at phone size (390×844), in the light theme, and tools/diagram-audit.js
// reports shapes that overlap, edges that cross or run through shapes and labels, labels that collide or are
// cut off, text cut by its box, content that scrolls sideways with no sign of it, and a page wider than the
// screen. Exits 1 on any problem.
import { launch } from './cdp.mjs';
import { execSync } from 'node:child_process';
import { readFileSync, mkdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
const flag = (f) => args.includes(f);
const val = (f) => (args.includes(f) ? args[args.indexOf(f) + 1] : null);
const shotsAt = val('--shots'), onlyKind = val('--only');
const filters = args.filter((a, i) => !a.startsWith('--') && !['--shots', '--only'].includes(args[i - 1]));
if (!flag('--no-build')) execSync('node build.mjs', { cwd: root, stdio: 'ignore' });
if (shotsAt) mkdirSync(shotsAt, { recursive: true });
const audit = readFileSync(join(root, 'tools/diagram-audit.js'), 'utf8');
const sizes = [[1440, 900]].concat(flag('--wide-only') ? [] : [[390, 844]]);
const wanted = (s) => (!onlyKind || onlyKind.split(',').includes(s.group)) && (!filters.length || filters.some((f) => s.name.includes(f)));
const waitPlayer = (id) => `await new Promise((r, j) => { let n = 0; const w = () => (Tooring.app.player && Tooring.app.player.t.id === ${JSON.stringify(id)}) ? r() : ++n > 300 ? j(new Error('no player')) : setTimeout(w, 30); w(); });`;
const waitFor = (expr) => `await new Promise((r, j) => { let n = 0; const w = () => (${expr}) ? r() : ++n > 300 ? j(new Error('timed out waiting for ${expr.replace(/'/g, '')}')) : setTimeout(w, 30); w(); });`;

let problems = 0, checked = 0;
for (const [W, H] of sizes) {
  const phone = W < 600;
  const b = await launch({ width: W, height: H, mobile: phone });
  try {
    await b.goto('');
    await b.waitFor('window.__tooringReady === true', 30000);
    await b.eval("Tooring.app.settings.theme = 'light'; Tooring.app.settings.predict = false; Tooring.app.applyTheme(); 1");
    // what there is to look at
    const plan = await b.eval(`(() => {
      const T = Tooring, out = [];
      for (const t of T.topics) {
        const runs = [{ label: 'default', values: {} }].concat(t.presets || []);
        runs.forEach((p, k) => {
          const r = T.run(t, T.inputOf(t, Object.assign(T.inputOf(t), p.values)));
          const n = r.frames.length, mid = Math.floor(n / 2);
          for (const i of [...new Set([0, Math.floor(n / 3), Math.floor(2 * n / 3), n - 1])]) out.push({ group: 'topics', kind: 'topic', id: t.id, preset: k, frame: i, name: 'topic ' + t.id + ' / ' + p.label + ' / frame ' + i });
          out.push({ group: 'topics', kind: 'topic', id: t.id, preset: k, frame: mid, tab: 'steps', name: 'topic ' + t.id + ' / ' + p.label + ' / steps tab' });
        });
      }
      T.KitLab.list().forEach((d, k) => { const n = d.frames().length; for (let i = 0; i < n; i++) out.push({ group: 'kits', kind: 'kit', demo: k, frame: i, name: d.name + ' / frame ' + i }); });
      out.push({ group: 'home', kind: 'homepage', name: 'home page' });
      for (const k of ['fa', 'pda', 'tm', 'grammar', 'regex']) out.push({ group: 'sandbox', kind: 'sandbox', sb: k, name: 'sandbox ' + k });
      const C = T.Content;
      out.push({ group: 'learn', kind: 'page', hash: 'learn', sel: '#learnView', name: 'learn list' });
      if (C) {
        for (const id of C.lessons.keys()) out.push({ group: 'learn', kind: 'page', hash: 'lesson=' + id, sel: '#lessonView', name: 'lesson ' + id });
        for (const id of C.exercises.keys()) out.push({ group: 'learn', kind: 'page', hash: 'exercise=' + id, sel: '#exerciseView', name: 'exercise ' + id });
        for (const id of C.courses.keys()) { out.push({ group: 'courses', kind: 'page', hash: 'course=' + id, sel: '#courseView', name: 'course ' + id }); out.push({ group: 'courses', kind: 'page', hash: 'course=' + id + '/0', sel: '#main', name: 'course ' + id + ' / step 1' }); }
      }
      out.push({ group: 'courses', kind: 'page', hash: 'courses', sel: '#coursesView', name: 'courses list' });
      out.push({ group: 'compare', kind: 'page', hash: 'compare', sel: '#compareChooser', name: 'compare chooser' });
      const some = T.topics.filter((t) => (t.presets || []).length >= 2).slice(0, 4);
      for (const t of some) out.push({ group: 'compare', kind: 'page', hash: 'compare=' + t.id + ',' + t.id, sel: '#compareView', name: 'compare ' + t.id });
      return out;
    })()`);
    // the home picture: every frame of every scene
    if (wanted({ group: 'home', name: 'home picture' })) {
      await b.eval(`(async () => { location.hash = '#'; ${waitFor('Tooring.app.hero')} })().then(() => 1)`);
      const scenes = await b.eval('Tooring.app.hero.scenes.map((s) => s.frames.length)');
      scenes.forEach((n, si) => { for (let fi = 0; fi < n; fi++) plan.push({ group: 'home', kind: 'hero', scene: si, frame: fi, name: 'home picture / scene ' + (si + 1) + ' / frame ' + fi }); });
    }
    let lastRoute = null;
    for (const s of plan.filter(wanted)) {
      let setup, rootSel, page = true;
      if (s.kind === 'topic') {
        const route = 'topic=' + s.id;
        setup = (lastRoute === route ? '' : `location.hash = '${route}'; ${waitPlayer(s.id)}`) + `
          const T = Tooring, t = T.byId('${s.id}'), p = T.app.player, pr = [{ values: {} }].concat(t.presets || [])[${s.preset}];
          p.input = T.inputOf(t, Object.assign(T.inputOf(t), pr.values)); p.buildInputs(); p.showTab('${s.tab || 'def'}'); p.run(); p.go(${s.frame}, true);
          p.drawer(${phone && s.tab === 'steps' ? 'true' : 'false'}); await new Promise((r) => setTimeout(r, ${phone && s.tab === 'steps' ? 260 : 0}));`;
        lastRoute = route;
        rootSel = '.topic';
      } else if (s.kind === 'kit') {
        setup = `location.hash = 'kits=${s.demo}'; ${waitFor('Tooring.app.page && Tooring.app.page.player')} Tooring.app.page.player.go(${s.frame}, true);`;
        rootSel = '.kit-card'; lastRoute = null; page = false;
      } else if (s.kind === 'hero') {
        setup = (lastRoute === 'home' ? '' : `location.hash = '#'; ${waitFor('Tooring.app.hero')}`) + ` Tooring.app.hero.show(${s.scene}, ${s.frame});`;
        rootSel = '.hero'; lastRoute = 'home';
      } else if (s.kind === 'homepage') {
        setup = `location.hash = 'part=foundations'; ${waitFor('Tooring.app.hero')} Tooring.app.hero.stop(); document.getElementById('main').scrollTop = 0;`;
        rootSel = '#main'; lastRoute = null;
      } else if (s.kind === 'sandbox') {
        setup = `location.hash = 'sandbox'; await new Promise((r) => setTimeout(r, 200)); document.querySelector('#sbKinds [data-kind=${s.sb}]').click(); await new Promise((r) => setTimeout(r, 200)); const p = Tooring.app.page.player; p.go(p.frames.length - 1, true);`;
        rootSel = '#sandbox'; lastRoute = null;
      } else {
        setup = `location.hash = ${JSON.stringify(s.hash)}; ${waitFor('document.querySelector(' + JSON.stringify(s.sel) + ')')} await new Promise((r) => setTimeout(r, 120));`;
        rootSel = s.sel; lastRoute = null;
      }
      let err = null;
      try { await b.eval('(async () => { ' + setup + ' })().then(() => 1)'); } catch (e) { err = e.message; }
      await b.sleep(s.kind === 'hero' ? 40 : 160);
      checked++;
      if (err) { problems++; console.log('FAIL ' + s.name + ' @' + W + ': setup failed: ' + err.slice(0, 200)); continue; }
      const list = JSON.parse(await b.eval(audit + '\n;JSON.stringify(TooringAudit.run(document.querySelector(' + JSON.stringify(rootSel) + ') || document.body, { html: true, page: ' + page + ' }))'));
      const errs = b.logs.filter((l) => l.type === 'error' || l.type === 'exception');
      b.logs.length = 0;
      if (shotsAt && (list.length || flag('--all-shots'))) await b.screenshot(join(shotsAt, s.name.replace(/[^\w.-]+/g, '_') + '-' + W + '.png'));
      const bad = list.length + errs.length;
      problems += bad;
      if (bad || flag('--verbose')) console.log((bad ? 'FAIL ' : 'ok   ') + s.name + ' @' + W + (bad ? ': ' + list.length + ' problems' + (errs.length ? ', ' + errs.length + ' console errors' : '') : ''));
      for (const p of list.slice(0, flag('--all') ? 1e9 : 12)) console.log('     ' + p.kind.padEnd(19) + p.msg + (p.a ? '  [' + p.a + (p.b ? ' | ' + p.b : '') + ']' : ''));
      if (list.length > 12 && !flag('--all')) console.log('     … and ' + (list.length - 12) + ' more (--all)');
      for (const e of errs.slice(0, 3)) console.log('     console: ' + e.text.slice(0, 300));
    }
  } finally { await b.close(); }
}
console.log(checked + ' pictures and pages checked: ' + (problems ? problems + ' problems' : 'no problems'));
process.exit(problems ? 1 : 0);
