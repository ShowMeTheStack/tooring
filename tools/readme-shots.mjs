// The screenshots in the README: node tools/readme-shots.mjs [name ...] [--no-build] [--base=url]
// Builds first, then drives the built page in headless Chrome and writes docs/images/*.png
// (1600×950 in the light theme, one dark, one phone at 390×844). Prints any console errors per shot.
// By default it uses the page already served at http://127.0.0.1:8095/ when that answers, else the
// driver's own server.
import { launch } from './cdp.mjs';
import { execSync } from 'node:child_process';
import { mkdirSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
if (!process.argv.includes('--no-build')) execSync('node build.mjs', { cwd: root, stdio: 'ignore' });
mkdirSync(join(root, 'docs/images'), { recursive: true });
const out = (n) => join(root, 'docs/images', n + '.png');
const only = process.argv.slice(2).filter((a) => !a.startsWith('--'));
const baseArg = (process.argv.find((a) => a.startsWith('--base=')) || '').slice(7);
let base = baseArg || 'http://127.0.0.1:8095/';
if (!baseArg) { try { const r = await fetch(base); if (!r.ok) base = ''; } catch (e) { base = ''; } }

// open a topic (with an optional input) and stop on a frame part of the way through
const topic = (id, frac, query) => ({ hash: 'topic=' + id + (query ? '?' + Object.entries(query).map(([k, v]) => k + '=' + encodeURIComponent(JSON.stringify(v))).join('&') : ''),
  js: `const p = Tooring.app.player; p.pause(); p.go(Math.round(${frac} * (p.frames.length - 1)), true);` });
const W = [1600, 950], PHONE = [390, 844];

// every player a page holds (the players in a lesson) to a frame part of the way through
const pagePlayers = (frac) => `for (const p of (Tooring.app.page && Tooring.app.page.players) || []) { p.pause(); p.go(Math.round(${frac} * (p.frames.length - 1)), true); }`;
// scroll the page so an element sits just under the top bar, whichever box does the scrolling
const scrollTo = (sel, expr) => `{ const e = ${expr || 'document.querySelector(' + JSON.stringify(sel) + ')'}; if (e) { e.scrollIntoView({ block: 'start' }); const top = e.getBoundingClientRect().top; const bar = document.querySelector('header, .top, #top'); const off = (bar ? bar.getBoundingClientRect().bottom : 56) + 16; const sc = [document.getElementById('main'), document.scrollingElement].find((x) => x && x.scrollHeight > x.clientHeight); if (sc) sc.scrollTop -= off - top; } }`;
const wait = (ms) => `await new Promise((r) => setTimeout(r, ${ms}));`;

// name: {hash, pre (before the route), js (after), size, wait ms, theme}
const SHOTS = {
  home: { hash: '', js: '', wait: 2500 },
  subset: topic('subset-build', 0.6),
  minimise: topic('min-table', 0.6),
  pumping: topic('pump-game', 0.75),
  cyk: topic('cyk-fill', 0.9),
  lr: topic('lr-parse', 0.5),
  tm: topic('tm-palindrome', 0.75),
  ntm: topic('tm-ntm-tree', 0.7),
  halting: topic('halt-diagonal', 0.8),
  pcp: topic('pcp-play', 0.7),
  reduction: topic('cx-red-clique', 0.7),
  cook: topic('cx-cook-windows', 0.6, { m: 'start: s\naccept: yes\ns, a -> s, a, R\ns, b -> s, b, R\ns, a -> fa, a, R\ns, b -> fb, b, R\nfa, b -> fa, b, R\nfa, a -> yes, a, S\nfb, a -> fb, a, R\nfb, b -> yes, b, S', w: 'aba', t: 3, fault: 'jump' }),
  lesson: { hash: 'lesson=reg-subset', js: wait(300) + pagePlayers(0.6) + wait(200) + scrollTo(null, `(() => { let e = Tooring.app.page.players[0].root; while (e.parentElement && !e.parentElement.matches('article')) e = e.parentElement; return e.previousElementSibling && e.previousElementSibling.previousElementSibling || e; })()`), wait: 1200 },
  exercise: {
    hash: 'exercise=reg-ex-dfa-contains-bba',
    pre: `const x = Tooring.Content.exercises.get('reg-ex-dfa-contains-bba'); const s = Tooring.UI.storage; const p = s.get('learn', {}); p.drafts = p.drafts || {}; p.drafts[x.id] = x.wrong[0]; s.set('learn', p);`,
    js: `document.getElementById('btnCheck').click(); ${wait(300)} const m = document.getElementById('main'); if (m) m.scrollTop = 0; document.scrollingElement.scrollTop = 0;`,
    wait: 1200,
  },
  editor: { hash: 'sandbox', js: '', wait: 1200 },
  dark: Object.assign(topic('pda-run', 0.6), { theme: 'dark' }),
  phone: (() => { const t = topic('nfa-run', 0.55); return { hash: t.hash, js: t.js + wait(300) + scrollTo('#stageWrap'), size: PHONE }; })(),
};

for (const [name, s] of Object.entries(SHOTS)) {
  if (only.length && !only.includes(name)) continue;
  const size = s.size || W;
  const b = await launch({ width: size[0], height: size[1], mobile: size[0] < 600 });
  try {
    const url = (base || b.url) + '#';
    await b.send('Page.navigate', { url });
    await b.waitFor('window.__tooringReady === true', 30000);
    await b.eval(`Tooring.app.settings.theme = ${JSON.stringify(s.theme || 'light')}; Tooring.app.settings.predict = false; Tooring.app.saveSettings(); Tooring.app.applyTheme(); ${s.pre || ''} 1`);
    await b.eval(`location.hash = ${JSON.stringify(s.hash)}; 1`);
    await b.sleep(400);
    if (s.hash.startsWith('topic=')) await b.waitFor('!!(Tooring.app.player && Tooring.app.player.frames.length > 1)', 20000);
    if (s.js) await b.eval('(async () => { ' + s.js + ' })().then(() => 1)');
    await b.sleep(s.wait || 900);
    await b.screenshot(out(name));
    const errs = b.logs.filter((l) => l.type === 'error' || l.type === 'exception');
    console.log(name + (errs.length ? '  (' + errs.length + ' console errors: ' + errs.map((e) => e.text.slice(0, 160)).join(' | ') + ')' : ''));
  } catch (e) {
    console.log(name + '  FAILED: ' + e.message);
  } finally { await b.close(); }
}
