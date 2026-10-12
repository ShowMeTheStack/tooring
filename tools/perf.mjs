// How quickly the built page starts: node tools/perf.mjs [--no-build] [runs]
// Loads index.html a few times in headless Chrome and prints the size of the file, the time until the app is
// ready (the home page drawn), the script's own start-up time, and how long opening a topic takes.
import { launch } from './cdp.mjs';
import { execSync } from 'node:child_process';
import { statSync } from 'node:fs';
import { join, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
if (!process.argv.includes('--no-build')) execSync('node build.mjs', { cwd: root, stdio: 'ignore' });
const runs = +(process.argv.slice(2).find((a) => /^\d+$/.test(a)) || 3);
const kb = (statSync(join(root, 'index.html')).size / 1024).toFixed(0);
const rows = [];
for (let r = 0; r < runs; r++) {
  const b = await launch({ width: 1440, height: 900 });
  try {
    await b.goto('');
    await b.waitFor('window.__tooringReady === true', 30000);
    const nav = await b.eval("JSON.stringify((() => { const n = performance.getEntriesByType('navigation')[0]; return { dom: n.domContentLoadedEventEnd, load: n.loadEventEnd }; })())");
    const ready = await b.eval('performance.now()');
    const topic = await b.eval(`(async () => { const t0 = performance.now(); location.hash = 'topic=' + Tooring.topics[0].id; await new Promise((r) => { const w = () => Tooring.app.player ? r() : setTimeout(w, 5); w(); }); return performance.now() - t0; })()`);
    const n = await b.eval('Tooring.topics.length');
    rows.push(Object.assign(JSON.parse(nav), { ready, topic, n }));
  } finally { await b.close(); }
}
const avg = (k) => (rows.reduce((s, x) => s + x[k], 0) / rows.length).toFixed(0);
console.log(`index.html ${kb} KB, ${rows[0].n} topics: DOMContentLoaded ${avg('dom')} ms, load ${avg('load')} ms, a topic opens in ${avg('topic')} ms (mean of ${runs})`);
