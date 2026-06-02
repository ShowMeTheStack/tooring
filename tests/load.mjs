// Load the core engines (the same files the page uses, in manifest order) into a vm context.
import fs from 'fs';
import path from 'path';
import vm from 'vm';
import { fileURLToPath } from 'url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
// "dir/*.js" and "dir/x-*.js" pull in matching files of a folder in name order; missing files are skipped
function expand(list) {
  return list.flatMap((f) => {
    if (f.includes('*')) {
      const d = f.slice(0, f.lastIndexOf('/'));
      const re = new RegExp('^' + f.slice(f.lastIndexOf('/') + 1).replace(/\./g, '\\.').replace('*', '.*') + '$');
      const dir = path.join(root, 'src', d);
      return fs.existsSync(dir) ? fs.readdirSync(dir).filter((x) => re.test(x) && !list.includes(d + '/' + x)).sort().map((x) => d + '/' + x) : [];
    }
    return fs.existsSync(path.join(root, 'src', f)) ? [f] : [];
  });
}
export function files(parts = ['core']) {
  const m = JSON.parse(fs.readFileSync(path.join(root, 'src/manifest.json'), 'utf8'));
  return [...new Set(parts.flatMap((p) => expand(m[p] || [])))];
}
// Returns the Tooring namespace from a fresh context holding every core file.
// `only` (optional) keeps just the files whose names it accepts, so one engine's tests can load that engine alone.
export function load(parts = ['core'], only = null) {
  const ctx = vm.createContext({ console, setTimeout, clearTimeout, TextEncoder, TextDecoder });
  for (const f of files(parts).filter((x) => !only || only(x))) vm.runInContext(fs.readFileSync(path.join(root, 'src', f), 'utf8'), ctx, { filename: f });
  return ctx.Tooring || vm.runInContext('globalThis.Tooring', ctx);
}

// A tiny test harness shared by the core tests: seeded randomness and counted checks.
export function rng(seed = 1) {
  let s = seed >>> 0 || 1;
  const r = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
  r.int = (n) => Math.floor(r() * n);
  r.pick = (a) => a[Math.floor(r() * a.length)];
  return r;
}
export function harness(name) {
  let pass = 0, fail = 0;
  const t = {
    ok(cond, msg) { if (cond) pass++; else { fail++; if (fail <= 30) console.log('FAIL ' + msg); } },
    eq(a, b, msg) { const x = JSON.stringify(a), y = JSON.stringify(b); t.ok(x === y, msg + ' : got ' + x + ' want ' + y); },
    done() { console.log(`${name}: ${pass} passed, ${fail} failed`); if (fail) process.exitCode = 1; return { pass, fail }; },
  };
  return t;
}
