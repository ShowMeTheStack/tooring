// A small macro language for building Turing machines from parts, compiled to a plain transition table.
//
//   alphabet: a b          input symbols          tape: A B #   extra tape symbols
//   sub NAME               starts a subroutine; statements before any `sub` (or in `sub main`) are the program
//   label:                 names the next statement
//   left [n] | right [n] | move L|R [n]
//   write s                write s and stay
//   map a:A b:B            rewrite the current symbol by the table (others unchanged)
//   seek L|R s1|s2         move until the head reads one of the symbols (checks the current cell first)
//   if s1|s2 goto lab      branch on the current symbol (also: if s1|s2 accept | reject | halt)
//   goto lab | accept | reject | halt
//   call NAME              inline a subroutine, a built-in one, or a library machine (call tm:bin-inc)
//
// Inside a subroutine, halt and accept return to the caller; reject rejects the whole machine.
// Every call site gets its own copy of the subroutine's states (prefix site.name.), so the result is
// an ordinary machine with no stack.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});

  const BUILTIN = `
sub seekend
  seek R _
sub seekstart
  seek L _
  right
sub erase
loop:
  if _ halt
  write _
  right
  goto loop
sub copy
  seek R _
  write #
  seek L _
  right
next:
  seek R a|b|#
  if # goto done
  if b goto takeb
  write A
  seek R _
  write a
  goto back
takeb:
  write B
  seek R _
  write b
back:
  seek L A|B
  right
  goto next
done:
  left
fix:
  if _ goto fin
  map A:a B:b
  left
  goto fix
fin:
  right
`;

  // Split the text into blocks of statements; collect every symbol mentioned.
  function parseProgram(text) {
    const blocks = { main: [] }, errors = [], dir = {}, symbols = new Set();
    let cur = 'main', pendingLabels = [];
    String(text).split('\n').forEach((line0, ln) => {
      let line = line0.replace(/\/\/.*$/, '').trim();
      if (!line) return;
      let m = /^(alphabet|tape|blank|name|start)\s*:\s*(.*)$/.exec(line);
      if (m) { dir[m[1]] = m[2].trim(); return; }
      m = /^sub\s+(\S+)$/.exec(line);
      if (m) { cur = m[1]; blocks[cur] = blocks[cur] || []; pendingLabels = []; return; }
      while ((m = /^([A-Za-z_][\w.]*)\s*:\s*(.*)$/.exec(line))) { pendingLabels.push(m[1]); line = m[2].trim(); if (!line) return; }
      const words = line.split(/\s+/), op = words[0].toLowerCase(), st = { op, line: ln + 1, text: line, labels: pendingLabels, block: cur };
      pendingLabels = [];
      const set = (s) => s.split('|').filter(Boolean);
      const count = (w) => (w == null ? 1 : Math.max(1, parseInt(w, 10) || 1));
      if (op === 'left' || op === 'right') { st.op = 'move'; st.dir = op === 'left' ? 'L' : 'R'; st.n = count(words[1]); }
      else if (op === 'move') { st.dir = (words[1] || '').toUpperCase(); st.n = count(words[2]); if (!['L', 'R'].includes(st.dir)) errors.push({ line: ln + 1, msg: 'move needs L or R' }); }
      else if (op === 'write') { st.sym = words[1]; if (!st.sym) errors.push({ line: ln + 1, msg: 'write needs a symbol' }); }
      else if (op === 'map') { st.map = {}; for (const p of words.slice(1)) { const [a, b] = p.split(':'); if (!a || !b) errors.push({ line: ln + 1, msg: `map entries look like a:b, not ${p}` }); else st.map[a] = b; } }
      else if (op === 'seek') { st.dir = (words[1] || '').toUpperCase(); st.set = set(words[2] || ''); if (!['L', 'R'].includes(st.dir) || !st.set.length) errors.push({ line: ln + 1, msg: 'seek needs a direction and symbols, like seek R _' }); }
      else if (op === 'if') {
        st.set = set(words[1] || ''); const act = (words[2] || '').toLowerCase();
        if (act === 'goto') { st.act = 'goto'; st.label = words[3]; } else if (['accept', 'reject', 'halt'].includes(act)) st.act = act;
        else errors.push({ line: ln + 1, msg: 'if needs: if s1|s2 goto label (or accept, reject, halt)' });
      } else if (op === 'goto') { st.label = words[1]; if (!st.label) errors.push({ line: ln + 1, msg: 'goto needs a label' }); }
      else if (op === 'call') { st.name = words[1]; if (!st.name) errors.push({ line: ln + 1, msg: 'call needs a name' }); }
      else if (!['accept', 'reject', 'halt'].includes(op)) { errors.push({ line: ln + 1, msg: `unknown statement "${words[0]}"` }); return; }
      (st.set || []).forEach((s) => symbols.add(s));
      if (st.sym) symbols.add(st.sym);
      if (st.map) Object.entries(st.map).forEach(([a, b]) => { symbols.add(a); symbols.add(b); });
      blocks[cur].push(st);
    });
    return { blocks, errors, dir, symbols };
  }

  // Compile a macro program into a machine. opts.machines: extra named machines callable as `call NAME`.
  function compile(text, opts = {}) {
    const prog = parseProgram(text), builtin = parseProgram(BUILTIN);
    const errors = prog.errors.slice(), trace = [];
    const blank = prog.dir.blank || '_';
    const blocks = Object.assign({}, builtin.blocks, prog.blocks);
    blocks.main = prog.blocks.main; // the built-in text has no main program of its own
    const input = (prog.dir.alphabet || '').split(/\s+/).filter(Boolean);
    const gamma = new Set([blank, ...input, ...(prog.dir.tape || '').split(/\s+/).filter(Boolean), ...prog.symbols]);
    // symbols of the subroutines and machines that are actually called
    const usedMachines = new Map();
    const findMachine = (name) => {
      if (opts.machines && opts.machines[name]) return opts.machines[name];
      if (/^tm:/.test(name) && T.tmLib) return T.tmLib.get(name.slice(3));
      return null;
    };
    const scan = (name, seen) => {
      if (seen.has(name)) return; seen.add(name);
      for (const st of blocks[name] || []) {
        if (st.op !== 'call') continue;
        if (blocks[st.name]) { if (st.name !== 'main') scan(st.name, seen); }
        else { const M = findMachine(st.name); if (M) { usedMachines.set(st.name, M); M.gamma.forEach((s) => gamma.add(s)); } }
      }
      if (builtin.blocks[name]) builtin.blocks[name].forEach((st) => { (st.set || []).forEach((s) => gamma.add(s)); if (st.sym) gamma.add(st.sym); if (st.map) Object.entries(st.map).forEach(([a, b]) => { gamma.add(a); gamma.add(b); }); });
    };
    scan('main', new Set());
    const G = [...gamma];
    const rules = [], states = new Set();
    const ACC = 'qa', REJ = 'qr';
    const rule = (from, read, to, write, move, src) => { rules.push({ from, read: [read], to, write: [write], move: [move], line: src.line }); states.add(from); return rules[rules.length - 1]; };

    // compile one block with a state prefix; exit = where `halt`/the end goes; returns the entry state
    const compileBlock = (name, prefix, exit, stack) => {
      const stmts = blocks[name];
      if (!stmts) { errors.push({ line: 0, msg: `no subroutine called ${name}` }); return REJ; }
      if (stack.includes(name)) { errors.push({ line: 0, msg: `${name} calls itself: subroutines are inlined, so recursion is not allowed` }); return REJ; }
      const labels = {};
      stmts.forEach((st, i) => st.labels.forEach((l) => { labels[l] = i; }));
      const own = (i) => prefix + (stmts[i].labels[0] || 'l' + stmts[i].line);
      const callEntry = new Map();
      const isMain = name === 'main' && !stack.length;
      const resolve = (i, guard = new Set()) => {
        if (i >= stmts.length) return exit;
        if (guard.has(i)) { errors.push({ line: stmts[i].line, msg: 'goto loop that never moves the head' }); return REJ; }
        guard.add(i);
        const st = stmts[i];
        if (st.op === 'goto') { if (!(st.label in labels)) { errors.push({ line: st.line, msg: `no label ${st.label}` }); return REJ; } return resolve(labels[st.label], guard); }
        if (st.op === 'accept') return isMain ? ACC : exit;
        if (st.op === 'halt') return exit;
        if (st.op === 'reject') return REJ;
        if (st.op === 'call') {
          if (!callEntry.has(i)) {
            const after = resolve(i + 1);
            const pre = prefix + st.name.replace(/^tm:/, '') + st.line + '.';
            let entry;
            if (blocks[st.name] && st.name !== 'main') entry = compileBlock(st.name, pre, after, stack.concat([name]));
            else if (usedMachines.has(st.name)) entry = inlineMachine(usedMachines.get(st.name), pre, after, st);
            else { errors.push({ line: st.line, msg: `no subroutine or machine called ${st.name}` }); entry = REJ; }
            callEntry.set(i, entry);
            trace.push({ kind: 'inline', say: `Line ${st.line}: call ${st.name} becomes a fresh copy of its states named ${pre}…, entered at ${entry} and leaving to ${after}.`, name: st.name, prefix: pre, entry, exit: after, block: name, line: st.line });
          }
          return callEntry.get(i);
        }
        return own(i);
      };
      const entry = resolve(0);
      stmts.forEach((st, i) => {
        if (['goto', 'accept', 'reject', 'halt', 'call'].includes(st.op)) { if (st.op === 'call') resolve(i); return; }
        const me = own(i), next = resolve(i + 1), made = [];
        if (st.op === 'move') {
          let from = me;
          for (let k = 1; k <= st.n; k++) { const to = k === st.n ? next : me + '~' + (k + 1); for (const s of G) made.push(rule(from, s, to, s, st.dir, st)); from = to; }
        } else if (st.op === 'write') for (const s of G) made.push(rule(me, s, next, st.sym, 'S', st));
        else if (st.op === 'map') for (const s of G) made.push(rule(me, s, next, st.map[s] || s, 'S', st));
        else if (st.op === 'seek') for (const s of G) made.push(st.set.includes(s) ? rule(me, s, next, s, 'S', st) : rule(me, s, me, s, st.dir, st));
        else if (st.op === 'if') {
          const target = st.act === 'goto' ? (st.label in labels ? resolve(labels[st.label]) : (errors.push({ line: st.line, msg: `no label ${st.label}` }), REJ))
            : st.act === 'reject' ? REJ : st.act === 'accept' && isMain ? ACC : exit;
          for (const s of G) made.push(rule(me, s, st.set.includes(s) ? target : next, s, 'S', st));
        }
        trace.push({ kind: 'stmt', say: `Line ${st.line} (${st.text}) becomes state ${me} with ${made.length} rules${next ? `, continuing to ${next}` : ''}.`, block: name, line: st.line, text: st.text, state: me, next, rules: made.map((r) => `${r.from}, ${r.read[0]} -> ${r.to}, ${r.write[0]}, ${r.move[0]}`) });
      });
      return entry;
    };

    // copy a machine's table with renamed states; its accepting states lead to `exit`, rejecting ones to qr
    const inlineMachine = (M, pre, exit, st) => {
      const name = (q) => (T.tm.isAccept(M, q) ? exit : T.tm.isReject(M, q) ? REJ : pre + q);
      for (const r of M.rules) rule(name(r.from), r.read[0], name(r.to), r.write[0], r.move[0], st);
      return name(M.start);
    };

    const start = compileBlock('main', '', ACC, []);
    const machine = errors.length ? null : T.tm.fromRules({ name: prog.dir.name || 'macro', start, accept: [ACC], reject: [REJ], input: input.length ? input : null, extra: G, output: opts.output || null, kind: opts.kind || null }, rules);
    trace.push({ kind: 'done', say: errors.length ? `${errors.length} problem${errors.length > 1 ? 's' : ''} stop the compilation.` : `The program compiles to ${machine.states.length} states and ${machine.rules.length} plain rules over ${G.length} tape symbols.`, states: machine ? machine.states.length : 0, rules: machine ? machine.rules.length : 0 });
    return { machine, errors, trace, text: machine ? T.tm.toText(machine) : '' };
  }

  T.tmMacro = { compile, parseProgram, BUILTIN };
})();
