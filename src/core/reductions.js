// Polynomial-time reductions as gadget builders. Each takes an instance, builds the target instance with a
// drawable structure (nodes and edges with roles and labels, or a digit table), and maps certificates both
// ways: forward turns a satisfying assignment into a target certificate, backward turns a target
// certificate into a satisfying assignment.
//
// Formulas are CNFs as in T.sat (clauses of at most three literals for the 3SAT reductions); assignments
// are arrays a[1..n] of booleans. Graphs are {n, edges, directed?} with vertices 0 … n-1.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const lt = (f, l) => T.sat.litText(f, l);
  const isTrue = (a, l) => (l > 0 ? !!a[l] : !a[-l]);
  const checkSize = (f, max = 3) => { if (f.clauses.some((c) => !c.length || c.length > max)) throw new Error(`clauses must have 1 to ${max} literals`); };

  // one node per literal occurrence: (clause j, position p)
  function occurrences(f) {
    const occ = [];
    f.clauses.forEach((c, j) => c.forEach((l, p) => occ.push({ id: occ.length, clause: j, pos: p, lit: l })));
    return occ;
  }

  // ---------- 3SAT -> CLIQUE ----------
  function sat3ToClique(f) {
    checkSize(f);
    const occ = occurrences(f), edges = [];
    for (const u of occ) for (const v of occ) if (u.id < v.id && u.clause !== v.clause && u.lit !== -v.lit) edges.push([u.id, v.id]);
    const G = { n: occ.length, edges }, k = f.clauses.length;
    const draw = {
      nodes: occ.map((o) => ({ id: o.id, label: lt(f, o.lit), role: 'literal', group: 'clause ' + (o.clause + 1) })),
      edges: edges.map(([a, b]) => ({ a, b, role: 'compatible' })),
    };
    const trace = [
      { kind: 'nodes', say: `One vertex for each literal in each clause: ${occ.length} vertices in ${k} groups.`, count: occ.length },
      { kind: 'edges', say: 'Join two vertices when they are in different clauses and are not a literal and its negation.', count: edges.length },
      { kind: 'target', say: `Ask for a clique of size k = ${k}, one vertex per clause.`, k },
    ];
    const forward = (a) => f.clauses.map((c, j) => occ.find((o) => o.clause === j && isTrue(a, o.lit)).id);
    const backward = (S) => { const a = new Array(f.n + 1).fill(false); for (const i of S) if (occ[i].lit > 0) a[occ[i].lit] = true; return a; };
    return { name: '3SAT → CLIQUE', graph: G, k, draw, forward, backward, trace };
  }

  // ---------- 3SAT -> INDEPENDENT SET ----------
  function sat3ToIS(f) {
    checkSize(f);
    const occ = occurrences(f), edges = [], roles = [];
    for (const u of occ) for (const v of occ) if (u.id < v.id) {
      if (u.clause === v.clause) { edges.push([u.id, v.id]); roles.push('clause'); }
      else if (u.lit === -v.lit) { edges.push([u.id, v.id]); roles.push('conflict'); }
    }
    const G = { n: occ.length, edges }, k = f.clauses.length;
    const draw = { nodes: occ.map((o) => ({ id: o.id, label: lt(f, o.lit), role: 'literal', group: 'clause ' + (o.clause + 1) })), edges: edges.map(([a, b], i) => ({ a, b, role: roles[i] })) };
    const trace = [
      { kind: 'triangles', say: 'Each clause becomes a triangle (or an edge, or a single vertex) of its literals: at most one per clause can be chosen.' },
      { kind: 'conflicts', say: 'Join every literal to each occurrence of its negation, so the choices are consistent.' },
      { kind: 'target', say: `Ask for an independent set of size k = ${k}.`, k },
    ];
    const forward = (a) => f.clauses.map((c, j) => occ.find((o) => o.clause === j && isTrue(a, o.lit)).id);
    const backward = (S) => { const a = new Array(f.n + 1).fill(false); for (const i of S) if (occ[i].lit > 0) a[occ[i].lit] = true; return a; };
    return { name: '3SAT → INDEPENDENT SET', graph: G, k, draw, forward, backward, trace };
  }

  // ---------- INDEPENDENT SET <-> VERTEX COVER <-> CLIQUE ----------
  const others = (n, S) => { const s = new Set(S); return Array.from({ length: n }, (_, i) => i).filter((i) => !s.has(i)); };
  function isToVC(G, k) {
    return { name: 'INDEPENDENT SET → VERTEX COVER', graph: G, k: G.n - k, forward: (S) => others(G.n, S), backward: (C) => others(G.n, C),
      draw: { nodes: Array.from({ length: G.n }, (_, i) => ({ id: i, label: String(i), role: 'vertex' })), edges: G.edges.map(([a, b]) => ({ a, b, role: 'edge' })) },
      trace: [{ kind: 'same', say: `Keep the graph and ask for a vertex cover of size n − k = ${G.n - k}: S is independent exactly when every edge has an end outside S.` }] };
  }
  function vcToIS(G, k) {
    return { name: 'VERTEX COVER → INDEPENDENT SET', graph: G, k: G.n - k, forward: (C) => others(G.n, C), backward: (S) => others(G.n, S),
      draw: { nodes: Array.from({ length: G.n }, (_, i) => ({ id: i, label: String(i), role: 'vertex' })), edges: G.edges.map(([a, b]) => ({ a, b, role: 'edge' })) },
      trace: [{ kind: 'same', say: `Keep the graph and ask for an independent set of size n − k = ${G.n - k}: the vertices left out of a cover touch no common edge.` }] };
  }
  function isToClique(G, k) {
    const H = T.cx.complement(G);
    return { name: 'INDEPENDENT SET → CLIQUE', graph: H, k, forward: (S) => S.slice(), backward: (S) => S.slice(),
      draw: { nodes: Array.from({ length: G.n }, (_, i) => ({ id: i, label: String(i), role: 'vertex' })), edges: H.edges.map(([a, b]) => ({ a, b, role: 'complement' })) },
      trace: [{ kind: 'complement', say: 'Swap edges and non-edges: no two vertices of S are joined in G exactly when all of them are joined in the complement.', edges: H.edges.length }] };
  }
  const cliqueToIS = (G, k) => Object.assign(isToClique(G, k), { name: 'CLIQUE → INDEPENDENT SET' });

  // ---------- 3SAT -> VERTEX COVER ----------
  // variable gadget: an edge x — ¬x; clause gadget: a triangle (or edge, or vertex) of its literal
  // occurrences, each joined to the matching variable vertex. k = n + Σ (|clause| − 1).
  function sat3ToVC(f) {
    checkSize(f);
    const nodes = [], edges = [], n = f.n;
    for (let v = 1; v <= n; v++) { nodes.push({ id: 2 * (v - 1), label: lt(f, v), role: 'variable', group: 'x' + v }); nodes.push({ id: 2 * (v - 1) + 1, label: lt(f, -v), role: 'variable', group: 'x' + v }); edges.push({ a: 2 * (v - 1), b: 2 * (v - 1) + 1, role: 'variable' }); }
    const litNode = (l) => 2 * (Math.abs(l) - 1) + (l < 0 ? 1 : 0);
    const occ = [];
    f.clauses.forEach((c, j) => {
      const ids = c.map((l, p) => { const id = nodes.length; nodes.push({ id, label: lt(f, l), role: 'clause', group: 'clause ' + (j + 1) }); occ.push({ id, clause: j, pos: p, lit: l }); return id; });
      for (let x = 0; x < ids.length; x++) for (let y = x + 1; y < ids.length; y++) edges.push({ a: ids[x], b: ids[y], role: 'clause' });
      ids.forEach((id, p) => edges.push({ a: id, b: litNode(c[p]), role: 'link' }));
    });
    const k = n + f.clauses.reduce((s, c) => s + c.length - 1, 0);
    const G = { n: nodes.length, edges: edges.map((e) => [e.a, e.b]) };
    const forward = (a) => {
      const C = [];
      for (let v = 1; v <= n; v++) C.push(litNode(a[v] ? v : -v));
      f.clauses.forEach((c, j) => { const mine = occ.filter((o) => o.clause === j); const keep = mine.find((o) => isTrue(a, o.lit)); mine.forEach((o) => { if (o !== keep) C.push(o.id); }); });
      return C;
    };
    // a small enough cover takes exactly one end of each variable edge: x is true when its positive end is taken
    const backward = (C) => { const s = new Set(C), a = new Array(n + 1).fill(false); for (let v = 1; v <= n; v++) a[v] = s.has(litNode(v)); return a; };
    const trace = [
      { kind: 'variables', say: `Each variable is an edge between its two literals: a cover must take at least one end, ${n} vertices in all.` },
      { kind: 'clauses', say: 'Each clause is a clique of its literal occurrences: a cover takes all but at most one of them.' },
      { kind: 'links', say: 'Join each occurrence to its literal: the occurrence left out of the cover needs its literal to be in the cover, that is, true.' },
      { kind: 'target', say: `Ask for a vertex cover of size k = ${k}.`, k },
    ];
    return { name: '3SAT → VERTEX COVER', graph: G, k, draw: { nodes, edges }, forward, backward, trace };
  }

  // ---------- 3SAT -> HAMILTONIAN PATH (directed) ----------
  // Variable i: top t_i, bottom b_i, and a two-way row s0 (p1 q1) s1 (p2 q2) s2 … (pm qm) sm. From t_i the
  // path enters the row at its left end (x_i true) or its right end (false), crosses it, and leaves to b_i,
  // then on to t_{i+1}. Clause j is a vertex reached by a detour p_ij → c_j → q_ij when x_i is in it (a
  // left-to-right crossing can make it) or q_ij → c_j → p_ij when ¬x_i is in it. The path runs t_1 → b_n.
  function sat3ToHamPath(f) {
    checkSize(f);
    const n = f.n, m = f.clauses.length, nodes = [], edgeSet = new Map();
    const node = (label, role, group) => { nodes.push({ id: nodes.length, label, role, group }); return nodes.length - 1; };
    const edge = (a, b, role) => { const k = a + ',' + b; if (!edgeSet.has(k)) edgeSet.set(k, { a, b, role }); };
    const V = [];
    for (let i = 1; i <= n; i++) {
      const g = 'x' + i, t = node('t' + i, 'top', g), row = [];
      for (let j = 0; j <= m; j++) { row.push(node(`s${i}.${j}`, 'separator', g)); if (j < m) { row.push(node(`p${i}.${j + 1}`, 'left', g)); row.push(node(`q${i}.${j + 1}`, 'right', g)); } }
      const b = node('b' + i, 'bottom', g);
      V.push({ t, b, row });
    }
    const C = f.clauses.map((c, j) => node('c' + (j + 1), 'clause', 'clauses'));
    V.forEach(({ t, b, row }, i) => {
      edge(t, row[0], 'enter'); edge(t, row[row.length - 1], 'enter');
      edge(row[0], b, 'exit'); edge(row[row.length - 1], b, 'exit');
      for (let x = 0; x + 1 < row.length; x++) { edge(row[x], row[x + 1], 'row'); edge(row[x + 1], row[x], 'row'); }
      if (i + 1 < n) edge(b, V[i + 1].t, 'link');
    });
    const pq = (i, j) => ({ p: V[i - 1].row[1 + 3 * j], q: V[i - 1].row[2 + 3 * j] });
    f.clauses.forEach((c, j) => c.forEach((l) => {
      const { p, q } = pq(Math.abs(l), j);
      if (l > 0) { edge(p, C[j], 'detour'); edge(C[j], q, 'detour'); } else { edge(q, C[j], 'detour'); edge(C[j], p, 'detour'); }
    }));
    const edges = [...edgeSet.values()];
    const G = { n: nodes.length, edges: edges.map((e) => [e.a, e.b]), directed: true };
    const s = V[0].t, t = V[n - 1].b;
    // forward: cross each row in the direction of its value, taking each clause's detour at its first true literal
    const forward = (a) => {
      const owner = f.clauses.map((c) => { const l = c.find((x) => isTrue(a, x)); return l == null ? null : Math.abs(l); });
      const path = [];
      V.forEach(({ t: top, b, row }, i0) => {
        const i = i0 + 1;
        path.push(top);
        const order = a[i] ? row.slice() : row.slice().reverse();
        for (let x = 0; x < order.length; x++) {
          path.push(order[x]);
          // after a p (going right) or a q (going left), the detour visits the clause, then the partner
          for (let j = 0; j < m; j++) {
            if (owner[j] !== i) continue;
            const { p, q } = pq(i, j);
            if ((a[i] && order[x] === p) || (!a[i] && order[x] === q)) { path.push(C[j]); }
          }
        }
        path.push(b);
      });
      return path;
    };
    const backward = (path) => { const a = new Array(n + 1).fill(false); V.forEach(({ t: top, row }, i) => { const at = path.indexOf(top); a[i + 1] = path[at + 1] === row[0]; }); return a; };
    const trace = [
      { kind: 'variables', say: `Each variable gets a row of ${3 * m + 1} vertices that can be crossed either way: left to right means true, right to left false.` },
      { kind: 'chain', say: 'The rows are chained from top to bottom, so the path must cross every row once.' },
      { kind: 'clauses', say: 'Each clause is a vertex the path can visit by a detour from a row, but only when crossing in the direction that makes one of its literals true.' },
      { kind: 'target', say: `Ask for a Hamiltonian path from ${nodes[s].label} to ${nodes[t].label} through all ${nodes.length} vertices.` },
    ];
    return { name: '3SAT → HAM-PATH', graph: G, s, t, draw: { nodes, edges }, forward, backward, trace };
  }

  // ---------- 3SAT -> SUBSET SUM ----------
  // Decimal columns: one per variable, one per clause. y_i (x_i true) and z_i (false) each have 1 in column i
  // and, in column j, how often x_i (resp. ¬x_i) occurs in clause j. Two slack numbers per clause have a 1
  // in its column. Target: 1 in every variable column, 3 in every clause column. No column can carry.
  function sat3ToSubsetSum(f) {
    checkSize(f);
    const n = f.n, m = f.clauses.length;
    if (n + m > 15) throw new Error('too many digits for exact arithmetic');
    const rows = [];
    const num = (digits) => digits.reduce((acc, d) => acc * 10 + d, 0);
    for (let i = 1; i <= n; i++) for (const sign of [1, -1]) {
      const d = new Array(n + m).fill(0);
      d[i - 1] = 1;
      f.clauses.forEach((c, j) => { d[n + j] = c.filter((l) => l === sign * i).length; });
      rows.push({ label: (sign > 0 ? 'y' : 'z') + i, role: sign > 0 ? 'true' : 'false', var: i, digits: d, value: num(d) });
    }
    for (let j = 0; j < m; j++) for (const s of ['g', 'h']) { const d = new Array(n + m).fill(0); d[n + j] = 1; rows.push({ label: s + (j + 1), role: 'slack', clause: j, digits: d, value: num(d) }); }
    const targetDigits = [...new Array(n).fill(1), ...new Array(m).fill(3)];
    const target = num(targetDigits), nums = rows.map((r) => r.value);
    const columns = [...Array.from({ length: n }, (_, i) => lt(f, i + 1)), ...f.clauses.map((_, j) => 'c' + (j + 1))];
    const forward = (a) => {
      const pick = [];
      rows.forEach((r, idx) => { if (r.role === 'true' && a[r.var]) pick.push(idx); if (r.role === 'false' && !a[r.var]) pick.push(idx); });
      f.clauses.forEach((c, j) => {
        const sat = c.filter((l) => isTrue(a, l)).length;
        const slack = rows.map((r, idx) => (r.role === 'slack' && r.clause === j ? idx : -1)).filter((x) => x >= 0);
        pick.push(...slack.slice(0, 3 - sat));
      });
      return pick.sort((x, y) => x - y);
    };
    const backward = (idx) => { const a = new Array(n + 1).fill(false); for (const i of idx) if (rows[i].role === 'true') a[rows[i].var] = true; return a; };
    const trace = [
      { kind: 'columns', say: `Write numbers in base 10 with ${n} variable columns and ${m} clause columns; no column can ever sum past 5, so nothing carries.` },
      { kind: 'variables', say: 'For each variable, the target\'s 1 in its column forces exactly one of y (true) and z (false).' },
      { kind: 'clauses', say: 'In a clause column the chosen literal rows give the number of true literals; the two slack numbers can add at most 2, so the target 3 needs at least one true literal.' },
      { kind: 'target', say: `Target ${target}.`, target },
    ];
    return { name: '3SAT → SUBSET SUM', nums, target, table: { columns, rows, targetDigits }, forward, backward, trace };
  }

  // ---------- 3SAT -> 3-COLOUR ----------
  // A palette triangle T, F, B. Each variable: x and ¬x joined to each other and to B, so one is T and one F.
  // Each clause (a ∨ b ∨ c): OR gadgets o1 = a ∨ b and o2 = o1 ∨ c (each: inputs x, y; vertices u, v, o with
  // x–u, y–v, u–v, u–o, v–o; o can be T only if an input is T), and o2 is joined to F and B, forcing it to T.
  function sat3To3Colour(f) {
    checkSize(f);
    const nodes = [], edges = [];
    const node = (label, role, group) => { nodes.push({ id: nodes.length, label, role, group }); return nodes.length - 1; };
    const edge = (a, b, role) => edges.push({ a, b, role });
    const Tn = node('T', 'palette', 'palette'), Fn = node('F', 'palette', 'palette'), Bn = node('B', 'palette', 'palette');
    edge(Tn, Fn, 'palette'); edge(Fn, Bn, 'palette'); edge(Bn, Tn, 'palette');
    const pos = [], neg = [];
    for (let v = 1; v <= f.n; v++) {
      pos[v] = node(lt(f, v), 'literal', 'x' + v); neg[v] = node(lt(f, -v), 'literal', 'x' + v);
      edge(pos[v], neg[v], 'variable'); edge(pos[v], Bn, 'variable'); edge(neg[v], Bn, 'variable');
    }
    const litNode = (l) => (l > 0 ? pos[l] : neg[-l]);
    const gadgets = [];
    const or = (x, y, g) => { const u = node('u', 'gadget', g), v = node('v', 'gadget', g), o = node('o', 'gadget-out', g); edge(x, u, 'gadget'); edge(y, v, 'gadget'); edge(u, v, 'gadget'); edge(u, o, 'gadget'); edge(v, o, 'gadget'); return [u, v, o]; };
    f.clauses.forEach((c, j) => {
      const g = 'clause ' + (j + 1), lits = c.length === 3 ? c : c.length === 2 ? [c[0], c[1], c[1]] : [c[0], c[0], c[0]];
      const [u1, v1, o1] = or(litNode(lits[0]), litNode(lits[1]), g), [u2, v2, o2] = or(o1, litNode(lits[2]), g);
      edge(o2, Fn, 'force'); edge(o2, Bn, 'force');
      gadgets.push([u1, v1, o1, u2, v2, o2]);
    });
    const G = { n: nodes.length, edges: edges.map((e) => [e.a, e.b]) };
    const adj = T.cx.adjacency(G);
    // forward: colour palette and literals from the assignment, then each gadget by a small search
    const forward = (a) => {
      const col = new Array(G.n).fill(-1);
      col[Tn] = 0; col[Fn] = 1; col[Bn] = 2;
      for (let v = 1; v <= f.n; v++) { col[pos[v]] = a[v] ? 0 : 1; col[neg[v]] = a[v] ? 1 : 0; }
      for (const gnodes of gadgets) {
        const go = (i) => {
          if (i === gnodes.length) return true;
          for (let c = 0; c < 3; c++) { if ([...adj[gnodes[i]]].some((u) => col[u] === c)) continue; col[gnodes[i]] = c; if (go(i + 1)) return true; }
          col[gnodes[i]] = -1; return false;
        };
        if (!go(0)) return null;
      }
      return col;
    };
    const backward = (col) => { const a = new Array(f.n + 1).fill(false); for (let v = 1; v <= f.n; v++) a[v] = col[pos[v]] === col[Tn]; return a; };
    const trace = [
      { kind: 'palette', say: 'A triangle T, F, B fixes the meaning of the three colours.' },
      { kind: 'variables', say: 'Each literal pair is joined to B and to each other: one literal gets T, the other F.' },
      { kind: 'clauses', say: 'Each clause gets two OR gadgets in a row; the last output is joined to F and B, so it must be T, which is possible only if some literal of the clause is T.' },
    ];
    return { name: '3SAT → 3-COLOUR', graph: G, k: 3, draw: { nodes, edges }, forward, backward, trace };
  }

  // ---------- SAT -> 3SAT ----------
  function satTo3Sat(f) { const r = T.sat.to3Sat(f); return { name: 'SAT → 3SAT', formula: r.formula, roles: r.roles, forward: r.forward, backward: r.backward, trace: r.trace }; }

  T.red = { occurrences, sat3ToClique, sat3ToIS, isToVC, vcToIS, isToClique, cliqueToIS, sat3ToVC, sat3ToHamPath, sat3ToSubsetSum, sat3To3Colour, satTo3Sat };
})();
