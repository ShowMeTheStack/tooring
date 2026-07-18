// The Tooring app: the top bar, the catalogue (parts, families and topics), the home page, routing between
// the home page, topics, lessons and exercises, courses, Compare, the sandbox and the kit gallery,
// settings, About, and keyboard shortcuts.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h, icon } = T.UI;
  const store = T.UI.storage;
  const TITLE = 'Tooring: theory of computation you can play with';

  class App {
    constructor() {
      T.app = this;
      this.settings = Object.assign({ theme: 'auto', projector: false, speed: 2, predict: true }, store.get('settings', {}));
      this.done = new Set(store.get('done', []));
      this.applyTheme();
      try { matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { if (this.settings.theme === 'auto') this.applyTheme(); }); } catch (e) { /* old browsers */ }
      this.buildTop();
      window.addEventListener('hashchange', () => this.route());
      document.addEventListener('keydown', (e) => this.onKey(e));
      document.addEventListener('visibilitychange', () => { if (!document.hidden && this.hero) this.hero.resume(); });
      this.route();
      window.__tooringReady = true;
    }
    saveSettings() { store.set('settings', this.settings); }
    applyTheme() {
      let t = this.settings.theme;
      if (t === 'auto') { try { t = matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light'; } catch (e) { t = 'light'; } }
      document.documentElement.dataset.theme = t;
      document.documentElement.dataset.projector = this.settings.projector ? 'on' : 'off';
      const meta = document.querySelector('meta[name="theme-color"]');
      if (meta) meta.setAttribute('content', t === 'dark' ? '#161a2d' : '#ffffff');
      if (this.btnTheme) { this.btnTheme.innerHTML = ''; this.btnTheme.appendChild(icon(t === 'dark' ? 'sun' : 'moon')); }
      if (this.btnProj) { this.btnProj.classList.toggle('on', !!this.settings.projector); this.btnProj.setAttribute('aria-pressed', String(!!this.settings.projector)); }
    }
    /** The player keys act on: a topic's, or the one a page (Compare, a kit, a lesson) offers */
    get activePlayer() { return this.player || (this.page && this.page.player) || null; }

    // ---- the frame of the page -------------------------------------------------------------------------
    buildTop() {
      const menu = document.getElementById('btnMenu');
      menu.appendChild(icon('menu'));
      menu.setAttribute('aria-expanded', 'false');
      menu.addEventListener('click', () => { const on = document.getElementById('app').classList.toggle('menu-open'); menu.setAttribute('aria-expanded', String(on)); });
      document.getElementById('brand').addEventListener('click', (e) => { e.preventDefault(); location.hash = ''; });
      const nav = document.getElementById('topNav');
      for (const [id, label, ic] of [['', 'Topics', 'library'], ['learn', 'Learn', 'learn'], ['courses', 'Courses', 'route'], ['sandbox', 'Sandbox', 'sandbox']]) {
        const b = h('button', { type: 'button', dataset: { route: id }, title: label }, icon(ic), h('span', label));
        b.addEventListener('click', () => { location.hash = id; });
        nav.appendChild(b);
      }
      const tools = document.getElementById('topTools');
      this.btnProj = h('button.icon-btn', { type: 'button', title: 'Projector mode: large type and strong lines for a classroom (Shift+P)', 'aria-label': 'Projector mode', id: 'btnProjector' }, icon('screen'));
      this.btnProj.addEventListener('click', () => this.setProjector(!this.settings.projector));
      this.btnTheme = h('button.icon-btn', { type: 'button', title: 'Light or dark (T)', 'aria-label': 'Light or dark', id: 'btnTheme' });
      this.btnTheme.addEventListener('click', () => this.toggleTheme());
      const about = h('button.icon-btn', { type: 'button', title: 'Help, settings and About', 'aria-label': 'Help and About', id: 'btnAbout' }, icon('help'));
      about.addEventListener('click', () => this.aboutMenu(about));
      tools.append(this.btnProj, this.btnTheme, about);
      this.applyTheme();
    }
    toggleTheme() { this.settings.theme = document.documentElement.dataset.theme === 'dark' ? 'light' : 'dark'; this.saveSettings(); this.applyTheme(); }
    setProjector(on) { this.settings.projector = on; this.saveSettings(); this.applyTheme(); const p = this.activePlayer; if (p && p.redraw) p.redraw(); if (this.player && this.player.tabBody) T.UI.fitTables(this.player.tabBody); }
    setPredict(on) { this.settings.predict = on; this.saveSettings(); T.UI.toast(on ? 'Predictions on: the player stops to ask what comes next.' : 'Predictions off: the player runs straight through.', 'ok', 2500); }
    aboutMenu(anchor) {
      const r = anchor.getBoundingClientRect();
      T.UI.showMenu([
        { label: 'Keyboard shortcuts', sc: '?', action: () => this.shortcuts() },
        { label: 'Settings…', action: () => this.settingsDialog() },
        T.Content && T.Content.tours.size ? { label: 'Guided tours', action: () => { location.hash = 'learn'; } } : null,
        { label: 'Compare two runs', action: () => { location.hash = 'compare'; } },
        { label: 'Drawing kits', action: () => { location.hash = 'kits'; } },
        { sep: true },
        { label: 'About Tooring', action: () => this.about() },
        { label: 'About the author', action: () => T.authorDialog && T.authorDialog() },
      ], r.right - 220, r.bottom + 4, { anchor, keyboard: true });
    }

    route() {
      let hash = '';
      try { hash = decodeURIComponent(location.hash.replace(/^#\/?/, '')); } catch (e) { hash = location.hash.replace(/^#\/?/, ''); }
      hash = this.canonical(hash);
      const appEl = document.getElementById('app');
      appEl.classList.remove('menu-open');
      if (this.player) { this.player.dispose(); this.player = null; }
      if (this.page && this.page.dispose) this.page.dispose();
      this.page = null;
      if (this.hero) { this.hero.stop(); this.hero = null; }
      if (T.Tour && T.Tour.onRoute) T.Tour.onRoute(hash);
      const sect = /^(sandbox|learn|lesson=|exercise=|courses|course=)/.exec(hash);
      const navOf = !sect ? (hash.startsWith('kits') || hash.startsWith('compare') ? null : '') : sect[1] === 'sandbox' ? 'sandbox' : /^(courses|course=)/.test(sect[1]) ? 'courses' : 'learn';
      for (const b of document.querySelectorAll('#topNav button')) { const on = b.dataset.route === navOf; b.classList.toggle('on', on); if (on) b.setAttribute('aria-current', 'page'); else b.removeAttribute('aria-current'); }
      appEl.classList.toggle('no-side', /^(sandbox|kits|compare|learn|lesson=|exercise=|courses)/.test(hash) || /^course=[^/]*$/.test(hash));
      const main = document.getElementById('main');
      main.innerHTML = '';
      main.scrollTop = 0;
      document.title = TITLE;
      if (hash.startsWith('topic=')) {
        const [id, q] = hash.slice(6).split('?');
        const t = T.byId(id);
        if (t) { this.openTopic(t, q); return; }
        this.renderHome(main, null, 'There is no topic called "' + id + '". It may have been renamed: pick one from the catalogue.');
        this.renderSide();
        return;
      }
      if (hash.startsWith('sandbox') && T.Sandbox) { this.page = T.Sandbox.open(this, main, hash.slice(7)); document.title = 'Sandbox · Tooring'; this.renderSide(); return; }
      if (hash.startsWith('kits') && T.KitLab) { this.page = T.KitLab.open(this, main, hash.slice(5)); document.title = 'Drawing kits · Tooring'; return; }
      if (hash.startsWith('compare') && T.Compare) { this.page = T.Compare.open(this, main, hash.slice(8)); this.renderSide(); return; }
      if (/^(courses|course=)/.test(hash) && T.Courses) { this.page = T.Courses.open(this, main, hash.startsWith('course=') ? hash.slice(7) : ''); this.renderSide(this.player ? this.player.t : null); return; }
      if (/^(learn|lesson=|exercise=|tour=)/.test(hash) && T.Learn) { this.page = T.Learn.open(this, main, hash); this.renderSide(); return; }
      const part = hash.startsWith('part=') ? hash.slice(5) : null;
      this.renderHome(main, part, hash && !part ? 'There is no page called "' + hash + '". It may have been renamed: start from the catalogue.' : null);
      this.renderSide();
    }

    /**
     * Every way a link may name a page, in one form: a bare topic, lesson, exercise or course id
     * (#dfa-run), topic/dfa-run, and the usual topic=dfa-run?w="ab"
     */
    canonical(hash) {
      const m = /^(topic|lesson|exercise|course|compare|sandbox|kits|part|tour)\/(.*)$/.exec(hash);
      if (m) hash = m[1] + '=' + m[2];
      if (!hash || hash.includes('=') || /^(learn|courses|compare|sandbox|kits)$/.test(hash)) return hash;
      const [id, q] = hash.split('?');
      const C = T.Content;
      if (T.byId(id)) return 'topic=' + id + (q ? '?' + q : '');
      if (C && C.lessons.has(id)) return 'lesson=' + id;
      if (C && C.exercises.has(id)) return 'exercise=' + id;
      if (C && C.courses.has(id)) return 'course=' + id;
      if (T.partOf(id)) return 'part=' + id;
      return hash;
    }

    // ---- the catalogue -----------------------------------------------------------------------------------
    renderSide(current) {
      const side = document.getElementById('side');
      let search = side.querySelector('.cat-search');
      if (!search) {
        search = h('input.cat-search', { type: 'search', placeholder: 'Find a topic  ( / )', 'aria-label': 'Find a topic', id: 'catSearch' });
        search.addEventListener('input', T.UI.debounce(() => this.renderSide(this.sideCurrent), 80));
        search.addEventListener('keydown', (e) => { if (e.key === 'Escape') { search.value = ''; this.renderSide(this.sideCurrent); search.blur(); } if (e.key === 'Enter') { const b = side.querySelector('.cat-topic'); if (b) b.click(); } });
      }
      this.sideCurrent = current;
      const query = search.value.trim().toLowerCase();
      // the catalogue only changes with the search, the topics done and the topic open: rebuild just then
      const sig = query + '|' + T.topics.length + '|' + this.done.size;
      if (this.sideSig === sig && side.querySelector('.cat-fam, .empty-state')) {
        for (const b of side.querySelectorAll('.cat-topic')) { const on = !!current && b.dataset.topic === current.id; b.classList.toggle('on', on); if (on) b.setAttribute('aria-current', 'page'); else b.removeAttribute('aria-current'); }
        if (current) { const fam = side.querySelector('.cat-fam[data-fam="' + current.family + '"]'); if (fam && !fam.classList.contains('open')) { fam.classList.add('open'); fam.firstChild.setAttribute('aria-expanded', 'true'); } }
        return;
      }
      this.sideSig = sig;
      for (const c of [...side.children]) if (c !== search) c.remove();
      if (!search.parentNode) side.appendChild(search);
      const open = new Set(store.get('openFams', []));
      if (current) open.add(current.family);
      let any = false;
      const frag = document.createDocumentFragment();
      for (const part of T.parts) {
        const blocks = [];
        for (const f of T.families.filter((x) => x.part === part.id)) {
          const ts = T.topics.filter((t) => t.family === f.id && (!query || (t.title + ' ' + f.title + ' ' + (t.blurb || '')).toLowerCase().includes(query)));
          if (!ts.length) continue;
          const isOpen = open.has(f.id) || !!query;
          const fam = h('div.cat-fam' + (isOpen ? '.open' : ''), { dataset: { fam: f.id } });
          const head = h('button', { type: 'button', 'aria-expanded': String(isOpen) }, h('span', f.title), h('span.n', String(ts.length)));
          head.addEventListener('click', () => {
            if (open.has(f.id)) open.delete(f.id); else open.add(f.id);
            store.set('openFams', [...open]);
            fam.classList.toggle('open');
            head.setAttribute('aria-expanded', String(fam.classList.contains('open')));
          });
          const list = h('div.cat-topics');
          for (const t of ts) {
            const b = h('button.cat-topic' + (current === t ? '.on' : ''), { type: 'button', dataset: { topic: t.id }, 'aria-current': current === t ? 'page' : null }, t.title, this.done.has(t.id) ? h('span.done', { title: 'Seen to the end' }, ' ✓') : null);
            b.addEventListener('click', () => { location.hash = 'topic=' + t.id; });
            list.appendChild(b);
          }
          fam.append(head, list);
          blocks.push(fam);
        }
        if (!blocks.length) continue;
        any = true;
        frag.appendChild(h('div.cat-group', h('b', String(part.n)), part.title));
        for (const b of blocks) frag.appendChild(b);
      }
      side.appendChild(frag);
      if (!any) {
        side.appendChild(query ? T.UI.empty('search', 'Nothing matches "' + query + '"', 'Try a shorter word, or a family name like DFA, grammar or Turing.', [{ label: 'Clear the search', icon: 'x', action: () => { search.value = ''; this.renderSide(this.sideCurrent); search.focus(); } }])
          : T.UI.empty('library', 'No topics yet', 'The topics are being written.'));
      }
    }

    renderHome(main, focusPart, notice) {
      const box = h('div.home');
      if (notice) box.appendChild(h('div.notice', icon('info'), h('span', notice)));
      const art = h('div.hero-art', { id: 'heroArt' });
      const start = h('button.btn.primary', { type: 'button', id: 'btnStart' }, icon('run'), 'Start with the first topic');
      start.addEventListener('click', () => { const t = T.topics[0]; if (t) location.hash = 'topic=' + t.id; });
      start.disabled = !T.topics.length;
      const sb = h('button.btn', { type: 'button', id: 'btnToSandbox' }, icon('sandbox'), 'Build a machine');
      sb.addEventListener('click', () => { location.hash = 'sandbox'; });
      const n = T.topics.length;
      box.appendChild(h('section.hero',
        h('div.hero-text', h('h1', 'Theory of computation you can play with.'),
          h('p.lead', 'Automata run and light their states, grammars grow parse trees, Turing machines walk their tapes and every construction happens in front of you, step by step. Pause to predict what comes next, or build your own machine and test it.'),
          h('div.cta', start, sb),
          n ? h('p.hero-stats', h('b', String(n)), ' topics in ', h('b', String(T.families.filter((f) => T.topics.some((t) => t.family === f.id)).length)), ' families, all drawn and narrated.') : null),
        h('div.hero-show', art, h('div.hero-cap', { id: 'heroCap', 'aria-live': 'off' }), h('div.hero-dots', { id: 'heroDots', role: 'tablist', 'aria-label': 'Examples' }))));
      // the other ways in
      const C = T.Content;
      const tool = (id, ic, title, text, hash) => { const b = h('button.tool-card', { type: 'button', id }, h('span.tc-icon', icon(ic)), h('span.tc-text', h('b', title), h('span', text))); b.addEventListener('click', () => { location.hash = hash; }); return b; };
      const nl = C ? C.lessons.size : 0, nx = C ? C.exercises.size : 0, nc = C ? C.courses.size : 0;
      box.appendChild(h('section.home-tools',
        tool('toLearn', 'learn', 'Learn', nl || nx ? nl + ' lessons and ' + nx + ' exercises, checked as you go.' : 'Lessons and exercises, checked as you go.', 'learn'),
        tool('toCourses', 'route', 'Courses', nc ? nc + ' guided paths through the topics.' : 'Guided paths through the topics.', 'courses'),
        tool('toCompare', 'compare', 'Compare', 'Two runs side by side, stepping together.', 'compare'),
        tool('toSandbox', 'sandbox', 'Sandbox', 'Draw a machine or write a grammar, then run it.', 'sandbox')));
      for (const part of T.parts) {
        const fams = T.families.filter((f) => f.part === part.id && T.topics.some((t) => t.family === f.id));
        const sec = h('section.part', { id: 'part-' + part.id, dataset: { part: part.id } });
        sec.appendChild(h('div.part-head', h('span.num', String(part.n)), h('h2', part.title)));
        sec.appendChild(h('p.part-blurb', part.blurb));
        if (fams.length) {
          const grid = h('div.fam-grid');
          for (const f of fams) {
            const ts = T.topics.filter((t) => t.family === f.id);
            const done = ts.filter((t) => this.done.has(t.id)).length;
            const card = h('button.fam-card', { type: 'button', dataset: { fam: f.id } },
              (() => { const a = h('div.fc-art', T.Previews ? T.Previews.svg(T.Previews.kindFor(f)) : null); if (T.Previews) T.Previews.live(a, f); return a; })(),
              h('div.fc-body', h('h3', f.title), h('p', f.blurb || ''),
                h('span.n', ts.length + ' topic' + (ts.length === 1 ? '' : 's') + (done ? ' · ' + done + ' done' : '')),
                done ? h('span.fc-bar', h('i', { style: { width: Math.round((100 * done) / ts.length) + '%' } })) : null));
            card.addEventListener('click', () => { const next = ts.find((t) => !this.done.has(t.id)) || ts[0]; location.hash = 'topic=' + next.id; });
            grid.appendChild(card);
          }
          sec.appendChild(grid);
        } else sec.appendChild(h('div.part-soon', icon('edit'), h('span', 'The topics of this part are being written. ', h('a', { href: '#sandbox' }, 'The sandbox'), ' already runs any machine or grammar you give it.')));
        box.appendChild(sec);
      }
      main.appendChild(box);
      // the picture starts once the page is on screen, so the first paint is not held up
      requestAnimationFrame(() => { if (art.isConnected) this.hero = this.heroDemo(art); });
      if (focusPart) requestAnimationFrame(() => { const el = document.getElementById('part-' + focusPart); if (el) el.scrollIntoView({ block: 'start' }); });
    }

    /**
     * The picture on the home page: five little machines, each running on a string with its narration
     * under it, one after the other (a DFA, an NFA with its cloud of states, a PDA and its stack, a Turing
     * machine on its tape, a grammar growing a tree). The dots under it jump to one.
     */
    heroDemo(el) {
      const INC = 'start: right\naccept: done\nright, 0 -> right, 0, R\nright, 1 -> right, 1, R\nright, _ -> carry, _, L\ncarry, 1 -> carry, 0, L\ncarry, 0 -> done, 1, S\ncarry, _ -> done, 1, S';
      const defs = [
        { name: 'A DFA', what: 'binary multiples of 3', src: { kind: 'dfa', text: 'start r0\naccept r0\nr0 -0-> r0\nr0 -1-> r1\nr1 -0-> r2\nr1 -1-> r0\nr2 -0-> r1\nr2 -1-> r2' }, w: '1001' },
        { name: 'An NFA', what: 'ends in ba', src: { kind: 'nfa', text: 'start p\naccept r\np -a,b-> p\np -b-> q\nq -a-> r' }, w: 'abba' },
        { name: 'A PDA', what: 'aⁿbⁿ', src: { kind: 'pda', text: 'start p\nstack-start Z\naccept f\np, a, Z -> p, A Z\np, a, A -> p, A A\np, b, A -> d, ε\nd, b, A -> d, ε\nd, ε, Z -> f, Z' }, w: 'aabb' },
        { name: 'A Turing machine', what: 'adds one in binary', src: { kind: 'tm', text: INC }, w: '1011' },
        { name: 'A grammar', what: 'balanced brackets', src: { kind: 'grammar', text: 'S → ( S ) S | ε' }, w: '(())' },
      ];
      const scenes = [];
      for (const d of defs) {
        let frames = [];
        try { frames = T.Sim.frames(d.src, d.w).filter((f) => f.items && f.items.length); } catch (e) { frames = []; }
        if (!frames.length) continue;
        const view = T.geom.union(frames.map((f) => T.stageBounds(f.items, { margin: 30, minW: 360, minH: 220 })));
        scenes.push(Object.assign({}, d, { frames: frames.map((f) => Object.assign({}, f, { view })) }));
      }
      const st = new T.Stage(el, { label: 'Machines running on strings' });
      const cap = document.getElementById('heroCap'), dots = document.getElementById('heroDots');
      const still = T.UI.reducedMotion();
      let s = 0, k = 0, timer = null, stopped = false;
      const btns = scenes.map((sc, i) => { const b = h('button.hero-dot', { type: 'button', role: 'tab', 'aria-label': sc.name + ': ' + sc.what, title: sc.name + ': ' + sc.what }, sc.name.replace(/^An? (.)/, (m, c) => c.toUpperCase())); b.addEventListener('click', () => { show(i, 0, true); if (!still) schedule(); }); dots.appendChild(b); return b; });
      const show = (si, fi, instant) => {
        const newScene = si !== s || instant;
        s = si; k = fi;
        const sc = scenes[s];
        if (!sc) return;
        if (newScene) st.clear();
        st.show(sc.frames[k], { duration: newScene || still ? 0 : 650 });
        btns.forEach((b, i) => { b.classList.toggle('on', i === s); b.setAttribute('aria-selected', String(i === s)); });
        if (cap) { cap.innerHTML = ''; cap.append(h('b', sc.name), ' ' + sc.what + ', on ' + sc.w + '. ', h('span', sc.frames[k].say || '')); }
      };
      const schedule = () => {
        clearTimeout(timer);
        if (stopped || still) return;
        const sc = scenes[s];
        const last = k >= sc.frames.length - 1;
        timer = setTimeout(() => {
          if (stopped || !el.isConnected) return;
          if (document.hidden) { timer = null; return; }
          if (last) {
            // a short fade between machines
            el.classList.add('fading');
            setTimeout(() => { if (stopped) return; show((s + 1) % scenes.length, 0, true); el.classList.remove('fading'); schedule(); }, 280);
          } else { show(s, k + 1); schedule(); }
        }, last ? 2400 : 1150);
      };
      if (scenes.length) { show(0, still ? scenes[0].frames.length - 1 : 0, true); schedule(); }
      return {
        scenes, show: (si, fi) => { clearTimeout(timer); stopped = true; show(si, fi, true); },
        stop() { stopped = true; clearTimeout(timer); },
        resume() { if (!stopped && !timer) schedule(); },
      };
    }

    // ---- a topic -------------------------------------------------------------------------------------------
    openTopic(t, query) {
      this.renderSide(t);
      const main = document.getElementById('main');
      const given = {};
      if (query) for (const part of query.split('&')) { const i = part.indexOf('='); if (i < 0) continue; try { given[part.slice(0, i)] = JSON.parse(decodeURIComponent(part.slice(i + 1))); } catch (e) { /* ignore */ } }
      const saved = store.get('in:' + t.id, null);
      let input = T.inputOf(t, Object.keys(given).length ? given : saved);
      if (T.checkInput(t, input)) input = T.inputOf(t);
      this.player = new T.Player(this, main, { topic: t, input });
      const f = T.familyOf(t);
      document.title = t.title + (f ? ' · ' + f.title : '') + ' · Tooring';
      return this.player;
    }
    markDone(t) { if (this.done.has(t.id)) return; this.done.add(t.id); store.set('done', [...this.done]); this.renderSide(t); }

    // ---- keyboard -----------------------------------------------------------------------------------------
    onKey(e) {
      if (T.UI.anyModalOpen()) return;
      if (e.key === 'Escape') {
        const p = this.player;
        if (p && p.root.classList.contains('drawer-open')) { e.preventDefault(); p.drawer(false); return; }
        if (p && p.stageWrap && p.stageWrap.closest('.fullscreen')) { e.preventDefault(); p.fullscreen(false); return; }
        if (document.getElementById('app').classList.contains('menu-open')) { document.getElementById('app').classList.remove('menu-open'); return; }
      }
      const tag = (e.target && e.target.tagName) || '';
      if (/INPUT|TEXTAREA|SELECT/.test(tag) || (e.target && e.target.isContentEditable)) return;
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      // a focused button or tab handles its own Space and arrows
      const onControl = (tag === 'BUTTON' || tag === 'A' || tag === 'SUMMARY') && (e.key === ' ' || e.key === 'Enter');
      if (onControl) return;
      const k = e.key;
      if (k === '?') { e.preventDefault(); this.shortcuts(); return; }
      if (k === 'P' && e.shiftKey) { e.preventDefault(); this.setProjector(!this.settings.projector); return; }
      if (k === 'p') { e.preventDefault(); this.setPredict(!this.settings.predict); return; }
      if (k === 't' || k === 'T') { e.preventDefault(); this.toggleTheme(); return; }
      if (k === '/') {
        const s = document.getElementById('catSearch');
        if (s && !document.getElementById('app').classList.contains('no-side')) { e.preventDefault(); document.getElementById('app').classList.add('menu-open'); s.focus(); s.select(); }
        return;
      }
      const p = this.activePlayer;
      if (!p) return;
      if (k === ' ' || k === 'k') { e.preventDefault(); p.toggle(); }
      else if (k === 'ArrowRight' || k === 'l') { e.preventDefault(); p.step(1); }
      else if (k === 'ArrowLeft' || k === 'j') { e.preventDefault(); p.step(-1); }
      else if (k === 'Home') { e.preventDefault(); p.pause(); p.go(0); }
      else if (k === 'End') { e.preventDefault(); p.pause(); p.go(p.frames.length - 1); }
      else if (k === 'r' || k === 'R') { e.preventDefault(); p.pause(); p.go(0, true); p.play(); }
      else if (k === 'F' && e.shiftKey && p.fullscreen) { e.preventDefault(); p.fullscreen(); }
      else if (k === 'f' || k === 'F' || k === '0') { e.preventDefault(); p.fit ? p.fit() : p.stage.fit(); }
      else if (k === '+' || k === '=') { e.preventDefault(); if (p.stage) p.stage.setZoom(p.stage.zoom * 1.4, true); }
      else if (k === '-') { e.preventDefault(); if (p.stage) p.stage.setZoom(p.stage.zoom / 1.4, true); }
      else if (k === 'b' || k === 'B') { e.preventDefault(); if (p.bigger) p.bigger(); }
      else if ((k === 'd' || k === 'D') && p.sideCard) { e.preventDefault(); if (getComputedStyle(p.drawerBtn).display !== 'none') p.drawer(); else p.showTab(p.tab === 'def' ? 'steps' : 'def'); }
      else if ((k === 'q' || k === 'Q') && p.quiz && this.player === p) { e.preventDefault(); p.quiz(); }
      else if (k === ']' || k === '[') { e.preventDefault(); const s = Math.max(0, Math.min(T.SPEEDS.length - 1, this.settings.speed + (k === ']' ? 1 : -1))); this.settings.speed = s; this.saveSettings(); if (p.speedEl) p.speedEl.value = String(s); }
    }
    shortcuts() {
      const groups = [
        ['Playing', [['Space', 'Play or pause'], ['→  ←', 'Next step, step back'], ['Home  End', 'First or last step'], ['R', 'Play again from the start'], ['[  ]', 'Slower, faster']]],
        ['Looking', [['F', 'Fit the picture to the stage'], ['Shift  F', 'The stage on the whole screen'], ['+  −', 'Zoom in, out'], ['B', 'A bigger stage'], ['D', 'Definition or steps (on a phone, the drawer)']]],
        ['Learning', [['P', 'Predictions on or off: ' + (this.settings.predict ? 'now on' : 'now off')], ['Q', 'The quiz of this topic']]],
        ['Everywhere', [['/', 'Find a topic'], ['T', 'Light or dark'], ['Shift  P', 'Projector mode'], ['Esc', 'Close a dialog or the drawer'], ['?', 'This list']]],
      ];
      const body = h('div.keys', ...groups.map(([title, rows]) => h('section', h('h4', title), h('table', ...rows.map(([k, v]) => h('tr', h('td', ...k.split('  ').map((x, i) => [i ? ' ' : '', h('kbd', x)])), h('td', v)))))));
      T.UI.modal({ title: 'Keyboard shortcuts', body, wide: true, cls: 'keys-modal', buttons: [{ label: 'OK', value: true, primary: true }], enterValue: true });
    }
    settingsDialog() {
      const s = this.settings;
      const row = (title, sub, ctl) => h('div.settings-row', h('div.what', h('b', title), h('span', sub)), ctl);
      const chk = (key, after) => { const c = h('input', { type: 'checkbox', checked: !!s[key], id: 'set-' + key }); c.addEventListener('change', () => { s[key] = c.checked; this.saveSettings(); this.applyTheme(); if (after) after(); }); return c; };
      const theme = h('select', { id: 'set-theme', 'aria-label': 'Theme' }, ...[['auto', 'Like the system'], ['light', 'Light'], ['dark', 'Dark']].map(([v, l]) => h('option', { value: v, selected: s.theme === v }, l)));
      theme.addEventListener('change', () => { s.theme = theme.value; this.saveSettings(); this.applyTheme(); });
      const speed = h('input', { type: 'range', min: '0', max: String(T.SPEEDS.length - 1), value: String(s.speed), id: 'set-speed', 'aria-label': 'Speed' });
      speed.addEventListener('input', () => { s.speed = +speed.value; this.saveSettings(); const p = this.activePlayer; if (p && p.speedEl) p.speedEl.value = speed.value; });
      T.UI.modal({ title: 'Settings', body: h('div',
        row('Theme', 'Light, dark, or whatever the system uses', theme),
        row('Speed', 'How fast the animations play', speed),
        row('Predictions', 'Stop at key moments and ask me what happens next (P)', chk('predict')),
        row('Projector mode', 'Large type and strong lines for a classroom (Shift+P)', chk('projector', () => this.setProjector(s.projector)))),
      buttons: [{ label: 'Close', value: true, primary: true }] });
    }
    about() {
      const more = h('a', { href: '#' }, 'About the author');
      more.addEventListener('click', (e) => { e.preventDefault(); T.UI.closeAllModals(); setTimeout(() => T.authorDialog && T.authorDialog(), 50); });
      T.UI.modal({
        title: 'About Tooring',
        body: h('div', h('p', h('b', 'Tooring'), ' @@VERSION@@ is the theory of computation you can play with: finite automata, regular expressions, grammars and parsers, pushdown automata, Turing machines, decidability and complexity, each drawn and animated step by step from engines written for it. Every example, machine and grammar in it was made for Tooring.'),
          h('p', 'It runs entirely in your browser from one file: no server, no account, nothing sent anywhere. What you build is kept in this browser and can be shared as a link.'),
          h('p', 'Free software under the GNU General Public License, version 3 or later. Every copy and every derived work must keep this attribution: Based on Tooring by Jyotiprakash Mishra (https://tooring.jyotiprakash.org).'),
          h('p', 'Copyright © 2026 Jyotiprakash Mishra. The name Tooring is not licensed for derived works.'), h('p', more)),
        buttons: [{ label: 'OK', value: true, primary: true }],
      });
    }
  }

  T.App = App;
  if (typeof document !== 'undefined' && document.getElementById && document.getElementById('app')) {
    const start = () => { try { new App(); } catch (e) { document.body.innerHTML = '<pre style="padding:20px;white-space:pre-wrap">Tooring could not start: ' + String(e.stack || e.message).replace(/</g, '&lt;') + '</pre>'; throw e; } };
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
  }
})();
