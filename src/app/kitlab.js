// The drawing kits on show: every demo of every kit on the stage, to look at in both themes and at every
// size, and for the diagram checker to measure. #kits shows them all; #kits=3 shows one, large.
(function () {
  'use strict';
  const T = (globalThis.Tooring = globalThis.Tooring || {});
  const { h } = T.UI;
  const KL = (T.KitLab = {});

  /** Every demo: [{kit, name, frames()}] */
  KL.list = function () {
    const out = [];
    for (const [kit, K] of Object.entries(T.Kit || {})) for (const d of K.demos || []) out.push({ kit, name: d.name, frames: d.frames });
    return out;
  };
  const topicOf = (d, i) => ({ id: 'kit-' + i, title: d.name, run: () => d.frames(), inputs: [] });

  KL.open = function (app, main, arg) {
    const list = KL.list();
    const one = arg !== undefined && arg !== '' ? +arg : null;
    const box = h('div.kits');
    const players = [];
    box.appendChild(h('div.t-head', h('div', h('div.crumbs', 'Tooring'), h('h1', 'Drawing kits'), h('p', 'The pieces every topic is drawn with: state diagrams, tapes, stacks, trees, tables, strings, sets, dominoes and gadget graphs. Step through each demo to see how it animates.'))));
    const grid = h('div.kit-grid');
    box.appendChild(grid);
    main.appendChild(box);
    list.forEach((d, i) => {
      if (one !== null && i !== one) return;
      const card = h('div.card.kit-card', { dataset: { demo: String(i) } }, h('h3', d.name));
      grid.appendChild(card);
      players.push(new T.Player(app, card, { topic: topicOf(d, i), embed: true, side: false, idp: 'k' + i + '-' }));
    });
    if (one !== null) grid.style.gridTemplateColumns = '1fr';
    return { players, player: players.length === 1 ? players[0] : null, dispose() { for (const p of players) p.dispose(); } };
  };
  // the route: #kits or #kits=N
  KL.route = (hash) => hash === 'kits' || hash.startsWith('kits=');
})();
