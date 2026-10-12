// Every shareable link opens its page, whether the page is loaded with it or the hash changes after load.
const ROUTES = [
  ['topic=dfa-run', "Tooring.app.player && Tooring.app.player.t.id === 'dfa-run'"],
  ['dfa-run', "Tooring.app.player && Tooring.app.player.t.id === 'dfa-run'"],
  ['topic/tm-run', "Tooring.app.player && Tooring.app.player.t.id === 'tm-run'"],
  ['topic=dfa-run?w=%22bab%22', "Tooring.app.player && Tooring.app.player.input.w === 'bab'"],
  ['lesson=reg-dfa-read', "!!document.getElementById('lessonView')"],
  ['reg-dfa-read', "!!document.getElementById('lessonView')"],
  ['exercise=parse-ex-first-2', "!!document.getElementById('exerciseView')"],
  ['learn', "!!document.getElementById('learnView')"],
  ['courses', "!!document.getElementById('coursesView')"],
  ['course=tur-course', "!!document.getElementById('courseView')"],
  ['course=tur-course/1', "!!document.getElementById('courseStrip') && !!document.getElementById('lessonView')"],
  ['compare', "!!document.getElementById('compareChooser')"],
  ['compare=tm-run,tm-run', "!!document.getElementById('compareView')"],
  ['sandbox', "!!document.getElementById('sandbox')"],
  ['kits', "!!document.querySelector('.kit-grid')"],
  ['part=turing', "!!document.getElementById('part-turing')"],
];
export default (t) => {
  for (const [hash, ok] of ROUTES) {
    t.test('loading #' + hash + ' opens its page', async (p) => {
      await p.fresh({ hash });
      await p.wait(ok, 10000);
    });
  }
  t.test('changing the hash after load opens each page', async (p) => {
    await p.fresh();
    for (const [hash, ok] of ROUTES) {
      await p.ev('location.hash = ' + JSON.stringify('#' + hash));
      await p.wait(ok, 10000);
      await p.ev("location.hash = '#'");
      await p.wait("!!document.getElementById('heroArt')", 5000);
    }
  });
  t.test('a share link carries the input and reopens it', async (p) => {
    await p.fresh({ hash: 'topic=dfa-run' });
    await p.wait('!!Tooring.app.player');
    const url = await p.ev(`(() => { Tooring.app.player.input = Object.assign({}, Tooring.app.player.input, { w: 'abba' }); const q = Object.entries(Tooring.app.player.input).map(([k, v]) => k + '=' + encodeURIComponent(JSON.stringify(v))).join('&'); return 'topic=dfa-run?' + q; })()`);
    await p.fresh({ hash: url });
    await p.wait("Tooring.app.player && Tooring.app.player.input.w === 'abba'", 10000);
  });
  t.test('an unknown link says so on the home page', async (p) => {
    await p.fresh({ hash: 'no-such-page' });
    await p.wait("!!document.querySelector('.notice')", 5000);
  });
};
