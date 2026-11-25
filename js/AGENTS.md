# js

- Owns the browser scripts in this folder. Lean sources and the Node server stay with [Lemma](../Lemma/AGENTS.md) and [mjs](../mjs/AGENTS.md).
- CodeMirror 6 is bundled the same way as the Vue pages. `npm run build:vue` (`vite build`, `vite.config.js`) has two entries: `js/vuePages.js` and `js/codemirrorBoot.js`.
- `js/codemirrorBoot.js` imports `@codemirror/*`, `@lezer/highlight`, `js/codemirror.js`, and `js/codemirror-lean.js`. Vite writes that graph to `dist/vue/codemirror.js`, with shared pieces in `dist/vue/chunks/*.js`. Lemma, mathlib, and new-theorem pages load `dist/vue/codemirror.js`.
- `js/vuePages.js` loads each `vue/*.vue` as its own chunk. A page downloads the chunk `createApp` asks for. CodeMirror stays on the editor chunk. See [vue](../vue/AGENTS.md).
- After changing any of those bundled sources, run `npm run build:vue` again. The site serves the files under `dist/vue/`, not the sources.
- Scripts loaded by a page directly (`js/std.js`, `js/py.js`, and the other classic scripts) are not part of that bundle. Edit them in place.
- Everything else is inherited from the parent [`AGENTS.md`](../AGENTS.md).
