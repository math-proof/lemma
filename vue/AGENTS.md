# vue

- Owns the Vue renderer of this site: the `Markdown*.vue` components that turn a lemma page payload into HTML — markdown nodes, headings, lists, tables, code blocks, and LaTeX (`MarkdownLatex.vue`).
- Scope is rendering only. Never edit Lean sources or the `mjs/` parser/payload to work around a display bug; report the needed AST/payload change to the owning folder instead.
- Formalization pipeline: renders the LaTeX of a lemma whose path was created by the [Lemma](../Lemma/AGENTS.md) agent; the page itself is built and served by the [mjs](../mjs/AGENTS.md) Node.js server.
- The browser does not compile `.vue` files. Vite precompiles them. From the repo root, `npm run build:vue` runs `vite build` (`vite.config.js`): `js/vuePages.js` imports every `vue/*.vue`. The same build bundles CodeMirror; that entry and its rebuild rule are in [js](../js/AGENTS.md).
- That build writes `dist/vue/pages.js`, `dist/vue/codemirror.js`, shared chunks under `dist/vue/chunks/*.js`, and `dist/vue/assets/style.css`. Pages load `dist/vue/pages.js`.
- After any change to a `vue/*.vue` file, run `npm run build:vue` again before the change is done. A source edit that is not rebuilt is invisible on the site.
- Everything else is inherited from the parent [`AGENTS.md`](../AGENTS.md).
