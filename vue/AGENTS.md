# vue

- Owns the Vue renderer of this site: the `Markdown*.vue` components that turn a lemma page payload into HTML — markdown nodes, headings, lists, tables, code blocks, and LaTeX (`MarkdownLatex.vue`).
- Scope is rendering only. Never edit Lean sources or the `mjs/` parser/payload to work around a display bug; report the needed AST/payload change to the owning folder instead.
- Formalization pipeline: renders the LaTeX of a lemma whose path was created by the [Lemma](../Lemma/AGENTS.md) agent; the page itself is built and served by the [mjs](../mjs/AGENTS.md) Node.js server.
- Everything else is inherited from the parent [`AGENTS.md`](../AGENTS.md).
