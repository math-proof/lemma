# mjs

- Owns the Node.js toolchain:
  - `app.mjs` — HTTP server rendering `?module=` / `?theorem=` pages: resolve module or theorem path → Lean file → `.echo.lean` → Vue payload via `mjs/lean/compiler` → `ejs/lemma.ejs`; run with `npm start`.
  - `lean/` — the lean.js parser, `render2vue`, and the lint rules behind `run.mjs` style warnings.
  - CLI tools — `run.mjs` (compile + style warnings), `lemmaPath.mjs`, `regression.mjs`, `lemmaSectionKind.mjs`, `scanLemmaPaths.mjs`.
- Scope: edit only `mjs/`. Never change Lean sources to make the parser or a rendered page look right; fix the pipeline instead.
- Formalization pipeline: deploys the site for a lemma whose path was created by the [Lemma](../Lemma/AGENTS.md) agent, with LaTeX rendered by the [vue](../vue/AGENTS.md) agent.
- Everything else is inherited from the parent [`AGENTS.md`](../AGENTS.md).
