# Lean compiler (`mjs/lean/compiler/`)

## compile → render2vue

- **`compile(source)`** tokenizes with `/\w+|\W/u` and builds an AST (`LeanModule`, `Lean_lemma`, tactics, `toLatex`).
- **`render2vue(false)`** on the root: walks the AST and produces the **JSON** the Vue app expects (`imply.latex`, `proof.by[].latex`, …).

## What exists in this repo (Node)

| Piece | Status |
|--------|--------|
| **`tokenize.mjs`** | Tokenizer regex `/\w+|\W/u`. |
| **`render2vue.mjs`** | Walks the JS AST (`js/parser/lean.js`) into the Vue payload. |
| **`index.mjs` → `render2vueFromSource`** | Always JS AST + `render2vue.mjs`. Falls back to regex stub when parse fails. |

## Long-term

The JS parser (`lean.js`) and `render2vue.mjs` can grow to cover more tactics and `toLatex` cases.
