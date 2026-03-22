# Lean compiler (`server/lean/compiler/`)

## What “compile → render2vue” is in PHP

- **`compile($source)`** (`php/parser/lean.php`): tokenizes with `/\w+|\W/u`, builds a full **AST** (`LeanModule`, `Lean_lemma`, tactics, `toLatex`, …). ~9k lines of parser + AST + LaTeX.
- **`render2vue(false)`** on the root: walks the AST and produces the **JSON** the Vue app expects (`imply.latex`, `proof.by[].latex`, …).

## What exists in this repo (Node)

| Piece | Status |
|--------|--------|
| **`tokenize.mjs`** | Same tokenizer regex as PHP `LeanParser::build`. |
| **`render2vue.mjs`** | Port of `LeanModule::render2vue` / `merge_proof` on the JS AST (`static/js/parser/lean.js`). Output matches the PHP **shape**; full parity depends on `compile()` / `toLatex` matching PHP. |
| **`index.mjs` → `render2vueFromSource`** | Always JS AST + `render2vue.mjs`. Falls back to regex stub when parse fails. |

## Long-term

The JS parser (`lean.js`) and `render2vue.mjs` can grow toward full parity with `lean.php` (tactics, `toLatex` special cases, …).
