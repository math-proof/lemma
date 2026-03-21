# Lean compiler (`server/lean/compiler/`)

## What “compile → render2vue / echo2vue” is in PHP

- **`compile($source)`** (`php/parser/lean.php`): tokenizes with `/\w+|\W/u`, builds a full **AST** (`LeanModule`, `Lean_lemma`, tactics, `toLatex`, …). ~9k lines of parser + AST + LaTeX.
- **`render2vue(false)`** on the root: walks the AST and produces the **JSON** the Vue app expects (`imply.latex`, `proof.by[].latex`, …).
- **`echo2vue`**: rewrites `echo` tactics, runs **Lean** on `*.echo.lean`, merges **goal-state JSON** into tactics (not the same as `render2vue` alone).

## What exists in this repo (Node)

| Piece | Status |
|--------|--------|
| **`tokenize.mjs`** | Same tokenizer regex as PHP `LeanParser::build`. |
| **`compilePhp.mjs` + `php-bridge/render2vue.php`** | Runs **real** `compile` → `render2vue(false)` via `php` CLI when available — **identical** output to PHP lemma page for that step. |
| **`render2vue.mjs`** | Port of `LeanModule::render2vue` / `merge_proof` on the JS AST (`static/js/parser/lean.js`). Output matches the PHP **shape**; full parity depends on `compile()` / `toLatex` matching PHP. |
| **`index.mjs` → `render2vueFromSource`** | `LEAN_COMPILER=auto`: PHP if available, else **JS** `render2vue`, else stub. `js`: JS only. `php`: PHP only. `stub`: regex stub. |
| **`echo2vue`** | **`echo2vueFromModule(module)`** in `index.mjs` runs **`php-bridge/echo2vue.php`** (same as `php/request/echo.php`): PHP `compile` → `echo2vue(path)` + lake + lean. Needs PHP, elan/lake, lean on PATH. |

## Environment

| Variable | Meaning |
|----------|---------|
| `LEAN_COMPILER` | `auto` (default): PHP if `php -v` works, else JS `render2vue`, else stub. `js` / `javascript`: JS AST + `render2vue.mjs` only. `php`: PHP bridge only. `stub`: regex stub. |
| `PHP_PATH` / `PHP_BIN` | Path to `php` executable. |

## Long-term

The JS parser (`lean.js`) and `render2vue.mjs` can grow toward full parity with `lean.php` (tactics, `toLatex` special cases, `echo2vue`, …).
