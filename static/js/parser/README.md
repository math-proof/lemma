# Lean Parser (JavaScript)

JavaScript port of the Lean 4 parser from `php/parser/lean.php`. Produces an AST for Lean source code used by the web UI (syntax highlighting, LaTeX export, proof echo).

### Maintainer checklist (translation + AST round-trip)

1. **Follow Steps 1 → 4 in order** (below): [Step 1](#step-1-class-inventory-and-missing-classes) inventory → [Step 2](#step-2-class-declaration-order) class order vs PHP → [Step 3](#step-3-per-class-function-audit) per-class audit → [Step 4](#step-4-output-and-verification) verification. Prefer **one class** (or a tight related set) per change so diffs stay reviewable.
2. **Within each class in `lean.js`:** respect **method declaration order** — **normally alphabetic** by method name, with `constructor` first and `static` field initializers next ([Step 3 §2](#step-3-per-class-function-audit)).
3. **AST → string → AST:** run **`node scripts/test-lean-parser.mjs`** after **every** `lean.js` edit so everything in **`round-trip-corpus.jsonl`** **keeps** passing; improve coverage by fixing **`round-trip-failures.jsonl`** **one row at a time**, then append that lemma to the corpus and rebuild failures ([Running Tests](#running-tests)).

## Files

| File | Description |
|------|-------------|
| `node.js` | Base `Node`, `IndentedNode`, `AbstractParser` |
| `lean.js` | Lean AST classes and `LeanParser` (~7100 lines) |
| `newline.js` | Newline handling utilities |
| `markdown.js` | Markdown parsing |
| `xml.js` | XML parsing |

## PHP → JS Parity

### Source of Truth
- **PHP**: `php/parser/lean.php` (~9500 lines)
- **JS**: `static/js/parser/lean.js` (~7100 lines)

### Class Mapping
JS mirrors several PHP abstract bases for `instanceof` parity (`LeanPairedGroup::is_indented`, `push_left`, …): **`LeanBinaryBoolean`** (PHP `trait LeanProp`: `isProp` → `true`), **`LeanRelational`**, **`LeanArithmetic`**, **`LeanUnaryArithmetic`**, **`LeanUnaryArithmeticPre`**, **`LeanUnaryArithmeticPost`** (concrete nodes extend these where PHP does). **`Lean_lnot`**, **`LeanNot`**, and **`LeanQuantifier`** keep explicit `isProp` like PHP’s `use LeanProp` on those classes. Still flattened or absent as named classes in JS (extend **`LeanBinary`** / **`LeanUnary`** directly): **`LeanLogic`**, **`LeanSetOperator`**
- PHP `Lean_is_not` ↔ JS `Lean_is_not` (identical)
- **PHP** uses `new $ClassName(...)` with no separate registry; **JS** uses **`LEAN_CLASSES`**: a map of **concrete** AST classes only (keys = `constructor.name`). **Abstract/intermediate** bases (`Lean`, `LeanArgs`, `LeanBinary`, `LeanUnary`, `LeanSyntax`, `LeanPairedGroup`, `LeanCommand`, marker classes, etc.) are **not** in the map—they remain normal exports in `lean.js`. **`getLeanClass(name)`** looks up `LEAN_CLASSES` only; unknown names throw (add the concrete class to `LEAN_CLASSES`). Prefix unary (`insert_unary`), postfix (`push_post_unary`), and `push_left` paired delimiters use **`getLeanClass`** like PHP `new $ClassName`.
- PHP `abstract class LeanSyntax extends LeanArgs` holds `insert` and related `__set` behavior; **JS** exports **`LeanSyntax`**. **`LeanTactic`**, **`Lean_let`**, **`Lean_have`**, and **`Lean_show`** extend **`LeanSyntax`** (single-arg nodes use `super([arg], indent, level, parent)`). **`get sequential_tactic_combinator`** is implemented on **`LeanSyntax`** (shared with `LeanTactic` / `Lean_let`). **`LeanAssign::split`** is ported for `Lean_let::split`.
- PHP **`Lean_fun` extends `LeanUnary`** (not `LeanCommand`); **JS** matches: **`Lean_fun extends LeanUnary`** with `command` → `\lambda` for LaTeX, `is_indented`, `jsonSerialize` like PHP. **`LeanCommand`** is used for **`Lean_import` / `Lean_open` / `Lean_set_option` / `Lean_namespace`** (not `Lean_fun`).

### Conventions (PHP → JS)

| PHP | JavaScript |
|-----|------------|
| `__construct` | `constructor` |
| `__get('x')` | getter `get x()` |
| `__set('x', v)` | setter `set x(v)` |
| `__toString` | `toString()` (uses `strFormat` + `strArgs`) |
| `relocate_last_comment` | `relocate_last_comment()` (keep **snake_case** like PHP for parity) |
| `__clone` | instance method **`clone()`** — see [AST cloning for translation](#ast-cloning-for-translation) under Translation Task Steps |
| `$this->args` | `this.args` |
| `parent::method()` | `super.method()` |
| `get_class($this)` | `this.constructor.name` |
| `throw new Exception(...)` | `throw new Error(...)` |

### Known Gaps
- `LeanArgsIndented::strArgs` adds optional line padding when `rhs` is `LeanArgsNewLineSeparated` (not in PHP); keeps AST→string→AST stable on quantifier/calc-indented bodies.
- `LeanArgsSpaceSeparated`, `LeanTacticBlock`, `Lean_let`, `LeanTactic` (and `Lean_have` via `strFormat` only): no `strArgs` override — same as PHP (inherit `Lean::strArgs` → `this.args`); `strFormat` follows PHP.
- `Lean_match` / `LeanWith`: echo and other edge cases may still differ from PHP in corner cases; `LeanBar.split` / `LeanCalc.split` use deep `clone()` like PHP
- Nested proof echo: worth spot-diffing `LeanTacticBlock::echo` / `LeanStatements::echo` against PHP after corpus changes
- Recent parity: **`LeanStack` → `LeanBigOperator`** (PHP ~9251–9286): `operator` / `command` / `stack_priority` 28, `latexArgs` marks class in syntax map, no-op `push_args_indented`, `LeanBracket` builds `new LeanStack(bound, …)` then `stack.scope = caret`; **`Lean_def`**: `operator`, `set attribute` / `set assignment`, `strArgs`, `strFormat` (keyword from `func`), `latexFormat`, `jsonSerialize` (top-level key from `operator` = `'def'` per PHP), `insert_tactic`, `is_indented`, `set_line` (PHP ~8616–8750); **`Lean_lemma::echo`** (`try` + `echo` around last tactic/let, PHP ~8758–8787); **`LeanCommand`** base: `is_indented`, `get command` (= `operator`), `strFormat` / `latexFormat`, **`jsonSerialize`** `{ [func]: arg }` (PHP ~5213–5234); deduped `strFormat` on import/open/set_option; **`Lean::regexp`** → `[]` (PHP ~904–906); **`Lean_fun` → `LeanUnary`** + `command` / `latexFormat` / `jsonSerialize` / `is_indented` (PHP ~9019–9056); **`Lean_import` / `Lean_open` / `Lean_set_option`**: PHP `append` + `push_attr` + explicit `stack_priority` 27 (PHP ~5253–5360); **`Lean_let` / `Lean_have` / `Lean_show` → `LeanSyntax`** (moved below `LeanSyntax` in `lean.js`; `echo`, `get_echo_token`, `insert_newline`, `insert_sequential_tactic_combinator`, `split`, PHP-shaped `jsonSerialize` for let/show), **`LeanAssign::split`**, **`LeanSyntax` `get sequential_tactic_combinator`**, `LeanArgs::traverse` (preorder over `args`, matching PHP; base `Lean::traverse` still yields only `this`), `LeanTacticBlock` (`echo`, `split`, `tactic_block`, `set_line`), `LeanArgsSpaceSeparated` (`tokens_space_separated`, `construct_prefix_tree`, `tactic_block_info`, `operand_count`), `LeanSequentialTacticCombinator`, `LeanTactic` echo/split helpers, `LeanBy::echo`, `LeanBitOr` / `LeanAngleBracket` / `LeanArgsCommaSeparated` token helpers

### Running Tests
```bash
node scripts/test-lean-parser.mjs
```

**AST → string → AST (sanity-check):** Run that command after **every** `lean.js` edit. **`scripts/round-trip-corpus.jsonl`** is the **regression contract** — every listed `Lemma/` must keep passing parse and round-trip (`jsonSerialize` stable). **Do not regress** those successes while fixing failures.

**Failure queue (one by one):** **`scripts/round-trip-failures.jsonl`** lists off-corpus lemmas that fail `parse1`, `parse2`, or `mismatch`. Regenerate: **`node scripts/build-round-trip-failures.mjs`**. Work **one `rel` per change**: `node scripts/test-lean-parser.mjs --round-trip-verbose Lemma/…`, adjust **`lean.js`** under [Translation Task Steps](#translation-task-steps-php--js) — especially **within-class method declaration order** in **`lean.js`** (**normally alphabetic**, Step 3 §2) and PHP parity — then **full** `test-lean-parser` again, append `{"rel":…,"note":…}` to **`round-trip-corpus.jsonl`**, and rebuild failures. **`sample-round-trip-corpus.mjs`** is optional; it only adds rows when round-tripping files still exist off-list.

**Step-by-step workflow:** (1) **Step 1** — class inventory / missing nodes (`scripts/audit-lean-classes.mjs`). (2) **Step 2** — class declaration order vs PHP when you touch structure. (3) **Step 3** — one shared class at a time: missing methods, **within-class method declaration order** (**normally alphabetic**; Step 3 §2), logic parity vs PHP. (4) **Step 4** — **preserve** corpus passes + **extend** by clearing **`round-trip-failures.jsonl`** entries individually (see two paragraphs above).

## Translation Task Steps (PHP ↔ JS)

Use this prompt when syncing `php/parser/lean.php` with `static/js/parser/lean.js`.

### AST cloning for translation

When a PHP method uses `clone $this`, `LeanArgs::__clone`, or otherwise duplicates part of the AST:

1. **Base pattern (same shell as `clone()` in the SQL parser’s `sql.js`)** — implement on **`Lean`** (or the relevant leaf class) as:
   - `const copy = Object.create(Object.getPrototypeOf(this));`
   - `Object.assign(copy, this);`
   - `copy.parent = null;`
   - `return copy;`  
   This copies own enumerable fields only (**shallow**).

2. **`LeanArgs`** — **override** `clone()`: use the same three lines as above, then replace `copy.args` with `this.args.map((a) => (a != null ? a.clone() : a))` and set `a.parent = copy` for each child. That mirrors PHP **`LeanArgs::__clone`** (deep-clone along `args` only).

3. **`LeanToken`** — override `clone()` to `const copy = super.clone(); copy.cache = null; return copy;` so tactic-block cache is not shared.

4. **Call sites** — use **`node.clone()`**, not a standalone helper such as `cloneLeanSubtree(node)`.

### Step 1: Class Inventory and Missing Classes

1. **List all classes** defined in `lean.php`:
   - Include both concrete classes (`class LeanCaret extends Lean`) and abstract/intermediate classes (`abstract class LeanBinary extends LeanArgs`).
   - Classes use consistent `Lean_` prefix (e.g. `Lean_is_not`).

2. **For each PHP class**, determine the JS equivalent:
   - **Explicit**: Same or similar class name in `lean.js`.
   - **In `LEAN_CLASSES`**: **Concrete** classes only—register under `constructor.name` if the parser ever does `new ThatClass(...)` or `getLeanClass('ThatClass')` / `push_binary('ThatClass')`. Do **not** add abstract/intermediate PHP bases (`abstract class LeanBinary`, `LeanUnary`, `LeanPairedGroup`, `LeanCommand`, etc.) to `LEAN_CLASSES`.
   - **`getLeanClass`** / **`LEAN_CLASSES`** for any dynamic `new ThatClass(...)` (same idea as PHP `new $ClassName`).
   - **Flattened**: PHP hierarchy (e.g. `LeanRelational`, `LeanArithmetic`) collapsed into `LeanBinary` or `LeanUnary` in JS.

3. **Print missing classes** — classes in PHP that have no equivalent (neither a concrete JS class nor an entry in `LEAN_CLASSES`). Remember this list.

4. **Translate missing classes** — for each missing class:
   - Port the class and its methods from PHP to JS.
   - Map conventions per the table above (`__construct` → `constructor`, `__get`/`__set` → getters/setters, etc.).
   - **If the class is concrete** (instantiable as an AST node): **add it to `LEAN_CLASSES`**. Abstract JS bases stay out of the map. Unknown names passed to `getLeanClass` throw at runtime.

### Step 2: Class Declaration Order

1. **Compare declaration order** — list classes in order of first occurrence in both files.

2. **If order differs**:
   - **Option A**: Adjust `lean.js` to match PHP order when feasible. Respect dependency order (base classes before derived).
   - **Option B**: If JS intentionally flattens hierarchies (many small `LeanBinary` subclasses vs PHP's `LeanRelational`/`LeanArithmetic`), document the structural difference and skip reordering if it would cause large refactors with little benefit.

3. **Output**: Either the reordered `lean.js` or a note explaining why order was left as-is.

4. **Automation**: `node scripts/audit-lean-classes.mjs` prints a pairwise-order statistic for shared class names (PHP file order vs `lean.js` order). A high inversion count is expected under Option B.

### Step 3: Per-Class Function Audit

Work **one class at a time** (inventory → order → precision) so PHP and JS stay aligned without mixing unrelated edits.

For each class defined in **both** `lean.php` and `lean.js`:

1. **Missing functions**
   - List PHP methods (excluding inherited unless overridden).
   - List JS methods (including getters/setters for `__get`/`__set`).
   - **If JS is missing methods**: Print the missing function names and port them from PHP into `lean.js`.

2. **If no missing functions** — check **function order** (within the same class only; do not reorder methods across unrelated classes):
   - In **`lean.js`**, instance and static **methods** should **normally** appear in **alphabetic order by method name** (Unicode code point order, case-sensitive: capitals before lowercase). Put **`constructor`** first when the class defines one, then **`static` field initializers** (e.g. `static input_priority = …`), then methods alphabetically. For **`get x` / `set x`**, sort by accessor name **`x`** as if it were a method named `x` (list getters before setters for the same name if both exist). Defer to a different order only when readability or inheritance overrides would suffer (document in a short class comment if so).
   - PHP’s `lean.php` uses its own ordering rules when refactoring there (`php/parser/README.md`); do **not** assume PHP declaration order matches JS alphabetical order.
   - **If order is wrong**: Reorder methods in `lean.js` to satisfy the rule above, then proceed to the translation precision check below.

3. **Translation precision**
   - For each method, compare PHP logic with JS implementation.
   - **If JS differs**: Update the JS implementation to match PHP behavior.
   - If PHP uses **`clone` / `__clone`**: port via **`clone()`** per [AST cloning for translation](#ast-cloning-for-translation) above (extend `Lean` / `LeanArgs` / `LeanToken` as needed).

4. **Comments in `lean.js` (maintainability)**
   - Do **not** cite the filename `lean.php` or **line numbers** (or `~1234` ranges) in **`lean.js`** comments—they drift and create churn. (This README may still name `lean.php` as the PHP side of the sync.)
   - Prefer short **behavioral** notes; when needed, name a PHP **class** or **method** (e.g. “matches PHP `LeanArgsCommaSeparated`”) without file paths.

### Step 4: Output and Verification

- Run `node scripts/test-lean-parser.mjs` after **every** `lean.js` edit (corpus: `scripts/round-trip-corpus.jsonl`) so existing round-trip successes **stay** successes.
- **Shrink the failure set:** choose one row from `scripts/round-trip-failures.jsonl`, debug with `node scripts/test-lean-parser.mjs --round-trip-verbose <Lemma/…>` (or that path as the only extra arg), align behavior with PHP where relevant, then append `{"rel":"Lemma/…","note":"…"}` to `round-trip-corpus.jsonl` and run `node scripts/build-round-trip-failures.mjs` to refresh the queue.
- Optional bulk discovery: `node scripts/sample-round-trip-corpus.mjs <seed> <count> --append` appends up to `<count>` new round-trip–verified paths when such files still exist off the list.
- Ensure no new linter errors.
- Optionally update this README with class mapping summary, known gaps, or caveats.

### Example Output Format (Last Audit)

Last run: Steps 1–4 (README 2026-04-11): **Running Tests** — **preserve** **2498** corpus lemmas (**2498/2498** round-trip via `test-lean-parser.mjs`); **extend** by fixing **`round-trip-failures.jsonl`** **one row at a time** ([Running Tests](#running-tests)).

```
## Step 1: Class inventory (node scripts/audit-lean-classes.mjs)

- PHP Lean* declarations: 162
- JS Lean* declarations: 171

Registry: LEAN_CLASSES + getLeanClass only.

PHP class names with no JS class of the same name (2, abstract / still flattened into LeanBinary in JS):
  LeanLogic, LeanSetOperator

(Abstract PHP bases that **do** exist as JS classes: `LeanBinaryBoolean`, `LeanArithmetic`, `LeanRelational`, `LeanUnaryArithmetic`, `LeanUnaryArithmeticPre`, `LeanUnaryArithmeticPost`.)

JS class names with no PHP class of the same name (12, extra concrete nodes / Unicode operator symbols in token2classname):
  LeanEDiv, LeanPrefixExpr, Lean_boxminus, Lean_boxplus, Lean_boxtimes, Lean_circledast, Lean_circledcirc,
  Lean_circleddash, Lean_circleeq, Lean_dotsquare, Lean_ominus, Lean_oslash

Missing classes to port: none — every concrete PHP Lean* node has a same-named JS class or an intentional JS-only split as above.

## Step 2: Order
- Option B: JS grouped by role; not matched to lean.php line order.
- Pairwise order check (shared names only, PHP declaration order vs lean.js): ~28.7% of class pairs inverted
  (see audit script output; 0% would mean identical ordering).

## Step 3: Per-class audit
- Full method-by-method parity is not automated here (naming camelCase vs snake_case, helpers on different bases).
- **Within-class method order** in **`lean.js`**: **normally alphabetic** by method name (Step 3 §2). Examples audited/reordered earlier: **`LeanCaret`**, **`LeanCommand`**, **`LeanArgsCommaSeparated`**, **`LeanArgsSemicolonSeparated`**, **`LeanArgsCommaNewLineSeparated`**, **`LeanLineComment`**, **`LeanBlockComment`**, **`LeanDocString`**, **`LeanToken`**, **`Lean_set_option`**, **`Lean_import`**, **`Lean_open`**.
- **Comments**: no `lean.php` filename or line ranges in `lean.js` (Step 3 §4).
- Track gaps via [Known Gaps](#known-gaps) and targeted ports (e.g. LeanTactic vs PHP sequential combinator / getEcho).
- Prior parity work (examples): LeanBinary.echo, LeanRightarrow.echo; Lean_match, LeanWith; clone() on Lean / LeanArgs / LeanToken; LeanCalc; tactic modifiers.

## Step 4: Verification
- node scripts/test-lean-parser.mjs — corpus OK; **2498/2498** listed lemmas pass AST round-trip (`jsonSerialize(compile(String(compile(file))))` vs `jsonSerialize(compile(file))`).
- Fix `scripts/round-trip-failures.jsonl` entries one by one; after each fix, full corpus test still **2498/2498** (until you append the fixed `rel`).
- No new linter issues on static/js/parser/lean.js
```

## References

- `scripts/compare-php-node.mjs` – comparison utilities
- `scripts/audit-lean-classes.mjs` – PHP vs JS `Lean*` class name diff (Step 1) + pairwise order statistic (Step 2)
- `scripts/reorder_lean_class.py` / `scripts/compare_lean_class_methods.py` – PHP class segment tools (`php/parser/README.md`; presets `leanargscommaseparated`, `leanargssemicolonseparated`, `leanargscommanewlineseparated`)
- `scripts/round-trip-corpus.jsonl` – one JSON object per line (`rel`, optional `note`); source list for parser round-trip tests
- `scripts/round-trip-failures.jsonl` – off-corpus `Lemma/` files that fail parse or AST→string→AST; regenerate via `node scripts/build-round-trip-failures.mjs`
- `scripts/load-round-trip-corpus.mjs` – loader for the JSONL corpus
- `scripts/sample-round-trip-corpus.mjs` – reproducible random sample from `Lemma/`; use `--append` to append winners to `round-trip-corpus.jsonl`
- `scripts/build-round-trip-failures.mjs` – writes `round-trip-failures.jsonl` for fixing round-trip gaps one file at a time
- `server/lean/compiler/render2vue.mjs` – uses `LeanTactic::getEcho`
