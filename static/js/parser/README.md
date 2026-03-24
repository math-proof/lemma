# Lean Parser (JavaScript)

JavaScript port of the Lean 4 parser from `php/parser/lean.php`. Produces an AST for Lean source code used by the web UI (syntax highlighting, LaTeX export, proof echo).

## Files

| File | Description |
|------|-------------|
| `node.js` | Base `Node`, `IndentedNode`, `AbstractParser` |
| `lean.js` | Lean AST classes and `LeanParser` |
| `newline.js` | Newline handling utilities |
| `markdown.js` | Markdown parsing |
| `xml.js` | XML parsing |

## PHP → JS Parity

### Source of Truth
- **PHP**: `php/parser/lean.php` (~9500 lines)
- **JS**: `static/js/parser/lean.js` (~4300 lines)

### Class Mapping
JS flattens some PHP hierarchies:
- PHP `LeanRelational`, `LeanArithmetic`, `LeanUnaryArithmeticPre`, `LeanUnaryArithmeticPost`, `LeanSetOperator`, `LeanLogic`, `LeanBinaryBoolean` → JS `LeanBinary` or `LeanUnary`
- PHP `Lean_is_not` ↔ JS `Lean_is_not` (identical)
- **PHP** uses `new $ClassName(...)` with no separate registry; **JS** uses **`LEAN_CLASSES`**: a map of **concrete** AST classes only (keys = `constructor.name`). **Abstract/intermediate** bases (`Lean`, `LeanArgs`, `LeanBinary`, `LeanUnary`, `LeanPairedGroup`, `LeanCommand`, marker classes, etc.) are **not** in the map—they remain normal exports in `lean.js`. **`getLeanClass(name)`** looks up `LEAN_CLASSES` only; unknown names throw (add the concrete class to `LEAN_CLASSES`). Prefix unary (`insert_unary`), postfix (`push_post_unary`), and `push_left` paired delimiters use **`getLeanClass`** like PHP `new $ClassName`.

### Conventions (PHP → JS)

| PHP | JavaScript |
|-----|------------|
| `__construct` | `constructor` |
| `__get('x')` | getter `get x()` |
| `__set('x', v)` | setter `set x(v)` |
| `__toString` | `toString()` (uses `strFormat` + `strArgs`) |
| `__clone` | instance method **`clone()`** — see [AST cloning for translation](#ast-cloning-for-translation) under Translation Task Steps |
| `$this->args` | `this.args` |
| `parent::method()` | `super.method()` |
| `get_class($this)` | `this.constructor.name` |
| `throw new Exception(...)` | `throw new Error(...)` |

### Known Gaps
- `Lean_match` / `LeanWith`: echo and other edge cases may still differ from PHP in corner cases; `LeanBar.split` / `LeanCalc.split` use deep `clone()` like PHP
- Nested proof echo: worth spot-diffing `LeanTacticBlock::echo` / `LeanStatements::echo` against PHP after corpus changes
- Recent parity: `LeanTacticBlock` (`echo`, `split`, `tactic_block`, `set_line`), `LeanArgsSpaceSeparated` (`tokens_space_separated`, `construct_prefix_tree`, `tactic_block_info`, `operand_count`), `LeanSequentialTacticCombinator`, `LeanTactic` echo/split helpers, `LeanBy::echo`, `LeanBitOr` / `LeanAngleBracket` / `LeanArgsCommaSeparated` token helpers

### Running Tests
```bash
node scripts/test-lean-parser.mjs
```

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

For each class defined in **both** `lean.php` and `lean.js`:

1. **Missing functions**
   - List PHP methods (excluding inherited unless overridden).
   - List JS methods (including getters/setters for `__get`/`__set`).
   - **If JS is missing methods**: Print the missing function names and port them from PHP into `lean.js`.

2. **If no missing functions** — check **function order**:
   - Compare the order of method declarations in PHP vs JS.
   - **If order is inconsistent**: Reorder methods in `lean.js` to follow PHP's order.
   - **If order is consistent**: Proceed to the translation precision check below.

3. **Translation precision**
   - For each method, compare PHP logic with JS implementation.
   - **If JS differs**: Update the JS implementation to match PHP behavior.
   - If PHP uses **`clone` / `__clone`**: port via **`clone()`** per [AST cloning for translation](#ast-cloning-for-translation) above (extend `Lean` / `LeanArgs` / `LeanToken` as needed).

### Step 4: Output and Verification

- Run `node scripts/test-lean-parser.mjs` after changes.
- Ensure no new linter errors.
- Optionally update this README with class mapping summary, known gaps, or caveats.

### Example Output Format (Last Audit)

Last run: Steps 1–4 (2026-03-24): `lean.js` — `LeanTactic.insert` matches PHP `LeanSyntax::insert` (~6946–6954): when caret is `end(args)`, push `Ctor(newCaret, indent, level)` for any insert type (not only `modifier`); `node scripts/test-lean-parser.mjs` — corpus OK.

```
## Step 1: Class inventory (node scripts/audit-lean-classes.mjs)

- PHP Lean* declarations: 161
- JS Lean* declarations: 165

Registry: LEAN_CLASSES + getLeanClass only.

PHP class names with no JS class of the same name (8, abstract / flattened into LeanBinary or LeanUnary in JS):
  LeanArithmetic, LeanBinaryBoolean, LeanLogic, LeanRelational, LeanSetOperator, LeanSyntax,
  LeanUnaryArithmetic, LeanUnaryArithmeticPre

(Also abstract in PHP, present in JS with the same name: LeanUnaryArithmeticPost — not in the list above.)

JS class names with no PHP class of the same name (12, extra concrete nodes / Unicode operator symbols in token2classname):
  LeanBigOperator, LeanEDiv, Lean_boxminus, Lean_boxplus, Lean_boxtimes, Lean_circledast, Lean_circledcirc,
  Lean_circleddash, Lean_circleeq, Lean_dotsquare, Lean_ominus, Lean_oslash

Missing classes to port: none — every concrete PHP Lean* node has a same-named JS class or an intentional JS-only split as above.

## Step 2: Order
- Option B: JS grouped by role; not matched to lean.php line order.
- Pairwise order check (shared names only, PHP declaration order vs lean.js): ~29% of class pairs inverted
  (see audit script output; 0% would mean identical ordering).

## Step 3: Per-class audit
- Full method-by-method parity is not automated here (naming camelCase vs snake_case, helpers on different bases).
- Track gaps via [Known Gaps](#known-gaps) and targeted ports (e.g. LeanTactic vs PHP sequential combinator / getEcho).
- Prior parity work (examples): LeanBinary.echo, LeanRightarrow.echo; Lean_match, LeanWith; clone() on Lean / LeanArgs / LeanToken; LeanCalc; tactic modifiers.

## Step 4: Verification
- node scripts/test-lean-parser.mjs — corpus OK
- No new linter issues on static/js/parser/lean.js
```

## References

- `scripts/compare-php-node.mjs` – comparison utilities
- `scripts/audit-lean-classes.mjs` – PHP vs JS `Lean*` class name diff (Step 1) + pairwise order statistic (Step 2)
- `server/lean/compiler/render2vue.mjs` – uses `LeanTactic::getEcho`
