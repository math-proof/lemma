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
- **JS**: `static/js/parser/lean.js` (~4200 lines)

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
- `LeanBar` / `Lean_match` / `LeanWith`: `split` and echo paths may still differ from PHP in edge cases
- Large tactic / proof surface still thin vs PHP: `LeanTactic` (`get_echo_token`, `has_tactic_block_followed`, `insert_sequential_tactic_combinator` wiring vs PHP `LeanSequentialTacticCombinator` unary), `LeanTacticBlock::echo`, `LeanRightarrow::echo`

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

Last run: Steps 1–4 (2025-03-24): `Lean_match.split` uses `this.clone()`; `Lean` / `LeanArgs` / `LeanToken` `clone()` (sql.js shell + deep `args`); README cloning note, tests.

```
## Step 1: Class inventory (~162 PHP Lean* vs ~166 JS Lean* incl. LeanBigOperator / LeanQuantifier)

Registry: LEAN_CLASSES + getLeanClass only.

Abstract in PHP only (flattened in JS): LeanArithmetic, LeanBinaryBoolean, LeanLogic, LeanRelational,
  LeanSetOperator, LeanUnaryArithmetic, LeanUnaryArithmeticPre, LeanSyntax.

PHP names still absent in JS (8 total): the abstracts listed above only (concrete Lean_match, LeanWith now in JS).

This pass: Lean_match, LeanWith + LEAN_CLASSES; LeanArgs.clone() mirrors PHP LeanArgs::__clone for split.

Prior ports: LeanCalc; LeanArgsSemicolonSeparated; LeanUsing, LeanFrom, LeanMOD, LeanGeneralizing, LeanIn;
  LeanNot, LeanTacticBlock; big operators; Lean_show; etc.

## Step 2: Order
- Option B: JS grouped by role; not matched to lean.php line order.

## Step 3: Per-class audit (sampled)
- Lean_match / LeanWith: insert (LeanWith), strFormat, latexFormat, latexArgs, insert_comma, relocateLastComment,
  insert_tactic, split, isProp; With sep, insert_newline, insert_bar, insert_tactic, insert_comma, set_line,
  tokens_bar_separated, unique_token, tokens_space_separated, stack_priority.
- LeanTactic: still thin vs PHP for sequential combinator / echo / jsonSerialize (see Known Gaps).

## Step 4: Verification
- node scripts/test-lean-parser.mjs — corpus OK
- No linter issues on static/js/parser/lean.js
```

## References

- `scripts/compare-php-node.mjs` – comparison utilities
- `server/lean/compiler/render2vue.mjs` – uses `LeanTactic::getEcho`
