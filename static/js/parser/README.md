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
- **JS**: `static/js/parser/lean.js` (~3500 lines)

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
| `__clone` | clone or copy logic |
| `$this->args` | `this.args` |
| `parent::method()` | `super.method()` |
| `get_class($this)` | `this.constructor.name` |
| `throw new Exception(...)` | `throw new Error(...)` |

### Known Gaps
- `Lean_match`, `LeanWith`: match/induction structure (partially handled)
- `Lean_namespace`, `LeanBar`: added for parity; `LeanBar` used when `LeanWith` is ported

### Running Tests
```bash
node scripts/test-lean-parser.mjs
```

## Translation Task Steps (PHP ↔ JS)

Use this prompt when syncing `php/parser/lean.php` with `static/js/parser/lean.js`.

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

### Step 4: Output and Verification

- Run `node scripts/test-lean-parser.mjs` after changes.
- Ensure no new linter errors.
- Optionally update this README with class mapping summary, known gaps, or caveats.

### Example Output Format (Last Audit)

Last run: automated name diff + spot checks (2025-03-24). Re-run the steps after large PHP or JS edits.

```
## Step 1: Class inventory (~162 PHP Lean* declarations vs ~156 JS Lean* classes)

Abstract / intermediate in PHP only (intentionally flattened or absent in JS):
- LeanArithmetic, LeanRelational, LeanBinaryBoolean, LeanLogic, LeanSetOperator,
  LeanUnaryArithmetic, LeanUnaryArithmeticPre, LeanSyntax → JS uses LeanBinary / LeanUnary / LeanArgs.

Concrete PHP classes still missing as dedicated JS classes (parser may delegate or not hit yet):
- Lean_match, LeanWith — match / induction (partial; README known gaps)
- LeanCalc, LeanFrom, LeanMOD, LeanUsing, LeanGeneralizing, LeanIn, LeanNot, LeanTacticBlock
- LeanArgsSemicolonSeparated

PHP maps tokens to class names that exist only in JS (no `class LeanEDiv` in PHP source; JS implements):
- LeanEDiv, Lean_ominus, Lean_oslash, Lean_circledcirc, Lean_circledast, Lean_circleddash, Lean_circleeq,
  Lean_boxplus, Lean_boxminus, Lean_boxtimes, Lean_dotsquare (see PHP token table vs JS LEAN_CLASSES)

PHP `LbigOperator` / `LeanQuantifier` → JS internal `LeanBigOperator` / `LeanQuantifier`; concretes
  Lean_forall, Lean_exists, Lean_sum, Lean_prod, Lean_bigcap, Lean_bigcup are in LEAN_CLASSES.

## Step 2: Order
- Left as-is: JS groups exports (args, binary cluster, unary, commands, parser); matching PHP file order
  would shuffle hundreds of lines with little runtime benefit.

## Step 3: Per-Class gaps (high level)
- Lean_rightarrow: ported is_indented, sep, strFormat, stack_priority 24, insert_newline, isProp (PHP ~5591–5645).
- LeanTactic, LeanRightarrow::echo, Lean_match / LeanWith, tactic block helpers: still large PHP surface;
  prioritize by failing corpus or render2vue usage.
- Full method-by-method pass: use grep on `class LeanFoo` in both files for remaining classes.

## Step 4: Verification
- node scripts/test-lean-parser.mjs — corpus OK
- No new linter issues on static/js/parser/lean.js
```

## References

- `scripts/compare-php-node.mjs` – comparison utilities
- `server/lean/compiler/render2vue.mjs` – uses `LeanTactic::getEcho`
