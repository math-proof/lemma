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
- Dynamic classes: JS uses `resolveUnaryCtor`, `resolveUnaryPostCtor`, `resolveCommandCtor` for unknown identifiers

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
- Some tactic-specific `echo` behaviors (e.g. `Lean_set_option::echo` maxHeartbeats)
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
   - **Via resolver**: Covered by `resolveUnaryCtor`, `resolveUnaryPostCtor`, or `resolveCommandCtor` (dynamic class creation).
   - **Flattened**: PHP hierarchy (e.g. `LeanRelational`, `LeanArithmetic`) collapsed into `LeanBinary` or `LeanUnary` in JS.

3. **Print missing classes** — classes in PHP that have no equivalent (neither explicit nor via resolver). Remember this list.

4. **Translate missing classes** — for each missing class:
   - Port the class and its methods from PHP to JS.
   - Map conventions per the table above (`__construct` → `constructor`, `__get`/`__set` → getters/setters, etc.).
   - Add to `lean.js` and wire into resolvers if needed (e.g. add to `resolveCommandCtor` switch).

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

### Example Output Format

```
## Step 1: Missing Classes
- LeanBar (added)
- Lean_namespace (added)

## Step 2: Order
- Order left as-is: JS flattens binary hierarchy; reordering would require large refactor.

## Step 3: Per-Class Gaps
### Lean (base)
- Added: tokens_space_separated, getEcho, strArgs, echo, traverse, set_line
### LeanCaret
- OK (methods match)
### LeanTactic
- getEcho: OK (precise)
```

## References

- `scripts/compare-php-node.mjs` – comparison utilities
- `server/lean/compiler/render2vue.mjs` – uses `LeanTactic::getEcho`
