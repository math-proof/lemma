# Lean PHP parser (`lean.php`)

Parser and AST classes for Lean 4 source. Main file: `lean.php`.

---

## Modification task steps: reorder class methods in `lean.php`

Use this workflow when you want a class in `lean.php` to follow a consistent method order.

### 1. Find a class whose methods are not in alphabetical order

- Search `lean.php` for `class …` / `abstract class …`.
- For each candidate, list method names in **declaration order** and compare to **alphabetical order** (case-insensitive, see rules below).

### 2. Reorder methods (and data members)

- **Data members first:** All **properties** (`public $…`, `protected $…`, `static $…`, etc.) must appear **before** any instance or static **methods** in the class body. Preserve the **relative order** of properties as you gather them (e.g. if `static $foo` was declared after `public $bar` in the file, keep that order when you move blocks). **Constants** and assignments **outside** the class (e.g. `LeanToken::$subscript_keys = …` after the closing `}`) stay where they are; only the **inside** of the class is reordered.
- **Alphabetic order** for instance methods:
  - **Magic methods** (`__construct`, `__clone`, `__get`, `__set`, `__toString`, …): keep them in a **first group**, sorted by `strtolower($name)`. (Do not merge them with normal methods by stripping `_` from the whole name, or `append` can sort before `__clone`.)
  - **Other instance methods**: sort by a key that ignores underscores only for *non-magic* names so names like `isProp` order before `is_space_separated` (plain ASCII would put `_` before letters).
- **Static methods** (`public static function`, `static function`): place **after** all instance methods, then sort among themselves alphabetically.

### 3. Implement the reorder with **Python**

- Prefer a small script (regex-based split of method blocks + sort + rewrite) rather than hand-editing huge classes.
- Repo helper: [`scripts/reorder_lean_class.py`](../../scripts/reorder_lean_class.py)  
  - **Presets:** `lean` (default) = `abstract class Lean`; `leancaret` = `class LeanCaret`; `leanlinecomment` = `class LeanLineComment`; `leanblockcomment` = `class LeanBlockComment`; `leandocstring` = `class LeanDocString`; `leanargs` = `abstract class LeanArgs`; `leanunary` = `abstract class LeanUnary`; `leanpairedgroup` = `abstract class LeanPairedGroup`; `leanparenthesis` = `class LeanParenthesis`; `leananglebracket` = `class LeanAngleBracket`; `leanbracket` = `class LeanBracket`; `leanbrace` = `class LeanBrace`; `leanabs` = `class LeanAbs`; `leandoubleanglequotation` = `class LeanDoubleAngleQuotation`; `leanbinary` = `abstract class LeanBinary`; `leanproperty` = `class LeanProperty`; `leancolon` = `class LeanColon`; `leanassign` = `class LeanAssign`; `leanbinaryboolean` = `abstract class LeanBinaryBoolean` (**members-first:** `use Trait;` lines with properties, then sorted methods); `leanrelational` = `abstract class LeanRelational`; `leanarithmetic` = `abstract class LeanArithmetic`; `leanmul` = `class LeanMul`; `leandiv` = `class LeanDiv`; `leanbitor` = `class LeanBitOr`; `leantoken` = `class LeanToken` (**members-first** reorder: all properties, then sorted methods).  
  - For classes **without** interleaved properties, the legacy path still applies; for **`LeanToken`**-style classes, use preset `leantoken` so properties are not merged into the previous method.  
  - Add a preset (and matching end marker) if you reorder another class.  
  - Run from repo root, e.g.:  
    `python scripts/reorder_lean_class.py`  
    `python scripts/reorder_lean_class.py leancaret`

### 4. Validate syntax with the **same PHP version as the site**

- Open **`http://localhost/info.php`** and read **PHP Version** (e.g. `8.0.26`).
- Run **`php -l`** with the matching binary (WAMP example):

  ```bash
  "D:\wamp64\bin\php\php8.0.26\php.exe" -l php/parser/lean.php
  ```

  Replace the folder under `D:\wamp64\bin\php\` so it matches your `info.php` version.

- Expect: `No syntax errors detected in …`

### 5. **Mandatory:** prove equivalence after reorder

- Run [`scripts/compare_lean_class_methods.py`](../../scripts/compare_lean_class_methods.py) (or an equivalent you maintain) so that **every** reorder is verified: **no method dropped or added**, and **each method body unchanged** aside from order (compare HEAD vs working tree for the edited class).
  - Same presets as reorder: e.g. `python scripts/compare_lean_class_methods.py leancaret`
- Add a preset in that script if you reordered a class not yet listed there.
- Do **not** treat this step as optional; a failed or skipped check means the task is not done.

### 6. **Mandatory:** `git diff` sanity-check before `git push`

- From the repo root, run:

  ```bash
  git diff php/parser/lean.php
  ```

  (Equivalent: `git diff -- php/parser/lean.php`.)

- **Read the whole diff** and confirm it is **safe to push**:
  - Changes are confined to the **intended class(es)** (no accidental edits elsewhere).
  - Hunks look like **moved property blocks and/or reordered method blocks** only (no surprise edits to logic, signatures, or unrelated lines).
  - If anything else appears (merge artifacts, encoding, accidental deletes), **fix or revert** before pushing.

- This step complements the compare script (structural equality); **both** are required before you treat the task as done and push.

---

## Related files

| Path | Role |
|------|------|
| `lean.php` | Parser + AST |
| `../std.php`, `newline_skipping_comment.php`, etc. | Dependencies |
| `../../scripts/reorder_lean_class.py` | Reorder one class block in `lean.php` |
| `../../scripts/compare_lean_class_methods.py` | **Required** after reorder: method list + body equality vs `HEAD` |
| `git diff php/parser/lean.php` | **Required** before push: human review that the diff is reorder-only / reasonable |

---

## Prompt (copy-paste for agents)

```text
Modification task steps for lean.php:
- Find a PHP class whose function order is not alphabetic order (and whose properties are not already grouped before all methods).
- Data members (properties: public/protected/private/static $…) must come first inside the class, in a sensible preserved order; then instance methods in alphabetic order (magic methods first per README); then static methods after instance methods.
- Use the PHP version shown at http://localhost/info.php to run php -l on the modified lean.php and confirm syntax.
- Use Python to perform the reorder (scripts/reorder_lean_class.py PRESET, or add a preset for the target class). Use preset leantoken for class LeanToken (members-first + method sort).
Afterward, you must run scripts/compare_lean_class_methods.py with the same PRESET (or an equivalent) so no method was dropped and bodies are unchanged aside from order; skipping this step is not allowed.
Before git push, you must run `git diff php/parser/lean.php`, read the full diff, and confirm changes are limited to the intended class(es) and look like property/method reorder only; skipping this review is not allowed.
```
