# Lean PHP parser (`lean.php`)

Parser and AST classes for Lean 4 source. Main file: `lean.php` (router). The abstract AST base (`Lean`) lives in `lean/base.php` (loaded before the leaf nodes). Leaf nodes (`LeanCaret`, `LeanToken`, comments) live in `lean/atomic.php` (loaded after `base.php`). Abstract argument bases (`LeanArgs`, `LeanUnary`, `LeanBinary`) live in `lean/abstract.php` (loaded after `LeanMultipleLine` and before `paired.php`). Interval notation (`LeanUpto`, `a..b`) lives in `lean/range.php` (loaded after `paired.php`). Field access (`LeanProperty`, `a.b`) lives in `lean/property.php` (loaded after `range.php`). Type ascription (`LeanColon`, `a : T`) lives in `lean/colon.php` (loaded after `property.php`). Assignment (`LeanAssign`, `:=`) lives in `lean/assign.php` (loaded after `colon.php`). The boolean-binary base (`LeanBinaryBoolean`) lives in `lean/boolean.php` (loaded after the `LeanProp` trait and before `relational.php`). Lazy application (`Lean_lazy`, `<|`) lives in `lean/lazy.php` (loaded after `arithmetic.php`). Pipeline dot (`LeanMethodChaining`, `|>.`) lives in `lean/pipeline.php` (loaded after `lazy.php`). Type tests (`Lean_is`, `Lean_is_not`) live in `lean/isinstance.php` (loaded after `indexing.php`). Statement lists (`LeanStatements`) live in `lean/statements.php` (loaded after `set.php`). The source file (`LeanModule`) lives in `lean/module.php` (loaded after `statements.php`). Top-level commands (`LeanCommand`, `import` / `open` / `set_option` / `namespace`) live in `lean/command.php` (loaded after `module.php`). The bar separator (`LeanBar`, `|`) lives in `lean/bar.php` (loaded after `command.php`). Arithmetic operators live in `lean/arithmetic.php` (loaded after `LeanBinary` / `LeanUnary`). Paired delimiters live in `lean/paired.php` (loaded after `LeanUnary`). Logic connectives live in `lean/logic.php` (loaded after `LeanBinaryBoolean`). Set operators and inclusion live in `lean/set.php` (loaded after `LeanLogic`, because `⊇` / `⊃` extend it). Relational comparisons live in `lean/relational.php` (loaded after `LeanBinaryBoolean`). Membership and iff live in `lean/membership.php` (loaded after `relational.php`). The big-operator base and the remaining big operators live in `lean/bigops.php` (loaded after `fun.php`). Quantifiers live in `lean/quantifier.php` (loaded after `bigops.php`). Binders (`fun`) live in `lean/fun.php` (loaded after `decl.php`). Indexing lives in `lean/indexing.php` (loaded after the `LeanGetElemBase` traits). Arrows live in `lean/arrows.php` (loaded after `LeanBar`). Negation lives in `lean/negation.php` (loaded after `arrows.php`). Match lives in `lean/match.php` (loaded after `negation.php`). If-then-else lives in `lean/ite.php` (loaded after `match.php`). Argument lists live in `lean/args.php` (loaded after `ite.php`). Tactics (`LeanSyntax`, `LeanTactic`, `by` / `from` / `calc` / `at` / `<;>` / tactic blocks / `with` / attributes) live in `lean/tactic.php` (loaded after `args.php`). Declarations (`def` / `theorem` / `abbrev` / `lemma`, `let` / `have` / `set` / `replace` / `show`) live in `lean/decl.php` (loaded after `tactic.php`). Reorder presets for those families read the family file.

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

### 4. Validate syntax with the **same PHP version as the site**

- Open **`http://localhost/info.php`** and read **PHP Version** (e.g. `8.0.26`).
- Run **`php -l`** with the matching binary (WAMP example):

  ```bash
  "D:\wamp64\bin\php\php8.0.26\php.exe" -l php/parser/lean.php
  ```

  Replace the folder under `D:\wamp64\bin\php\` so it matches your `info.php` version.

- Expect: `No syntax errors detected in …`

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


---

## Related files

| Path | Role |
|------|------|
| `lean.php` | Parser + AST router |
| `lean/base.php` | Abstract AST base (`Lean`) |
| `lean/atomic.php` | Leaf nodes (`LeanCaret`, `LeanToken`, comments) |
| `lean/abstract.php` | Abstract argument bases (`LeanArgs`, `LeanUnary`, `LeanBinary`) |
| `lean/range.php` | Interval notation (`LeanUpto`, `a..b`) |
| `lean/property.php` | Field access (`LeanProperty`, `a.b`) |
| `lean/colon.php` | Type ascription (`LeanColon`, `a : T`) |
| `lean/assign.php` | Assignment (`LeanAssign`, `:=`) |
| `lean/boolean.php` | Boolean-binary base (`LeanBinaryBoolean`) |
| `lean/lazy.php` | Lazy application (`Lean_lazy`, `<|`) |
| `lean/pipeline.php` | Pipeline dot (`LeanMethodChaining`, `|>.`) |
| `lean/isinstance.php` | Type tests (`Lean_is`, `Lean_is_not`) |
| `lean/statements.php` | Statement lists (`LeanStatements`) |
| `lean/arithmetic.php` | Arithmetic operator family (`LeanArithmetic`, unary arithmetic) |
| `lean/paired.php` | Paired delimiters (`LeanPairedGroup` and children) |
| `lean/logic.php` | Logic connectives (`LeanLogic`, `&&` / `||` / `^^` / `∨` / `∧`) |
| `lean/set.php` | Set operators and inclusion (`LeanSetOperator`, `\\`, `∪`, `∩`, `⊆`, `⊂`, `⊇`, `⊃`) |
| `lean/relational.php` | Relational comparisons (`LeanRelational`, `>`, `<`, `=`, `≠`, `≡`, `≃`, `≈`, `∣`, …) |
| `lean/membership.php` | Membership and iff (`∈`, `∉`, `↔`) |
| `lean/quantifier.php` | Quantifiers (`LeanQuantifier`, `∀`, `∃`) |
| `lean/bigops.php` | Big operators (`LeanBigOperator`, `∑`, `lim`, `∏`, `∫`, `⋂`, `⋃`, `Stack`) |
| `lean/fun.php` | Lambda binder (`Lean_fun` / `fun`) |
| `lean/indexing.php` | Indexing (`LeanGetElem`, `LeanGetElemQue`, `LeanGetElemQuote`) |
| `lean/arrows.php` | Arrows (`LeanRightarrow`, `Lean_rightarrow`, `Lean_mapsto`, `Lean_leftarrow`) |
| `lean/negation.php` | Negation (`Lean_lnot` / `¬`, `LeanNot` / `!`) |
| `lean/match.php` | Match (`Lean_match`) |
| `lean/ite.php` | If-then-else (`LeanIte`) |
| `lean/args.php` | Argument lists (space, newline, indented, comma, semicolon) |
| `lean/tactic.php` | Syntax and tactics (`LeanSyntax`, `LeanTactic`, `by` through attributes) |
| `lean/decl.php` | Declarations (`def`, `theorem`, `abbrev`, `lemma`, `let`, `have`, `show`) |
| `../std.php`, `newline_skipping_comment.php`, etc. | Dependencies |
| `git diff php/parser/lean.php` | **Required** before push: human review that the diff is reorder-only / reasonable |

---

## Prompt (copy-paste for agents)

```text
Modification task steps for lean.php:
- Find a PHP class whose function order is not alphabetic order (and whose properties are not already grouped before all methods).
- Data members (properties: public/protected/private/static $…) must come first inside the class, in a sensible preserved order; then instance methods in alphabetic order (magic methods first per README); then static methods after instance methods.
- Use the PHP version shown at http://localhost/info.php to run php -l on the modified lean.php and confirm syntax.
Before git push, you must run `git diff php/parser/lean.php`, read the full diff, and confirm changes are limited to the intended class(es) and look like property/method reorder only; skipping this review is not allowed.
```
