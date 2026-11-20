# Lemma path patterns

`mjs/lemmaPath.mjs` takes the parsed expression's `toJSON()` output and uses
`json2pathPatterns` in `js/parser/lean/json2regex.js` to generate base and plural
patterns and DAG-based suggestions. The path checker uses `suggestionMatches`
from the same module.

The parser represents binders and their bodies as follows.

## Expect / Prob / Var

Binder sugars now promote to `LeanBigOperator` subclasses in `js/parser/lean/bigops.js`:

| Surface | AST class | bound | scope | pathToken |
|---------|-----------|-------|-------|-----------|
| `𝔼[binder](body)` | `Lean_Expect` | binder | Parenthesis | `Expect` |
| `ℙ[π](event)` / `ℙ[π]{event}` | `Lean_Prob` | `π` | Parenthesis/Brace | `Prob` |
| `𝕍𝕒𝕣[binder](body)` | `Lean_Var` | binder | Parenthesis | `Var` |

Mathlib `Var[Y]` / `Var[x \| m]` (no body delimiter) stays plain `LeanGetElem` — do not treat as `Lean_Var`.

## Limits ops max/min/sup/inf/max⁻¹/min⁻¹

Binder sugars promote to `LeanLimitsBigOp` subclasses in `js/parser/lean/bigops.js`:

| Surface | AST class | pathToken |
|---------|-----------|-----------|
| `max[binder] body` | `Lean_max` | `Max` |
| `min[…] body` | `Lean_min` | `Min` |
| `sup[…] body` | `Lean_sup` | `Sup` |
| `inf[…] body` | `Lean_inf` | `Inf` |
| `max⁻¹[…] body` | `Lean_argmax` | `ArgMax` |
| `min⁻¹[…] body` | `Lean_argmin` | `ArgMin` |

Walk via `.bound` / `.scope` (same contract as `Lean_Expect` / `Lean_partial`).
Legacy fallback: `GetElem(limitsOp, binder)` + SpaceSeparated body (pre-promote / incomplete).
`LeanGetElem.limitsOperator` remains for colon newline-body detection and plain-GetElem latex fallback.
Unicode `⨅`/`⨆` stay `LeanInf`/`LeanSup` — not these classes.
Bare `max` / ordinary `x[i]` stay Token / GetElem.
