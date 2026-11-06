# holeRegex dispatch (Body t366) — for mjs

## API (lean.js AST)

`node.holeRegex(opts) -> string | null`

- `null` / `""` = hole contribution (parent inserts `_` via `wrapHoleOpt`)
- string = regex fragment (`Eq_(_|Mul…)`, `Deriv_`, `Sin(_|Arctan(_|Deriv_))`, …)

### Default (`Node#holeRegex`)
If `opts.frozen` is a function, returns `opts.frozen(this)` (or null if empty).
Else returns `null`.

### opts (lemmaPath should pass)
| key | purpose |
|-----|---------|
| `frozen(node)` | today’s catch-all `nameExpr` → `escapeHoleReLit(sanitizePathSeg(...))` |
| `nameToken(text)` | full lemmaPath `nameToken` (SYMBOL/TOKEN_ALIAS); else AST default CamelCase |
| `isLeaf(text)` | binder/leaf check (`isLeafName`) |
| `peelGuards(node)` | `peelGuardForalls` for `All` body |
| `mulBothHolesBare` | Mul both-holes → `Mul` not `Mul(_)(_)` (plural MulS RHS) |
| `inTrigProp` | set when walking object of `.sin`/`.arctan` |
| `leaves` | optional Set; Token uses if `isLeaf` absent |

Helpers (import from `js/parser/lean/pathChoices.js`):
`escapeHoleReLit`, `wrapHoleOpt`, `HOLE_RE_TRIG_FN`, `holeRegexDefaultNameToken`,
`holeRegexChild`, `holeRegexCombineArith`, `holeRegexCombineRel`, `holeRegexCombineUnary`.

## Overrides
- peel: `LeanParenthesis`, `LeanColon`, `LeanRightarrow` / `Lean_rightarrow` (rhs)
- quant: `Lean_forall`→`All_…`, `Lean_exists`→`Any_…` (+ `opts.peelGuards`)
- bigop: `Lean_partial`→`Deriv_`, `Lean_nabla`→`Grad_`
- `LeanProperty` / `LeanArgsSpaceSeparated`: trig/log heads
- arith tags: Add/Sub/Mul/Div/Pow; MatMul→`Dot`; Neg/Inv/Sqrt unary
- rel tags via `holeRegexTag`: Eq/Ne/Lt/Gt/Le/Ge/Dvd; Iff; Subset
- `LeanToken`: leaf→null; digit literal; else named token

## What mjs should change (keep plural MulS separate)

```js
import { escapeHoleReLit, wrapHoleOpt } from "../js/parser/lean/pathChoices.js";
// optional: re-export already there

function holeRegexExpr(node, opts) {
  const u = peelHoleExpr(node);
  if (!u) return null;
  const holeOpts = {
    ...opts,
    nameToken,           // existing lemmaPath fn
    isLeaf: (t) => isLeafName(t, opts.leaves),
    peelGuards: peelGuardForalls,
    frozen: (n) => {
      const frozen = nameExpr(n, opts);
      return frozen ? escapeHoleReLit(sanitizePathSeg(frozen)) : null;
    },
  };
  if (typeof u.holeRegex === "function")
    return u.holeRegex(holeOpts);
  return holeOpts.frozen(u);
}

export function implyHoleRegexFromAst(implyStmts, opts = {}) {
  const root = peelHoleExpr(implyStmts);
  if (!root) return "";
  const frag = holeRegexExpr(root, opts);
  if (frag == null || frag === "" || frag === "_") return "";
  return frag;
}
```

**Do not** fold `pluralMulSHoleRegex` into AST default. Keep Body shape:
`All_(Eq(Sub(MulS_(…)))(_|Mul(_|Mul(_)(_))_)` as a separate alt in `holeRegexAlternatives`.

Peel of Statements / NewLineSeparated can stay in `peelHoleExpr` (mjs) before the call.

## Expect / Prob / Var (Body t174) — AST reshape

Binder sugars now promote to `LeanBigOperator` subclasses in `js/parser/lean/bigops.js`:

| Surface | AST class | bound | scope | pathToken |
|---------|-----------|-------|-------|-----------|
| `𝔼[binder](body)` | `Lean_Expect` | binder | Parenthesis | `Expect` |
| `ℙ[π](event)` / `ℙ[π]{event}` | `Lean_Prob` | `π` | Parenthesis/Brace | `Prob` |
| `𝕍𝕒𝕣[binder](body)` | `Lean_Var` | binder | Parenthesis | `Var` |

Mathlib `Var[Y]` / `Var[x \| m]` (no body delimiter) stays plain `LeanGetElem` — do not treat as `Lean_Var`.

### lemmaPath helpers (done)

Former shape:
`LeanArgsSpaceSeparated(LeanGetElem(𝔼|ℙ|𝕍𝕒𝕣, binder), Parenthesis|Brace)`

New shape:
`Lean_Expect` / `Lean_Prob` / `Lean_Var` with `.bound` / `.scope` (same contract as `Lean_partial` / `Lean_nabla`).

**lemmaPath status (Body t174 / teammate js):** helpers prefer `.bound` / `.scope`.

| Helper | Now checks |
|--------|------------|
| `expectProbVarBoundScope` | `Lean_Expect` / `Lean_Prob` / `Lean_Var` → `{bound, scope, kind}` |
| `legacyExpectProbVarApp` | pre-promote `GetElem(op, binder)` + SpaceSeparated body |
| `isExpectDotPowId` | `Lean_Expect.scope` is DotPow_Id (legacy GetElem+SS fallback) |
| `isVarApp` | `Lean_Var` (legacy binder+scope); **not** Mathlib `Var[Y]` GetElem |
| `isExpectCondApp` / `expectScope` | Expect scope with `|` condSigma |
| `expectSMulGradLogNames` / `expectDotFunSMulGradLogName` | Expect `.scope` body |
| `matchProbApp` / `isExpectAppNode` | `Lean_Prob` / `Lean_Expect` (+ legacy) |
| GradExpect walks | unchanged: `gradientBody` → nabla `.scope` → `isExpectDotPowId(Lean_Expect)` |
| `nameExpr` / `preAlts` | direct `Lean_Expect` / `Lean_Var` / `Lean_Prob` cases |

Mathlib `Var[Y]` / `Var[x | m]` remains `LeanGetElem` (Cap `Var` token in `nameExprBase`).

`pathChoices` / `holeRegex` already live on the new nodes (`Expect_*`, `Prob_*`, `Var_*`).

Latex/color (magenta RA `ℙ`, Expect paren keep) unchanged by design.

## Limits ops max/min/sup/inf/max⁻¹/min⁻¹ (Body t175)

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

### lemmaPath status (Body t175 / teammate js)

**lemmaPath status:** helpers prefer `.bound` / `.scope`.

| Helper | Now checks |
|--------|------------|
| `limitsBigOpBoundScope` | `Lean_max` / `min` / `sup` / `inf` / `argmax` / `argmin` → `{bound, scope, kind, pathToken}` |
| `legacyLimitsBigOpApp` | pre-promote `GetElem(op, binder)` + SpaceSeparated body |
| `isArgMaxMinApp` / `argMaxMinBody` / `argMaxMinTokenName` | prefer `Lean_argmax` / `Lean_argmin`; legacy GetElem+SS fallback |
| `isArgMaxMinGetElem` | bare / pre-promote GetElem `max⁻¹`/`min⁻¹` (indented-sibling body) |
| `findArgMaxImplyEq` / `isArgMaxProbCondEqMulProdShape` | ArgMax bigop or legacy; path stays `ArgMax_ProbCond` underscore style |
| `isSupLtInfty` / `supBoundKind` | `Lean_sup.scope` body `< ∞` → `GtInftySup` / `GtInftySup_Sum` (+ legacy GetElem) |
| `maxBvarOperands` | `Lean_max` bound/scope (+ legacy GetElem max) |
| `fnLikeHead` | ArgMax/ArgMin bigop or GetElem (no `Get` prefix) |
| `nameExpr` / `preAlts` / `nameExprBase` | ArgMax/ArgMin atom-only; Max/Min/Sup/Inf fuse scope like Expect |

ArgMax policy: path atom is `ArgMax` / `ArgMin` only — do **not** CamelCase-fuse body into `GetArgMaxProbCond` / `ArgMaxProbCond`. ProbCond / Mul / Prod remain separate segments (`ArgMax_ProbCond` underscore join).
`pathChoices` on the AST may emit `ArgMaxProb`; lemmaPath naming for imply of-houses keeps the underscore style above.

