import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Def.Probability.SymbolicProbability.Part2
import Theorem.Function
import Syntax.Probability.JointRv.Part4
open MeasureTheory
open scoped ProbabilityTheory


open Lean


/-- Right-nested `JointRandomSymbol` chain of `Expectation.asRV` binders:
`#[x,y,z]` ↦ `JointRandomSymbol (Expectation.asRV x) (JointRandomSymbol (Expectation.asRV y) (Expectation.asRV z))`.
One element returns `Expectation.asRV y` (ordinary RV or flipped process path). -/
partial def Expectation.Macro.mkRestJoint (ys : Array Syntax) : MacroM Term := do
  match ys.toList with
  | [] => Macro.throwError "𝔼[…](…) requires at least one random variable in this slot"
  | [y] =>
    let y : Term := ⟨y⟩
    `(Expectation.asRV $y)
  | y :: rest =>
    let y : Term := ⟨y⟩
    let tail ← Expectation.Macro.mkRestJoint rest.toArray
    `(JointRandomSymbol (Expectation.asRV $y) $tail)

/-- Right-nested `JointRandomSymbol` chain of arbitrary conditioning terms (no `asRV`):
`#[y, z, w]` ↦ `JointRandomSymbol y (JointRandomSymbol z w)`; one term is returned bare. -/
partial def Expectation.Macro.mkJointTerms (ys : Array Syntax) : MacroM Term := do
  match ys.toList with
  | [] => Macro.throwError "𝔼[…](… | …) requires at least one conditioning term"
  | [y] => pure ⟨y⟩
  | y :: rest =>
    let y : Term := ⟨y⟩
    let tail ← Expectation.Macro.mkJointTerms rest.toArray
    `(JointRandomSymbol $y $tail)

/-- Unpack a right-nested product into `let y := nest.1; …; body`.
`rebind[i] = false` skips the `let` for that binder (the body keeps the outer local).
`asFun[i] = true` wraps the value path as `Fun.mk`, so `y[t]` stays `Fun` indexing. -/
partial def Expectation.Macro.unpackRest
    (ys : Array Syntax) (nest : Term) (body : Term) (rebind : Array Bool) (asFun : Array Bool) : MacroM Term := do
  let bind (y : Ident) (rhs : Term) (funProcess : Bool) (body : Term) : MacroM Term :=
    if funProcess then `(let $y := Fun.mk $rhs; $body) else `(let $y := $rhs; $body)
  match ys.toList, rebind.toList, asFun.toList with
  | [], _, _ => pure body
  | [y], r :: _, f :: _ =>
    if r then
      bind ⟨y⟩ nest f body
    else
      pure body
  | y :: rest, r :: rs, f :: fs =>
    let nest2 ← `(Prod.snd $nest)
    let body' ← Expectation.Macro.unpackRest rest.toArray nest2 body rs.toArray fs.toArray
    if r then
      bind ⟨y⟩ (← `(Prod.fst $nest)) f body'
    else
      pure body'
  | _, [], _ => Macro.throwError "𝔼 binder unpack: rebind mask shorter than the binder list"
  | _, _, [] => Macro.throwError "𝔼 binder unpack: Fun mask shorter than the binder list"

/-- The measure term of an `expectMeasure` slot: `f a b` ↦ the application `f a b`. -/
def Expectation.Macro.measure (π : TSyntax `expectMeasure) : MacroM Term :=
  match π with
  | `(expectMeasure| $f:term $[$args:term]*) =>
    if args.isEmpty then pure f else `($f $args*)
  | _ => Macro.throwUnsupported

/-! ### Binder notation `ℙ`

Syntax sugar for pointwise evaluation of the canonical densities `prob` / `condProb`.

* `ℙ[π](x)` / `ℙ[π](x, y, …)` → `Measure.probRA π (JointRandomSymbol …)`
  (= `fun ω ↦ ℙ[π](x = (x ω) ∧ y = (y ω) ∧ …)`), magenta joint RA
* `ℙ[π](x, y | z = z0)` / `ℙ[π](x | y = y0 ∧ z = z0 ∧ …)` → `Measure.probCond …`
  (= `fun ω ↦ ℙ[π](x = (x ω) ∧ y = (y ω) | z = z0 ∧ …)`), magenta given black
  (commas left of `|`; `∧`-chains of `=` on the right)
* `ℙ[π](x, y | z)` / `ℙ[π](x, y | z, w, …)` / `ℙ[π](a t | s t)` → `Measure.probCondRA …`
  (= `fun ω ↦ ℙ[π](x = (x ω) ∧ y = (y ω) | z = (z ω) ∧ …)`), magenta on both sides
  (commas on both sides of `|`; RA slots are `term:51`, so applications like `a t` are allowed)
* `ℙ[π](x = x0)` → `Measure.prob π x x0` (point / black value)
* `ℙ[π](x = x0 ∧ y = y0 ∧ …)` → `Measure.prob π (JointRandomSymbol …) (x0, …)`
* `ℙ[π](x = x0 | y = y0 ∧ …)` → `Measure.condProb π (JointRandomSymbol x …) (x0, …)`
* `ℙ[π](x = x0 ∧ y = y0 | z = z0)` →
  `Measure.condProb π (JointRandomSymbol (JointRandomSymbol x y) z) ((x0, y0), z0)`
* Both sides of `|` accept any nonempty `∧`-chain of fixed observations.
* `ℙ[π](x = x0 | y)` / `ℙ[π](x = x0 | y t)` → `Measure.condProbRA π (x, y) x0`
  (= `fun ω ↦ Measure.condProb π (x, y) (x0, y ω)`), a random expression in `y`.
  Several RAs: `ℙ[π](x = x0 | y, z, …)`; joint left: `ℙ[π](x = x0 ∧ w = w0 | y)`.

**Inside an outer op that threads aliases** (today: `𝔼` binder elaborators via
`desugarProbRA` / `mapChildren`; `𝕍𝕒𝕣`/`ℂ𝕠𝕧` are plain defs, so nested sugar under them
is rewritten only when they sit in such an `𝔼` body): RA forms whose heads are integrated
binders already in scope (`ℙ[π](a t | s t)`, `ℙ[π](a[t] | s[t])`, `ℙ[π](a | s)`, …) are
rewritten to the scalar observation form `ℙ[π]((a₀ t) = (a t) | (s₀ t) = (s t))`
(GetElem `a[t]` / `s[t]` becomes app on both sides of `=` after unpack) with fresh aliases
`a₀ := a` of the outer processes taken before unpack. That is the same scalar as today's
handwritten `let a₀ := a; let s₀ := s` pattern, so `(ℙ[M θ](a t | s t) : ℝ)` and
`(ℙ[M θ](a[t] | s[t]) : ℝ)` work under `𝔼[s, a, …]`. Outside such an outer op, the same
surface stays `probCondRA` (`Ω → ENNReal`).
  Nested conditional expectations use the same alias check via `rewriteNestedExpectRA`:
  `𝔼[r : π](f | s[t], a[t])` under any ancestor that passed aliases becomes
  `𝔼[r : π](f | s₀ t = s t ∧ a₀ t = a t)` (`condEvent` / pointwise). Standalone
  (no outer aliases) `| s[t], a[t]` still elaborates to `Expectation.condSigma`.

Read `=` as “evaluated at” (like `x ↦ x0`), not as an event `{ω | x ω = x0}`.
`∧` packs a joint point; `|` is conditioning (fixed `=` or random arguments).
-/

/-- Right-nested `JointRandomSymbol` chain: `#[x,y,z]` ↦ `JointRandomSymbol x (JointRandomSymbol y z)`. -/
partial def Probability.Macro.mkJointRV (ts : Array Syntax) : MacroM Term := do
  match ts.toList with
  | [] => Macro.throwError "ℙ[π](…) requires at least one factor"
  | [t] => pure ⟨t⟩
  | t :: rest =>
    let t : Term := ⟨t⟩
    let tail ← Probability.Macro.mkJointRV rest.toArray
    `(JointRandomSymbol $t $tail)

/-- Right-nested product of values: `#[a,b,c]` ↦ `(a, (b, c))`. -/
partial def Probability.Macro.mkProd (ts : Array Syntax) : MacroM Term := do
  match ts.toList with
  | [] => Macro.throwError "ℙ[π](…) requires at least one factor"
  | [t] => pure ⟨t⟩
  | t :: rest =>
    let t : Term := ⟨t⟩
    let tail ← Probability.Macro.mkProd rest.toArray
    `(($t, $tail))

