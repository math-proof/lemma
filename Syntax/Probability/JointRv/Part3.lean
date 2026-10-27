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
import Def.Probability.JointRv.Part5
open MeasureTheory
open scoped ProbabilityTheory


/--
`rv%[μ] x` reads `x` as a random variable on `Ω` (`μ : Measure Ω`), lifting a function applied to
random variables pointwise:

* `rv%[π] (V t (s t))` ↦ `fun ω ↦ V t (s t ω)` (`V t : S → ℝ`, `s : ℕ → Ω → S`);
* `rv%[π] (V t s[t])` ↦ `fun ω ↦ V t (s[t] ω)` (`s : Fun ℕ (Ω → S)`, rebound with `Fun.mk`);
* `rv%[π] (Q t (s t) (a t))` ↦ `fun ω ↦ Q t (s t ω) (a t ω)`;
* `rv%[π] (u X)` ↦ `fun ω ↦ u (X ω)` (`X : Ω → α`).

`x` is first elaborated as is (normal elaboration order, postponement passed through); only if that
throws an error are the local names of type `Ω → α`, `ℕ → Ω → α`, `Fin n → Ω → α`, or
`Fun ℕ (Ω → α)` occurring in `x` rebound to their values at `ω`. If that fails too, the original
error is rethrown. So every `x` that already elaborates (e.g. `fun ω ↦ V t (s t ω)`,
`𝔼[r: π](… | s t)`, `0`) is unchanged.
It is applied to both sides of `=ᵐ[μ]` (see the `macro_rules` below), e.g.
`∀ t, V t (s[t]) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t])`.
-/
syntax (name := liftRV) "rv%[" term "] " term:max : term

