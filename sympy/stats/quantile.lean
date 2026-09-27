import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Bounds.Basic

/-!
# Quantiles of a real random variable

Ported from MDPLib `MDPLib/Probability/Quantile.lean` (namespace `Statistic`).

MDPLib works with its own finite distributions `Findist R Ω` and Boolean random variables
`X ≤ᵣ q`; here the distribution is a Mathlib measure `μ : Measure Ω` (a probability measure
in all lemmas) and events are sets, so `ℙ[X ≤ᵣ q // P]` becomes `μ.real {ω | X ω ≤ q}`.

* `IsQuantile μ X α q`: `α ≤ ℙ[X ≤ q]` and `1 - α ≤ ℙ[q ≤ X]`.
* `IsQuantileLower μ X α q`: `1 - α ≤ ℙ[q ≤ X]` (a lower bound on an `α`-quantile).
* `quantile μ X α`, `quantileLower μ X α`: the sets of such `q`.

MDPLib's `IsGreatestQuantile P X α q` / `IsLeastQuantile P X α q` are Mathlib's
`IsGreatest (quantile μ X α) q` / `IsLeast (quantile μ X α) q`.
-/
open MeasureTheory

universe u

-- q is an α-quantile of X under μ (MDPLib: `Statistic.IsQuantile`)
class IsQuantile {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α q : ℝ) : Prop where
  le_prob_le : α ≤ μ.real {ω | X ω ≤ q}
  le_prob_ge : 1 - α ≤ μ.real {ω | q ≤ X ω}

-- q is a lower bound on an α-quantile of X under μ (MDPLib: `Statistic.IsQuantileLower`)
class IsQuantileLower {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α q : ℝ) : Prop where
  le_prob_ge : 1 - α ≤ μ.real {ω | q ≤ X ω}

-- the set of α-quantiles of X under μ (MDPLib: `Statistic.quantile`)
def quantile {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) : Set ℝ :=
  {q | IsQuantile μ X α q}

-- the set of lower bounds on an α-quantile of X under μ (MDPLib: `Statistic.quantileLower`)
def quantileLower {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) : Set ℝ :=
  {q | IsQuantileLower μ X α q}
