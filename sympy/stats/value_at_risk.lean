import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max
import sympy.stats.quantile

/-!
# Value at risk

Ported from MDPLib `MDPLib/Risk/VaR.lean` (namespace `Risk`).

MDPLib bundles the risk level as `α : RiskLevel R = {α // 0 ≤ α ∧ α < 1}`; here `α : ℝ` is
plain and the lemmas carry the hypotheses `0 ≤ α` and `α < 1` where they are needed.

* `IsVaR μ X α v`: `v` is the greatest lower bound on an `α`-quantile,
  `IsGreatest (quantileLower μ X α) v`.
* `IsVaRQuantile μ X α v`: `v` is the greatest `α`-quantile, `IsGreatest (quantile μ X α) v`
  (MDPLib's `Statistic.IsGreatestQuantile` is the same predicate).
* `finVaR μ X α`: on a finite sample space, the largest value `t` of `X` with
  `ℙ[X < t] ≤ α` (`0` if there is none, which cannot happen for `0 ≤ α`).
-/
open MeasureTheory

universe u

-- v is the value at risk of X at level α (MDPLib: `Risk.IsVaR`)
class IsVaR {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α v : ℝ) : Prop where
  isGreatest : IsGreatest (quantileLower μ X α) v

-- v is the greatest α-quantile of X (MDPLib: `Risk.IsVaRQuantile`, `Statistic.IsGreatestQuantile`)
class IsVaRQuantile {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α v : ℝ) : Prop where
  isGreatest : IsGreatest (quantile μ X α) v

-- value at risk on a finite sample space: max {t ∈ X(Ω) | ℙ[X < t] ≤ α} (MDPLib: `Risk.finVaR`)
noncomputable def finVaR {Ω : Type u} [Fintype Ω] [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (α : ℝ) : ℝ :=
  let S := (Finset.univ.image X).filter fun t => μ.real {ω | X ω < t} ≤ α
  if h : S.Nonempty then S.max' h else 0
