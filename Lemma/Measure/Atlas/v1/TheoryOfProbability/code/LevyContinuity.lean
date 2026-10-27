import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.TheoryOfProbability.code.LevyContinuity
open MeasureTheory Complex Filter ProbabilityTheory
open scoped Topology BoundedContinuousFunction


namespace ProbabilityTheory

/--
[weakConvergence_iff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/LevyContinuity.lean)
-/
@[path]
lemma weakConvergence_iff_tendsto
  {μs : ℕ → ProbabilityMeasure ℝ}
  {μ : ProbabilityMeasure ℝ} :
-- imply
  WeakConvergence (fun n ↦ (μs n : Measure ℝ)) (μ : Measure ℝ) ↔ Tendsto μs atTop (𝓝 μ) :=
-- proof
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.symm

end ProbabilityTheory

namespace ProbabilityTheory

/--
[levy_continuity_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/LevyContinuity.lean)
-/
@[path]
lemma levy_continuity_backward
  {μs : ℕ → ProbabilityMeasure ℝ}
  {μ : ProbabilityMeasure ℝ}
-- given
  (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (↑(μs n)) t) atTop (𝓝 (charFun (↑μ) t))) :
-- imply
  WeakConvergence (fun n ↦ (μs n : Measure ℝ)) (μ : Measure ℝ) := by
-- proof
  rw [weakConvergence_iff_tendsto]
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simp_rw [← charFun_eq_measureTheory_charFun]
  exact h t

end ProbabilityTheory


-- created on 2026-10-23
