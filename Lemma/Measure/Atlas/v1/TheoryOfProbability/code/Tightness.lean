import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.Tightness
open MeasureTheory Set MeasureTheory.Measure


namespace MeasureTheory.Measure

/--
[IsTightFamilyReal.isTightFamily](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Tightness.lean)
-/
@[path]
lemma IsTightFamilyReal.isTightFamily
  {μ : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)]
-- given
  (h : IsTightFamilyReal μ) :
-- imply
  IsTightFamily μ := by
-- proof
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨Set.Icc (-M) M, isCompact_Icc, hM⟩

end MeasureTheory.Measure

namespace MeasureTheory.Measure

/--
[IsTightFamily.isTightFamilyReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/Tightness.lean)
-/
@[path]
lemma IsTightFamily.isTightFamilyReal
  {μ : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)]
-- given
  (h : IsTightFamily μ) :
-- imply
  IsTightFamilyReal μ := by
-- proof
  intro ε hε
  obtain ⟨K, hK_compact, hK_meas⟩ := h ε hε
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK_compact.isBounded
  refine ⟨r, fun i => ?_⟩
  calc (1 : ENNReal) - ε ≤ μ i K := hK_meas i
    _ ≤ μ i (Set.Icc (-r) r) := by
      rw [← Real.closedBall_zero_eq_Icc]
      exact measure_mono hr

end MeasureTheory.Measure


-- created on 2026-10-23
