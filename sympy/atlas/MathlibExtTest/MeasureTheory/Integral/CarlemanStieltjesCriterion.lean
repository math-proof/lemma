/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/MeasureTheory/Integral/CarlemanStieltjesCriterion.lean -/


import sympy.atlas.MeasureTheory.Integral.CarlemanStieltjesCriterion
import Lemma.Measure.Integral.CarlemanStieltjesCriterion


open MeasureTheory Set
open scoped BigOperators

namespace MathlibExtTest.MeasureTheory.Integral.CarlemanStieltjesCriterion

-- The zero Dirac mass exercises the degenerate branch of Carleman's criterion.
example : MetaMathlibExt.StieltjesMomentDeterminate (Measure.dirac (0 : ℝ)) := by
  apply MetaMathlibExt.carleman_stieltjes_criterion
  · simp
  · intro k hk
    exact integrable_dirac' ((continuous_abs.comp continuous_id).pow k).stronglyMeasurable
      (by simp)
  · apply ENNReal.tsum_eq_top_of_eq_top
    refine ⟨0, ?_⟩
    norm_num [ProbabilityTheory.moment, ENNReal.zero_rpow_of_neg]

-- Carleman's inequality sends a concrete geometric sequence to a summable sequence.
example : Summable (fun n : ℕ =>
    (∏ k ∈ Finset.range (n + 1), ((1 / 2 : ℝ) ^ k)) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) := by
  apply MetaMathlibExt.summable_geometric_means
  · intro n
    positivity
  · exact summable_geometric_of_norm_lt_one (by norm_num)

end MathlibExtTest.MeasureTheory.Integral.CarlemanStieltjesCriterion
