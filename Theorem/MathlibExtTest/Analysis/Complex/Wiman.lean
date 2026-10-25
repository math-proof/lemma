/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/Wiman.lean -/


import Theorem.Analysis.Complex.Wiman.Filevych
import Lemma.Complex.Wiman.Filevych


namespace Complex

example (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    wimanTerm f (-r) n = wimanTerm f r n := by
  simp

example (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumTerm f (-r) = wimanMaximumTerm f r := by
  simp

example (f : ℂ → ℂ) (r : ℝ) :
    wimanMaximumModulus f (-r) = wimanMaximumModulus f r := by
  simp

example (f : ℂ → ℂ) (r : ℝ) (n : ℕ) : 0 ≤ wimanTerm f r n :=
  wimanTerm_nonneg f r n

example (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) (R : ℝ) :
    ∃ r : ℝ, R < r ∧ wimanMaximumModulus f r ≤
        wimanMaximumTerm f r *
          Real.log (wimanMaximumTerm f r) ^ (2 / 3 : ℝ) :=
  exists_wiman_radius_two_thirds f hf htrans R

end Complex
