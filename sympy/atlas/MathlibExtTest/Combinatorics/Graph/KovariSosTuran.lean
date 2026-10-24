/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Graph/KovariSosTuran.lean -/


import Lemma.Finset.Graph.KovariSosTuran

namespace MetaMathlibExt

-- Forbidding one left vertex leaves only the linear error term.
example (m n t : ℕ) (ht : 0 < t) (htn : t ≤ n) :
    (SimpleGraph.zarankiewicz m n 1 t : ℝ) ≤ ((t : ℝ) - 1) * (m : ℝ) := by
  have h := kovari_sos_turan m n 1 t ht (by omega) htn
  have hz : (0 : ℝ) ^ ((t : ℝ)⁻¹) = 0 := Real.zero_rpow (by positivity)
  norm_num at h
  rw [hz] at h
  norm_num at h
  exact h

-- Forbidding one right vertex gives the symmetric linear bound.
example (m n s : ℕ) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    (SimpleGraph.zarankiewicz m n s 1 : ℝ) ≤ ((s : ℝ) - 1) * (n : ℝ) := by
  have h := kovari_sos_turan m n s 1 (by omega) hs hn
  norm_num [Real.rpow_one, Real.rpow_zero] at h
  simpa [mul_assoc] using h

end MetaMathlibExt
