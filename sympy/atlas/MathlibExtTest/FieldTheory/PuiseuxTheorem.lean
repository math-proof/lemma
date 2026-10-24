/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/PuiseuxTheorem.lean -/


import sympy.atlas.FieldTheory.PuiseuxTheorem
import Lemma.PowerSeries.PuiseuxTheorem


namespace MathlibExtTest.FieldTheory.PuiseuxTheorem

open Polynomial

-- Algebraic closedness supplies a square root of the Hahn monomial `t`.
example {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] :
    ∃ x : HahnSeries Rat K, x ^ 2 = HahnSeries.single 1 1 := by
  let _ : IsAlgClosed (HahnSeries Rat K) := HahnSeries.isAlgClosed_rat
  let t : HahnSeries Rat K := HahnSeries.single 1 1
  have hdegree : ((X ^ 2 - C t) : Polynomial (HahnSeries Rat K)).degree ≠ 0 := by
    rw [degree_X_pow_sub_C (by norm_num)]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root
    ((X ^ 2 - C t) : Polynomial (HahnSeries Rat K)) hdegree
  refine ⟨x, ?_⟩
  apply sub_eq_zero.mp
  simpa [Polynomial.IsRoot] using hx

end MathlibExtTest.FieldTheory.PuiseuxTheorem
