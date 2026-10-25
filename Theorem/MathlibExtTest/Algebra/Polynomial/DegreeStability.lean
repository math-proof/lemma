/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/DegreeStability.lean -/


import Lemma.Polynomial.DegreeStability
import Mathlib.Algebra.Polynomial.Monic


namespace Polynomial

variable {K : Type*} [Ring K] [Nontrivial K]

-- Generic API: the degree-stability theorem applies to any pair of monics.
example (v : AbsoluteValue K ℝ) (f g : Polynomial K)
    (hf : f.Monic) (hg : g.Monic) (h : l1Norm v (f - g) < 1) :
    f.natDegree = g.natDegree :=
  natDegree_eq_of_monic_of_l1Norm_sub_lt_one v hf hg h

-- Concrete monic degree-one case over `ℝ`.
example : (X : Polynomial ℝ).natDegree
    = (X + C (1 / 2 : ℝ)).natDegree := by
  apply natDegree_eq_of_monic_of_l1Norm_sub_lt_one
    (AbsoluteValue.abs : AbsoluteValue ℝ ℝ) monic_X (monic_X_add_C _) _
  have hsub : (X : Polynomial ℝ) - (X + C (1 / 2 : ℝ)) = -(C (1 / 2 : ℝ)) := by
    ring
  rw [hsub, l1Norm_def]
  simp only [support_neg, coeff_neg, map_neg_eq_map, AbsoluteValue.abs_apply]
  norm_num

end Polynomial
