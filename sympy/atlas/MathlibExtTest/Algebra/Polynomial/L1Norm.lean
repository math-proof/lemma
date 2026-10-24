/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/L1Norm.lean -/


import sympy.atlas.Algebra.Polynomial.L1Norm
import Lemma.Polynomial.L1Norm


namespace Polynomial

variable {K : Type*} [Semiring K]

example (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    l1Norm v p = ∑ i ∈ p.support, v (p.coeff i) :=
  l1Norm_def v p

example (v : AbsoluteValue K ℝ) : l1Norm v (0 : Polynomial K) = 0 :=
  l1Norm_zero v

example (v : AbsoluteValue K ℝ) (p : Polynomial K) : 0 ≤ l1Norm v p :=
  l1Norm_nonneg v p

example (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    l1Norm v p = ∑ i ∈ Finset.range (p.natDegree + 1), v (p.coeff i) :=
  l1Norm_eq_sum_range v p

section Monic

variable [Nontrivial K]

example (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
    l1Norm v f = (∑ i ∈ Finset.range f.natDegree, v (f.coeff i)) + 1 :=
  l1Norm_eq_sum_range_add_one_of_monic v f hf

example (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
    1 ≤ l1Norm v f :=
  one_le_l1Norm_of_monic v f hf

end Monic

end Polynomial
