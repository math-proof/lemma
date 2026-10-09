import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.L1Norm

open Polynomial

/--
[l1Norm_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
private lemma l1Norm_def_eq
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) (p : Polynomial K) :
-- imply
  l1Norm v p = ∑ i ∈ p.support, v (p.coeff i) := by
-- proof
  apply l1Norm_def


/--
[l1Norm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
private lemma l1Norm_zero_eq
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) :
-- imply
  l1Norm v (0 : Polynomial K) = 0 := by
-- proof
  apply l1Norm_zero


/--
[l1Norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
private lemma l1Norm_nonneg_eq
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) (p : Polynomial K) :
-- imply
  0 ≤ l1Norm v p := by
-- proof
  apply l1Norm_nonneg


/--
[l1Norm_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
private lemma l1Norm_eq_sum_range_eq
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) (p : Polynomial K) :
-- imply
  l1Norm v p = ∑ i ∈ Finset.range (p.natDegree + 1), v (p.coeff i) := by
-- proof
  apply l1Norm_eq_sum_range


/--
[l1Norm_eq_sum_range_add_one_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
private lemma l1Norm_eq_sum_range_add_one_of_monic_eq
  [Semiring K] [Nontrivial K]
-- given
  (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
-- imply
  l1Norm v f = (∑ i ∈ Finset.range f.natDegree, v (f.coeff i)) + 1 := by
-- proof
  apply l1Norm_eq_sum_range_add_one_of_monic
  exact hf


/--
[one_le_l1Norm_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
private lemma one_le_l1Norm_of_monic_eq
  [Semiring K] [Nontrivial K]
-- given
  (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
-- imply
  1 ≤ l1Norm v f := by
-- proof
  apply one_le_l1Norm_of_monic
  exact hf


-- created on 2026-10-09
