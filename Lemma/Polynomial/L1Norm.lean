import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.Polynomial.L1Norm
open Polynomial

namespace Polynomial

/--
[l1Norm_def](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
lemma l1Norm_def
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) (p : Polynomial K) :
-- imply
  l1Norm v p = ∑ i ∈ p.support, v (p.coeff i) :=
-- proof
  rfl

end Polynomial

namespace Polynomial

/--
[l1Norm_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
lemma l1Norm_eq_sum_range
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) (p : Polynomial K) :
-- imply
  l1Norm v p = ∑ i ∈ Finset.range (p.natDegree + 1), v (p.coeff i) := by
-- proof
  rw [l1Norm_def]
  apply Finset.sum_subset supp_subset_range_natDegree_succ
  intro i _ hi
  rw [Polynomial.mem_support_iff, not_not] at hi
  rw [hi, map_zero]

end Polynomial

namespace Polynomial

/--
[l1Norm_eq_sum_range_add_one_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
lemma l1Norm_eq_sum_range_add_one_of_monic
  [Semiring K] [Nontrivial K]
-- given
  (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
-- imply
  l1Norm v f = (∑ i ∈ Finset.range f.natDegree, v (f.coeff i)) + 1 := by
-- proof
  rw [l1Norm_eq_sum_range, Finset.sum_range_succ, coeff_natDegree,
    hf.leadingCoeff, map_one v]
  exact hf

end Polynomial

namespace Polynomial

/--
[one_le_l1Norm_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
lemma one_le_l1Norm_of_monic
  [Semiring K] [Nontrivial K]
-- given
  (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
-- imply
  1 ≤ l1Norm v f := by
-- proof
  have h1 : v (f.coeff f.natDegree) = 1 := by
    rw [coeff_natDegree, hf.leadingCoeff, map_one v]
  rw [l1Norm_eq_sum_range, ← h1]
  exact Finset.single_le_sum (fun i _ ↦ v.nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_self _))
end Polynomial
  exact hf

/--
[l1Norm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
lemma l1Norm_zero
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) :
-- imply
  l1Norm v (0 : Polynomial K) = 0 := by
-- proof
  simp [l1Norm]

namespace Polynomial

/--
[l1Norm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/L1Norm.lean)
-/
@[path]
lemma l1Norm_nonneg
  [Semiring K]
-- given
  (v : AbsoluteValue K ℝ) (p : Polynomial K) :
-- imply
  0 ≤ l1Norm v p := by
-- proof
  rw [l1Norm_def]
  exact Finset.sum_nonneg fun i _ ↦ v.nonneg _

end Polynomial

-- created on 2026-10-09
-- updated on 2026-10-26
