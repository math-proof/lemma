import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.PartitionPolynomialDerivatives
open MetaMathlibExt


/--
[partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomialDerivatives.lean)
-/
@[path]
private lemma partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond_general_eq
  {k d : ℕ}
  {m : ℕ → ℕ}
  {x : ℝ}
-- given
  (hx : x ≠ 0) :
-- imply
  let f : ℝ → ℝ := by
-- proof
  apply MetaMathlibExt.partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond_general k d m x hx

/--
[partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomialDerivatives.lean)
-/
@[path]
private lemma partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond_eq
  {k d : ℕ}
  {m : ℕ → ℕ}
  {x : ℝ}
-- given
  (hk : 0 < k)
  (hm_top : m k ≠ 0)
  (hm_support : ∀ i, m i ≠ 0 → i ∈ Finset.Icc 1 k)
  (hx : x ≠ 0)
  (hd : d ≤ k) :
-- imply
  let f : ℝ → ℝ := by
-- proof
  apply MetaMathlibExt.partitionPolynomial_iteratedDeriv_eq_sum_stirlingSecond k d m hk hm_top hm_support x hx hd


-- created on 2026-10-20
