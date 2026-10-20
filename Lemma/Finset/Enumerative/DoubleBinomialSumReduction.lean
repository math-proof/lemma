import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.DoubleBinomialSumReduction
open MetaMathlibExt


/--
[double_binomial_sum_eq_single_binomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DoubleBinomialSumReduction.lean)
-/
@[path]
private lemma double_binomial_sum_eq_single_binomial_sum_eq
  {β m n : ℕ} :
-- imply
  Finset.sum (Finset.range (2 * m + 1)) (fun i =>
    Finset.sum (Finset.range (2 * n + 1)) (fun j =>
    Nat.choose (2 * m) i * Nat.choose (2 * n) j *
    Int.natAbs ((i : ℤ) - (m : ℤ) - ((j : ℤ) - (n : ℤ))) ^ β)) =
    Finset.sum (Finset.range (2 * (m + n) + 1)) (fun k =>
    Nat.choose (2 * (m + n)) k *
    Int.natAbs ((k : ℤ) - (m : ℤ) - (n : ℤ)) ^ β) := by
-- proof
  apply MetaMathlibExt.double_binomial_sum_eq_single_binomial_sum β m n


-- created on 2026-10-20
