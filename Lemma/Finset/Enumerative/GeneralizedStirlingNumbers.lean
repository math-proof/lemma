import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GeneralizedStirlingNumbers
open MetaMathlibExt


/--
[generalizedStirlingFirst_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedStirlingNumbers.lean)
-/
@[path]
private lemma generalizedStirlingFirst_eq_sum_eq
  {n m : ℕ}
  {x : ℝ}
-- given
  (_h : m ≤ n) :
-- imply
  generalizedStirlingFirst n m x =
      Finset.sum (Finset.range (n - m + 1)) (fun i =>
        (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i) := by
-- proof
  apply MetaMathlibExt.generalizedStirlingFirst_eq_sum n m x _h

/--
[generalizedStirlingSecond_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedStirlingNumbers.lean)
-/
@[path]
private lemma generalizedStirlingSecond_eq_sum_eq
  {n m : ℕ}
  {x : ℝ}
-- given
  (_h : m ≤ n) :
-- imply
  generalizedStirlingSecond n m x =
      Finset.sum (Finset.range (n - m + 1)) (fun i =>
        (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) := by
-- proof
  apply MetaMathlibExt.generalizedStirlingSecond_eq_sum n m x _h


-- created on 2026-10-20
