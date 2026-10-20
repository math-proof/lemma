import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.AssociatedStirlingSecond
open MetaMathlibExt


/--
[twoAssocStirlingSecond_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingSecond.lean)
-/
@[path]
private lemma twoAssocStirlingSecond_recurrence_eq
  {m k : ℕ}
-- given
  (hk : 1 ≤ k)
  (hkm : k ≤ m) :
-- imply
  twoAssocStirlingSecond (m + 2) k =
    (k : ℤ) * twoAssocStirlingSecond (m + 1) k +
    (m + 1 : ℤ) * twoAssocStirlingSecond m (k - 1) := by
-- proof
  apply MetaMathlibExt.twoAssocStirlingSecond_recurrence m k hk hkm

/--
[twoAssocStirlingSecond_eq_zero_of_lt_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingSecond.lean)
-/
@[path]
private lemma twoAssocStirlingSecond_eq_zero_of_lt_two_mul_eq
  {n k : ℕ}
-- given
  (hnk : n < 2 * k) :
-- imply
  twoAssocStirlingSecond n k = 0 := by
-- proof
  apply MetaMathlibExt.twoAssocStirlingSecond_eq_zero_of_lt_two_mul n k hnk


-- created on 2026-10-20
