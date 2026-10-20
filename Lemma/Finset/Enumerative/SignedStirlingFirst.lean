import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.SignedStirlingFirst
open MetaMathlibExt


/--
[signedStirlingFirst_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
private lemma signedStirlingFirst_apply_eq
  {n k : ℕ} :
-- imply
  signedStirlingFirst n k = (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ) := by
-- proof
  apply MetaMathlibExt.signedStirlingFirst_apply n k

/--
[signedStirlingFirst_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
private lemma signedStirlingFirst_succ_succ_eq
  {n k : ℕ} :
-- imply
  signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - (n : ℤ) * signedStirlingFirst n (k + 1) := by
-- proof
  apply MetaMathlibExt.signedStirlingFirst_succ_succ n k

/--
[signedStirlingFirst_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
private lemma signedStirlingFirst_succ_zero_eq
  {n : ℕ} :
-- imply
  signedStirlingFirst (n + 1) 0 = 0 := by
-- proof
  apply MetaMathlibExt.signedStirlingFirst_succ_zero n

/--
[signedStirlingFirst_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
private lemma signedStirlingFirst_self_eq
  {n : ℕ} :
-- imply
  signedStirlingFirst n n = 1 := by
-- proof
  apply MetaMathlibExt.signedStirlingFirst_self n

/--
[signedStirlingFirst_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
private lemma signedStirlingFirst_eq_zero_of_lt_eq
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  signedStirlingFirst n k = 0 := by
-- proof
  apply MetaMathlibExt.signedStirlingFirst_eq_zero_of_lt h


-- created on 2026-10-20
