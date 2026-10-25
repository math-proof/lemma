import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.SignedStirlingFirst
open MetaMathlibExt


namespace MetaMathlibExt

/--
[signedStirlingFirst_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
lemma signedStirlingFirst_apply
  {n k : ℕ} :
-- imply
  signedStirlingFirst n k = (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[signedStirlingFirst_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
lemma signedStirlingFirst_succ_succ
  {n k : ℕ} :
-- imply
  signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - (n : ℤ) * signedStirlingFirst n (k + 1) := by
-- proof
  have h1 : n + 1 - (k + 1) = n - k := by omega
  have e1 : signedStirlingFirst (n + 1) (k + 1)
    = (-1 : ℤ) ^ (n + 1 - (k + 1)) * ((Nat.stirlingFirst (n + 1) (k + 1) : ℕ) : ℤ) := rfl
  have e2 : signedStirlingFirst n k
    = (-1 : ℤ) ^ (n - k) * ((Nat.stirlingFirst n k : ℕ) : ℤ) := rfl
  have e3 : signedStirlingFirst n (k + 1)
    = (-1 : ℤ) ^ (n - (k + 1)) * ((Nat.stirlingFirst n (k + 1) : ℕ) : ℤ) := rfl
  rw [e1, e2, e3, h1, Nat.stirlingFirst_succ_succ]
  push_cast
  by_cases h : k + 1 ≤ n
  · have h2 : n - k = (n - (k + 1)) + 1 := by omega
    rw [h2, pow_succ]
    ring
  · have hlt : n < k + 1 := by omega
    rw [Nat.stirlingFirst_eq_zero_of_lt hlt]
    push_cast
    ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[signedStirlingFirst_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
lemma signedStirlingFirst_succ_zero
  {n : ℕ} :
-- imply
  signedStirlingFirst (n + 1) 0 = 0 := by
-- proof
  have e : signedStirlingFirst (n + 1) 0
    = (-1 : ℤ) ^ (n + 1 - 0) * ((Nat.stirlingFirst (n + 1) 0 : ℕ) : ℤ) := rfl
  have h0 : Nat.stirlingFirst (n + 1) 0 = 0 := Nat.stirlingFirst_succ_zero n
  rw [e, h0]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[signedStirlingFirst_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
lemma signedStirlingFirst_self
  {n : ℕ} :
-- imply
  signedStirlingFirst n n = 1 := by
-- proof
  have e : signedStirlingFirst n n
    = (-1 : ℤ) ^ (n - n) * ((Nat.stirlingFirst n n : ℕ) : ℤ) := rfl
  rw [e, Nat.sub_self, Nat.stirlingFirst_self]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[signedStirlingFirst_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean)
-/
@[path]
lemma signedStirlingFirst_eq_zero_of_lt
  {n k : ℕ}
-- given
  (h : n < k) :
-- imply
  signedStirlingFirst n k = 0 := by
-- proof
  have e : signedStirlingFirst n k
    = (-1 : ℤ) ^ (n - k) * ((Nat.stirlingFirst n k : ℕ) : ℤ) := rfl
  rw [e, Nat.stirlingFirst_eq_zero_of_lt h]
  simp

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
