/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedStirlingFirst.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-- `signedStirlingFirst n k = (-1)^(n-k) s(n,k)` with `s` the unsigned first-kind Stirling
number. -/
def signedStirlingFirst : ℕ → ℕ → ℤ :=
  fun n k => (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

theorem signedStirlingFirst_apply (n k : ℕ) :
    signedStirlingFirst n k = (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ) :=
  rfl

theorem signedStirlingFirst_succ_succ (n k : ℕ) :
    signedStirlingFirst (n + 1) (k + 1) =
      signedStirlingFirst n k - (n : ℤ) * signedStirlingFirst n (k + 1) := by
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

@[simp]
theorem signedStirlingFirst_succ_zero (n : ℕ) : signedStirlingFirst (n + 1) 0 = 0 := by
  have e : signedStirlingFirst (n + 1) 0
      = (-1 : ℤ) ^ (n + 1 - 0) * ((Nat.stirlingFirst (n + 1) 0 : ℕ) : ℤ) := rfl
  have h0 : Nat.stirlingFirst (n + 1) 0 = 0 := Nat.stirlingFirst_succ_zero n
  rw [e, h0]
  simp

@[simp]
theorem signedStirlingFirst_self (n : ℕ) : signedStirlingFirst n n = 1 := by
  have e : signedStirlingFirst n n
      = (-1 : ℤ) ^ (n - n) * ((Nat.stirlingFirst n n : ℕ) : ℤ) := rfl
  rw [e, Nat.sub_self, Nat.stirlingFirst_self]
  simp

theorem signedStirlingFirst_eq_zero_of_lt {n k : ℕ} (h : n < k) : signedStirlingFirst n k = 0 := by
  have e : signedStirlingFirst n k
      = (-1 : ℤ) ^ (n - k) * ((Nat.stirlingFirst n k : ℕ) : ℤ) := rfl
  rw [e, Nat.stirlingFirst_eq_zero_of_lt h]
  simp

end MetaMathlibExt
