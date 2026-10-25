/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean -/

import Mathlib.NumberTheory.Padics.RingHoms
import Def.NumberTheory.Padics.Digits
set_option autoImplicit false

/-!
# Digits of p-adic integers

This file defines the digits of a p-adic integer from consecutive `PadicInt.appr` values and
proves the one-step and finite-sum reconstruction formulas.
-/


namespace PadicInt

variable {p : Nat} [hp : Fact p.Prime]

/-- Each `p`-adic digit is strictly below `p`, via `dvd_appr_sub_appr`,
`appr_lt`, and primality, exactly as in ATLAS. -/
theorem padicDigit_lt (a : ℤ_[p]) (n : Nat) : padicDigit a n < p := by
  unfold padicDigit
  obtain ⟨k, hk⟩ := dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
  rw [hk, Nat.mul_div_cancel_left _
    (pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))]
  have h_sub_lt : a.appr (n + 1) - a.appr n < p ^ (n + 1) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (appr_lt a (n + 1))
  rw [hk, pow_succ] at h_sub_lt
  exact Nat.lt_of_mul_lt_mul_left h_sub_lt

end PadicInt
