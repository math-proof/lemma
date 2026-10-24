/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean -/

import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Digits of p-adic integers

This file defines the digits of a p-adic integer from consecutive `PadicInt.appr` values and
proves the one-step and finite-sum reconstruction formulas.
-/

set_option autoImplicit false

namespace PadicInt

variable {p : Nat} [hp : Fact p.Prime]

/-- The `n`-th `p`-adic digit of `a`, from successive approximations. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : Nat) : Nat :=
  (a.appr (n + 1) - a.appr n) / p ^ n

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

/-- The `n`-th digit bundled as an element of `Fin p`. -/
noncomputable def padicExpansion (a : ℤ_[p]) (n : Nat) : Fin p :=
  ⟨padicDigit a n, padicDigit_lt a n⟩

/-- Value bridge between the bundled expansion and the raw digit. -/
@[simp] theorem padicExpansion_val (a : ℤ_[p]) (n : Nat) :
    (padicExpansion a n).val = padicDigit a n := rfl
end PadicInt
