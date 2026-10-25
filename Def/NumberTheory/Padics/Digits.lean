/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean -/

import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

/-!
# Digits of p-adic integers

This file defines the digits of a p-adic integer from consecutive `PadicInt.appr` values and
proves the one-step and finite-sum reconstruction formulas.
-/


namespace PadicInt

variable {p : Nat} [hp : Fact p.Prime]

/-- The `n`-th `p`-adic digit of `a`, from successive approximations. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : Nat) : Nat :=
  (a.appr (n + 1) - a.appr n) / p ^ n

end PadicInt
