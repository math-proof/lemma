/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean -/

import Mathlib.NumberTheory.Padics.RingHoms
import Theorem.NumberTheory.Padics.Digits
set_option autoImplicit false

/-!
# Digits of p-adic integers

This file defines the digits of a p-adic integer from consecutive `PadicInt.appr` values and
proves the one-step and finite-sum reconstruction formulas.
-/


namespace PadicInt

variable {p : Nat} [hp : Fact p.Prime]

/-- The `n`-th digit bundled as an element of `Fin p`. -/
noncomputable def padicExpansion (a : ℤ_[p]) (n : Nat) : Fin p :=
  ⟨padicDigit a n, padicDigit_lt a n⟩

end PadicInt
