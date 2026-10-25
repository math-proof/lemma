/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/Digits.lean -/

import Mathlib.NumberTheory.Padics.RingHoms
import Def.NumberTheory.Padics.Digits.Part2
set_option autoImplicit false

/-!
# Digits of p-adic integers

This file defines the digits of a p-adic integer from consecutive `PadicInt.appr` values and
proves the one-step and finite-sum reconstruction formulas.
-/


namespace PadicInt

variable {p : Nat} [hp : Fact p.Prime]

/-- Value bridge between the bundled expansion and the raw digit. -/
@[simp] theorem padicExpansion_val (a : ℤ_[p]) (n : Nat) :
    (padicExpansion a n).val = padicDigit a n := rfl

end PadicInt
