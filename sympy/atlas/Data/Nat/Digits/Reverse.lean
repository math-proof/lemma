/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/Digits/Reverse.lean -/

import Mathlib.Data.Nat.Digits.Defs

namespace Nat

/-- The natural number obtained by reversing the base-`b` digits of `n`.

This is totalized using `Nat.digits`: for the invalid bases `0` and `1`,
Mathlib's conventions make digit reversal the identity. -/
def reverseDigits (b n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits b n).reverse

@[simp] theorem reverseDigits_base_zero (n : ℕ) : reverseDigits 0 n = n := by
  cases n <;> simp [reverseDigits]

@[simp] theorem reverseDigits_base_one (n : ℕ) : reverseDigits 1 n = n := by
  simp [reverseDigits, Nat.ofDigits_one]

end Nat
