/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/Digits/Reverse.lean -/

import Mathlib.Data.Nat.Digits.Defs


namespace Nat

/-- The natural number obtained by reversing the base-`b` digits of `n`.

This is totalized using `Nat.digits`: for the invalid bases `0` and `1`,
Mathlib's conventions make digit reversal the identity. -/
def reverseDigits (b n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits b n).reverse

end Nat
