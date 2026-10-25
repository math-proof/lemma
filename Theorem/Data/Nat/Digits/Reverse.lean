/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Nat/Digits/Reverse.lean -/

import Mathlib.Data.Nat.Digits.Defs
import Def.Data.Nat.Digits.Reverse


namespace Nat

@[simp] theorem reverseDigits_base_zero (n : ℕ) : reverseDigits 0 n = n := by
  cases n <;> simp [reverseDigits]

@[simp] theorem reverseDigits_base_one (n : ℕ) : reverseDigits 1 n = n := by
  simp [reverseDigits, Nat.ofDigits_one]

end Nat
