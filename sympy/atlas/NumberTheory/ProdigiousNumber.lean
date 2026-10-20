/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProdigiousNumber.lean -/

import Mathlib.Data.Nat.Digits.Defs

namespace MetaMathlibExt

/-- Product of the nonzero base-`b` digits of `n`. -/
def nonzeroDigitProd (b n : ℕ) : ℕ :=
  ((Nat.digits b n).filter (· != 0)).prod

/-- A positive integer `n` is `b`-prodigious iff `2 ≤ b`, `0 < n`,
and `n` is divisible by the product of its nonzero base-`b` digits. -/
def IsProdigious (b n : ℕ) : Prop :=
  2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n

instance instDecidableIsProdigious (b n : ℕ) :
    Decidable (IsProdigious b n) :=
  inferInstanceAs (Decidable (2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n))

end MetaMathlibExt
