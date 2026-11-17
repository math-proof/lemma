/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProdigiousNumber.lean -/

module

public import Mathlib.Data.Nat.Digits.Defs
public import Def.NumberTheory.ProdigiousNumber

@[expose] public section

namespace MetaMathlibExt

instance instDecidableIsProdigious (b n : ℕ) :
    Decidable (IsProdigious b n) :=
  inferInstanceAs (Decidable (2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n))

end MetaMathlibExt
