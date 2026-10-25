/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ProdigiousNumber.lean -/

import Mathlib.Data.Nat.Digits.Defs
import Def.NumberTheory.ProdigiousNumber


namespace MetaMathlibExt

instance instDecidableIsProdigious (b n : ℕ) :
    Decidable (IsProdigious b n) :=
  inferInstanceAs (Decidable (2 ≤ b ∧ 0 < n ∧ nonzeroDigitProd b n ∣ n))

end MetaMathlibExt
