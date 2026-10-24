/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LucasSpecialPrime.lean -/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Basic

namespace MetaMathlibExt

/-- Special prime for integral Lucas parameters (concept `jis_term_9fa09acd972f484f5b457a48`):
  `IsLucasSpecialPrime P Q p` means `p` is prime and `p` divides `Int.gcd P Q`.
  Sources: `jis_source_eb765815f14b18e047ccd51b`, `jis_source_e9bb56af5eef26576559cf4c`,
  `jis_source_de2518f50026ac96429ae911`. -/
def IsLucasSpecialPrime (P Q : Int) (p : Nat) : Prop :=
  Nat.Prime p ∧ p ∣ Int.gcd P Q
end MetaMathlibExt
