import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.FermatQuotient
open Int


namespace Int

/--
[fermatQuotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatQuotient.lean)
-/
@[path]
lemma fermatQuotient_eq
  {p : ℕ}
  {a : ℤ}
-- given
  (hp : Nat.Prime p)
  (ha : IsCoprime a (p : ℤ)) :
-- imply
  fermatQuotient p hp a ha = (a ^ (p - 1) - 1) / (p : ℤ) :=
-- proof
  rfl

end Int

namespace Int

/--
[natCast_mul_fermatQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatQuotient.lean)
-/
@[path]
lemma natCast_mul_fermatQuotient
  {p : ℕ}
  {a : ℤ}
-- given
  (hp : Nat.Prime p)
  (ha : IsCoprime a (p : ℤ)) :
-- imply
  (p : ℤ) * fermatQuotient p hp a ha = a ^ (p - 1) - 1 := by
-- proof
  unfold fermatQuotient
  exact Int.mul_ediv_cancel' (Int.prime_dvd_pow_sub_one hp ha)

end Int


-- created on 2026-10-20
-- updated on 2026-10-26
