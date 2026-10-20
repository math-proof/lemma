import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FermatQuotient
open Int


/--
[fermatQuotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatQuotient.lean)
-/
@[path]
private lemma fermatQuotient_eq_eq
  {p : ℕ}
  {a : ℤ}
-- given
  (hp : Nat.Prime p)
  (ha : IsCoprime a (p : ℤ)) :
-- imply
  fermatQuotient p hp a ha = (a ^ (p - 1) - 1) / (p : ℤ) := by
-- proof
  apply Int.fermatQuotient_eq p hp a ha

/--
[natCast_mul_fermatQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FermatQuotient.lean)
-/
@[path]
private lemma natCast_mul_fermatQuotient_eq
  {p : ℕ}
  {a : ℤ}
-- given
  (hp : Nat.Prime p)
  (ha : IsCoprime a (p : ℤ)) :
-- imply
  (p : ℤ) * fermatQuotient p hp a ha = a ^ (p - 1) - 1 := by
-- proof
  apply Int.natCast_mul_fermatQuotient p hp a ha


-- created on 2026-10-20
