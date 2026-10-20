import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.WilsonQuotient
open Int


/--
[mul_wilsonQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WilsonQuotient.lean)
-/
@[path]
private lemma mul_wilsonQuotient_eq
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  (p : ℤ) * wilsonQuotient p = (Nat.factorial (p - 1) : ℤ) + 1 := by
-- proof
  apply Int.mul_wilsonQuotient p hp

/--
[factorial_eq_mul_wilsonQuotient_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/WilsonQuotient.lean)
-/
@[path]
private lemma factorial_eq_mul_wilsonQuotient_sub_one_eq
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  (Nat.factorial (p - 1) : ℤ) = (p : ℤ) * wilsonQuotient p - 1 := by
-- proof
  apply Int.factorial_eq_mul_wilsonQuotient_sub_one p hp


-- created on 2026-10-20
