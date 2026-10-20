import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticReciprocityBridgeNeg
open MetaMathlibExt


/--
[jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeNeg.lean)
-/
@[path]
private lemma jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg_eq
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (hneg : D < 0)
  (h0 : D % 4 = 1) :
-- imply
  jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
-- proof
  apply MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg D p hp hp2 hneg h0

/--
[jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeNeg.lean)
-/
@[path]
private lemma jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_eq
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (h0 : D % 4 = 1) :
-- imply
  jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
-- proof
  apply MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four D p hp hp2 h0


-- created on 2026-10-20
