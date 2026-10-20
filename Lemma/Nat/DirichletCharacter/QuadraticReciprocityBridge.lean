import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticReciprocityBridge
open MetaMathlibExt


/--
[jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridge.lean)
-/
@[path]
private lemma jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos_eq
  {D : ℤ}
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2)
  (hpos : 0 < D)
  (h0 : D % 4 = 1) :
-- imply
  jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
-- proof
  apply MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_pos D p hp hp2 hpos h0


-- created on 2026-10-20
