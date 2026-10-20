import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticReciprocityThreeOdd
open MetaMathlibExt


/--
[chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityThreeOdd.lean)
-/
@[path]
private lemma chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four_eq
  {D : ℤ}
  {p : ℕ}
-- given
  (hp_odd : Odd p)
  (h0 : D % 4 = 3) :
-- imply
  (ZMod.χ₄ p : ℤ) * jacobiSym (p : ℤ) D.natAbs = kroneckerSym D p := by
-- proof
  apply MetaMathlibExt.chi4_mul_jacobiSym_natAbs_eq_kroneckerSym_of_odd_of_three_mod_four D p hp_odd h0


-- created on 2026-10-20
