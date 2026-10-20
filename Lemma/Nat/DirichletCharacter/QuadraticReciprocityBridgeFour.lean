import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticReciprocityBridgeFour
open MetaMathlibExt


/--
[jacobiSym_four_mul_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacobiSym_four_mul_of_odd_eq
  {m : ℤ}
  {p : ℕ}
-- given
  (hp_odd : Odd p) :
-- imply
  jacobiSym (4 * m) p = jacobiSym m p := by
-- proof
  apply MetaMathlibExt.jacobiSym_four_mul_of_odd m p hp_odd

/--
[jacobiSym_two_mul_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
private lemma jacobiSym_two_mul_of_odd_eq
  {m : ℤ}
  {p : ℕ}
-- given
  (hp_odd : Odd p) :
-- imply
  jacobiSym (2 * m) p = (ZMod.χ₈ p : ℤ) * jacobiSym m p := by
-- proof
  apply MetaMathlibExt.jacobiSym_two_mul_of_odd m p hp_odd


-- created on 2026-10-20
