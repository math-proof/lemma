import Mathlib
import sympy.Basic
import Theorem.NumberTheory.DirichletCharacter.QuadraticReciprocityBridgeFour
open MetaMathlibExt


namespace MetaMathlibExt

/--
[jacobiSym_four_mul_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
lemma jacobiSym_four_mul_of_odd
  {m : ℤ}
  {p : ℕ}
-- given
  (hp_odd : Odd p) :
-- imply
  jacobiSym (4 * m) p = jacobiSym m p := by
-- proof
  rw [jacobiSym.mul_left, jacobiSym.at_four hp_odd, one_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[jacobiSym_two_mul_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeFour.lean)
-/
@[path]
lemma jacobiSym_two_mul_of_odd
  {m : ℤ}
  {p : ℕ}
-- given
  (hp_odd : Odd p) :
-- imply
  jacobiSym (2 * m) p = (ZMod.χ₈ p : ℤ) * jacobiSym m p := by
-- proof
  have hsplit : jacobiSym (2 * m) p = jacobiSym 2 p * jacobiSym m p :=
    jacobiSym.mul_left 2 m p
  have hat : jacobiSym (2 : ℤ) p = ZMod.χ₈ (p : ZMod 8) :=
    jacobiSym.at_two hp_odd
  rw [hsplit, hat]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
