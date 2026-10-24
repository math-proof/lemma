import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ArithmeticFunctions
open DirichletCharacter MulChar


/--
[lem_18_12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem1812.lean)
-/
@[path]
lemma lem_18_12
  {m : ℕ}
  [NeZero m]
  {χ : DirichletCharacter ℂ m} :
-- imply
  ∑ n : ZMod m, χ n ≠ 0 ↔ χ = 1 := by
-- proof
  constructor
  · intro h
    by_contra hχ
    exact h (MulChar.sum_eq_zero_of_ne_one hχ)
  · intro h
    subst h
    classical
    rw [MulChar.sum_one_eq_card_units]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero


-- created on 2026-10-23
