import Mathlib
import Initialize.Tactic.Attr.Basic
open DirichletCharacter MulChar


/--
[cor_18_15](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1815.lean)
-/
@[path]
lemma cor_18_15
  {m : ℕ}
  [NeZero m]
  {χ : DirichletCharacter ℂ m} :
-- imply
  ∑ n : ZMod m, χ n ≠ 0 ↔ χ.conductor = 1 := by
-- proof
  rw [lem_18_12 χ, eq_one_iff_conductor_eq_one (NeZero.ne m)]


-- created on 2026-10-23
