import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothCoordinateBase_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ) :
-- imply
  0 < rothCoordinateBase α := by
-- proof
  unfold rothCoordinateBase
  exact lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)


-- created on 2026-10-21
