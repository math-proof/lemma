import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_box_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
-- given
  (r : Fin m → ℕ) :
-- imply
  Fintype.card (RothBox r) = ∏ h, (r h + 1) := by
-- proof
  simp [RothBox, Fintype.card_pi]


-- created on 2026-10-21
