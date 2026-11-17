module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_box_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.CardRothBox.eq.Prod_Add_1
  {m : ℕ}
-- given
  (r : Fin m → ℕ) :
-- imply
  Fintype.card (RothBox r) = ∏ h, (r h + 1) := by
-- proof
  simp [RothBox, Fintype.card_pi]


-- updated on 2026-11-13
-- created on 2026-10-21
