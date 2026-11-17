module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothRidoutComplement_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
  {m : ℕ}
  (r : Fin m → ℕ) (i : RothMvIndex m) (h : Fin m) :
-- imply
  rothRidoutComplement r i h = r h - i h := by
-- proof
  simp [rothRidoutComplement]


-- updated on 2026-11-13
-- created on 2026-10-21
