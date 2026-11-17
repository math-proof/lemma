module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFlip_apply_same](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.GetRothFlip.eq.Sub.of.RothBox
  {m : ℕ}
-- given
  (r : Fin m → ℕ)
  (h : Fin m)
  (j : RothBox r) :
-- imply
  ((rothFlip r h j) h : ℕ) = r h - j h := by
-- proof
  simp [rothFlip]


-- updated on 2026-11-13
-- created on 2026-10-21
