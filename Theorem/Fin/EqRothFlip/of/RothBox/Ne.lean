module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFlip_apply_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.EqRothFlip.of.RothBox.Ne
  {m : ℕ}
  {r : Fin m → ℕ}
  {h k : Fin m}
-- given
  (hhk : k ≠ h)
  (j : RothBox r) :
-- imply
  rothFlip r h j k = j k := by
-- proof
  simp [rothFlip, hhk]


-- updated on 2026-11-13
-- created on 2026-10-21
