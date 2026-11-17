module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothBoxIndex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.EqRothBoxIndex.of.RothBox
  {m : ℕ} {r : Fin m → ℕ}
-- given
  (j : RothBox r)
  (h : Fin m) :
-- imply
  rothBoxIndex j h = j h := by
-- proof
  simp [rothBoxIndex]


-- updated on 2026-11-13
-- created on 2026-10-21
