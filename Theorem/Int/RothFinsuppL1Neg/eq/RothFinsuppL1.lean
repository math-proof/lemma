module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFinsuppL1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Int.RothFinsuppL1Neg.eq.RothFinsuppL1
  (f : Finsupp α ℤ) :
-- imply
  rothFinsuppL1 (-f) = rothFinsuppL1 f := by
-- proof
  classical
  unfold rothFinsuppL1
  rw [Finsupp.support_neg]
  congr with a
  apply Int.natAbs_neg


-- created on 2026-10-21
-- updated on 2026-11-13
