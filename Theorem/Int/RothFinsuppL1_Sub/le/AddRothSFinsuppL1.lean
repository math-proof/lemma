module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary
public import Theorem.Int.RothFinsuppL1Add.le.AddRothSFinsuppL1
public import Theorem.Int.RothFinsuppL1Neg.eq.RothFinsuppL1

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Int


/--
[rothFinsuppL1_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Int.RothFinsuppL1_Sub.le.AddRothSFinsuppL1
  (f g : Finsupp α ℤ) :
-- imply
  rothFinsuppL1 (f - g) ≤ rothFinsuppL1 f + rothFinsuppL1 g := by
-- proof
  rw [sub_eq_add_neg]
  have h := RothFinsuppL1Add.le.AddRothSFinsuppL1 f (-g)
  rw [RothFinsuppL1Neg.eq.RothFinsuppL1 g] at h
  apply h


-- created on 2026-10-21
-- updated on 2026-11-13
