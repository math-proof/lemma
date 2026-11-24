module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.RothAuxiliary
public import Lemma.Int.RothFinsuppL1Add.le.AddRothSFinsuppL1
public import Lemma.Int.RothFinsuppL1Neg.eq.RothFinsuppL1
open MathlibExt.NumberTheory.RothAuxiliary
open Int


public section

/--
[rothFinsuppL1_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
