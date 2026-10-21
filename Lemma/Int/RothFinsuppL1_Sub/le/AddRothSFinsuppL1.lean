import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Int.RothFinsuppL1Add.le.AddRothSFinsuppL1
import Lemma.Int.RothFinsuppL1Neg.eq.RothFinsuppL1
open MathlibExt.NumberTheory.RothAuxiliary
open Int


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
