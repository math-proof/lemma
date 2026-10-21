import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFinsuppL1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
