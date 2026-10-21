import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main :
-- imply
  rothPolyL1 (X : ℤ[X]) = 1 := by
-- proof
  unfold rothPolyL1 rothFinsuppL1
  rw [toFinsupp_X]
  simp


-- created on 2026-10-21
