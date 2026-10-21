import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (c : ℤ) :
-- imply
  rothPolyL1 (C c) = c.natAbs := by
-- proof
  classical
  unfold rothPolyL1 rothFinsuppL1
  rw [toFinsupp_C]
  if hc : c = 0 then
    simp [hc]
  else
    simp [hc]


-- created on 2026-10-21
