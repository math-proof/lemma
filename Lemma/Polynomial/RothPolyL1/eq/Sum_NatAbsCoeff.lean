import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X]) :
-- imply
  rothPolyL1 P = ∑ n ∈ P.support, (P.coeff n).natAbs := by
-- proof
  unfold rothPolyL1 rothFinsuppL1
  rw [support_toFinsupp]
  simp only [toFinsupp_apply]


-- created on 2026-10-21
