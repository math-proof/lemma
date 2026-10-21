import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothPolyL1Add.le.AddRothSPolyL1
import Lemma.Polynomial.RothPolyL1Neg.eq.RothPolyL1
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P Q : ℤ[X]) :
-- imply
  rothPolyL1 (P - Q) ≤ rothPolyL1 P + rothPolyL1 Q := by
-- proof
  rw [sub_eq_add_neg]
  have h := RothPolyL1Add.le.AddRothSPolyL1 P (-Q)
  rw [RothPolyL1Neg.eq.RothPolyL1 Q] at h
  apply h


-- created on 2026-10-21
