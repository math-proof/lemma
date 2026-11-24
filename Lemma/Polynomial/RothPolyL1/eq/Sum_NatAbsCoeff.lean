module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.NumberTheory.RothAuxiliary
public import Def.NumberTheory.RothAuxiliary.Part2
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


public section

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
-- updated on 2026-11-13
