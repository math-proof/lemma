module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary
public import Def.NumberTheory.RothAuxiliary.Part2

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_X](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.RothPolyL1X.eq.One :
-- imply
  rothPolyL1 (X : ℤ[X]) = 1 := by
-- proof
  unfold rothPolyL1 rothFinsuppL1
  rw [toFinsupp_X]
  simp


-- created on 2026-10-21
-- updated on 2026-11-13
