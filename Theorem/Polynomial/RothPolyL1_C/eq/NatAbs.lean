module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary
public import Def.NumberTheory.RothAuxiliary.Part2

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Polynomial.RothPolyL1_C.eq.NatAbs
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
-- updated on 2026-11-13
