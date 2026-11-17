module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFinsuppL1_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Int.RothFinsuppL1_Single.eq.NatAbs
  (a : α)
  (c : ℤ) :
-- imply
  rothFinsuppL1 (Finsupp.single a c) = c.natAbs := by
-- proof
  classical
  if hc : c = 0 then
    simp [hc, rothFinsuppL1]
  else
    simp [rothFinsuppL1, hc]


-- created on 2026-10-21
-- updated on 2026-11-13
