module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFinsuppL1_apply_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Int.NatAbs.le.RothFinsuppL1
  (f : Finsupp α ℤ)
  (a : α) :
-- imply
  (f a).natAbs ≤ rothFinsuppL1 f := by
-- proof
  classical
  unfold rothFinsuppL1
  if ha : f a = 0 then
    simp [ha]
  else
    apply Finset.single_le_sum (fun b _ ↦ Nat.zero_le (f b).natAbs)
    apply Finsupp.mem_support_iff.mpr ha


-- created on 2026-10-21
-- updated on 2026-11-13
