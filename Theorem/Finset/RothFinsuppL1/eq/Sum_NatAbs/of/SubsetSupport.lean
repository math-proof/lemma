module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothFinsuppL1_sum_superset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Finset.RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport
  {f : Finsupp α ℤ}
  {s : Finset α}
-- given
  (hfs : f.support ⊆ s) :
-- imply
  rothFinsuppL1 f = ∑ a ∈ s, (f a).natAbs := by
-- proof
  unfold rothFinsuppL1
  apply Finset.sum_subset hfs
  intro a ha hnot
  rw [Finsupp.notMem_support_iff.mp hnot]
  simp


-- created on 2026-10-21
-- updated on 2026-11-13
