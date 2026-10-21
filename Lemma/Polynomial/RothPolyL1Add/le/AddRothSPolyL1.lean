import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P Q : ℤ[X]) :
-- imply
  rothPolyL1 (P + Q) ≤ rothPolyL1 P + rothPolyL1 Q := by
-- proof
  classical
  unfold rothPolyL1
  rw [toFinsupp_add]
  let f := P.toFinsupp.coeff
  let g := Q.toFinsupp.coeff
  change rothFinsuppL1 (f + g) ≤ rothFinsuppL1 f + rothFinsuppL1 g
  let s := f.support ∪ g.support
  have hsum : rothFinsuppL1 (f + g) = ∑ a ∈ s, ((f + g) a).natAbs := by
    unfold rothFinsuppL1
    apply Finset.sum_subset Finsupp.support_add
    intro a _ hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp
  have hf : rothFinsuppL1 f = ∑ a ∈ s, (f a).natAbs := by
    unfold rothFinsuppL1
    apply Finset.sum_subset Finset.subset_union_left
    intro a _ hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp
  have hg : rothFinsuppL1 g = ∑ a ∈ s, (g a).natAbs := by
    unfold rothFinsuppL1
    apply Finset.sum_subset Finset.subset_union_right
    intro a _ hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp
  rw [hsum, hf, hg, ← Finset.sum_add_distrib]
  gcongr with a _
  apply Int.natAbs_add_le


-- created on 2026-10-21
