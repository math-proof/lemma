import Mathlib
import Lemma.Finset.RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport
open MathlibExt.NumberTheory.RothAuxiliary
open Finset


private lemma rothFinsuppL1_add
  (f g : Finsupp α ℤ) :
-- imply
  rothFinsuppL1 (f + g) ≤ rothFinsuppL1 f + rothFinsuppL1 g := by
-- proof
  classical
  let s := f.support ∪ g.support
  rw [RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport (f := f + g) (s := s) Finsupp.support_add]
  rw [RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport (f := f) (s := s) Finset.subset_union_left]
  rw [RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport (f := g) (s := s) Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  gcongr with a ha
  apply Int.natAbs_add_le

/--
[rothFinsuppL1_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
-- given
  (s : Finset ι)
  (f : ι → Finsupp α ℤ) :
-- imply
  rothFinsuppL1 (∑ a ∈ s, f a) ≤ ∑ a ∈ s, rothFinsuppL1 (f a) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [rothFinsuppL1]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    apply (rothFinsuppL1_add _ _).trans
    apply Nat.add_le_add_left ih


-- created on 2026-10-21
