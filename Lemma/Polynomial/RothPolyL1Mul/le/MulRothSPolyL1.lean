import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


private lemma finsuppL1_single
  {α : Type*}
  (a : α)
  (c : ℤ) :
    rothFinsuppL1 (Finsupp.single a c) = c.natAbs := by
  classical
  if hc : c = 0 then
    simp [hc, rothFinsuppL1]
  else
    simp [rothFinsuppL1, hc]

private lemma finsuppL1_add
  {α : Type*}
  (f g : Finsupp α ℤ) :
    rothFinsuppL1 (f + g) ≤ rothFinsuppL1 f + rothFinsuppL1 g := by
  classical
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

private lemma finsuppL1_finset_sum
  {α ι : Type*}
  (s : Finset ι)
  (f : ι → Finsupp α ℤ) :
    rothFinsuppL1 (∑ a ∈ s, f a) ≤ ∑ a ∈ s, rothFinsuppL1 (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [rothFinsuppL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      apply (finsuppL1_add (f a) (∑ x ∈ s, f x)).trans
      apply Nat.add_le_add_left ih

private lemma addMonoidAlgebraL1_mul
  {M : Type*} [Add M]
  (f g : AddMonoidAlgebra ℤ M) :
    rothFinsuppL1 (f * g).coeff ≤
      rothFinsuppL1 f.coeff * rothFinsuppL1 g.coeff := by
  classical
  rw [AddMonoidAlgebra.mul_def, Finsupp.sum, AddMonoidAlgebra.coeff_sum]
  calc
    _ ≤ ∑ a ∈ f.coeff.support,
          rothFinsuppL1 ((g.coeff.sum fun b d ↦
            AddMonoidAlgebra.single (a + b) (f.coeff a * d)).coeff) :=
      finsuppL1_finset_sum f.coeff.support _
    _ = ∑ a ∈ f.coeff.support,
          rothFinsuppL1 (g.coeff.sum fun b d ↦
            Finsupp.single (a + b) (f.coeff a * d)) := by
      congr with a
      rw [Finsupp.sum, AddMonoidAlgebra.coeff_sum]
      rfl
    _ = ∑ a ∈ f.coeff.support,
          rothFinsuppL1 (∑ b ∈ g.coeff.support,
            Finsupp.single (a + b) (f.coeff a * g.coeff b)) := by
      congr with a
    _ ≤ ∑ a ∈ f.coeff.support, ∑ b ∈ g.coeff.support,
          rothFinsuppL1 (Finsupp.single (a + b) (f.coeff a * g.coeff b)) := by
      gcongr with a _
      apply finsuppL1_finset_sum g.coeff.support _
    _ = ∑ a ∈ f.coeff.support,
          (f.coeff a).natAbs * rothFinsuppL1 g.coeff := by
      congr with a
      simp only [finsuppL1_single, Int.natAbs_mul]
      unfold rothFinsuppL1
      rw [Finset.mul_sum]
    _ = rothFinsuppL1 f.coeff * rothFinsuppL1 g.coeff := by
      unfold rothFinsuppL1
      rw [Finset.sum_mul]

/--
[rothPolyL1_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P Q : ℤ[X]) :
-- imply
  rothPolyL1 (P * Q) ≤ rothPolyL1 P * rothPolyL1 Q := by
-- proof
  unfold rothPolyL1
  rw [toFinsupp_mul]
  apply addMonoidAlgebraL1_mul


-- created on 2026-10-21
