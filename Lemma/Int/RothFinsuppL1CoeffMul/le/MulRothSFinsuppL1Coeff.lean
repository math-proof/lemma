import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Int.RothFinsuppL1_Single.eq.NatAbs
import Lemma.Int.RothFinsuppL1Add.le.AddRothSFinsuppL1
open MathlibExt.NumberTheory.RothAuxiliary
open Int


private lemma finsuppL1_finset_sum
  (s : Finset ι)
  (f : ι → Finsupp α ℤ) :
    rothFinsuppL1 (∑ a ∈ s, f a) ≤ ∑ a ∈ s, rothFinsuppL1 (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [rothFinsuppL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      apply (RothFinsuppL1Add.le.AddRothSFinsuppL1 (f a) (∑ x ∈ s, f x)).trans
      apply Nat.add_le_add_left ih

/--
[rothAddMonoidAlgebraL1_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [Add M]
  (f g : AddMonoidAlgebra ℤ M) :
-- imply
  rothFinsuppL1 (f * g).coeff ≤
    rothFinsuppL1 f.coeff * rothFinsuppL1 g.coeff := by
-- proof
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
      simp only [RothFinsuppL1_Single.eq.NatAbs, Int.natAbs_mul]
      unfold rothFinsuppL1
      rw [Finset.mul_sum]
    _ = rothFinsuppL1 f.coeff * rothFinsuppL1 g.coeff := by
      unfold rothFinsuppL1
      rw [Finset.sum_mul]


-- created on 2026-10-21
