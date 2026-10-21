import Mathlib
import Lemma.Fin.RothMvL1Add.le.AddRothSMvL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (s : Finset ι) (P : ι → MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 (∑ a ∈ s, P a) ≤ ∑ a ∈ s, rothMvL1 (P a) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [rothMvL1, rothFinsuppL1]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (RothMvL1Add.le.AddRothSMvL1 _ _).trans (Nat.add_le_add_left ih _)


-- created on 2026-10-21
