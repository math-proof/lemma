import Mathlib
import Lemma.Fin.RothDegreeBoundAdd
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothDegreeBound_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} (s : Finset J) {P : J → MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : ∀ j ∈ s, rothDegreeBound (P j) r) :
-- imply
  rothDegreeBound (∑ j ∈ s, P j) r := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [rothDegreeBound]
  | @insert j s hjs ih =>
    rw [Finset.sum_insert hjs]
    apply RothDegreeBoundAdd
    ·
      apply hP j (Finset.mem_insert_self _ _)
    ·
      apply ih
      intro t ht
      apply hP t (Finset.mem_insert_of_mem ht)


-- created on 2026-10-21
