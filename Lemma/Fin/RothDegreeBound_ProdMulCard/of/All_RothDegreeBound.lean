import Mathlib
import Lemma.Fin.RothDegreeBound
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothDegreeBound_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} (s : Finset J) {P : J → MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
-- given
  (hP : ∀ j ∈ s, rothDegreeBound (P j) r) :
-- imply
  rothDegreeBound (∏ j ∈ s, P j) (fun h ↦ s.card * r h) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro i hi h
    simp only [Finset.card_empty, zero_mul]
    rw [Finset.prod_empty, MvPolynomial.support_one] at hi
    rw [Finset.mem_singleton.mp hi]
    simp
  | @insert j s hjs ih =>
    rw [Finset.prod_insert hjs]
    have hmul := RothDegreeBound
      (hP j (Finset.mem_insert_self _ _))
      (ih fun t ht ↦ hP t (Finset.mem_insert_of_mem ht))
    simpa [Finset.card_insert_of_notMem hjs, Nat.add_mul, add_comm] using hmul


-- created on 2026-10-21
