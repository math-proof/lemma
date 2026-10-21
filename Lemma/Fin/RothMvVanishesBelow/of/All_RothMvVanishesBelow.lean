import Mathlib
import Lemma.Fin.RothMvVanishesBelow
import Lemma.Fin.RothMvWeight.ge.Zero.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvVanishesBelow_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} [CommRing R]
  (s : Finset J) (P : J → MvPolynomial (Fin m) R)
  (a : J → ℝ) {x : Fin m → R} {r : Fin m → ℕ}
-- given
  (hP : ∀ j ∈ s, rothMvVanishesBelow (P j) x r (a j)) :
-- imply
  rothMvVanishesBelow (∏ j ∈ s, P j) x r (∑ j ∈ s, a j) := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro i hi
    simp only [Finset.prod_empty, map_one]
    exact (not_lt_of_ge (RothMvWeight.ge.Zero.of.RothMvIndex r i) hi).elim
  | @insert j s hjs ih =>
    rw [Finset.prod_insert hjs, Finset.sum_insert hjs]
    exact RothMvVanishesBelow (hP j (Finset.mem_insert_self _ _))
      (ih fun k hk ↦ hP k (Finset.mem_insert_of_mem hk))


-- created on 2026-10-21
