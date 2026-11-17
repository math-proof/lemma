module

public import Mathlib
public import Theorem.Fin.RothMvVanishesBelow0
public import Theorem.Fin.RothMvVanishesBelowAdd

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvVanishesBelow_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
  {m : ℕ} [CommRing R]
  (s : Finset J) {P : J → MvPolynomial (Fin m) R}
  {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
-- given
  (hP : ∀ j ∈ s, rothMvVanishesBelow (P j) x r t) :
-- imply
  rothMvVanishesBelow (∑ j ∈ s, P j) x r t := by
-- proof
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using RothMvVanishesBelow0 x r t
  | @insert j s hjs ih =>
    rw [Finset.sum_insert hjs]
    exact RothMvVanishesBelowAdd (hP j (Finset.mem_insert_self _ _))
      (ih fun k hk ↦ hP k (Finset.mem_insert_of_mem hk))


-- created on 2026-10-21
