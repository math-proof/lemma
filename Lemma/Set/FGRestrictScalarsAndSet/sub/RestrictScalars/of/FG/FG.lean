import Mathlib
import sympy.Basic


/--
[Subalgebra_fg_restrictScalars_and_le_of_fg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subalgebra_fg_restrictScalars_and_le_of_fg.lean)
-/
@[path]
private lemma main
  {A₀ A : Type u} [CommRing A₀] [CommRing A] [Algebra A₀ A]
  {T : Subalgebra A₀ A}
  {T' : Subalgebra ↥T A}
-- given
  (hT : T.FG)
  (hT' : T'.FG) :
-- imply
  (T'.restrictScalars A₀).FG ∧ (T : Set A) ⊆ (T'.restrictScalars A₀ : Set A) := by
-- proof
  classical
  obtain ⟨s, rfl⟩ := hT
  obtain ⟨t, rfl⟩ := hT'
  have key : (Algebra.adjoin (↥(Algebra.adjoin A₀ (↑s : Set A))) (↑t : Set A)).restrictScalars A₀ =
      Algebra.adjoin A₀ ((↑s : Set A) ∪ ↑t) :=
    (Algebra.adjoin_union_eq_adjoin_adjoin A₀ (↑s : Set A) ↑t).symm
  refine ⟨⟨s ∪ t, ?_⟩, ?_⟩
  · rw [key, Finset.coe_union]
  · rw [key]
    exact Algebra.adjoin_mono Set.subset_union_left


-- created on 2026-10-05
