import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_mem_isClosed_singleton_ne_of_isIrreducible.lean)
-/
@[main]
private lemma main
  {k : Type u} [Field k]
  {X : Scheme.{u}}
  {t : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
  {Z : Set X}
  {x : X}
-- given
  (hZ : IsClosed Z)
  (hZ' : IsIrreducible Z)
  (hxZ : x ∈ Z)
  (hx : IsClosed ({x} : Set X))
  (hne : Z ≠ {x}) :
-- imply
  ∃ x' ∈ Z, IsClosed ({x'} : Set X) ∧ x' ≠ x := by
-- proof
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t
  by_contra h
  push Not at h
  apply hne
  have hsub : Z ∩ closedPoints X ⊆ {x} := by
    rintro y ⟨hyZ, hy⟩
    exact h y hyZ (mem_closedPoints_iff.mp hy)
  have h1 : Z ⊆ {x} := by
    rw [← JacobsonSpace.closure_inter_closedPoints hZ]
    exact (closure_mono hsub).trans hx.closure_subset
  exact Set.Subset.antisymm h1 (Set.singleton_subset_iff.mpr hxZ)


-- created on 2026-10-05
