import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_dense_setOf_exists_section_of_isAlgClosed.lean)
-/
@[main]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}}
  {f : X ⟶ Spec (.of k)} [LocallyOfFiniteType f] :
-- imply
  Dense {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} := by
-- proof
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hsub : closedPoints X ⊆
      {x : X | ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint k) = x} :=
    fun x hx => ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx,
      pointOfClosedPoint_apply f x hx _⟩
  exact Dense.mono hsub (dense_iff_closure_eq.mpr (closure_closedPoints (X := X)))


-- created on 2026-10-05
