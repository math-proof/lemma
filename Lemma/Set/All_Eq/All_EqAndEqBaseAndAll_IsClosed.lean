import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_base_closedPoint_eq_and_exists_base_closedPoint_eq_and_isClosed_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {κ : Type u} [Field κ] [IsAlgClosed κ]
  {Y : Scheme.{u}}
  {f : Y ⟶ Spec (CommRingCat.of κ)} [LocallyOfFiniteType f] :
-- imply
  (∀ (y y' : Spec (CommRingCat.of κ) ⟶ Y), y ≫ f = 𝟙 _ → y' ≫ f = 𝟙 _ →
        y.base (IsLocalRing.closedPoint κ) = y'.base (IsLocalRing.closedPoint κ) → y = y') ∧
    (∀ q : Y, IsClosed ({q} : Set Y) →
        ∃ y : Spec (CommRingCat.of κ) ⟶ Y, y ≫ f = 𝟙 _ ∧ y.base (IsLocalRing.closedPoint κ) = q) ∧
    (Finite Y → ∀ q : Y, IsClosed ({q} : Set Y)) := by
-- proof
  refine ⟨?_, ?_, ?_⟩
  · intro y y' hy hy' h
    exact ext_of_apply_closedPoint_eq f hy hy' h
  · intro q hq
    exact ⟨pointOfClosedPoint f q hq, pointOfClosedPoint_comp f q hq,
      pointOfClosedPoint_apply f q hq _⟩
  · intro hY q
    have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace f
    have : Finite Y := hY
    exact isClosed_discrete _


-- created on 2026-10-05
