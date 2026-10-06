import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_range_subset_of_closedPoint_mem.lean)
-/

private lemma  AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux {O : Type u} [CommRing O] [IsLocalRing O] {Y : Scheme.{u}}
    (W : Y.Opens) (σ : Spec (CommRingCat.of O) ⟶ Y) (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
    Set.range σ.base ⊆ (W : Set Y) := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map σ.continuous).mem_open W.2 hW
@[main]
private lemma main
  {O : Type u} [CommRing O] [IsLocalRing O]
  {Y : Scheme.{u}}
  {W : Y.Opens}
  {σ : Spec (CommRingCat.of O) ⟶ Y}
-- given
  (hW : σ.base (IsLocalRing.closedPoint O) ∈ W) :
-- imply
  Set.range σ.base ⊆ (W : Set Y) :=
-- proof
  AlgebraicGeometry.Scheme.Hom.range_subset_of_closedPoint_mem_aux W σ hW


-- created on 2026-10-05
