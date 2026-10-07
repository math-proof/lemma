import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_forall_comp_eq_of_dense_of_isReduced.lean)
-/

private lemma  epi_specMap_of_field {κ k : Type u} [Field κ] [Field k] (φ : CommRingCat.of κ ⟶ CommRingCat.of k) :
    Epi (Spec.map φ) := by
  have : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let : Algebra κ k := φ.hom.toAlgebra
    show Module.Flat κ k
    infer_instance
  have : Surjective (Spec.map φ) := ⟨fun p => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _
@[main]
private lemma main
  {X Y S : Scheme.{u}} [IsReduced X]
  {F G : X ⟶ Y}
  {i : Y ⟶ S} [IsSeparated i]
  {D : Set ↥X}
-- given
  (hFG : F ≫ i = G ≫ i)
  (hD : Dense D)
  (h : ∀ x ∈ D, ∃ (k : Type u) (_ : Field k) (y : Spec (CommRingCat.of k) ⟶ X), x ∈ Set.range y.base ∧ y ≫ F = y ≫ G) :
-- imply
  F = G := by
-- proof
  refine AlgebraicGeometry.ext_of_fromSpecResidueField_eq F G i D hD (fun x hx => ?_) hFG
  obtain ⟨k, _, y, ⟨p, rfl⟩, hy⟩ := h x hx
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  have := epi_specMap_of_field (X.descResidueField (Scheme.stalkClosedPointTo y))
  rw [← cancel_epi (Spec.map (X.descResidueField (Scheme.stalkClosedPointTo y))), ← Category.assoc, ← Category.assoc,
    X.descResidueField_stalkClosedPointTo_fromSpecResidueField k y]
  exact hy


-- created on 2026-10-05
