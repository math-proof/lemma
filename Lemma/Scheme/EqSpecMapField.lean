import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_eq_of_specMap_comp_eq_of_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_of_specMap_comp_eq_of_field.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type 1)} {κ κ' : Type} [Field κ] [Field κ'] (i : κ →+* κ')
  (P Q : Spec (CommRingCat.of κ) ⟶ X)
  (h : Spec.map (CommRingCat.ofHom i) ≫ P = Spec.map (CommRingCat.ofHom i) ≫ Q) :
  -- imply
  P = Q := by
  -- proof
  obtain ⟨⟨xP, φP⟩, rfl⟩ := (Scheme.SpecToEquivOfField κ X).symm.surjective P
  obtain ⟨⟨xQ, φQ⟩, rfl⟩ := (Scheme.SpecToEquivOfField κ X).symm.surjective Q
  have key : ∀ (x : ↥X) (φ : X.residueField x ⟶ CommRingCat.of κ),
      Spec.map (CommRingCat.ofHom i) ≫ (Scheme.SpecToEquivOfField κ X).symm ⟨x, φ⟩ =
        (Scheme.SpecToEquivOfField κ' X).symm ⟨x, φ ≫ CommRingCat.ofHom i⟩ := by
    intro x φ
    show Spec.map (CommRingCat.ofHom i) ≫ (Spec.map φ ≫ X.fromSpecResidueField x) =
      Spec.map (φ ≫ CommRingCat.ofHom i) ≫ X.fromSpecResidueField x
    rw [Spec.map_comp, Category.assoc]
  rw [key, key] at h
  have h2 := (Scheme.SpecToEquivOfField κ' X).symm.injective h
  rw [Scheme.SpecToEquivOfField_eq_iff] at h2
  obtain ⟨hx, hφ⟩ := h2
  dsimp at hx
  subst hx
  congr 1
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨rfl, ?_⟩
  let _ : Mono (CommRingCat.ofHom i) := ConcreteCategory.mono_of_injective _ i.injective
  rw [← cancel_mono (CommRingCat.ofHom i)]
  simpa using hφ


-- created on 2026-10-20
