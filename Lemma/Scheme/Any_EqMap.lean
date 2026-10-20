import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq.lean)
-/
@[path]
private lemma main
    {F L : Type u} [Field F] [Field L] [Algebra F L] (H : Subgroup (L ≃ₐ[F] L))
    {X : Scheme.{u}} (x : Spec (CommRingCat.of L) ⟶ X)
    (hx : ∀ σ ∈ H, Spec.map (CommRingCat.ofHom (σ : L ≃ₐ[F] L).toRingEquiv.toRingHom) ≫ x = x) :
    ∃ y : Spec (CommRingCat.of ↥(IntermediateField.fixedField H)) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField H) L)) ≫ y = x := by
  let pt : X := x.base (IsLocalRing.closedPoint L)
  obtain ⟨_, ⟨U', hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ pt) isOpen_univ
  let U : X.Opens := U'
  have hU : IsAffineOpen U := hU
  have hpt : pt ∈ U := hpt
  have hrange : Set.range x.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have : q = IsLocalRing.closedPoint L := Subsingleton.elim _ _
    rw [this]; exact hpt
  let x' : Spec (CommRingCat.of L) ⟶ U := IsOpenImmersion.lift U.ι x hrange
  have hx' : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  let φ : Γ(X, U) ⟶ CommRingCat.of L := Spec.preimage (x' ≫ hU.isoSpec.hom)
  have hφ : Spec.map φ = x' ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hfix : ∀ r : Γ(X, U), φ.hom r ∈ IntermediateField.fixedField H := by
    intro r
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 : Spec.map (CommRingCat.ofHom (σ : L ≃ₐ[F] L).toRingEquiv.toRingHom) ≫ x' = x' := by
      rw [← cancel_mono U.ι, Category.assoc, hx', hx σ hσ]
    have h2 : Spec.map (φ ≫ CommRingCat.ofHom (σ : L ≃ₐ[F] L).toRingEquiv.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ, reassoc_of% h1]
    have h3 := Spec.map_inj.1 h2
    exact congrArg (fun ψ : Γ(X, U) ⟶ CommRingCat.of L => ψ.hom r) h3
  let ψ : Γ(X, U) →+* ↥(IntermediateField.fixedField H) :=
    (φ.hom : Γ(X, U) →+* L).codRestrict (IntermediateField.fixedField H).toSubalgebra.toSubring.toSubsemiring hfix
  have hψ : (algebraMap ↥(IntermediateField.fixedField H) L).comp ψ = φ.hom := RingHom.ext fun r => rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Spec.map_comp_assoc]
  have : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField H) L) = φ := by
    rw [← CommRingCat.ofHom_comp, hψ]; rfl
  rw [this, hφ, Category.assoc, Iso.hom_inv_id_assoc, hx']

-- created on 2026-10-20
