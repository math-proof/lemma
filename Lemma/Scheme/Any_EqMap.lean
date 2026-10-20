import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq.lean)
-/
@[path]
private lemma main
  {F L : Type u} [Field F] [Field L] [Algebra F L] (H : Subgroup (AlgEquiv F L L))
  {X : (Scheme : Type (u + 1))} (x : Spec (CommRingCat.of L) ⟶ X)
  (hx : ∀ σ ∈ H, Spec.map (CommRingCat.ofHom (σ : AlgEquiv F L L).toRingEquiv.toRingHom) ≫ x = x) :
  -- imply
  ∃ y : Spec (CommRingCat.of ↥(IntermediateField.fixedField H)) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField H) L)) ≫ y = x := by
  -- proof
  let pt : X := x.base (closedPoint L)
  obtain ⟨_, ⟨U', hU, rfl⟩, hpt, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ pt) isOpen_univ
  let U : X.Opens := U'
  have hU : IsAffineOpen U := hU
  have hpt : pt ∈ U := hpt
  have hrange : Set.range x.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have : q = closedPoint L := Subsingleton.elim _ _
    rw [this]
    apply hpt
  let x' : Spec (CommRingCat.of L) ⟶ U := IsOpenImmersion.lift U.ι x hrange
  have hx' : x' ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  let φ : X.presheaf.obj (Opposite.op U) ⟶ CommRingCat.of L := Spec.preimage (x' ≫ hU.isoSpec.hom)
  have hφ : Spec.map φ = x' ≫ hU.isoSpec.hom := Spec.map_preimage _
  have hfix : ∀ r : X.presheaf.obj (Opposite.op U), φ.hom r ∈ IntermediateField.fixedField H := by
    intro r
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have h1 : Spec.map (CommRingCat.ofHom (σ : AlgEquiv F L L).toRingEquiv.toRingHom) ≫ x' = x' := by
      rw [← cancel_mono U.ι, Category.assoc, hx', hx σ hσ]
    have h2 : Spec.map (φ ≫ CommRingCat.ofHom (σ : AlgEquiv F L L).toRingEquiv.toRingHom) = Spec.map φ := by
      rw [Spec.map_comp, hφ]
      rw [← Category.assoc, h1]
    refine congrArg (fun ψ : X.presheaf.obj (Opposite.op U) ⟶ CommRingCat.of L => ψ.hom r) (Spec.map_inj.1 h2)
  let ψ : X.presheaf.obj (Opposite.op U) →+* ↥(IntermediateField.fixedField H) :=
    (φ.hom : X.presheaf.obj (Opposite.op U) →+* L).codRestrict (IntermediateField.fixedField H).toSubalgebra.toSubring.toSubsemiring hfix
  have hψ : (algebraMap ↥(IntermediateField.fixedField H) L).comp ψ = φ.hom := RingHom.ext fun r => rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Spec.map_comp_assoc]
  have : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap ↥(IntermediateField.fixedField H) L) = φ := by
    rw [← CommRingCat.ofHom_comp, hψ]
    rfl
  rw [this, hφ, Category.assoc, Iso.hom_inv_id_assoc, hx']


-- created on 2026-10-20
