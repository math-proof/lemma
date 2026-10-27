import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma ring_lift
  {R A : (CommRingCat : Type (u + 1))} (φ : R ⟶ A) (hφ : φ.hom.FormallySmooth)
  {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
  (τ : R ⟶ CommRingCat.of C) (ξ₀ : A ⟶ CommRingCat.of (C ⧸ J))
  (h : φ ≫ ξ₀ = τ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)) :
    ∃ ψ : A ⟶ CommRingCat.of C, φ ≫ ψ = τ ∧ ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = ξ₀ := by
  let _ : Algebra R A := φ.hom.toAlgebra
  let _ : Algebra R C := τ.hom.toAlgebra
  let _ : Algebra.FormallySmooth R A := hφ
  let g : AlgHom R C (C ⧸ J) := Ideal.Quotient.mkₐ R J
  have hg : Function.Surjective g := Ideal.Quotient.mkₐ_surjective R J
  have hg' : IsNilpotent (RingHom.ker (g : RingHom C (C ⧸ J))) := by
    rwa [Ideal.Quotient.mkₐ_ker]
  have hcomm (r : R) : ξ₀.hom (algebraMap R A r) = algebraMap R (C ⧸ J) r := by
    change ξ₀.hom (φ.hom r) = Ideal.Quotient.mk J (τ.hom r)
    rw [← CommRingCat.comp_apply, h]
    rfl
  let f₀ : AlgHom R A (C ⧸ J) := AlgHom.mk ξ₀.hom hcomm
  let ψ := Algebra.FormallySmooth.liftOfSurjective f₀ g hg hg'
  refine ⟨CommRingCat.ofHom ψ.toRingHom, ?_, ?_⟩
  ·
    ext r
    change ψ (φ.hom r) = τ.hom r
    apply ψ.commutes r
  ·
    ext a
    change g (ψ a) = ξ₀.hom a
    apply Algebra.FormallySmooth.liftOfSurjective_apply f₀ g hg hg' a

private lemma spec_lift
  {R A : (CommRingCat : Type (u + 1))} (φ : R ⟶ A) (hφ : φ.hom.FormallySmooth)
  {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
  (t : Spec (CommRingCat.of C) ⟶ Spec R) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ Spec A)
  (hx₀ : x₀ ≫ Spec.map φ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ x : Spec (CommRingCat.of C) ⟶ Spec A, x ≫ Spec.map φ = t ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ x = x₀ := by
  let τ : R ⟶ CommRingCat.of C := Spec.preimage t
  have hτ : Spec.map τ = t := Spec.map_preimage t
  let ξ₀ : A ⟶ CommRingCat.of (C ⧸ J) := Spec.preimage x₀
  have hξ₀ : Spec.map ξ₀ = x₀ := Spec.map_preimage x₀
  have h : φ ≫ ξ₀ = τ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    rwa [← Spec.map_inj, Spec.map_comp, Spec.map_comp, hξ₀, hτ]
  obtain ⟨ψ, h1, h2⟩ := ring_lift φ hφ J hJ τ ξ₀ h
  refine ⟨Spec.map ψ, ?_, ?_⟩
  · rw [← Spec.map_comp, h1, hτ]
  · rw [← Spec.map_comp, h2, hξ₀]

/--
[AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine.lean)
-/
@[path]
private lemma main
  {X S : (Scheme : Type (u + 1))} [IsAffine X] [IsAffine S] (f : X ⟶ S) [Smooth f]
  {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
  (t : Spec (CommRingCat.of C) ⟶ S) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ X)
  (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ x : Spec (CommRingCat.of C) ⟶ X, x ≫ f = t ∧ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ x = x₀ := by
  have hs : Smooth f := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)] at hs
  have hφ : (f.appTop).hom.FormallySmooth := hs.formallySmooth
  have hx₀' : (x₀ ≫ X.isoSpec.hom) ≫ Spec.map f.appTop = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (t ≫ S.isoSpec.hom) := by
    rw [Category.assoc, Scheme.isoSpec_hom_naturality, ← Category.assoc, hx₀, Category.assoc]
  obtain ⟨y, hy1, hy2⟩ := spec_lift f.appTop hφ J hJ (t ≫ S.isoSpec.hom) (x₀ ≫ X.isoSpec.hom) hx₀'
  refine ⟨y ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc, hy1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [← Category.assoc, hy2, Category.assoc, Iso.hom_inv_id, Category.comp_id]


-- created on 2026-10-20
