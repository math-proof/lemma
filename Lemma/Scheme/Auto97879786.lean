import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma formallyUnramified_of_isReduced_of_finite (K : Type u) [Field K] [PerfectField K]
    (R : Type u) [CommRing R] [Algebra K R] [Module.Finite K R] [IsReduced R] : Algebra.FormallyUnramified K R := by
  let _ : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : ∀ I : MaximalSpectrum R, Algebra.FormallyUnramified K (R ⧸ I.asIdeal) := by
    intro I
    let _ := I.isMaximal
    let _ : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    exact Algebra.FormallyUnramified.of_isSeparable K _
  let _ : Algebra.FormallyUnramified K (∀ I : MaximalSpectrum R, R ⧸ I.asIdeal) :=
    (Algebra.FormallyUnramified.pi_iff _).mpr this
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi R).restrictScalars K).symm
/--
[AlgebraicGeometry_etale_of_isFinite_of_isReduced_of_perfectField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_etale_of_isFinite_of_isReduced_of_perfectField.lean)
-/
@[path]
private lemma main
    {K : Type u} [Field K] [PerfectField K]
    {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of K)) [IsFinite g] [IsReduced B] : Etale g := by
  let _ : IsAffine B := isAffine_of_isAffineHom g
  let φ : CommRingCat.of K ⟶ Γ(B, ⊤) := Spec.preimage (B.isoSpec.inv ≫ g)
  have hφ : Spec.map φ = B.isoSpec.inv ≫ g := Spec.map_preimage _
  let _ : Algebra K Γ(B, ⊤) := φ.hom.toAlgebra
  let _ : Module.Finite K Γ(B, ⊤) := by
    have h1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact h1
  let _ : Algebra.FormallyUnramified K Γ(B, ⊤) := formallyUnramified_of_isReduced_of_finite K _
  let hFU : FormallyUnramified (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    show Algebra.FormallyUnramified K Γ(B, ⊤)
    infer_instance
  let hFP : LocallyOfFinitePresentation (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.FinitePresentation.of_finiteType.mp (show φ.hom.FiniteType from
      show Algebra.FiniteType K Γ(B, ⊤) from inferInstance)
  have hE : Etale (Spec.map φ) := Etale.of_formallyUnramified_of_flat _
  have : g = B.isoSpec.hom ≫ Spec.map φ := by rw [hφ, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance

-- created on 2026-10-20
