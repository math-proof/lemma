import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed.lean)
-/
@[path]
private lemma main
    {M X : Scheme.{u}} (π : M ⟶ X) [IsIntegralHom π] (hsurj : Function.Surjective π.base)
    (k : Type u) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ X) :
    ∃ x : Spec (CommRingCat.of k) ⟶ M, x ≫ π = y := by
  classical
  let F := pullback π y
  let snd : F ⟶ Spec (CommRingCat.of k) := pullback.snd π y
  let _ : IsIntegralHom snd := inferInstance
  let _ : IsAffine F := isAffine_of_isAffineHom snd
  let _ : Surjective π := ⟨hsurj⟩
  let hs : Surjective snd := MorphismProperty.pullback_snd _ _ inferInstance
  have hne : Nonempty F := by
    obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum k))
    obtain ⟨z, -⟩ := hs.surj p
    exact ⟨z⟩
  let eK := Scheme.ΓSpecIso (CommRingCat.of k)
  let φ : k →+* Γ(F, ⊤) := snd.appTop.hom.comp eK.inv.hom
  let alg : Algebra k Γ(F, ⊤) := φ.toAlgebra
  have hφint : φ.IsIntegral := by
    have h1 : snd.appTop.hom.IsIntegral := IsIntegralHom.isIntegral_app snd ⊤ (isAffineOpen_top _)
    have h2 : (eK.inv.hom).IsIntegral :=
      RingHom.isIntegral_of_surjective _ eK.symm.commRingCatIsoToRingEquiv.surjective
    exact RingHom.IsIntegral.trans _ _ h2 h1
  let _ : Algebra.IsIntegral k Γ(F, ⊤) := ⟨fun b => hφint b⟩
  let _ : Nontrivial Γ(F, ⊤) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : IsEmpty (Spec Γ(F, ⊤)) := by
      change IsEmpty (PrimeSpectrum Γ(F, ⊤))
      infer_instance
    exact this.false (F.isoSpec.hom.base hne.some)
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal Γ(F, ⊤)
  let _ : Field (Γ(F, ⊤) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let _ : Algebra.IsIntegral k (Γ(F, ⊤) ⧸ 𝔪) :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ k 𝔪) (Ideal.Quotient.mkₐ_surjective k 𝔪)
  let _ : Algebra.IsAlgebraic k (Γ(F, ⊤) ⧸ 𝔪) := Algebra.IsIntegral.isAlgebraic
  let ψ : (Γ(F, ⊤) ⧸ 𝔪) →ₐ[k] k := IsAlgClosed.lift
  let θ : Γ(F, ⊤) →ₐ[k] k := ψ.comp (Ideal.Quotient.mkₐ k 𝔪)
  have hθφ : θ.toRingHom.comp φ = RingHom.id k := by
    ext c; exact θ.commutes c
  let σ : Spec (CommRingCat.of k) ⟶ F := Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ F.isoSpec.inv
  have hσ : σ ≫ snd = 𝟙 _ := by
    have hnat : F.isoSpec.inv ≫ snd = Spec.map snd.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv :=
      (Scheme.isoSpec_inv_naturality snd).symm
    simp only [σ, Category.assoc, hnat, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    have : eK.inv ≫ snd.appTop ≫ CommRingCat.ofHom θ.toRingHom = 𝟙 _ := by
      ext c
      exact θ.commutes c
    rw [this, Spec.map_id]
  refine ⟨σ ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (σ ≫ snd) ≫ y = y
  rw [hσ, Category.id_comp]

-- created on 2026-10-20
