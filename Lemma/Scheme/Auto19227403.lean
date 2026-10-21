import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_comp_eq_of_isIntegralHom_of_surjective_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {M X : (Scheme : Type (u + 1))} (π : M ⟶ X) [IsIntegralHom π] (hsurj : Function.Surjective π.base)
  (k : Type u) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ X) :
  -- imply
  ∃ x : Spec (CommRingCat.of k) ⟶ M, x ≫ π = y := by
  -- proof
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
  let topΓ := F.presheaf.obj (op (⊤ : F.Opens))
  let φ : RingHom k topΓ := snd.appTop.hom.comp eK.inv.hom
  let alg : Algebra k topΓ := φ.toAlgebra
  have hφint : φ.IsIntegral := by
    have h1 : snd.appTop.hom.IsIntegral := IsIntegralHom.isIntegral_app snd ⊤ (isAffineOpen_top _)
    have h2 : (eK.inv.hom).IsIntegral := RingHom.isIntegral_of_surjective _ eK.symm.commRingCatIsoToRingEquiv.surjective
    refine RingHom.IsIntegral.trans _ _ h2 h1
  let _ : Algebra.IsIntegral k topΓ := ⟨fun b => hφint b⟩
  let _ : Nontrivial topΓ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : IsEmpty (Spec topΓ) := by
      change IsEmpty (PrimeSpectrum topΓ)
      infer_instance
    apply this.false (F.isoSpec.hom.base hne.some)
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal topΓ
  let _ : Field (topΓ ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let _ : Algebra.IsIntegral k (topΓ ⧸ 𝔪) := Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ k 𝔪) (Ideal.Quotient.mkₐ_surjective k 𝔪)
  let _ : Algebra.IsAlgebraic k (topΓ ⧸ 𝔪) := Algebra.IsIntegral.isAlgebraic
  let ψ : AlgHom k (topΓ ⧸ 𝔪) k := IsAlgClosed.lift
  let θ : AlgHom k topΓ k := ψ.comp (Ideal.Quotient.mkₐ k 𝔪)
  have hθφ : θ.toRingHom.comp φ = RingHom.id k := by
    ext c
    apply θ.commutes c
  let σ : Spec (CommRingCat.of k) ⟶ F := Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ F.isoSpec.inv
  have hσ : σ ≫ snd = 𝟙 _ := by
    have hnat : F.isoSpec.inv ≫ snd = Spec.map snd.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv := (Scheme.isoSpec_inv_naturality snd).symm
    simp only [σ, Category.assoc, hnat, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    have : eK.inv ≫ snd.appTop ≫ CommRingCat.ofHom θ.toRingHom = 𝟙 _ := by
      ext c
      apply θ.commutes c
    rw [this, Spec.map_id]
  refine ⟨σ ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  change (σ ≫ snd) ≫ y = y
  rw [hσ, Category.id_comp]


-- created on 2026-10-20
