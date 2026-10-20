import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective.lean)
-/
@[path]
private lemma main
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f]
    (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ Y) :
    ∃ x : Spec (CommRingCat.of k) ⟶ X, x ≫ f = y := by
  classical
  let P : Scheme.{0} := pullback f y
  let g : P ⟶ Spec (CommRingCat.of k) := pullback.snd f y
  let _ : IsIntegralHom g := inferInstance
  let _ : IsAffine P := isAffine_of_isAffineHom g
  obtain ⟨t⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨x₀, hx₀⟩ := f.surjective (y t)
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x₀ t hx₀
  let A : CommRingCat := Γ(P, ⊤)
  let φ : CommRingCat.of k ⟶ A := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop
  have hφ : φ.hom.IsIntegral := by
    have h := ((HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom) (f := g)).mp inferInstance).2
    have h' : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.IsIntegral :=
      RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).surjective
    have h__af := RingHom.IsIntegral.trans _ _ h' h
    simp only [φ, CommRingCat.hom_comp] at h__af
    exact h__af
  let _ : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨P.isoSpec.hom z⟩
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal A
  let _ : Algebra k A := φ.hom.toAlgebra
  let _ : Algebra k (A ⧸ 𝔪) := ((Ideal.Quotient.mk 𝔪).comp φ.hom).toAlgebra
  let _ : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let _ : Algebra.IsIntegral k (A ⧸ 𝔪) :=
    ⟨RingHom.IsIntegral.trans _ _ hφ (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)⟩
  let _ : Algebra.IsAlgebraic k (A ⧸ 𝔪) := inferInstance
  let ψ : (A ⧸ 𝔪) →ₐ[k] k := IsAlgClosed.lift
  let χ : A →+* k := ψ.toRingHom.comp (Ideal.Quotient.mk 𝔪)
  have hχ : φ ≫ CommRingCat.ofHom χ = 𝟙 _ := by
    ext a
    change ψ ((Ideal.Quotient.mk 𝔪) (φ.hom a)) = a
    exact ψ.commutes a
  let x' : Spec (CommRingCat.of k) ⟶ P := Spec.map (CommRingCat.ofHom χ) ≫ P.isoSpec.inv
  have hx' : x' ≫ g = 𝟙 _ := by
    simp only [x', Category.assoc]
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, ← Spec.map_comp,
      ← Category.assoc, show (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop = φ from rfl, hχ, Spec.map_id]
  refine ⟨x' ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx', Category.id_comp]


-- created on 2026-10-20
