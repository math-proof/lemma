import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {X : Scheme}
  {ξ : X ⟶ Spec (CommRingCat.of R)}
-- given
  (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
    φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) :
-- imply
  LocallyOfFiniteType ξ := by
-- proof
  classical
  suffices key : ∀ p : X, ∃ (Y : Scheme) (j : Y ⟶ X) (_ : IsOpenImmersion j),
      p ∈ Set.range ⇑j ∧ LocallyOfFiniteType (j ≫ ξ) by
    choose Y j hj hmem hlft using key
    exact IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
      (Scheme.Cover.mkOfCovers X Y j (fun x => ⟨x, hmem x⟩) (fun x => hj x)) hlft
  intro p
  obtain ⟨B, ι, hι, y, hy⟩ : ∃ (B : CommRingCat) (ι : Spec B ⟶ X) (_ : IsOpenImmersion ι) (y : Spec B), ι y = p := by
    obtain ⟨V, hV, hpV, -⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ p ∈ V ∧ V ≤ ⊤ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)) (show p ∈ (⊤ : X.Opens) from trivial)
    refine ⟨X.presheaf.obj (Opposite.op V), hV.isoSpec.inv ≫ V.ι, inferInstance, hV.isoSpec.hom ⟨p, hpV⟩, ?_⟩
    show V.ι (hV.isoSpec.inv (hV.isoSpec.hom ⟨p, hpV⟩)) = p
    calc
      _ = ((hV.isoSpec.hom ≫ hV.isoSpec.inv) ≫ V.ι) ⟨p, hpV⟩ := by simp
      _ = V.ι ⟨p, hpV⟩ := by rw [Category.assoc, hV.isoSpec.hom_inv_id_assoc]
      _ = p := by rw [Scheme.Opens.ι_apply, Subtype.coe_mk]
  let _ : Algebra R B := (Spec.preimage (ι ≫ ξ)).hom.toAlgebra
  have hιξ : ι ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨B₀, hB₀, φ₀, hφ₀, hfac⟩ := h B ι hιξ
  let _ : Algebra.FiniteType R ↥B₀ := (Subalgebra.fg_iff_finiteType B₀).mp hB₀
  have hq : (Spec.map (CommRingCat.ofHom B₀.val.toRingHom)) y ∈
    (TopologicalSpace.Opens.map φ₀.base).obj ι.opensRange := by
    show φ₀ (Spec.map (CommRingCat.ofHom B₀.val.toRingHom) y) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hfac]
    exact ⟨y, rfl⟩
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hfU⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hq
  let f : B := (f₀ : B)
  let j₀ : Spec (CommRingCat.of (Localization.Away f₀)) ⟶ Spec (CommRingCat.of ↥B₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥B₀ (Localization.Away f₀)))
  let jB : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec B :=
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away f)))
  have hpow : Submonoid.powers f₀ ≤ (Submonoid.powers f).comap B₀.val.toRingHom := by
    rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [f]⟩
  let g : Localization.Away f₀ →+* Localization.Away f :=
    IsLocalization.map (Localization.Away f) B₀.val.toRingHom hpow
  have hsq : jB ≫ Spec.map (CommRingCat.ofHom B₀.val.toRingHom) = Spec.map (CommRingCat.ofHom g) ≫ j₀ := by
    simp only [jB, j₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (IsLocalization.map_comp hpow).symm
  have hrange : Set.range ⇑(j₀ ≫ φ₀) ⊆ Set.range ⇑ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hz : j₀ z ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum ↥B₀)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f₀) f₀]
      exact ⟨z, rfl⟩
    have := hfU hz
    rwa [← Scheme.Hom.coe_opensRange]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : B →+* Localization.Away f₀, Spec.map (CommRingCat.ofHom ρ) ≫ ι = j₀ ≫ φ₀ :=
    ⟨(Spec.preimage (IsOpenImmersion.lift ι (j₀ ≫ φ₀) hrange)).hom,
      by rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  have hcomp : g.comp ρ = algebraMap B (Localization.Away f) := by
    have h1 : Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom ρ) = jB := by
      rw [← cancel_mono ι, Category.assoc, hρ, ← Category.assoc, ← hsq, Category.assoc, hfac]
    have h2 := Spec.map_injective ((Spec.map_comp _ _).trans h1)
    refine congrArg CommRingCat.Hom.hom h2
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    refine ⟨ρ b * IsLocalization.mk' (Localization.Away f₀) 1 (⟨f₀ ^ n, n, rfl⟩ : Submonoid.powers f₀), ?_⟩
    have e1 : g (ρ b) = algebraMap B (Localization.Away f) b := by rw [← RingHom.comp_apply, hcomp]
    have e2 : g (IsLocalization.mk' (Localization.Away f₀) 1 (⟨f₀ ^ n, n, rfl⟩ : Submonoid.powers f₀)) =
        IsLocalization.mk' (Localization.Away f) 1 (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) := by
      rw [IsLocalization.map_mk']
      rfl
    show g (_ * _) = IsLocalization.mk' (Localization.Away f) b (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
    rw [map_mul, e1, e2, ← IsLocalization.mk'_eq_mul_mk'_one]
  let _ : Algebra R (Localization.Away f₀) := inferInstance
  have hgR : ∀ r : R, g (algebraMap R (Localization.Away f₀) r) = algebraMap R (Localization.Away f) r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R ↥B₀ (Localization.Away f₀), IsScalarTower.algebraMap_apply R B (Localization.Away f)]
    change (g.comp (algebraMap ↥B₀ (Localization.Away f₀))) _ = _
    rw [IsLocalization.map_comp hpow]
    rfl
  let gₐ : Localization.Away f₀ →ₐ[R] Localization.Away f := { g with commutes' := hgR }
  let _ : Algebra.FiniteType R (Localization.Away f) := Algebra.FiniteType.of_surjective gₐ hsurj
  refine ⟨Spec (CommRingCat.of (Localization.Away f)), jB ≫ ι, inferInstance, ?_, ?_⟩
  ·
    have hyf : y ∈ Set.range ⇑jB := by
      change y ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away f)))
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      refine hqf
    obtain ⟨z, hz⟩ := hyf
    exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
  have hjB : jB ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R (↑B) (Localization.Away f)]
  ·
    rw [Category.assoc, hιξ, hjB]
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
    refine RingHom.finiteType_algebraMap.mpr inferInstance


-- created on 2026-10-20
