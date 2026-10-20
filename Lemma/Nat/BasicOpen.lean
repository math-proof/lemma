import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection.lean)
-/
@[path]
private lemma main
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f g : A} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') :
    Proj.basicOpen 𝒜 (f * g) =
      (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg)) := by
  let V : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 f
  let e : HomogeneousLocalization.Away 𝒜 f := HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg
  let s : Γ(Proj 𝒜, V) := Proj.awayToSection 𝒜 f e
  have h1 : (Proj 𝒜).basicOpen s = V.ι ''ᵁ (V : Scheme.{u}).basicOpen (V.topIso.inv s) := by
    rw [Scheme.Opens.ι_image_basicOpen, Scheme.Opens.topIso_inv]
    exact (((Proj 𝒜).basicOpen_res s _).trans
      (inf_eq_right.mpr (((Proj 𝒜).basicOpen_le s).trans (Scheme.Opens.ι_image_top V).ge))).symm
  have h2 : V.topIso.inv s =
      (Proj.basicOpenToSpec 𝒜 f).appTop ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e) := by
    show V.topIso.inv s = (Proj.basicOpenToSpec 𝒜 f).app ⊤ _
    rw [Proj.basicOpenToSpec_app_top]
    show V.topIso.inv s = V.topIso.inv (Proj.awayToSection 𝒜 f
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e)))
    rw [Iso.inv_hom_id_apply]
  have h3' : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e) = PrimeSpectrum.basicOpen e :=
    basicOpen_eq_of_affine (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)) e
  have h4 : Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ (PrimeSpectrum.basicOpen e) = V.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    have := Proj.awayι_preimage_basicOpen 𝒜 f_deg hm g_deg hm'
    rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm, Scheme.Hom.comp_preimage] at this
    rw [← this, ← Scheme.Hom.comp_preimage, ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm, Iso.hom_inv_id,
      Scheme.Hom.id_preimage]
  calc Proj.basicOpen 𝒜 (f * g) = V ⊓ Proj.basicOpen 𝒜 g := Proj.basicOpen_mul 𝒜 f g
    _ = V.ι ''ᵁ (V.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    _ = V.ι ''ᵁ (Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ (PrimeSpectrum.basicOpen e)) := by rw [h4]
    _ = V.ι ''ᵁ (Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e)) := by rw [h3']
    _ = V.ι ''ᵁ (V : Scheme.{u}).basicOpen ((Proj.basicOpenToSpec 𝒜 f).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e)) := by
        rw [Scheme.preimage_basicOpen_top]
    _ = V.ι ''ᵁ (V : Scheme.{u}).basicOpen (V.topIso.inv s) := by rw [h2]
    _ = (Proj 𝒜).basicOpen s := h1.symm


-- created on 2026-10-20
