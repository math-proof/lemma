import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift.lean)
-/
@[path]
private lemma main
    {A₀ Ak Y : Scheme.{u}} (U : A₀.Opens) (g : (U : Scheme.{u}) ⟶ Y)
    (O : A₀.Opens → Y.Opens) (hO : ∀ W : A₀.Opens, g ⁻¹ᵁ O W = U.ι ⁻¹ᵁ W)
    (i₀ : Ak ⟶ A₀) (W : A₀.Opens) (hW : W ≤ U) :
    ∃ aW : (↑(i₀ ⁻¹ᵁ W) : Scheme.{u}) ⟶ ↑(O W),
      aW ≫ (O W).ι = Ak.homOfLE (i₀.preimage_mono hW) ≫ (i₀ ∣_ U) ≫ g ∧
      IsPullback (Ak.homOfLE (i₀.preimage_mono hW)) aW ((i₀ ∣_ U) ≫ g) (O W).ι := by
  set φ : (↑(i₀ ⁻¹ᵁ U) : Scheme.{u}) ⟶ Y := (i₀ ∣_ U) ≫ g with hφ
  have hK : IsPullback (φ ⁻¹ᵁ O W).ι (φ ∣_ O W) φ (O W).ι := (isPullback_morphismRestrict φ (O W)).flip
  have hrange : Set.range (φ ⁻¹ᵁ O W).ι.base = Set.range (Ak.homOfLE (i₀.preimage_mono hW)).base := by
    rw [Scheme.Opens.range_ι]
    ext y
    constructor
    · intro hy
      refine ⟨⟨y.1, ?_⟩, ?_⟩
      · change φ.base y ∈ O W at hy
        rw [hφ, Scheme.Hom.comp_apply] at hy
        have hy' : (i₀ ∣_ U).base y ∈ g ⁻¹ᵁ O W := hy
        rw [hO] at hy'
        change ((U.ι).base ((i₀ ∣_ U).base y)) ∈ W at hy'
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply] at hy'
        exact hy'
      · exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rintro ⟨x, rfl⟩
      change φ.base (Ak.homOfLE _ x) ∈ O W
      rw [hφ, Scheme.Hom.comp_apply]
      show (i₀ ∣_ U).base ((Ak.homOfLE (i₀.preimage_mono hW)).base x) ∈ g ⁻¹ᵁ O W
      rw [hO]
      change ((U.ι).base ((i₀ ∣_ U).base ((Ak.homOfLE (i₀.preimage_mono hW)).base x))) ∈ W
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (i₀ ⁻¹ᵁ U).ι,
        Scheme.homOfLE_ι]
      exact x.2
  let e : (↑(φ ⁻¹ᵁ O W) : Scheme.{u}) ≅ ↑(i₀ ⁻¹ᵁ W) :=
    IsOpenImmersion.isoOfRangeEq (φ ⁻¹ᵁ O W).ι (Ak.homOfLE (i₀.preimage_mono hW)) hrange
  have he : e.hom ≫ Ak.homOfLE (i₀.preimage_mono hW) = (φ ⁻¹ᵁ O W).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he' : e.inv ≫ (φ ⁻¹ᵁ O W).ι = Ak.homOfLE (i₀.preimage_mono hW) := by
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨e.inv ≫ (φ ∣_ O W), ?_, ?_⟩
  · rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he']
  · refine hK.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, he]
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp [hφ]
    · simp

-- created on 2026-10-20
