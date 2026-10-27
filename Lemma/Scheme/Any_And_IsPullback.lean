import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isPullback_homOfLE_morphismRestrict_comp_openCover_lift.lean)
-/
@[path]
private lemma main
  {A₀ Ak Y : (Scheme : Type (u + 1))} (U : A₀.Opens) (g : (U : (Scheme : Type (u + 1))) ⟶ Y)
  (O : A₀.Opens → Y.Opens) (hO : ∀ W : A₀.Opens, ((TopologicalSpace.Opens.map g.base).obj (O W)) = ((TopologicalSpace.Opens.map U.ι.base).obj W))
  (i₀ : Ak ⟶ A₀) (W : A₀.Opens) (hW : W ≤ U) :
  -- imply
  ∃ aW : (↑((TopologicalSpace.Opens.map i₀.base).obj W) : (Scheme : Type (u + 1))) ⟶ ↑(O W), aW ≫ (O W).ι = Ak.homOfLE (i₀.preimage_mono hW) ≫ morphismRestrict i₀ U ≫ g ∧ IsPullback (Ak.homOfLE (i₀.preimage_mono hW)) aW (morphismRestrict i₀ U ≫ g) (O W).ι := by
  -- proof
  set φ : (↑((TopologicalSpace.Opens.map i₀.base).obj U) : (Scheme : Type (u + 1))) ⟶ Y := morphismRestrict i₀ U ≫ g with hφ
  have hK : IsPullback (Scheme.Opens.ι ((TopologicalSpace.Opens.map φ.base).obj (O W))) (morphismRestrict φ (O W)) φ (O W).ι := (isPullback_morphismRestrict φ (O W)).flip
  have hrange : Set.range (Scheme.Opens.ι ((TopologicalSpace.Opens.map φ.base).obj (O W))).base = Set.range (Ak.homOfLE (i₀.preimage_mono hW)).base := by
    rw [Scheme.Opens.range_ι]
    ext y
    constructor
    ·
      intro hy
      refine ⟨⟨y.1, ?_⟩, ?_⟩
      ·
        change φ.base y ∈ O W at hy
        rw [hφ, Scheme.Hom.comp_apply] at hy
        have hy' : (morphismRestrict i₀ U).base y ∈ ((TopologicalSpace.Opens.map g.base).obj (O W)) := hy
        rw [hO] at hy'
        change (U.ι.base ((morphismRestrict i₀ U).base y)) ∈ W at hy'
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply] at hy'
        apply hy'
      ·
        refine Subtype.ext (Scheme.homOfLE_apply _ _)
    ·
      rintro ⟨x, rfl⟩
      change φ.base (Ak.homOfLE _ x) ∈ O W
      rw [hφ, Scheme.Hom.comp_apply]
      show (morphismRestrict i₀ U).base ((Ak.homOfLE (i₀.preimage_mono hW)).base x) ∈ ((TopologicalSpace.Opens.map g.base).obj (O W))
      rw [hO]
      change (U.ι.base ((morphismRestrict i₀ U).base ((Ak.homOfLE (i₀.preimage_mono hW)).base x))) ∈ W
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (Scheme.Opens.ι ((TopologicalSpace.Opens.map i₀.base).obj U)), Scheme.homOfLE_ι]
      apply x.2
  let e : (↑((TopologicalSpace.Opens.map φ.base).obj (O W)) : (Scheme : Type (u + 1))) ≅ ↑((TopologicalSpace.Opens.map i₀.base).obj W) := IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι ((TopologicalSpace.Opens.map φ.base).obj (O W))) (Ak.homOfLE (i₀.preimage_mono hW)) hrange
  have he : e.hom ≫ Ak.homOfLE (i₀.preimage_mono hW) = Scheme.Opens.ι ((TopologicalSpace.Opens.map φ.base).obj (O W)) := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have he' : e.inv ≫ Scheme.Opens.ι ((TopologicalSpace.Opens.map φ.base).obj (O W)) = Ak.homOfLE (i₀.preimage_mono hW) := by
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨e.inv ≫ morphismRestrict φ (O W), ?_, ?_⟩
  · rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, he']
  ·
    refine hK.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, he]
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · simp [hφ]
    · simp


-- created on 2026-10-20
