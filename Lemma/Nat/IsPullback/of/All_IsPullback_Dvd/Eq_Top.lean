import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_isPullback_of_iSup_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isPullback_of_iSup_eq_top.lean)
-/

private lemma  isPullback_of_iSup_eq_top {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
    IsPullback fst snd f g := by
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U hU
  refine Scheme.isPullback_of_openCover fst snd f g 𝒰 fun i => ?_

  refine (h i).of_iso' (pullbackRestrictIsoRestrict fst (U i)) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    exact pullbackRestrictIsoRestrict_hom_morphismRestrict fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc]
    congr 1
    exact pullbackRestrictIsoRestrict_hom_ι fst (U i)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
@[main]
private lemma main
  {P X Y Z : Scheme.{u}}
  {fst : P ⟶ X}
  {snd : P ⟶ Y}
  {f : X ⟶ Z}
  {g : Y ⟶ Z}
  {ι : Type v}
  {U : ι → X.Opens}
-- given
  (hU : ⨆ i, U i = ⊤)
  (h : ∀ i, IsPullback (fst ∣_ U i) ((fst ⁻¹ᵁ U i).ι ≫ snd) ((U i).ι ≫ f) g) :
-- imply
  IsPullback fst snd f g :=
-- proof
  isPullback_of_iSup_eq_top fst snd f g U hU h


-- created on 2026-10-05
