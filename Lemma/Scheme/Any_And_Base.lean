import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom.lean)
-/
@[path]
private lemma main
  {X Y Y' : (Scheme : Type (u + 1))} (U : X.Opens) (α : (U : (Scheme : Type (u + 1))) ⟶ Y) (z : X) (hzU : z ∈ U)
  [X.IsGermInjectiveAt z]
  (β : Y' ⟶ Y) [LocallyOfFiniteType β]
  {O : Type u} [CommRing O] [IsLocalRing O]
  (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y) (ℓ : Spec (CommRingCat.of O) ⟶ Y') (hℓ : ℓ ≫ β = ℓ₀)
  (φ : CommRingCat.of O ⟶ X.presheaf.stalk z) [IsLocalHom φ.hom]
  (hφ : Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α) :
    ∃ (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U') (α' : (U' : (Scheme : Type (u + 1))) ⟶ Y'),
      α' ≫ β = X.homOfLE hU' ≫ α ∧ α'.base ⟨z, hzU'⟩ = ℓ.base (IsLocalRing.closedPoint O) := by
  let _ : (U : (Scheme : Type (u + 1))).IsGermInjectiveAt (⟨z, hzU⟩ : ↥U) := by
    apply (isGermInjectiveAt_iff_of_isOpenImmersion (f := U.ι) (x := (⟨z, hzU⟩ : ↥U))).mp
    rw [show U.ι.base (⟨z, hzU⟩ : ↥U) = z from rfl]
    infer_instance
  let w : Spec ((U : (Scheme : Type (u + 1))).presheaf.stalk ⟨z, hzU⟩) ⟶ Y' := Spec.map (U.ι.stalkMap ⟨z, hzU⟩) ≫ Spec.map φ ≫ ℓ
  have hUfrom : Spec.map (U.ι.stalkMap ⟨z, hzU⟩) ≫ U.fromSpecStalkOfMem z hzU = (U : (Scheme : Type (u + 1))).fromSpecStalk ⟨z, hzU⟩ := by
    simp only [Scheme.Opens.fromSpecStalkOfMem, Spec.map_inv]
    apply IsIso.hom_inv_id_assoc
  have hw : w ≫ β = (U : (Scheme : Type (u + 1))).fromSpecStalk ⟨z, hzU⟩ ≫ α := by
    simp only [w, Category.assoc, hℓ]
    erw [hφ, ← Category.assoc, hUfrom]
  obtain ⟨W, hzW, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' α β w hw
  have hzW' : z ∈ (Scheme.Hom.opensFunctor U.ι).obj W := (Scheme.Opens.mem_ι_image_iff (x := (⟨z, hzU⟩ : ↥U))).mpr hzW
  refine ⟨(Scheme.Hom.opensFunctor U.ι).obj W, Scheme.Opens.ι_image_le U W, hzW', (U.ι.isoImage W).inv ≫ g, ?_, ?_⟩
  ·
    rw [Category.assoc, hg₂, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.homOfLE_ι]
  ·
    have hpt : ((U.ι.isoImage W).inv ≫ g).base ⟨z, hzW'⟩ = g.base ⟨⟨z, hzU⟩, hzW⟩ := by
      rw [Scheme.Hom.comp_apply]
      congr 1
      have h1 : ((U.ι.isoImage W).inv ≫ W.ι).base ⟨z, hzW'⟩ = ⟨z, hzU⟩ := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.isoImage_inv_ι]
        rfl
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h1]
      rfl
    rw [hpt]
    have h2 : g.base ⟨⟨z, hzU⟩, hzW⟩ = w.base (IsLocalRing.closedPoint _) := by
      have := congrArg (fun k => k.base (IsLocalRing.closedPoint ((U : (Scheme : Type (u + 1))).presheaf.stalk ⟨z, hzU⟩))) hg₁
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]
      congr 1
      have h4 : (W.fromSpecStalkOfMem ⟨z, hzU⟩ hzW ≫ W.ι).base (IsLocalRing.closedPoint _) = ⟨z, hzU⟩ := by
        rw [Scheme.Opens.fromSpecStalkOfMem_ι]
        apply Scheme.fromSpecStalk_closedPoint
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h4]
      rfl
    rw [h2]
    simp only [w, Scheme.Hom.comp_apply]
    congr 1
    have e1 : (Spec.map (U.ι.stalkMap ⟨z, hzU⟩)).base
      (IsLocalRing.closedPoint ((U : (Scheme : Type (u + 1))).presheaf.stalk ⟨z, hzU⟩)) = IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint (U.ι.stalkMap ⟨z, hzU⟩).hom
    have e2 : (Spec.map φ).base (IsLocalRing.closedPoint (X.presheaf.stalk z)) = IsLocalRing.closedPoint O :=
      @IsLocalRing.comap_closedPoint _ _ _ _ _ _ φ.hom ‹_›
    rw [e1]
    apply e2


-- created on 2026-10-20
