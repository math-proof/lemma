import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency false in
private lemma AlgebraicGeometry.isIso_morphismRestrict_pullbackLift_of_isPullback_morphismRestrict
    {P X Y S : Scheme.{u}} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (w : p ≫ f = q ≫ g)
    (U : X.Opens) (hA : IsPullback (p ∣_ U) ((p ⁻¹ᵁ U).ι ≫ q) (U.ι ≫ f) g) :
    IsIso (pullback.lift p q w ∣_ (pullback.fst f g ⁻¹ᵁ U)) := by
  have hB : IsPullback (pullback.fst f g ∣_ U) ((pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g)
      (U.ι ≫ f) g :=
    (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert (IsPullback.of_hasPullback f g)
  have hcV : pullback.lift p q w ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U) = p ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst]
  have r₁ : (hA.isoIsPullback _ _ hB).hom ≫ (pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.fst f g =
      (p ⁻¹ᵁ U).ι ≫ p := by
    calc (hA.isoIsPullback _ _ hB).hom ≫ (pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.fst f g
        = (hA.isoIsPullback _ _ hB).hom ≫ (pullback.fst f g ∣_ U) ≫ U.ι := by
          rw [morphismRestrict_ι]
      _ = (p ∣_ U) ≫ U.ι := by rw [IsPullback.isoIsPullback_hom_fst_assoc]
      _ = (p ⁻¹ᵁ U).ι ≫ p := morphismRestrict_ι _ _
  have r₂ : (hA.isoIsPullback _ _ hB).hom ≫ (pullback.fst f g ⁻¹ᵁ U).ι ≫ pullback.snd f g =
      (p ⁻¹ᵁ U).ι ≫ q :=
    hA.isoIsPullback_hom_snd _ _ hB
  have key : pullback.lift p q w ∣_ (pullback.fst f g ⁻¹ᵁ U) =
      (P.isoOfEq hcV).hom ≫ (hA.isoIsPullback _ _ hB).hom := by
    rw [← cancel_mono (pullback.fst f g ⁻¹ᵁ U).ι]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [morphismRestrict_ι_assoc, pullback.lift_fst, r₁, Scheme.isoOfEq_hom_ι_assoc]
    · simp only [Category.assoc]
      rw [morphismRestrict_ι_assoc, pullback.lift_snd, r₂, Scheme.isoOfEq_hom_ι_assoc]
  rw [key]; infer_instance
set_option backward.isDefEq.respectTransparency false in
/--
[AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict.lean)
-/
@[path]
private lemma main
    {P X Y S : Scheme.{u}} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) (w : p ≫ f = q ≫ g)
    (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.I₀, IsPullback (p ∣_ (𝒰.f i).opensRange) ((p ⁻¹ᵁ (𝒰.f i).opensRange).ι ≫ q)
      ((𝒰.f i).opensRange.ι ≫ f) g) :
    IsPullback p q f g := by
  have hc₁ : pullback.lift p q w ≫ pullback.fst f g = p := pullback.lift_fst _ _ _
  have hc₂ : pullback.lift p q w ≫ pullback.snd f g = q := pullback.lift_snd _ _ _
  have : IsIso (pullback.lift p q w) :=
    (MorphismProperty.isomorphisms.iff _).mp
      (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun i => pullback.fst f g ⁻¹ᵁ (𝒰.f i).opensRange)
        ((pullback.fst f g).iSup_preimage_eq_top 𝒰.iSup_opensRange)
        fun i => (MorphismProperty.isomorphisms.iff _).mpr
          (isIso_morphismRestrict_pullbackLift_of_isPullback_morphismRestrict p q f g w _ (h i)))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso (pullback.lift p q w)) hc₁ hc₂

-- created on 2026-10-20
