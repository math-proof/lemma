import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma AlgebraicGeometry.isIso_morphismRestrict_pullbackLift_of_isPullback_morphismRestrict
  {P X Y S : (Scheme : Type (u + 1))}
  (p : P ⟶ X)
  (q : P ⟶ Y)
  (f : X ⟶ S)
  (g : Y ⟶ S)
  (w : p ≫ f = q ≫ g)
  (U : X.Opens)
  (hA : IsPullback (morphismRestrict p U) (Scheme.Opens.ι ((TopologicalSpace.Opens.map p.base).obj U) ≫ q) (U.ι ≫ f) g) :
  IsIso (morphismRestrict (pullback.lift p q w) ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U)) := by
  have hB : IsPullback (morphismRestrict (pullback.fst f g) U) (Scheme.Opens.ι ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U) ≫ pullback.snd f g) (U.ι ≫ f) g :=
    (isPullback_morphismRestrict (pullback.fst f g) U).paste_vert (IsPullback.of_hasPullback f g)
  have hcV : ((TopologicalSpace.Opens.map (pullback.lift p q w).base).obj ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U)) = ((TopologicalSpace.Opens.map p.base).obj U) := by
    rw [← Scheme.Hom.comp_preimage, pullback.lift_fst]
  have r₁ : (hA.isoIsPullback _ _ hB).hom ≫ Scheme.Opens.ι ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U) ≫ pullback.fst f g = Scheme.Opens.ι ((TopologicalSpace.Opens.map p.base).obj U) ≫ p := calc
    _ = (hA.isoIsPullback _ _ hB).hom ≫ (morphismRestrict (pullback.fst f g) U) ≫ U.ι := by rw [morphismRestrict_ι]
    _ = (morphismRestrict p U) ≫ U.ι := by rw [IsPullback.isoIsPullback_hom_fst_assoc]
    _ = Scheme.Opens.ι ((TopologicalSpace.Opens.map p.base).obj U) ≫ p := morphismRestrict_ι _ _
  have r₂ : (hA.isoIsPullback _ _ hB).hom ≫ Scheme.Opens.ι ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U) ≫ pullback.snd f g = Scheme.Opens.ι ((TopologicalSpace.Opens.map p.base).obj U) ≫ q :=
    hA.isoIsPullback_hom_snd _ _ hB
  have key : morphismRestrict (pullback.lift p q w) ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U) = (P.isoOfEq hcV).hom ≫ (hA.isoIsPullback _ _ hB).hom := by
    rw [← cancel_mono (Scheme.Opens.ι ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj U))]
    apply pullback.hom_ext
    ·
      simp only [Category.assoc]
      rw [morphismRestrict_ι_assoc, pullback.lift_fst, r₁, Scheme.isoOfEq_hom_ι_assoc]
    ·
      simp only [Category.assoc]
      rw [morphismRestrict_ι_assoc, pullback.lift_snd, r₂, Scheme.isoOfEq_hom_ι_assoc]
  rw [key]
  infer_instance

/--
[AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isPullback_of_openCover_of_isPullback_morphismRestrict.lean)
-/
@[path]
private lemma main
  {P X Y S : (Scheme : Type (u + 1))}
  (p : P ⟶ X)
  (q : P ⟶ Y)
  (f : X ⟶ S)
  (g : Y ⟶ S)
  (w : p ≫ f = q ≫ g)
  (𝒰 : X.OpenCover)
  (h : ∀ i : 𝒰.I₀, IsPullback (morphismRestrict p (𝒰.f i).opensRange) (Scheme.Opens.ι ((TopologicalSpace.Opens.map p.base).obj (𝒰.f i).opensRange) ≫ q) ((𝒰.f i).opensRange.ι ≫ f) g) :
  IsPullback p q f g := by
  have hc₁ : pullback.lift p q w ≫ pullback.fst f g = p := pullback.lift_fst _ _ _
  have hc₂ : pullback.lift p q w ≫ pullback.snd f g = q := pullback.lift_snd _ _ _
  have : IsIso (pullback.lift p q w) :=
    (MorphismProperty.isomorphisms.iff _).mp
      (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
        (fun i => ((TopologicalSpace.Opens.map (pullback.fst f g).base).obj (𝒰.f i).opensRange))
        ((pullback.fst f g).iSup_preimage_eq_top 𝒰.iSup_opensRange)
        fun i => (MorphismProperty.isomorphisms.iff _).mpr
          (isIso_morphismRestrict_pullbackLift_of_isPullback_morphismRestrict p q f g w _ (h i)))
  apply IsPullback.of_iso_pullback ⟨w⟩ (asIso (pullback.lift p q w)) hc₁ hc₂


-- created on 2026-10-20
