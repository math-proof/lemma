import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma restrictLiftComm
  {T' T : Type u} [CommRing T'] [CommRing T] (π : RingHom T' T)
  {A₀ : (Scheme : Type (u + 1))} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
  {Y₁ Y₂ : (Scheme : Type (u + 1))} (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
  (g₁ : (↑U₁ : (Scheme : Type (u + 1))) ⟶ Y₁) (g₂ : (↑U₂ : (Scheme : Type (u + 1))) ⟶ Y₂)
  (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
  (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π))) :
    let W : (pullback f₀ f₀).Opens := ((TopologicalSpace.Opens.map (pullback.fst f₀ f₀).base).obj U₁) ⊓ ((TopologicalSpace.Opens.map (pullback.snd f₀ f₀).base).obj U₂)
    (((pullback f₀ f₀).homOfLE (inf_le_left : W ≤ _)) ≫ morphismRestrict (pullback.fst f₀ f₀) U₁ ≫ g₁) ≫ q₁ = (((pullback f₀ f₀).homOfLE (inf_le_right : W ≤ _)) ≫ morphismRestrict (pullback.snd f₀ f₀) U₂ ≫ g₂) ≫ q₂ := by
  simp only [Category.assoc]
  rw [hg₁.w, hg₂.w]
  simp only [Category.assoc, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, pullback.condition_assoc]

/--
[AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isPullback_pullback_lift_morphismRestrict_of_isPullback.lean)
-/
@[path]
private lemma main
  {T' T : Type u} [CommRing T'] [CommRing T] (π : RingHom T' T)
  {A₀ : (Scheme : Type (u + 1))} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (U₁ U₂ : A₀.Opens)
  (Y₁ Y₂ : (Scheme : Type (u + 1))) (q₁ : Y₁ ⟶ Spec (CommRingCat.of T')) (q₂ : Y₂ ⟶ Spec (CommRingCat.of T'))
  (g₁ : (↑U₁ : (Scheme : Type (u + 1))) ⟶ Y₁) (g₂ : (↑U₂ : (Scheme : Type (u + 1))) ⟶ Y₂)
  (hg₁ : IsPullback g₁ (U₁.ι ≫ f₀) q₁ (Spec.map (CommRingCat.ofHom π)))
  (hg₂ : IsPullback g₂ (U₂.ι ≫ f₀) q₂ (Spec.map (CommRingCat.ofHom π))) :
    let W : (pullback f₀ f₀).Opens := ((TopologicalSpace.Opens.map (pullback.fst f₀ f₀).base).obj U₁) ⊓ ((TopologicalSpace.Opens.map (pullback.snd f₀ f₀).base).obj U₂)
    IsPullback (pullback.lift (((pullback f₀ f₀).homOfLE (inf_le_left : W ≤ _)) ≫ morphismRestrict (pullback.fst f₀ f₀) U₁ ≫ g₁) (((pullback f₀ f₀).homOfLE (inf_le_right : W ≤ _)) ≫ morphismRestrict (pullback.snd f₀ f₀) U₂ ≫ g₂) (restrictLiftComm π f₀ U₁ U₂ q₁ q₂ g₁ g₂ hg₁ hg₂) : (↑W : (Scheme : Type (u + 1))) ⟶ pullback q₁ q₂) (W.ι ≫ pullback.fst f₀ f₀ ≫ f₀) (pullback.fst q₁ q₂ ≫ q₁) (Spec.map (CommRingCat.ofHom π)) := by
  set W₀ : (pullback f₀ f₀).Opens := ((TopologicalSpace.Opens.map (pullback.fst f₀ f₀).base).obj U₁) ⊓ ((TopologicalSpace.Opens.map (pullback.snd f₀ f₀).base).obj U₂)
  set a₁ : (↑W₀ : (Scheme : Type (u + 1))) ⟶ ↑U₁ := (pullback f₀ f₀).homOfLE (inf_le_left : W₀ ≤ _) ≫ morphismRestrict (pullback.fst f₀ f₀) U₁ with ha₁
  set a₂ : (↑W₀ : (Scheme : Type (u + 1))) ⟶ ↑U₂ := (pullback f₀ f₀).homOfLE (inf_le_right : W₀ ≤ _) ≫ morphismRestrict (pullback.snd f₀ f₀) U₂ with ha₂
  have ha₁ι : a₁ ≫ U₁.ι = W₀.ι ≫ pullback.fst f₀ f₀ := by
    rw [ha₁, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have ha₂ι : a₂ ≫ U₂.ι = W₀.ι ≫ pullback.snd f₀ f₀ := by
    rw [ha₂, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hW : IsPullback a₁ a₂ (U₁.ι ≫ f₀) (U₂.ι ≫ f₀) := by
    have hP : IsPullback (pullback.fst f₀ f₀) (pullback.snd f₀ f₀) f₀ f₀ := IsPullback.of_hasPullback f₀ f₀
    have sB := (isPullback_morphismRestrict (pullback.fst f₀ f₀) U₁).paste_vert hP
    set pre1 : (pullback f₀ f₀).Opens := (TopologicalSpace.Opens.map (pullback.fst f₀ f₀).base).obj U₁
    have sC := ((isPullback_morphismRestrict ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀) U₂).paste_vert sB.flip).flip
    set pre2 : (↑pre1 : (Scheme : Type (u + 1))).Opens := (TopologicalSpace.Opens.map ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀).base).obj U₂
    have hVimg : (Scheme.Hom.opensFunctor (Scheme.Opens.ι pre1)).obj pre2 = W₀ := by
      unfold pre2
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    let e : (↑pre2 : (Scheme : Type (u + 1))) ≅ ↑W₀ :=
      ((Scheme.Opens.ι pre1).isoImage pre2).trans ((pullback f₀ f₀).isoOfEq hVimg)
    have he : e.hom ≫ W₀.ι = (Scheme.Opens.ι pre2) ≫ (Scheme.Opens.ι pre1) := by
      simp only [e, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
    have he' : e.inv ≫ (Scheme.Opens.ι pre2) ≫ (Scheme.Opens.ι pre1) = W₀.ι := by
      rw [← he, Iso.inv_hom_id_assoc]
    have h1 : e.inv ≫ (Scheme.Opens.ι pre2) ≫ morphismRestrict (pullback.fst f₀ f₀) U₁ = a₁ := by
      rw [← cancel_mono U₁.ι, Category.assoc, Category.assoc, morphismRestrict_ι]
      rw [show Scheme.Opens.ι ((TopologicalSpace.Opens.map (pullback.fst f₀ f₀).base).obj U₁) = Scheme.Opens.ι pre1 from rfl]
      rw [ha₁ι, ← he']
      simp only [Category.assoc]
    have h2 : e.inv ≫ morphismRestrict ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀) U₂ = a₂ := by
      rw [← cancel_mono U₂.ι, Category.assoc, morphismRestrict_ι ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀) U₂]
      rw [show Scheme.Opens.ι ((TopologicalSpace.Opens.map ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀).base).obj U₂) = Scheme.Opens.ι pre2 from rfl]
      rw [ha₂ι, ← he']
      simp only [Category.assoc]
    have s : IsPullback e.inv (e.inv ≫ morphismRestrict ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀) U₂) (morphismRestrict ((Scheme.Opens.ι pre1) ≫ pullback.snd f₀ f₀) U₂) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]⟩
    have := s.paste_horiz sC
    rwa [Category.id_comp, h1, h2] at this
  have hrect : IsPullback (a₂ ≫ g₂) a₁ q₂ (g₁ ≫ q₁) := by
    have t := hW.paste_vert hg₂.flip
    rw [hg₁.w]
    apply t.flip
  set G₀ := (pullback.lift (a₁ ≫ g₁) (a₂ ≫ g₂) (restrictLiftComm π f₀ U₁ U₂ q₁ q₂ g₁ g₂ hg₁ hg₂) : (↑W₀ : (Scheme : Type (u + 1))) ⟶ pullback q₁ q₂)
  have hGa : G₀ ≫ pullback.fst q₁ q₂ = a₁ ≫ g₁ := by
    apply pullback.lift_fst _ _ _
  have hGb : G₀ ≫ pullback.snd q₁ q₂ = a₂ ≫ g₂ := by
    apply pullback.lift_snd _ _ _
  have htop : IsPullback G₀ a₁ (pullback.fst q₁ q₂) g₁ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd q₁ q₂) (v₁₃ := q₂) (h₂₂ := q₁) ?_ hGa (IsPullback.of_hasPullback q₁ q₂).flip
    rwa [hGb]
  have := htop.paste_vert hg₁
  rwa [← Category.assoc, ha₁ι, Category.assoc] at this


-- created on 2026-10-20
