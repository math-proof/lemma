import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma isEmpty_pullback_ι
  {X : (Scheme : Type (u + 1))} (A B : X.Opens) (hd : A ⊓ B = ⊥) :
  IsEmpty ↑(pullback A.ι B.ι) := by
  refine ⟨fun p => ?_⟩
  have h1 : (pullback.fst A.ι B.ι ≫ A.ι).base p = (pullback.snd A.ι B.ι ≫ B.ι).base p := by
    rw [pullback.condition]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at h1
  have hA : ((pullback.fst A.ι B.ι).base p).1 ∈ A := ((pullback.fst A.ι B.ι).base p).2
  have hB : ((pullback.snd A.ι B.ι).base p).1 ∈ B := ((pullback.snd A.ι B.ι).base p).2
  rw [← h1] at hB
  have hmem : ((pullback.fst A.ι B.ι).base p).1 ∈ A ⊓ B := ⟨hA, hB⟩
  rw [hd] at hmem
  apply hmem

private lemma helper_main
  {X Y : (Scheme : Type (u + 1))} {ι : Type v} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤)
  (hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (f : ∀ i, (W i : (Scheme : Type (u + 1))) ⟶ Y) :
  ∃! g : X ⟶ Y, ∀ i, (W i).ι ≫ g = f i := by
  classical
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover W hW
  have hcompat : ∀ i j : ι, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ f j := by
    intro i j
    if hij : i = j then
      subst hij
      show pullback.fst (W i).ι (W i).ι ≫ f i = pullback.snd (W i).ι (W i).ι ≫ f i
      rw [fst_eq_snd_of_mono_eq]
    else
      let _ := isEmpty_pullback_ι (W i) (W j) (hdisj i j hij)
      apply (isInitialOfIsEmpty (X := pullback (W i).ι (W j).ι)).hom_ext _ _
  refine ⟨𝒰.glueMorphisms f hcompat, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat i, ?_⟩
  intro g hg
  apply Scheme.Cover.hom_ext 𝒰 _ _
  intro i
  show (W i).ι ≫ g = (W i).ι ≫ Scheme.Cover.glueMorphisms 𝒰 f hcompat
  rw [hg i]
  apply (Scheme.Cover.ι_glueMorphisms 𝒰 f hcompat i).symm

/--
[AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_forall_opensInclusion_comp_eq_of_iSup_eq_top_of_disjoint.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} {ι : Type v} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤)
  (hdisj : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (f : ∀ i, (W i : (Scheme : Type (u + 1))) ⟶ Y) :
  -- imply
  ∃! g : X ⟶ Y, ∀ i, (W i).ι ≫ g = f i :=
  helper_main W hW hdisj f


-- created on 2026-10-20
