import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated.lean)
-/
@[path]
private lemma main
  {σ : Type u} (X : σ → (Scheme : Type (u + 1))) {Y : (Scheme : Type (u + 1))} (f : ∀ i, X i ⟶ Y)
  (hf : ∀ i, IsSeparated (f i)) :
  -- imply
  IsSeparated (Sigma.desc f) := by
  -- proof
  constructor
  refine IsZariskiLocalAtTarget.of_openCover
    (Scheme.Pullback.openCoverOfLeftRight (sigmaOpenCover X) (sigmaOpenCover X) (Sigma.desc f) (Sigma.desc f)) ?_
  rintro ⟨i, j⟩
  have H := pullback_map_diagonal_isPullback (Sigma.ι X i) (Sigma.ι X j) (Sigma.desc f)
  show IsClosedImmersion (pullback.snd (pullback.diagonal (Sigma.desc f))
    (pullback.map (Sigma.ι X i ≫ Sigma.desc f) (Sigma.ι X j ≫ Sigma.desc f) (Sigma.desc f) (Sigma.desc f)
      (Sigma.ι X i) (Sigma.ι X j) (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion H.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  if hij : i = j then
    subst hij
    have hfi : Sigma.ι X i ≫ Sigma.desc f = f i := Sigma.ι_comp_desc _ _
    let _ : IsSeparated (Sigma.ι X i ≫ Sigma.desc f) := by
      rw [hfi]
      apply hf i
    let this : IsClosedImmersion
      (pullback.fst (Sigma.ι X i) (Sigma.ι X i) ≫ pullback.diagonal (Sigma.ι X i ≫ Sigma.desc f)) :=
      inferInstance
    convert this using 2
    apply pullback.hom_ext <;> simp [fst_eq_snd_of_mono_eq]
  else
    let _ : IsEmpty ↑(pullback (Sigma.ι X i) (Sigma.ι X j)) := isEmpty_pullback_sigmaι_of_ne X hij
    infer_instance


-- created on 2026-10-20
