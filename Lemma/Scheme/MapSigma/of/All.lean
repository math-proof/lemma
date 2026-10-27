import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma sigmaMap_sigmaι_apply
  {σ : Type u} {X Y : σ → (Scheme : Type (u + 1))} (f : ∀ i, X i ⟶ Y i) (i : σ) (x : X i) :
-- imply
  (Limits.Sigma.map f) ((Limits.Sigma.ι X i) x) = (Limits.Sigma.ι Y i) (f i x) := by
-- proof
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_map]

private lemma isPullback_sigmaι_sigmaMap
  {σ : Type u} {X Y : σ → (Scheme : Type (u + 1))} (f : ∀ i, X i ⟶ Y i) (j : σ) :
-- imply
  IsPullback (f j) (Limits.Sigma.ι X j) (Limits.Sigma.ι Y j) (Limits.Sigma.map f) := by
-- proof
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  ·
    rintro x ⟨y, hxy⟩
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
    rw [sigmaMk_mk] at hxy ⊢
    have hxy' : (Limits.Sigma.ι Y j) y = (Limits.Sigma.ι Y i) (f i x) := by
      rwa [← sigmaMap_sigmaι_apply]
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff Y j i _ _).mp hxy')
    refine ⟨x, rfl⟩
  ·
    rintro _ ⟨x, rfl⟩
    refine ⟨f j x, (sigmaMap_sigmaι_apply f j x).symm⟩

/--
[AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.lean)
-/
@[path]
private lemma main
  {P : MorphismProperty (Scheme : Type (u + 1))} [IsZariskiLocalAtTarget P]
  {σ : Type u} {X Y : σ → (Scheme : Type (u + 1))} {f : ∀ i, X i ⟶ Y i}
-- given
  (hf : ∀ i, P (f i)) :
-- imply
  P (Limits.Sigma.map f) := by
-- proof
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y) ?_
  intro j
  show P (Limits.pullback.snd (Limits.Sigma.map f) (Limits.Sigma.ι Y j))
  rw [← MorphismProperty.cancel_left_of_respectsIso P (isPullback_sigmaι_sigmaMap f j).flip.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  apply hf


-- created on 2026-10-20
