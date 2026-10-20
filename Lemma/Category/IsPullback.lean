import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isPullback_lift_fst_comp_fst_snd_comp_fst_prodStr.lean)
-/
@[path]
private lemma main
    {S R : Type} [CommRing S] [CommRing R] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) :
    IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.snd f σ)
      (pullback.fst f f ≫ f) σ := by
  have hg : IsPullback (pullback.fst f σ) (pullback.snd f σ) f σ := IsPullback.of_hasPullback f σ
  have s₁ : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ)) (pullback.fst (pullback.snd f σ) (pullback.snd f σ))
      (pullback.snd f σ) (pullback.snd f σ) := (IsPullback.of_hasPullback _ _).flip
  have s : IsPullback (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rw [hg.w]
    exact s₁.paste_horiz hg
  have s' : IsPullback
      (pullback.lift (pullback.fst (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (pullback.snd (pullback.snd f σ) (pullback.snd f σ) ≫ pullback.fst f σ)
        (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f σ).w, ← Category.assoc, pullback.condition,
          Category.assoc]) ≫ pullback.snd f f)
      (pullback.fst (pullback.snd f σ) (pullback.snd f σ)) f (pullback.fst f σ ≫ f) := by
    rwa [pullback.lift_snd]
  have step1 := IsPullback.of_right s' (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f f).flip
  exact step1.paste_vert hg

-- created on 2026-10-20
