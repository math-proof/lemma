import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isAffineHom_and_isPullback_pullback_lift_of_isPullback](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isAffineHom_and_isPullback_pullback_lift_of_isPullback.lean)
-/
@[path]
private lemma main
  {T k : Type u} [CommRing T] [CommRing k] (ρ : RingHom T k)
  {A₀ Ak : (Scheme : Type (u + 1))} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (fk : Ak ⟶ Spec (CommRingCat.of k)) (i₀ : Ak ⟶ A₀) [IsAffineHom i₀]
  (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
  -- imply
  IsAffineHom (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀) (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ∧ IsPullback (pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀) (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (pullback.fst fk fk ≫ fk) (pullback.fst f₀ f₀ ≫ f₀) (Spec.map (CommRingCat.ofHom ρ)) := by
  -- proof
  set jP := pullback.lift (pullback.fst fk fk ≫ i₀) (pullback.snd fk fk ≫ i₀) (by rw [Category.assoc, Category.assoc, hi₀.w, ← Category.assoc, ← Category.assoc, pullback.condition]) with hjP
  have hj1 : jP ≫ pullback.fst f₀ f₀ = pullback.fst fk fk ≫ i₀ := pullback.lift_fst _ _ _
  have hj2 : jP ≫ pullback.snd f₀ f₀ = pullback.snd fk fk ≫ i₀ := pullback.lift_snd _ _ _
  have hrect : IsPullback (pullback.snd fk fk ≫ i₀) (pullback.fst fk fk) f₀ (i₀ ≫ f₀) := by
    have s : IsPullback (pullback.fst fk fk) (pullback.snd fk fk) fk fk := IsPullback.of_hasPullback fk fk
    have t := s.paste_vert hi₀.flip
    rw [hi₀.w]
    apply t.flip
  have htop : IsPullback jP (pullback.fst fk fk) (pullback.fst f₀ f₀) i₀ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd f₀ f₀) (v₁₃ := f₀) (h₂₂ := f₀) ?_ hj1 (IsPullback.of_hasPullback f₀ f₀).flip
    rw [hj2]
    apply hrect
  refine ⟨?_, htop.paste_vert hi₀⟩
  refine MorphismProperty.of_isPullback htop.flip inferInstance


-- created on 2026-10-20
