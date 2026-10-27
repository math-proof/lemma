import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma surj_appTop_of_isPullback_away
  {S : Type u} [CommRing S] {A : (Scheme : Type (u + 1))} (f : A ⟶ Spec (CommRingCat.of S))
  (hΓ : ∀ r : S, Function.Surjective ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
  (r : S) (B : Type u) [CommRing B] [Algebra S B] [IsLocalization.Away r B]
  {A' : (Scheme : Type (u + 1))} (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
  (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) :
    Function.Surjective (f'.appTop).hom := by
  classical
  let L := Localization.Away r
  let ε : AlgEquiv S L B := IsLocalization.algEquiv (Submonoid.powers r) L B
  have hε : (ε.toAlgHom.toRingHom).comp (algebraMap S L) = algebraMap S B := ε.toAlgHom.comp_algebraMap
  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap S B)) = Spec.map (CommRingCat.ofHom ε.toAlgHom.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S L)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]
  let ιε : Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of L) := Scheme.Spec.mapIso (ε.toRingEquiv.toCommRingCatIso).op
  have hιε : ιε.hom = Spec.map (CommRingCat.ofHom ε.toAlgHom.toRingHom) := rfl
  have hsq : IsPullback g (f' ≫ ιε.hom) f (Spec.map (CommRingCat.ofHom (algebraMap S L))) := by
    have := hg
    rw [hSpec, ← hιε] at this
    refine IsPullback.of_iso this (Iso.refl _) (Iso.refl _) ιε (Iso.refl _) (by simp) (by simp) (by simp) (by simp [hιε])
  let P₀ := pullback f (Spec.map (CommRingCat.ofHom (algebraMap S L)))
  let θ : A' ≅ P₀ := hsq.isoPullback
  have hθ : θ.hom ≫ pullback.snd _ _ = f' ≫ ιε.hom := hsq.isoPullback_hom_snd
  have h1 : Function.Surjective ((θ.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S L)))).appTop).hom := by
    rw [Scheme.Hom.comp_appTop]
    show Function.Surjective ((θ.hom.appTop).hom ∘ (pullback.snd f _).appTop.hom)
    let _ : IsIso θ.hom.appTop := by
      rw [← Scheme.Γ_map_op]
      apply Functor.map_isIso Scheme.Γ θ.op.hom
    apply (ConcreteCategory.bijective_of_isIso θ.hom.appTop).2.comp (hΓ r)
  rw [hθ, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp] at h1
  apply Function.Surjective.of_comp h1

/--
[AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_surjective_appTop_and_forall_away_of_isPullback_of_forall_surjective_appTop_away.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] {A : (Scheme : Type (u + 1))} (f : A ⟶ Spec (CommRingCat.of S))
  (hΓ : ∀ r : S, Function.Surjective ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))).appTop).hom)
  (r : S) (B : Type u) [CommRing B] [Algebra S B] [IsLocalization.Away r B]
  {A' : (Scheme : Type (u + 1))} (f' : A' ⟶ Spec (CommRingCat.of B)) (g : A' ⟶ A)
  (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom (algebraMap S B)))) :
    Function.Surjective (f'.appTop).hom ∧ ∀ r' : B, Function.Surjective ((pullback.snd f' (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r'))))).appTop).hom := by
  classical
  refine ⟨surj_appTop_of_isPullback_away f hΓ r B f' g hg, fun r' => ?_⟩
  let T := Localization.Away r'
  obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hs⟩ := IsLocalization.surj (Submonoid.powers r) (S := B) r'
  have hu : IsUnit (algebraMap B T (algebraMap S B (r ^ n))) := by
    rw [map_pow, map_pow]
    apply (((IsLocalization.Away.algebraMap_isUnit (S := B) r).map (algebraMap B T)).pow n)
  let _ : IsLocalization.Away (algebraMap S B s) T := by
    rw [← hs]
    apply IsLocalization.Away.mul_of_isUnit r' _ hu
  let _ : IsLocalization.Away (s * r) T := IsLocalization.Away.mul B T r s
  apply surj_appTop_of_isPullback_away f hΓ (s * r) T _ _ <| by
    have := (IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom (algebraMap B T)))).paste_horiz hg
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq S B T] at this


-- created on 2026-10-20
