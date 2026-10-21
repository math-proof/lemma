import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma flat_specMap
  {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S'] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  show (algebraMap S S').Flat
  have h : (algebraMap S S').toAlgebra = ‹Algebra S S'› := Algebra.algebra_ext _ _ fun _ => rfl
  unfold RingHom.Flat
  rw [h]
  infer_instance

private lemma helper_main
  {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
  {T T' T'' : (Scheme : Type (u + 1))} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
  (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
  (t'' : T'' ⟶ Spec (CommRingCat.of (TensorProduct S S' S'))) (q₁ q₂ : T'' ⟶ T')
  (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : RingHom S' (TensorProduct S S' S')))))
  (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : AlgHom S S' (TensorProduct S S' S')).toRingHom)))
  (hq : q₁ ≫ p = q₂ ≫ p)
  {Y : (Scheme : Type (u + 1))} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap S S'))
  let ιL := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : RingHom S' (TensorProduct S S' S')))
  let ιR := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : AlgHom S S' (TensorProduct S S' S')).toRingHom)
  let _ : Flat ι := flat_specMap
  let _ : Surjective ι := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  let _ : QuasiCompact ι := inferInstance
  let _ : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  let _ : Surjective p := MorphismProperty.of_isPullback hp.flip inferInstance
  let _ : QuasiCompact p := MorphismProperty.of_isPullback hp.flip inferInstance
  let _ : EffectiveEpi p := inferInstance
  have hSpec : IsPullback ιL ιR ι ι :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')
  have hbig : IsPullback (t'' ≫ ιR) q₁ ι (t' ≫ ι) := hq₁.flip.paste_horiz hSpec.flip
  have hbig' : IsPullback (q₂ ≫ t') q₁ ι (p ≫ t) := by
    rw [hq₂.w, hp.w]
    apply hbig
  have hPB : IsPullback q₂ q₁ p p := IsPullback.of_right hbig' hq.symm hp.flip
  have key : ∀ {Z : (Scheme : Type (u + 1))} (g₁ g₂ : Z ⟶ T'), g₁ ≫ p = g₂ ≫ p → g₁ ≫ φ' = g₂ ≫ φ' := by
    intro Z g₁ g₂ hg
    have h1 := hPB.lift_fst g₂ g₁ hg.symm
    have h2 := hPB.lift_snd g₂ g₁ hg.symm
    calc
      _ = (hPB.lift g₂ g₁ hg.symm ≫ q₁) ≫ φ' := by rw [h2]
      _ = hPB.lift g₂ g₁ hg.symm ≫ (q₂ ≫ φ') := by rw [Category.assoc, hφ']
      _ = g₂ ≫ φ' := by rw [← Category.assoc, h1]
  refine ⟨EffectiveEpi.desc p φ' key, EffectiveEpi.fac p φ' key, fun φ hφ => EffectiveEpi.uniq p φ' key φ hφ⟩

/--
[AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_comp_eq_of_isPullback_of_faithfullyFlat.lean)
-/
@[path]
private lemma main
  {S S' : Type u} [CommRing S] [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
  {T T' T'' : (Scheme : Type (u + 1))} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S'))
  (p : T' ⟶ T) (hp : IsPullback p t' t (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
  (t'' : T'' ⟶ Spec (CommRingCat.of (TensorProduct S S' S'))) (q₁ q₂ : T'' ⟶ T')
  (hq₁ : IsPullback q₁ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : RingHom S' (TensorProduct S S' S')))))
  (hq₂ : IsPullback q₂ t'' t' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : AlgHom S S' (TensorProduct S S' S')).toRingHom)))
  (hq : q₁ ≫ p = q₂ ≫ p)
  {Y : (Scheme : Type (u + 1))} (φ' : T' ⟶ Y) (hφ' : q₁ ≫ φ' = q₂ ≫ φ') :
    ∃! φ : T ⟶ Y, p ≫ φ = φ' :=
  helper_main t t' p hp t'' q₁ q₂ hq₁ hq₂ hq φ' hφ'


-- created on 2026-10-20
