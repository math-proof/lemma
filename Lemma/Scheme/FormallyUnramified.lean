import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma ring_core
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  -- given
  (H : ∀ (p : Ideal R) [p.IsPrime], Algebra.FormallyUnramified (Localization.AtPrime p) (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) :
  -- imply
  Algebra.FormallyUnramified R S := by
  -- proof
  rw [Algebra.formallyUnramified_iff_forall]
  intro Q
  let q : Ideal S := Q.asIdeal
  let p : Ideal R := q.under R
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have f : AlgHom S Sp Sq := by
    refine IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl) (f := Algebra.ofId _ _) ?_
    rintro ⟨_, x, hx, rfl⟩
    have h__af := (IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x, by simp_all [q.over_def p]⟩)
    simp at h__af
    apply h__af
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := IsScalarTower.to₁₃₄ _ S _ _
  have heq : algebraMap Rp Sq = (algebraMap Sp Sq).comp (algebraMap Rp Sp) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsScalarTower Rp Sp Sq := IsScalarTower.of_algebraMap_eq' heq
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq := by
    refine IsLocalization.isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _ ?_
    rintro _ ⟨x, hx, rfl⟩
    simp_all [q.over_def p]
  have h1 : Algebra.FormallyUnramified Sp Sq :=
    Algebra.FormallyUnramified.of_isLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  have h2 : Algebra.FormallyUnramified Rp Sp := H p
  have h3 : Algebra.FormallyUnramified Rp Sq := Algebra.FormallyUnramified.comp Rp Sp Sq
  have h4 : Algebra.FormallyUnramified R Rp := Algebra.FormallyUnramified.of_isLocalization p.primeCompl
  apply Algebra.FormallyUnramified.comp R Rp Sq

private lemma ring_hyp
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (p : Ideal R) [p.IsPrime]
  -- given
  (H : FormallyUnramified (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
  -- imply
  Algebra.FormallyUnramified (Localization.AtPrime p) (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
  -- proof
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  have hpo : Algebra.IsPushout R Rp S Sp := (Algebra.isPushout_of_isLocalization p.primeCompl Rp S Sp).symm
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R Rp S Sp)
  have e : Spec.map (CommRingCat.ofHom (algebraMap Rp Sp)) =
    hsq.flip.isoPullback.hom ≫ pullback.snd _ _ := (hsq.flip.isoPullback_hom_snd).symm
  have : FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap Rp Sp))) := by
    rw [e]
    apply MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso @FormallyUnramified _) H
  rwa [HasRingHomProperty.Spec_iff (P := @FormallyUnramified), CommRingCat.hom_ofHom,
    RingHom.formallyUnramified_algebraMap] at this

private lemma of_affine
  {R : Type u} [CommRing R]
  {X : (Scheme : Type (u + 1))}
  (g : X ⟶ Spec (CommRingCat.of R))
  -- given
  (H : ∀ (p : Ideal R) [p.IsPrime], FormallyUnramified (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))))))
  (hX : ∃ S, X = Spec S) :
  -- imply
  FormallyUnramified g := by
  -- proof
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  have eφ : φ = CommRingCat.ofHom (algebraMap R S) := by
    ext
    rfl
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  show (algebraMap R S).FormallyUnramified
  rw [RingHom.formallyUnramified_algebraMap]
  refine ring_core (fun p _ => ring_hyp p ?_)
  rw [← eφ]
  apply H p

/--
[AlgebraicGeometry_FormallyUnramified_of_forall_pullback_snd_localization_atPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_FormallyUnramified_of_forall_pullback_snd_localization_atPrime.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {X : (Scheme : Type (u + 1))}
  (g : X ⟶ Spec (CommRingCat.of R))
  -- given
  (H : ∀ (p : Ideal R) [p.IsPrime], FormallyUnramified (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :
  -- imply
  FormallyUnramified g := by
  -- proof
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
  intro i
  refine of_affine _ (fun p _ => ?_) ⟨_, rfl⟩
  have h2 := H p
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  have h1 : FormallyUnramified (pullback.snd (X.affineCover.f i)
    (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  refine MorphismProperty.comp_mem _ _ _ (MorphismProperty.of_isIso @FormallyUnramified _)
    (MorphismProperty.comp_mem _ _ _ h1 h2)


-- created on 2026-10-20
