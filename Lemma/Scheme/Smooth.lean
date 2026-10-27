import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_smooth_pullback_snd_specMap_of_forall_mem_smoothLocus_of_isFractionRing.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
  {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (.of A)) [LocallyOfFinitePresentation f]
  (hgen : ∀ x : X, (f.base x).asIdeal = ⊥ → x ∈ f.smoothLocus) :
  -- imply
  Smooth (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A L)))) := by
  -- proof
  classical
  set jL := Spec.map (CommRingCat.ofHom (algebraMap A L)) with hjL
  set fst := pullback.fst f jL with hfst
  set snd := pullback.snd f jL with hsnd
  set V : X.Opens := f.smoothLocus with hV
  let hsm : Smooth (V.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    apply Scheme.Opens.ι_preimage_self V
  have hsq : IsPullback fst snd f jL := IsPullback.of_hasPullback f jL
  have hsqV : IsPullback (morphismRestrict fst V) (Scheme.Opens.ι ((TopologicalSpace.Opens.map fst.base).obj V) ≫ snd) (V.ι ≫ f) jL :=
    (isPullback_morphismRestrict fst V).paste_vert hsq
  let _ : Smooth (Scheme.Opens.ι ((TopologicalSpace.Opens.map fst.base).obj V) ≫ snd) :=
    MorphismProperty.of_isPullback (P := @Smooth) hsqV hsm
  have hmem : ∀ z : ↑(pullback f jL), fst.base z ∈ V := by
    intro z
    apply hgen
    have h1 : f.base (fst.base z) = jL.base (snd.base z) := by
      change (fst ≫ f).base z = (snd ≫ jL).base z
      rw [pullback.condition]
    rw [h1]
    change Ideal.comap (algebraMap A L) (snd.base z).asIdeal = ⊥
    have h2 : (snd.base z).asIdeal = ⊥ := by
      ext a
      simp only [Ideal.mem_bot]
      constructor
      ·
        intro ha
        by_contra hne
        apply (snd.base z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha (IsUnit.mk0 a hne))
      ·
        rintro rfl
        apply Ideal.zero_mem _
    rw [h2, Ideal.comap_bot_of_injective _ (IsFractionRing.injective A L)]
  have htop : (Scheme.Opens.ι ((TopologicalSpace.Opens.map fst.base).obj V) ≫ snd).smoothLocus = ⊤ :=
    Scheme.Hom.smoothLocus_eq_top _
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine top_le_iff.mp (fun z _ => ?_)
  have hz' : (⟨z, hmem z⟩ : ↥((TopologicalSpace.Opens.map fst.base).obj V)) ∈ ((TopologicalSpace.Opens.map (Scheme.Opens.ι ((TopologicalSpace.Opens.map fst.base).obj V)).base).obj snd.smoothLocus) := by
    rw [htop]
    trivial
  refine hz'


-- created on 2026-10-20
