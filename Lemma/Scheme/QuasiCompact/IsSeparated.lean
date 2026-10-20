import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_quasiCompact_and_isSeparated_of_isPullback_of_faithfullyFlat.lean)
-/
@[path]
private lemma main
  {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
  {X X' : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X) [QuasiCompact f'] [IsSeparated f']
  (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) :
  -- imply
  QuasiCompact f ∧ IsSeparated f := by
  -- proof
  have hff : (CommRingCat.ofHom (algebraMap S S')).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap S S'))).mpr hff
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty (Scheme : Type (u + 1))) (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
    ⟨⟨hsurj, hflat⟩, inferInstance⟩
  refine ⟨?_, ?_⟩
  ·
    let _ : Surjective c := MorphismProperty.of_isPullback (P := @Surjective) hc.flip hsurj
    let _ : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
    have hs : Function.Surjective c.base := c.surjective
    have hX : IsCompact (Set.univ : Set X) := by
      rw [← hs.range_eq]
      apply isCompact_range c.continuous
    let _ : CompactSpace X := ⟨hX⟩
    apply (quasiCompact_iff_compactSpace f).mpr inferInstance
  ·
    have hP : (MorphismProperty.diagonal @UniversallyClosed : MorphismProperty (Scheme : Type (u + 1))) f' := by
      show UniversallyClosed (pullback.diagonal f')
      infer_instance
    let hU : UniversallyClosed (pullback.diagonal f) :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc.flip hQ hP
    refine ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range⟩


-- created on 2026-10-20
