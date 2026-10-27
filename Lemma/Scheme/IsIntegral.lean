import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
  {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (.of A)) [Flat f] [IsIntegral ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A L))))] :
  -- imply
  IsIntegral X := by
  -- proof
  classical
  set g := Spec.map (CommRingCat.ofHom (algebraMap A L)) with hg
  set pr := pullback.fst f g with hpr
  let _ : QuasiCompact g := inferInstance
  let _ : IsDominant g := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap A L))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro a ha
    rw [RingHom.mem_ker] at ha
    have : a = 0 := (IsFractionRing.injective A L) (by rw [ha, map_zero])
    rw [this]
    apply Ideal.zero_mem
  let _ : IsSchemeTheoreticallyDominant g := IsSchemeTheoreticallyDominant.of_isDominant g
  let _ : IsSchemeTheoreticallyDominant pr := IsSchemeTheoreticallyDominant.pullbackFst f g
  let _ : QuasiCompact pr := inferInstance
  let _ : IsDominant pr := inferInstance
  let _ : IsReduced X := IsSchemeTheoreticallyDominant.isReduced pr
  let _ : IrreducibleSpace X := by
    have hirr : IsIrreducible (Set.range pr.base) := by
      have := (IrreducibleSpace.isIrreducible_univ (↑(pullback f g))).image pr.base pr.base.hom.continuous.continuousOn
      rwa [Set.image_univ] at this
    have hcl : closure (Set.range pr.base) = Set.univ := pr.denseRange.closure_range
    have := hirr.closure
    rw [hcl] at this
    exact (irreducibleSpace_def _).mpr this
  apply isIntegral_of_irreducibleSpace_of_isReduced X


-- created on 2026-10-20
