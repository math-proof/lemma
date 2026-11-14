import Mathlib
import Lemma.ContinuousMap.isTopologicalModule
import Lemma.ContinuousMap.moduleTopology_le
import Lemma.ContinuousMap.isModuleTopology
open ModuleTopology IsModuleTopology Continuous ContinuousMap


@[path]
private lemma main
  [CommRing R]
  [TopologicalSpace R]
  [CommRing S]
  [TopologicalSpace S]
  [Algebra R S]
  [AddCommGroup M]
  [Module R M]
  [Module S M]
  [IsScalarTower R S M]
  [IsTopologicalRing R]
  [Module.Finite R S]
  [IsModuleTopology R S] :
-- imply
  moduleTopology R M = moduleTopology S M := by
-- proof
  have := isTopologicalModule (R := R) (M := S)
  refine le_antisymm moduleTopology_le ?_
  let instTS : TopologicalSpace M := moduleTopology R M
  have : IsModuleTopology R M := isModuleTopology (R := R) (S := M)
  have : ContinuousAdd M := continuousAdd R M
  have ⟨cts_smul⟩ : ContinuousSMul R M := continuousSMul R M
  suffices ContinuousSMul S M from _root_.moduleTopology_le S M
  constructor
  let bil : S →ₗ[R] M →ₗ[R] M := {
    toFun s := {
      toFun m := s • m
      map_add' := DistribSMul.smul_add s
      map_smul' := smul_comm s
    }
    map_add' s t := by
      ext m
      apply Module.add_smul s t m
    map_smul' r s := by
      ext m
      apply IsScalarTower.smul_assoc r s m
  }
  apply continuous_bilinear_of_finite_left bil


-- created on 2026-11-13
-- updated on 2026-11-14
