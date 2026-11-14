import Mathlib
import Lemma.ContinuousMap.IffIsModuleTopologyEq_ModuleTopology
import Lemma.ContinuousMap.moduleTopology_trans
open ContinuousMap


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
  [IsModuleTopology R S]
  [TopologicalSpace M] :
-- imply
  IsModuleTopology R M ↔ IsModuleTopology S M := by
-- proof
  rw [IffIsModuleTopologyEq_ModuleTopology, IffIsModuleTopologyEq_ModuleTopology]
  rw [moduleTopology_trans (R := R) (S := S) (M := M)]


-- created on 2026-11-13
-- updated on 2026-11-14
