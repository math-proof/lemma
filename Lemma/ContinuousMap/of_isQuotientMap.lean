import Mathlib
import Lemma.ContinuousMap.IffIsModuleTopologyEq_ModuleTopology
open Topology ModuleTopology Continuous


@[path]
private lemma main
  [Ring R]
  [TopologicalSpace R]
  [AddCommGroup M]
  [Module R M]
  [TopologicalSpace M]
  [AddCommGroup N]
  [Module R N]
  [TopologicalSpace N]
  [IsModuleTopology R N]
  {f : N →ₗ[R] M}
-- given
  (h : IsQuotientMap f) :
-- imply
  IsModuleTopology R M := by
-- proof
  rw [IffIsModuleTopologyEq_ModuleTopology, eq_coinduced_of_surjective h.surjective,
    h.eq_coinduced]


-- created on 2026-11-13
