import Mathlib
import Lemma.ContinuousMap.of_isQuotientMap
open Topology IsModuleTopology IsQuotientMap


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
  [ContinuousAdd M]
  [ContinuousSMul R M]
  {f : N →ₗ[R] M}
  {g : M → N}
-- given
  (hc : Continuous g)
  (hi : Function.LeftInverse f g) :
-- imply
  IsModuleTopology R M := by
-- proof
  apply of_isQuotientMap (f := f)
  apply IsQuotientMap.of_inverse hc (continuous_of_linearMap f) hi


-- created on 2026-11-13
