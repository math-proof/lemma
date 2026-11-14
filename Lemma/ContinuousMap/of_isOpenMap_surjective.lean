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
-- given
  (h : IsOpenMap f)
  (hsurj : Function.Surjective f) :
-- imply
  IsModuleTopology R M := by
-- proof
  apply of_isQuotientMap (f := f)
  apply IsOpenQuotientMap.isQuotientMap
  refine ⟨hsurj, continuous_of_linearMap f, h⟩


-- created on 2026-11-13
