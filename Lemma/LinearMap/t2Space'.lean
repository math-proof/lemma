import Mathlib
import Lemma.LinearMap.t2Space
open LinearMap


@[path]
private lemma main
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [TopologicalSpace K]
  [TopologicalSpace V]
  [T2Space K]
  [ContinuousAdd K]
  [ContinuousMul K]
  [IsModuleTopology K V] :
-- imply
  T2Space V := by
-- proof
  apply t2Space (R := K)


-- created on 2026-11-13
