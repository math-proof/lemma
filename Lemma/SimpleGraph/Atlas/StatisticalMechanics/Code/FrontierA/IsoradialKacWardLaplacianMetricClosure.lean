import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacianMetricClosure
open Finset SimpleGraph StatMech StatMech.FrontierA StatMech.FrontierA.MetricCriticalIsoradialGenusZeroOneEmbedding


/--
[det_eq_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacianMetricClosure.lean)
-/
@[path]
private lemma det_eq_laplacian_eq
  {g : Nat}
  {GraphVertex : Type u}
  {embedding : MetricCriticalIsoradialGenusZeroOneEmbedding g G DualVertex Qprimal Qdual Component} :
-- imply
  (1 - embedding.isoradial.primalKacWard).det = (-1 : Complex) ^ coneExceptionCount embedding.isoradial.primalExceptional * kwEulerPowerPrefactor (Fintype.card GraphVertex) (Fintype.card (finiteGraphEdge G)) * kwLaplacianEdgePrefactor embedding.isoradial.theta * (finiteTwistedLaplacian (isoradialLaplacianConductance embedding.thetaVertex) embedding.transport).det := by
-- proof
  apply StatMech.FrontierA.MetricCriticalIsoradialGenusZeroOneEmbedding.det_eq_laplacian embedding


-- created on 2026-10-23
