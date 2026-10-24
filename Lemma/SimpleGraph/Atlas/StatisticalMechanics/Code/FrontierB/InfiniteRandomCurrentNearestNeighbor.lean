import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.InfiniteRandomCurrentNearestNeighbor
open Filter MeasureTheory Set Topology StatMech StatMech.FrontierB


/--
[nearestNeighborInfiniteRandomCurrentPackage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteRandomCurrentNearestNeighbor.lean)
-/
@[path]
private lemma nearestNeighborInfiniteRandomCurrentPackage_eq
  {d : Nat}
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hd : 1 <= d) :
-- imply
  NearestNeighborInfiniteRandomCurrentPackage d beta hbeta hd where plus_weak := by
-- proof
  apply StatMech.FrontierB.nearestNeighborInfiniteRandomCurrentPackage d beta hbeta hd


-- created on 2026-10-23
