import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualEdgeInteraction
open Finset StatMech StatMech.FrontierD


/--
[fkRectRefined_perpendicular_centerlines_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualEdgeInteraction.lean)
-/
@[path]
private lemma fkRectRefined_perpendicular_centerlines_interaction_eq
  {L : Nat}
  [Fact (8 < L)]
  {pairing : Bool}
  {c : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedPrimalCenterlineDarts (!pairing) c).map (fkRectIntegralSquareDartMod L)) ((fkRectRefinedPrimalCenterlineDarts pairing c).map (fkRectIntegralSquareDartMod L)) = if pairing then 1 else -1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefined_perpendicular_centerlines_interaction pairing c


-- created on 2026-10-23
