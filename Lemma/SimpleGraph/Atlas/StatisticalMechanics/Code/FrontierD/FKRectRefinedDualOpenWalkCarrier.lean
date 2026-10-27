import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
open StatMech StatMech.FrontierD


/--
[FKRectRefinedDualOpenWalkBlocksAlong.toOpenEdgeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualOpenWalkCarrier.lean)
-/
@[path]
private lemma toOpenEdgeBlocks_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l) :
-- imply
  FKRectRefinedDualOpenEdgeBlocks R omega l := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenWalkBlocksAlong.toOpenEdgeBlocks R omega h

/--
[FKRectRefinedDualOpenWalkBlocksAlong.toSquareWalkLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualOpenWalkCarrier.lean)
-/
@[path]
private lemma toSquareWalkLift_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l) :
-- imply
  FKRectSquareWalkLift R w p q := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedDualOpenWalkBlocksAlong.toSquareWalkLift R omega h

/--
[exists_fkRectRefinedDualOpenWalkCarrierAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualOpenWalkCarrier.lean)
-/
@[path]
private lemma exists_fkRectRefinedDualOpenWalkCarrierAlong_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x y}
  {p : Int × Int}
-- given
  (hp : fkRectLiftedVertex R p = x) :
-- imply
  ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart, fkRectLiftedVertex R q = y ∧ FKRectSquareWalkLift R w p q ∧ FKRectIntegralSquareDartPath (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) l ∧ FKRectRefinedDualOpenEdgeBlocks R omega l ∧ FKRectRefinedDualOpenWalkBlocksAlong R omega w p q l := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRefinedDualOpenWalkCarrierAlong R omega w p hp

/--
[exists_fkRectRefinedDualOpenWalkCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualOpenWalkCarrier.lean)
-/
@[path]
private lemma exists_fkRectRefinedDualOpenWalkCarrier_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x y}
  {p : Int × Int}
-- given
  (hp : fkRectLiftedVertex R p = x) :
-- imply
  ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart, fkRectLiftedVertex R q = y ∧ FKRectSquareWalkLift R w p q ∧ FKRectIntegralSquareDartPath (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q)) l ∧ FKRectRefinedDualOpenEdgeBlocks R omega l := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRefinedDualOpenWalkCarrier R omega w p hp


-- created on 2026-10-23
