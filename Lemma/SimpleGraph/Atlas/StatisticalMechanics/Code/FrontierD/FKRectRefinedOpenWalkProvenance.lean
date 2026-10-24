import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenWalkProvenance
open StatMech StatMech.FrontierD


/--
[FKRectRefinedOpenWalkBlocksAlong.toOpenEdgeBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkProvenance.lean)
-/
@[path]
private lemma toOpenEdgeBlocks_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectRefinedOpenWalkBlocksAlong R F w p q l) :
-- imply
  FKRectRefinedOpenEdgeBlocks R F l := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenWalkBlocksAlong.toOpenEdgeBlocks R F h

/--
[FKRectRefinedOpenWalkBlocksAlong.toSquareWalkLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkProvenance.lean)
-/
@[path]
private lemma toSquareWalkLift_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectRefinedOpenWalkBlocksAlong R F w p q l) :
-- imply
  FKRectSquareWalkLift R w p q := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenWalkBlocksAlong.toSquareWalkLift R F h

/--
[exists_fkRectRefinedOpenWalkCarrierAlong](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkProvenance.lean)
-/
@[path]
private lemma exists_fkRectRefinedOpenWalkCarrierAlong_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
  {p : Int × Int}
-- given
  (hp : fkRectLiftedVertex R p = x) :
-- imply
  ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart, fkRectLiftedVertex R q = y ∧ FKRectSquareWalkLift R w p q ∧ FKRectIntegralSquareDartPath (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l ∧ FKRectRefinedOpenEdgeBlocks R F l ∧ FKRectRefinedOpenWalkBlocksAlong R F w p q l := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRefinedOpenWalkCarrierAlong R F w p hp


-- created on 2026-10-23
