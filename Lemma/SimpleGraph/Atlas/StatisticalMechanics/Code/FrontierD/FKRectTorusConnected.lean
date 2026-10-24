import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectTorusGraph_adj_verticalPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_verticalPred_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {y : Fin R.height} :
-- imply
  (fkRectTorusGraph R).Adj (x, y) (x, SixVertexArrows.cyclicPred R.height_pos y) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_verticalPred R x y

/--
[fkRectTorusGraph_reachable_horizontalPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean)
-/
@[path]
private lemma fkRectTorusGraph_reachable_horizontalPred_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {y : Fin R.height} :
-- imply
  (fkRectTorusGraph R).Reachable (x, y) (SixVertexArrows.cyclicPred R.width_pos x, y) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_reachable_horizontalPred R x y

/--
[fkRectCoordinateCycleGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean)
-/
@[path]
private lemma fkRectCoordinateCycleGraph_connected_eq
  {R : FKRectTorus} :
-- imply
  (fkRectCoordinateCycleGraph R).Connected := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateCycleGraph_connected R

/--
[fkRectTorusGraph_reachable_of_coordinate_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean)
-/
@[path]
private lemma fkRectTorusGraph_reachable_of_coordinate_adj_eq
  {R : FKRectTorus}
  {u v : R.Vertex}
-- given
  (huv : (fkRectCoordinateCycleGraph R).Adj u v) :
-- imply
  (fkRectTorusGraph R).Reachable u v := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_reachable_of_coordinate_adj R huv

/--
[fkRectTorusGraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean)
-/
@[path]
private lemma fkRectTorusGraph_connected_eq
  {R : FKRectTorus} :
-- imply
  (fkRectTorusGraph R).Connected := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_connected R

/--
[fkRectFinsetClusterCount_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusConnected.lean)
-/
@[path]
private lemma fkRectFinsetClusterCount_univ_eq
  {R : FKRectTorus} :
-- imply
  fkRectFinsetClusterCount R Finset.univ = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectFinsetClusterCount_univ R


-- created on 2026-10-23
