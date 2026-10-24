import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualPrimalOpenDependence
open StatMech StatMech.FrontierD


/--
[fkRect_dualOpen_primalOpen_closedWalks_not_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalOpenDependence.lean)
-/
@[path]
private lemma fkRect_dualOpen_primalOpen_closedWalks_not_windingIndependent_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {z : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Walk x x}
  {w : (fkRectOpenGraph R omega).Walk y y} :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R z) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRect_dualOpen_primalOpen_closedWalks_not_windingIndependent R omega z w


-- created on 2026-10-23
