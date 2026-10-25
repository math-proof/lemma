import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRect_boundaryOrbit_winding_dependent_of_openWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenBoundaryDependence.lean)
-/
@[path]
private lemma fkRect_boundaryOrbit_winding_dependent_of_openWalk_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x x}
  {d : FKMedialDart R.medialTorus} :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R F) d)) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRect_boundaryOrbit_winding_dependent_of_openWalk R F w d


-- created on 2026-10-23
