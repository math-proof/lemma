import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectMedialClosedCycles
open Equiv StatMech StatMech.FrontierD


/--
[fkRectClosedMedialPairing_eq_not_vertexParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectClosedMedialPairing_eq_not_vertexParity_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectClosedMedialPairing R v = !fkMedialVertexParity v := by
-- proof
  apply StatMech.FrontierD.fkRectClosedMedialPairing_eq_not_vertexParity R v

/--
[fkRectConfigurationToMedialPairing_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectConfigurationToMedialPairing_empty_eq
  {R : FKRectTorus} :
-- imply
  fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R ∅) = fkRectClosedMedialPairing R := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationToMedialPairing_empty R

/--
[fkRectFullMedialPairing_eq_vertexParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectFullMedialPairing_eq_vertexParity_eq
  {R : FKRectTorus}
  {v : R.medialTorus.Vertex} :
-- imply
  fkRectFullMedialPairing R v = fkMedialVertexParity v := by
-- proof
  apply StatMech.FrontierD.fkRectFullMedialPairing_eq_vertexParity R v

/--
[fkRectClosedBlackBoundaryPerm_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectClosedBlackBoundaryPerm_pow_four_eq
  {R : FKRectTorus} :
-- imply
  fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R) ^ 4 = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectClosedBlackBoundaryPerm_pow_four R

/--
[fkRectClosedBlackBoundaryPerm_sq_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectClosedBlackBoundaryPerm_sq_ne_eq
  {R : FKRectTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ((fkMedialBlackBoundaryPerm (fkRectClosedMedialPairing R)) ^ 2) d ≠ d := by
-- proof
  apply StatMech.FrontierD.fkRectClosedBlackBoundaryPerm_sq_ne R d

/--
[fkRectFullBlackBoundaryPerm_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectFullBlackBoundaryPerm_pow_four_eq
  {R : FKRectTorus} :
-- imply
  fkMedialBlackBoundaryPerm (fkRectFullMedialPairing R) ^ 4 = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectFullBlackBoundaryPerm_pow_four R

/--
[fkRectFullBlackBoundaryPerm_sq_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectFullBlackBoundaryPerm_sq_ne_eq
  {R : FKRectTorus}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  ((fkMedialBlackBoundaryPerm (fkRectFullMedialPairing R)) ^ 2) d ≠ d := by
-- proof
  apply StatMech.FrontierD.fkRectFullBlackBoundaryPerm_sq_ne R d

/--
[fkRectClosedMedialLoopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectClosedMedialLoopCount_eq
  {R : FKRectTorus} :
-- imply
  fkMedialLoopCount R.medialTorus (fkRectClosedMedialPairing R) = R.width * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectClosedMedialLoopCount R

/--
[fkRectFullMedialLoopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectFullMedialLoopCount_eq
  {R : FKRectTorus} :
-- imply
  fkMedialLoopCount R.medialTorus (fkRectFullMedialPairing R) = R.width * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectFullMedialLoopCount R

/--
[fkRectMedialLoopCount_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_empty_eq
  {R : FKRectTorus} :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R ∅) = R.width * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_empty R

/--
[fkRectEulerHomologyDefect_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_empty_eq
  {R : FKRectTorus} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R ∅) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_empty R

/--
[fkRectMedialLoopCount_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectMedialLoopCount_univ_eq
  {R : FKRectTorus} :
-- imply
  fkRectMedialLoopCount R (fkRectConfigurationOfEdges R Finset.univ) = R.width * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCount_univ R

/--
[fkRectEulerHomologyDefect_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClosedCycles.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_univ_eq
  {R : FKRectTorus} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R Finset.univ) = 2 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_univ R


-- created on 2026-10-23
