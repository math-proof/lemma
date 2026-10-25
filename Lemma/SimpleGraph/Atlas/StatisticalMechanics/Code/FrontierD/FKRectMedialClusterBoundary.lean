import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialClusterBoundary.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectMedialDartPrimalLabel_dartAtPrimalVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectMedialDartPrimalLabel_dartAtPrimalVertex_eq
  {R : FKRectTorus}
  {x : R.Vertex} :
-- imply
  fkRectMedialDartPrimalLabel R (fkRectMedialDartAtPrimalVertex R x) = x := by
-- proof
  apply StatMech.FrontierD.fkRectMedialDartPrimalLabel_dartAtPrimalVertex R x

/--
[fkRectMedialComponentToPrimalComponent_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectMedialComponentToPrimalComponent_mk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialComponentToPrimalComponent R omega ((fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d) = (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialComponentToPrimalComponent_mk R omega d

/--
[fkRectMedialComponentToPrimalComponent_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectMedialComponentToPrimalComponent_surjective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Surjective (fkRectMedialComponentToPrimalComponent R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialComponentToPrimalComponent_surjective R omega

/--
[fkRectNumClusters_le_medialLoopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectNumClusters_le_medialLoopCount_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectNumClusters R omega <= fkRectMedialLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNumClusters_le_medialLoopCount R omega

/--
[fkRectEulerHomologyDefect_le_cycleRankInt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_le_cycleRankInt_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex} :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) <= (F.card : Int) + (fkRectFinsetClusterCount R F : Int) - (Fintype.card R.Vertex : Int) := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_le_cycleRankInt R F

/--
[fkRectEulerHomologyDefect_eq_zero_of_cycleRankInt_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectEulerHomologyDefect_eq_zero_of_cycleRankInt_le_one_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
-- given
  (hrank : (F.card : Int) + (fkRectFinsetClusterCount R F : Int) - (Fintype.card R.Vertex : Int) <= 1) :
-- imply
  fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectEulerHomologyDefect_eq_zero_of_cycleRankInt_le_one R F hrank

/--
[fkRectCycleRankInt_ge_two_of_eulerHomologyDefect_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialClusterBoundary.lean)
-/
@[path]
private lemma fkRectCycleRankInt_ge_two_of_eulerHomologyDefect_eq_two_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
-- given
  (hdefect : fkRectEulerHomologyDefect R (fkRectConfigurationOfEdges R F) = 2) :
-- imply
  2 <= (F.card : Int) + (fkRectFinsetClusterCount R F : Int) - (Fintype.card R.Vertex : Int) := by
-- proof
  apply StatMech.FrontierD.fkRectCycleRankInt_ge_two_of_eulerHomologyDefect_eq_two R F hdefect


-- created on 2026-10-23
