import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[exists_fkRectRawHorizontalCrossingComponent_of_closedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma exists_fkRectRawHorizontalCrossingComponent_of_closedWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x x}
-- given
  (havoid : ∀ e ∈ p.edges, ¬ fkRectCrossesVerticalSeam R e)
  (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
-- imply
  ∃ C : (fkRectOpenGraph R (fkRectForceCutClosed R omega)).ConnectedComponent, FKRectRawHorizontalCrossingComponent R (fkRectForceCutClosed R omega) C := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRawHorizontalCrossingComponent_of_closedWalk R omega p havoid hwind

/--
[exists_fkRectRawHorizontalCrossingComponent_touched_by_closedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma exists_fkRectRawHorizontalCrossingComponent_touched_by_closedWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x x}
-- given
  (havoid : ∀ e ∈ p.edges, ¬ fkRectCrossesVerticalSeam R e)
  (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
-- imply
  ∃ C : (fkRectOpenGraph R (fkRectForceCutClosed R omega)).ConnectedComponent, FKRectRawHorizontalCrossingComponent R (fkRectForceCutClosed R omega) C ∧ ∃ z ∈ p.support, (fkRectOpenGraph R (fkRectForceCutClosed R omega)).connectedComponentMk z = C := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRawHorizontalCrossingComponent_touched_by_closedWalk R omega p havoid hwind

/--
[exists_fkRectRawHorizontalCrossingComponent_touched_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma exists_fkRectRawHorizontalCrossingComponent_touched_of_winding_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {x : R.Vertex}
  {p : (fkRectOpenGraph R eta).Walk x x}
-- given
  (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
-- imply
  ∃ C : (fkRectOpenGraph R eta).ConnectedComponent, FKRectRawHorizontalCrossingComponent R eta C ∧ ∃ z ∈ p.support, (fkRectOpenGraph R eta).connectedComponentMk z = C := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRawHorizontalCrossingComponent_touched_of_winding R eta p hwind

/--
[exists_fkRectRightBoundaryVertex_mem_support_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma exists_fkRectRightBoundaryVertex_mem_support_of_winding_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {x : R.Vertex}
  {p : (fkRectOpenGraph R eta).Walk x x}
-- given
  (hwind : (fkRectWalkWinding R p).1 ≠ 0) :
-- imply
  ∃ y : Fin R.height, (fkRectRightColumn R, y) ∈ p.support := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRightBoundaryVertex_mem_support_of_winding R eta p hwind

/--
[fkRectBlackOrbitDisplacement_fst_sub_snd_eq_zero_of_avoidsSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma fkRectBlackOrbitDisplacement_fst_sub_snd_eq_zero_of_avoidsSeam_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C)
  (hdC : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d.1 = C) :
-- imply
  (ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection (fkRectConfigurationToMedialPairing R omega) d))).1 - (ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection (fkRectConfigurationToMedialPairing R omega) d))).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitDisplacement_fst_sub_snd_eq_zero_of_avoidsSeam R omega C havoid d hdC

/--
[fkRectBlackBoundaryPrimalCycleWalk_winding_snd_eq_zero_of_avoidsSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWalk_winding_snd_eq_zero_of_avoidsSeam_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C)
  (hdC : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d.1 = C) :
-- imply
  (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWalk_winding_snd_eq_zero_of_avoidsSeam R omega C havoid d hdC

/--
[exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean)
-/
@[path]
private lemma exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
-- given
  (hturn : FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C = 0)
  (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C) :
-- imply
  ∃ d : FKMedialBlackDart R.medialTorus, (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d.1 = C ∧ (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).1 ≠ 0 ∧ (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 = 0 := by
-- proof
  apply StatMech.FrontierD.exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam R omega C hturn havoid


-- created on 2026-10-23
