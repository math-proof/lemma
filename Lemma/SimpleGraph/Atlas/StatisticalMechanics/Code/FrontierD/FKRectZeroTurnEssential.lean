import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectBlackBoundaryPrimalCycleWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnEssential.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWalk_winding_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) = fkRectMedialBoundaryPrimalSeamTrace R (fkRectConfigurationToMedialPairing R omega) d.1 (fkRectBlackOrbitList (fkRectConfigurationToMedialPairing R omega) d).length := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWalk_winding R omega d

/--
[fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnEssential.lean)
-/
@[path]
private lemma fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {C : FKMedialLoop R.medialTorus pairing}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hdC : (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d.1 = C)
  (hturn : canonicalComponentTurn pairing C = 0) :
-- imply
  ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection pairing d)) ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitDisplacement_ne_zero_of_turn_eq_zero R pairing C d hdC hturn

/--
[fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnEssential.lean)
-/
@[path]
private lemma fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hdisp : ons_pathDisplacement (List.ofFn (fkRectBlackOrbitDirection (fkRectConfigurationToMedialPairing R omega) d)) ≠ (0, 0)) :
-- imply
  fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryPrimalCycleWalk_winding_ne_zero_of_displacement R omega d hdisp

/--
[exists_nonzero_primalBoundaryWinding_of_zeroTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnEssential.lean)
-/
@[path]
private lemma exists_nonzero_primalBoundaryWinding_of_zeroTurn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
-- given
  (hturn : canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C = 0) :
-- imply
  ∃ d : FKMedialBlackDart R.medialTorus, (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk d.1 = C ∧ fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d) ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.exists_nonzero_primalBoundaryWinding_of_zeroTurn R omega C hturn


-- created on 2026-10-23
