import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleWeight.Part2
open Equiv Finset StatMech StatMech.FrontierD


/--
[fkMedialCheckerColor_localMate_eq_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkMedialCheckerColor_localMate_eq_not_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialCheckerColor (fkMedialLocalMate pairing d) = !fkMedialCheckerColor d := by
-- proof
  apply StatMech.FrontierD.fkMedialCheckerColor_localMate_eq_not pairing d

/--
[fkMedial_reachable_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkMedial_reachable_localMate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).Reachable d (fkMedialLocalMate pairing d) := by
-- proof
  apply StatMech.FrontierD.fkMedial_reachable_localMate pairing d

/--
[fkMedialBoundaryStep_localMate_conj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_localMate_conj_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  fkMedialLocalMateEquiv pairing * fkMedialBoundaryStep pairing * (fkMedialLocalMateEquiv pairing)⁻¹ = (fkMedialBoundaryStep pairing)⁻¹ := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_localMate_conj pairing

/--
[fkMedialBoundaryStep_sameCycle_localMate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkMedialBoundaryStep_sameCycle_localMate_iff_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d e : FKMedialDart T} :
-- imply
  (fkMedialBoundaryStep pairing).SameCycle (fkMedialLocalMate pairing d) (fkMedialLocalMate pairing e) ↔ (fkMedialBoundaryStep pairing).SameCycle d e := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryStep_sameCycle_localMate_iff pairing d e

/--
[fkRectMedialBoundaryPrimalSeamIncrement_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalSeamIncrement_localMate_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialBoundaryPrimalSeamIncrement R pairing (fkMedialLocalMate pairing d) = -fkRectMedialBoundaryPrimalSeamIncrement R pairing d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalSeamIncrement_localMate R pairing d

/--
[fkRectBoundaryCycleClassWinding_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkRectBoundaryCycleClassWinding_localMate_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectBoundaryCycleClassWinding R pairing (fkMedialLocalMate pairing d) = -fkRectBoundaryCycleClassWinding R pairing d := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryCycleClassWinding_localMate R pairing d

/--
[fkMedialBoundaryOrbitVisitCount_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkMedialBoundaryOrbitVisitCount_localMate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  permOrbitVisitCount (fkMedialBoundaryStep pairing) (fkMedialLocalMate pairing d) (fkMedialLocalMate pairing d) = permOrbitVisitCount (fkMedialBoundaryStep pairing) d d := by
-- proof
  apply StatMech.FrontierD.fkMedialBoundaryOrbitVisitCount_localMate pairing d

/--
[fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d) = permOrbitVisitCount (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega)) d d • fkRectBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R omega) d := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_visitCount_nsmul R omega d

/--
[fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean)
-/
@[path]
private lemma fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega (fkMedialLocalMate (fkRectConfigurationToMedialPairing R omega) d)) = -fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate R omega d


-- created on 2026-10-23
