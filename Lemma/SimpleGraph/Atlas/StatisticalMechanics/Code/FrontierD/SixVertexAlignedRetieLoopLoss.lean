import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAlignedRetieLoopLoss
open StatMech StatMech.FrontierD StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss


/--
[omega_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma omega_ice_eq :
-- imply
  omega.IceRule := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.omega_ice

/--
[eta_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma eta_ice_eq :
-- imply
  eta.IceRule := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.eta_ice

/--
[locallyDegreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma locallyDegreeTwo_eq :
-- imply
  SixVertexLocallyDegreeTwo omega eta := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.locallyDegreeTwo

/--
[source_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma source_compatible_eq
  {layer : Bool}
  {v : sixVertexFourByTwoTorus.Vertex} :
-- imply
  fkLoopPairingCompatible (source layer v) (if layer then eta else omega) v := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.source_compatible layer v

/--
[source_aligned_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma source_aligned_exit_eq
  {v : sixVertexFourByTwoTorus.Vertex}
  {d : Fin 4}
-- given
  (hdisagree : sixVertexLocalIncomingPattern omega v d != sixVertexLocalIncomingPattern eta v d)
  (hincoming : sixVertexLocalIncomingPattern omega v d = true) :
-- imply
  sixVertexLocalIncomingPattern omega v (localMate (source true v) (localMate (source false v) d)) != sixVertexLocalIncomingPattern eta v (localMate (source true v) (localMate (source false v) d)) := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.source_aligned_exit v d hdisagree hincoming

/--
[lower_source_cycleCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma lower_source_cycleCount_eq :
-- imply
  StatMech.FrontierA.permCycleCount (fkMedialBlackBoundaryPerm lowerPairing) = 4 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.lower_source_cycleCount

/--
[upper_source_cycleCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma upper_source_cycleCount_eq :
-- imply
  StatMech.FrontierA.permCycleCount (fkMedialBlackBoundaryPerm upperPairing) = 4 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.upper_source_cycleCount

/--
[lower_target_cycleCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma lower_target_cycleCount_eq :
-- imply
  StatMech.FrontierA.permCycleCount (fkMedialBlackBoundaryPerm (retie lowerPairing)) = 2 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.lower_target_cycleCount

/--
[upper_target_cycleCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma upper_target_cycleCount_eq :
-- imply
  StatMech.FrontierA.permCycleCount (fkMedialBlackBoundaryPerm (retie upperPairing)) = 2 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.upper_target_cycleCount

/--
[lower_source_loopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma lower_source_loopCount_eq :
-- imply
  fkMedialLoopCount sixVertexFourByTwoTorus lowerPairing = 4 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.lower_source_loopCount

/--
[upper_source_loopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma upper_source_loopCount_eq :
-- imply
  fkMedialLoopCount sixVertexFourByTwoTorus upperPairing = 4 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.upper_source_loopCount

/--
[lower_target_loopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma lower_target_loopCount_eq :
-- imply
  fkMedialLoopCount sixVertexFourByTwoTorus (retie lowerPairing) = 2 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.lower_target_loopCount

/--
[upper_target_loopCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma upper_target_loopCount_eq :
-- imply
  fkMedialLoopCount sixVertexFourByTwoTorus (retie upperPairing) = 2 := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.upper_target_loopCount

/--
[totalLoopCount_loss](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma totalLoopCount_loss_eq :
-- imply
  fkMedialLoopCount sixVertexFourByTwoTorus (retie (source false)) + fkMedialLoopCount sixVertexFourByTwoTorus (retie (source true)) + 4 = fkMedialLoopCount sixVertexFourByTwoTorus (source false) + fkMedialLoopCount sixVertexFourByTwoTorus (source true) := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.totalLoopCount_loss

/--
[not_layeredTwoCutBalanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedRetieLoopLoss.lean)
-/
@[path]
private lemma not_layeredTwoCutBalanced_eq :
-- imply
  Not (FKMedialLayeredTwoCutBalanced source first second) := by
-- proof
  apply StatMech.FrontierD.FourByTwoAlignedRetieLoopLoss.not_layeredTwoCutBalanced


-- created on 2026-10-23
