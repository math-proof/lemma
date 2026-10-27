import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
open StatMech StatMech.FrontierD


/--
[fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoopHeight.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q)
  (charge : ∀ omega : R.Configuration, FKRectZeroTurnMixedAnnulusCharge R omega) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + 2 * R.height + 2) ≤ (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge_height R hq charge

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoopHeight.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (charge : ∀ omega : R.Configuration, FKRectZeroTurnMixedAnnulusCharge R omega) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge_height R hq charge

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoopHeight.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (certificate : ∀ omega : R.Configuration, FKRectZeroTurnMixedTouchedCertificate R omega) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings_height R hq certificate

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_geometricResidues_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoopHeight.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_geometricResidues_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (hdisconnected : ∀ omega : R.Configuration, FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
  (hdual : ∀ omega : R.Configuration, FKRectZeroTurnOriginalDualSameSideUnique R omega) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_geometricResidues_height R hq hdisconnected hdual

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoopHeight.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (hregular : ∀ omega : R.Configuration, FKRectPrimalRankOneRegularNeighborhood R omega)
  (hdual : ∀ omega : R.Configuration, FKRectZeroTurnOriginalDualSameSideUnique R omega) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_regularNeighborhood_height R hq hregular hdual


-- created on 2026-10-23
