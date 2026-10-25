import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
open StatMech StatMech.FrontierD


/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {charge : FKRectZeroTurnMixedAnnulusCharge R omega} :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimalDual_of_mixedCharge R omega charge

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {charge : FKRectZeroTurnMixedAnnulusCharge R omega} :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCharge R omega charge

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCrossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {crossing : FKRectZeroTurnCutRemainderComponent R omega → FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega}
-- given
  (hunique : ∀ C D, crossing C = crossing D → fkRectZeroTurnRemainderSide R omega C = fkRectZeroTurnRemainderSide R omega D → C = D) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedCrossing R omega crossing hunique

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedAnnulusCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedAnchor_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {crossing : FKRectZeroTurnCutRemainderComponent R omega → FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega}
  {anchor : FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega → Bool → FKMedialDart R.medialTorus}
-- given
  (hanchor : ∀ C, (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk (anchor (crossing C) (fkRectZeroTurnRemainderSide R omega C)) = C.1) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_mixedAnchor R omega crossing anchor hanchor


-- created on 2026-10-23
