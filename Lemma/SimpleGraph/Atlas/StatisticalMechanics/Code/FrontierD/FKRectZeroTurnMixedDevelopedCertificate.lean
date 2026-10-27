import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedDevelopedCertificate.Part2
open StatMech StatMech.FrontierD


/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_disconnectedIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedDevelopedCertificate.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_disconnectedIncidence_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hdisconnected : FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega)
  (hdual : FKRectZeroTurnOriginalDualSameSideUnique R omega) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_disconnectedIncidence R omega hdisconnected hdual


-- created on 2026-10-23
