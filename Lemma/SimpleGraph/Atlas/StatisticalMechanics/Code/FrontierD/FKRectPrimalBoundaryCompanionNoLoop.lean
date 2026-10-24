import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryCompanionNoLoop
open StatMech StatMech.FrontierD


/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_companionUnique_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryCompanionNoLoop.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_companionUnique_height_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 4 < q)
  (hunique : forall omega : R.Configuration, ¬ FKRectHasNet R omega -> FKRectPrimalBoundaryCompanionUnique R omega)
  (hextreme : forall omega : R.Configuration, FKRectPrimalDevelopedExtremeSameSign R omega)
  (hdual : forall omega : R.Configuration, FKRectZeroTurnOriginalDualSameSideUnique R omega) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * R.height + 2) / (2 * q) <= fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_companionUnique_height R hq hunique hextreme hdual


-- created on 2026-10-23
