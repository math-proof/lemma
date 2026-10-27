import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge.Part3
open StatMech StatMech.FrontierD


/--
[fkRectZeroTurnUsesAdaptiveDualRoute_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnUsesAdaptiveDualRoute_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega} :
-- imply
  FKRectZeroTurnUsesAdaptiveDualRoute R omega C ↔ ∀ X : FKRectRawPrimalHorizontalCrossingComponent R omega, X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C → ¬ (fkRectOpenGraph R omega).Reachable (fkRectMedialWestPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))) (fkRectMedialEastPrimal R (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X (fkRectZeroTurnRemainderSide R omega C))) := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnUsesAdaptiveDualRoute_iff R omega C

/--
[fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
  {X : FKRectRawWiredDualHorizontalCrossingComponent R omega}
-- given
  (hX : (fkRectZeroTurnAdaptiveMixedRouting R omega).crossing C = Sum.inr X) :
-- imply
  FKRectZeroTurnUsesAdaptiveDualRoute R omega C := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr R omega C X hX

/--
[fkRectZeroTurnAdaptiveMixedRouting_eq_inr_of_usesDualRoute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnAdaptiveMixedRouting_eq_inr_of_usesDualRoute_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectZeroTurnCutRemainderComponent R omega}
-- given
  (hC : FKRectZeroTurnUsesAdaptiveDualRoute R omega C) :
-- imply
  (fkRectZeroTurnAdaptiveMixedRouting R omega).crossing C = Sum.inr (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnAdaptiveMixedRouting_eq_inr_of_usesDualRoute R omega C hC

/--
[fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_dualRouteUniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean)
-/
@[path]
private lemma fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_dualRouteUniqueness_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hdual : FKRectZeroTurnAdaptiveDualRouteSameSideUnique R omega) :
-- imply
  fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnCutRemainderCount_le_two_mul_rawPrimal_add_two_of_dualRouteUniqueness R omega hdual


-- created on 2026-10-23
