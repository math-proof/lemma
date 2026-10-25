/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnUsesAdaptiveDualRoute_of_routing_eq_inr
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawWiredDualHorizontalCrossingComponent R omega)
    (hX : (fkRectZeroTurnAdaptiveMixedRouting R omega).crossing C =
      Sum.inr X) :
    FKRectZeroTurnUsesAdaptiveDualRoute R omega C := by
  classical
  unfold FKRectZeroTurnUsesAdaptiveDualRoute
  intro h
  change (if h' : ∃ Y : FKRectRawPrimalHorizontalCrossingComponent R omega,
      FKRectZeroTurnReachablePrimalTouchedCrossing R omega C Y then
        Sum.inl (Classical.choose h')
      else
        Sum.inr
          (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose) =
      Sum.inr X at hX
  rw [dif_pos h] at hX
  exact Sum.inl_ne_inr hX


theorem fkRectZeroTurnAdaptiveMixedRouting_eq_inr_of_usesDualRoute
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesAdaptiveDualRoute R omega C) :
    (fkRectZeroTurnAdaptiveMixedRouting R omega).crossing C =
      Sum.inr
        (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose := by
  classical
  change ¬ ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
    FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X at hC
  change (if h : ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
      FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X then
        Sum.inl (Classical.choose h)
      else
        Sum.inr
          (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose) = _
  rw [dif_neg hC]


end
end StatMech.FrontierD
