/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge


namespace StatMech.FrontierD

noncomputable section

structure FKRectZeroTurnAdaptiveMixedRouting
    (R : FKRectTorus) (omega : R.Configuration) where
  crossing : FKRectZeroTurnCutRemainderComponent R omega →
    FKRectRawPrimalWiredDualHorizontalCrossingComponent R omega
  primal_spec : ∀ C X, crossing C = Sum.inl X →
    FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X
  dual_spec : ∀ C X, crossing C = Sum.inr X →
    X ∈ fkRectZeroTurnDualTouchedCrossings R omega C


end
end StatMech.FrontierD
