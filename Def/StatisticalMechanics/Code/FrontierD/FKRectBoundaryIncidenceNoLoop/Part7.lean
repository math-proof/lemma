/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part6


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


def FKRectForcedDualSameSideOriginalComponent
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega C))) =
        fkRectBlackBoundaryCyclePrimalComponent R
          (fkRectDualConfigurationEquiv R omega)
          (fkRectBlackBoundaryCycleDualEquiv R omega
            (Quot.mk _ (fkRectZeroTurnRemainderBlackDart R omega D)))


end
end StatMech.FrontierD
