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


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


def FKRectForcedDualSameSideSharedRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      ∃ y : Fin R.height,
        y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ∧
          y ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D


def FKRectForcedDualSameSideRightBoundaryConnected
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      ∃ yC yD : Fin R.height,
        yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ∧
          yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D ∧
          (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).Reachable
            (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)


def FKRectForcedDualSameSideRightBoundaryConnectivityReflection
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  forall C D : FKRectZeroTurnCutRemainderComponent R omega,
    forall X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C ->
      ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega D ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega C ->
      X ∈ fkRectZeroTurnDualTouchedCrossings R omega D ->
      fkRectZeroTurnRemainderSide R omega C =
        fkRectZeroTurnRemainderSide R omega D ->
      forall yC yD : Fin R.height,
        yC ∈ fkRectZeroTurnDualRightBoundaryContacts R omega C ->
        yD ∈ fkRectZeroTurnDualRightBoundaryContacts R omega D ->
        (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R omega))).Reachable
              (fkRectRightColumn R, yC) (fkRectRightColumn R, yD) ->
        (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R omega)).Reachable
            (fkRectRightColumn R, yC) (fkRectRightColumn R, yD)


end
end StatMech.FrontierD
