/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part10
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectZeroTurnPrimalDevelopedExtremeIncidence
    (R : FKRectTorus) (omega : R.Configuration) : Prop :=
  ∀ (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega),
    X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C →
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) = C.1


end
end StatMech.FrontierD
