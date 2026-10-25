/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part9


namespace StatMech.FrontierD

noncomputable section

theorem FKRectZeroTurnCrossingMatches.of_extremeDart_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hcomponent :
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingExtremeDart R omega X side) = C.1) :
    FKRectZeroTurnCrossingMatches R omega C X := by
  unfold FKRectZeroTurnCrossingMatches
    fkRectZeroTurnRemainderPrimalComponent
  rw [← hcomponent]
  rw [fkRectMedialComponentToPrimalComponent_mk]
  rw [fkRectRawPrimalCrossingExtremeDart_label]
  unfold fkRectRawPrimalCrossingTorusComponent
  rw [← fkRectRawPrimalCrossingExtremeRow_component R omega X side]
  exact fkRectRawPrimalCrossingTorusComponent_mk R omega _


end
end StatMech.FrontierD
