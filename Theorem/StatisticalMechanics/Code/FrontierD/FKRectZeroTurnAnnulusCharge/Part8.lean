/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part8


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnRemainderPrimalComponent_eq_label
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnRemainderPrimalComponent R omega C =
      (fkRectOpenGraph R omega).connectedComponentMk
        (fkRectMedialDartPrimalLabel R
          (fkRectZeroTurnRemainderBlackDart R omega C).1) := by
  unfold fkRectZeroTurnRemainderPrimalComponent
  rw [← fkRectZeroTurnRemainderBlackDart_component R omega C]
  exact fkRectMedialComponentToPrimalComponent_mk R omega _


end
end StatMech.FrontierD
