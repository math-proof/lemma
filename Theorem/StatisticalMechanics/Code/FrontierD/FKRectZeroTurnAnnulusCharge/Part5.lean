/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectRawPrimalCrossingExtremeDart_label
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectMedialDartPrimalLabel R
        (fkRectRawPrimalCrossingExtremeDart R omega C side) =
      (fkRectLeftColumn R,
        fkRectRawPrimalCrossingExtremeRow R omega C side) := by
  exact fkRectMedialDartPrimalLabel_dartAtPrimalVertex R _


theorem fkRectRawPrimalCrossing_eq_of_extremeDart_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hdart : fkRectRawPrimalCrossingExtremeDart R omega C side =
      fkRectRawPrimalCrossingExtremeDart R omega D side) :
    C = D := by
  apply fkRectRawPrimalCrossing_eq_of_extremeRow_eq R omega C D side
  have hlabel := congrArg (fkRectMedialDartPrimalLabel R) hdart
  simpa only [fkRectRawPrimalCrossingExtremeDart_label, Prod.mk.injEq,
    true_and] using hlabel


end
end StatMech.FrontierD
