/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingExtremeRow_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawPrimalCrossingExtremeRow R omega C side) = C.1 := by
  cases side <;> simp [fkRectRawPrimalCrossingExtremeRow,
    fkRectRawPrimalCrossingFirstRow_component,
    fkRectRawPrimalCrossingLastRow_component]


theorem fkRectRawPrimalCrossing_eq_of_extremeRow_eq
    (R : FKRectTorus) (omega : R.Configuration)
    (C D : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool)
    (hrow : fkRectRawPrimalCrossingExtremeRow R omega C side =
      fkRectRawPrimalCrossingExtremeRow R omega D side) :
    C = D := by
  cases side
  · exact fkRectRawPrimalCrossingLastRow_injective R omega
      (by simpa [fkRectRawPrimalCrossingExtremeRow] using hrow)
  · exact fkRectRawPrimalCrossingFirstRow_injective R omega
      (by simpa [fkRectRawPrimalCrossingExtremeRow] using hrow)


theorem fkRectOpenGraph_forceCutClosed_le
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenGraph R (fkRectForceCutClosed R omega) ≤
      fkRectOpenGraph R omega := by
  apply fkRectOpenGraph_mono R
  intro e he
  by_cases hcut : e ∈ fkRectTorusCutEdges R
  · rw [fkRectForceCutClosed_of_mem R omega e hcut] at he
    contradiction
  · rwa [fkRectForceCutClosed_of_not_mem R omega e hcut] at he


end
end StatMech.FrontierD
