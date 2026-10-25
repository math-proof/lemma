/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexMarkedSectorRowCycleDiagonalGradeCount
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) : Nat :=
  ∑ vertical : SixVertexVerticalRowsInSector T sector,
    if 2 * sixVertexVerticalRowsTotalC vertical.1 = totalC then
      ∏ j, Fintype.card
        (SixVertexHorizontalTransitionWitness vertical.1 j)
    else 0

def sixVertexMarkedSectorRowCycleDiagonalGradeFiberEquiv
    (T : EvenTorus) (sector : Fin (T.width + 1))
    (totalC : Nat) :
    {rows : SixVertexMarkedSectorRowCycle T sector //
      2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC} ≃
      Sigma fun vertical : SixVertexVerticalRowsInSector T sector =>
        {_witness : forall j,
            SixVertexHorizontalTransitionWitness vertical.1 j //
          2 * sixVertexVerticalRowsTotalC vertical.1 = totalC} :=
  subtypeSigmaBaseEquiv _
    (sixVertexMarkedSectorRowCycleEquivVerticalTransitions T sector)
    (fun rows => 2 * sixVertexMarkedSectorRowCycleTotalC rows = totalC)
    (fun vertical => 2 * sixVertexVerticalRowsTotalC vertical.1 = totalC)
    (fun _ => Iff.rfl)

end
end StatMech.FrontierD
