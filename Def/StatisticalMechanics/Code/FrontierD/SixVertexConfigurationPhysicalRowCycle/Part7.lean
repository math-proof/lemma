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
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalSourceEquivRowCycles
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width} :
    SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt ≃
      SixVertexPhysicalRowCycleSource T middle hmiddle_pos hmiddle_lt :=
  Equiv.prodCongr
    (sixVertexMarkedSectorConfigurationEquivRowCycle T
      ⟨middle.val - 1, by omega⟩)
    (sixVertexMarkedSectorConfigurationEquivRowCycle T
      ⟨middle.val + 1, by omega⟩)

def sixVertexPhysicalTargetEquivRowCycles
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexConfigurationPhysicalTarget T middle ≃
      SixVertexPhysicalRowCycleTarget T middle :=
  Equiv.prodCongr
    (sixVertexMarkedSectorConfigurationEquivRowCycle T middle)
    (sixVertexMarkedSectorConfigurationEquivRowCycle T middle)

end
end StatMech.FrontierD
