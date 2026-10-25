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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalRowCycleOffDiagonalForget
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexPhysicalRowCycleOffDiagonalTarget T middle ↪
      SixVertexPhysicalRowCycleTarget T middle where
  toFun target := target.1
  inj' := Subtype.val_injective

def sixVertexPhysicalRowCycleOffDiagonalSwap
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexPhysicalRowCycleOffDiagonalTarget T middle ↪
      SixVertexPhysicalRowCycleTarget T middle where
  toFun target := (target.1.2, target.1.1)
  inj' := by
    intro first second heq
    apply Subtype.ext
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)

end
end StatMech.FrontierD
