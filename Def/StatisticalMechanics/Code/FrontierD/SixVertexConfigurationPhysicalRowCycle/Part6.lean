module
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalCommonFactor.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
public import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle.Part3
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalRowCycle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalRowCyclePairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorRowCycle T left ×
      SixVertexMarkedSectorRowCycle T right) : Nat :=
  sixVertexMarkedSectorRowCyclePairTotalC pair


end
end StatMech.FrontierD
