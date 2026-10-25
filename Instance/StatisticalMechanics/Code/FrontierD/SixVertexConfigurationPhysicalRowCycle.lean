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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalRowCycle
open Finset


namespace StatMech.FrontierD

noncomputable section

instance instFintypeMarkedSectorRowCycle
    (T : EvenTorus) (sector : Fin (T.width + 1)) :
    Fintype (SixVertexMarkedSectorRowCycle T sector) :=
  Fintype.ofFinite _


end
end StatMech.FrontierD
