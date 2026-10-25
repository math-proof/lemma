/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexConfigurationPairBigradeFiber
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (grade : Nat × Nat) :=
  {pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right //
    sixVertexConfigurationPairBigrade pair = grade}

end
end StatMech.FrontierD
