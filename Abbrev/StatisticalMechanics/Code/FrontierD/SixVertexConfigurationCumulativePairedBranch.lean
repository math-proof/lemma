/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationCumulativePairedBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBidegreeCumulativeHall.Part4
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationCumulativePairedBranch


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexConfigurationCumulativeSource
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :=
  SixVertexMarkedSectorConfiguration T
      ⟨middle.val - 1, by omega⟩ ×
    SixVertexMarkedSectorConfiguration T
      ⟨middle.val + 1, by omega⟩

abbrev SixVertexConfigurationCumulativeTarget
    (T : EvenTorus) (middle : Fin (T.width + 1)) :=
  SixVertexMarkedSectorConfiguration T middle ×
    SixVertexMarkedSectorConfiguration T middle

end
end StatMech.FrontierD
