/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPairedBranchHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairBigrade.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPairedBranchHall
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexConfigurationLowerSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) : Fin (T.width + 1) :=
  ⟨middle.val - 1, by omega⟩

def sixVertexConfigurationUpperSector
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_lt : middle.val < T.width) : Fin (T.width + 1) :=
  ⟨middle.val + 1, by omega⟩


end
end StatMech.FrontierD
