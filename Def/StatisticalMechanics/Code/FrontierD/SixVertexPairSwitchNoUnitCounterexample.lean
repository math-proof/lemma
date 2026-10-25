/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairSwitchNoUnitCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition.Part6
open Finset


namespace StatMech.FrontierD

def sixVertexFourByTwoTorus : EvenTorus where
  width := 4
  height := 2
  width_pos := by norm_num
  height_pos := by norm_num
  width_even := by norm_num
  height_even := by norm_num


def sixVertexFourByTwoLowArrows :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal _ := false
  vertical _ := false


def sixVertexFourByTwoHighArrows :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := decide (v.1.val % 2 = v.2.val % 2)
  vertical v := decide (v.1.val % 2 ≠ v.2.val % 2)

end StatMech.FrontierD
