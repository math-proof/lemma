/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedBoundaryGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
open Finset


namespace StatMech.FrontierD

def EvenTorus.double (T : EvenTorus) : EvenTorus where
  width := T.width + T.width
  height := T.height + T.height
  width_pos := Nat.add_pos_left T.width_pos T.width
  height_pos := Nat.add_pos_left T.height_pos T.height
  width_even := T.width_even.add T.width_even
  height_even := T.height_even.add T.height_even


end StatMech.FrontierD
