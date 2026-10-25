/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4


namespace StatMech.FrontierD

structure FKRectTorus where
  width : Nat
  height : Nat
  width_gt_two : 2 < width
  height_gt_two : 2 < height
  height_even : Even height

end StatMech.FrontierD
