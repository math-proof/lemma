/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Structure.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial


namespace StatMech.FrontierD

def FKRectTorus.width_pos (R : FKRectTorus) : 0 < R.width := by
  exact lt_trans (by norm_num : 0 < 2) R.width_gt_two

def FKRectTorus.height_pos (R : FKRectTorus) : 0 < R.height := by
  exact lt_trans (by norm_num : 0 < 2) R.height_gt_two

def FKRectTorus.medialTorus (R : FKRectTorus) : EvenTorus where
  width := 2 * R.width
  height := R.height
  width_pos := mul_pos (by norm_num) R.width_pos
  height_pos := R.height_pos
  width_even := ⟨R.width, by omega⟩
  height_even := R.height_even

end StatMech.FrontierD
