/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectUnitLeftBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectUnitLeftBarrierGap (R : FKRectTorus) : R.EdgeIndex :=
  (false,
    (⟨1, lt_trans Nat.one_lt_two R.width_gt_two⟩,
      ⟨0, R.height_pos⟩))

end
end StatMech.FrontierD
