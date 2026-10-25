/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDualBarrierNetObstructionHorizontalWalk
    (R : FKRectTorus) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Walk
      ((⟨0, R.width_pos⟩ : Fin R.width),
        (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
      ((⟨0, R.width_pos⟩ : Fin R.width),
        (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height)) :=
  (fkRectDualBarrierNetObstructionHorizontalAux R R.width).copy rfl (by
    rw [fkRectCyclicPred_iterate_zero_card])

end
end StatMech.FrontierD
