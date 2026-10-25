/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDualBarrierNetObstructionVerticalWalk
    (R : FKRectTorus) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Walk
      (fkRectUnitGapColumn R, (⟨0, R.height_pos⟩ : Fin R.height))
      (fkRectUnitGapColumn R, (⟨0, R.height_pos⟩ : Fin R.height)) :=
  (fkRectDualBarrierNetObstructionVerticalAux R R.height).copy rfl (by
    rw [fkRectCyclicPred_iterate_zero_card])

noncomputable def fkRectDualBarrierNetObstructionHorizontalAux
    (R : FKRectTorus) :
    (n : Nat) →
      (fkRectOpenGraph R
        (fkRectDualBarrierNetObstructionConfiguration R)).Walk
        ((⟨0, R.width_pos⟩ : Fin R.width),
          (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
        ((SixVertexArrows.cyclicPred R.width_pos)^[n]
            (⟨0, R.width_pos⟩ : Fin R.width),
          (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
  | 0 => .nil
  | n + 1 =>
      ((fkRectDualBarrierNetObstructionHorizontalAux R n).concat
        (fkRectDualBarrierNetObstruction_rowOneVerticalAdj R
          ((SixVertexArrows.cyclicPred R.width_pos)^[n]
            (⟨0, R.width_pos⟩ : Fin R.width)))).concat
        (by
          have h := fkRectDualBarrierNetObstruction_rowOneDiagonalAdj R
            ((SixVertexArrows.cyclicPred R.width_pos)^[n]
              (⟨0, R.width_pos⟩ : Fin R.width))
          simpa only [Function.iterate_succ_apply'] using h)

end
end StatMech.FrontierD
