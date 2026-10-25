/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierNetObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualRankOneWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierNetObstruction.Part4
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectDualBarrierNetObstructionConnectionWalk
    (R : FKRectTorus) :
    (fkRectOpenGraph R
      (fkRectDualBarrierNetObstructionConfiguration R)).Walk
      ((⟨0, R.width_pos⟩ : Fin R.width),
        (⟨1, lt_trans Nat.one_lt_two R.height_gt_two⟩ : Fin R.height))
      (fkRectUnitGapColumn R,
        (⟨0, R.height_pos⟩ : Fin R.height)) := by
  have hpred :
      (SixVertexArrows.cyclicPred R.width_pos)^[R.width - 1]
          (⟨0, R.width_pos⟩ : Fin R.width) = fkRectUnitGapColumn R := by
    apply Fin.ext
    rw [fkRectCyclicPred_iterate_zero_val R.width_pos (R.width - 1)]
    · have hw := R.width_gt_two
      have hne : R.width - 1 ≠ 0 := by omega
      rw [if_neg hne]
      change R.width - (R.width - 1) = 1
      omega
    · omega
  let p := fkRectDualBarrierNetObstructionHorizontalAux R (R.width - 1)
  let p' := p.copy rfl (by rw [hpred])
  exact p'.concat
    (fkRectDualBarrierNetObstruction_rowOneVerticalAdj R
      (fkRectUnitGapColumn R))


end
end StatMech.FrontierD
