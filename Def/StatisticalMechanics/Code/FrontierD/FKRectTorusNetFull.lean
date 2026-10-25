/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectVerticalFundamentalWalkAux (R : FKRectTorus)
    (x : Fin R.width) (y : Fin R.height) :
    (n : Nat) -> (fkRectFullOpenGraph R).Walk (x, y)
      (x, (SixVertexArrows.cyclicPred R.height_pos)^[n] y)
  | 0 => .nil
  | n + 1 => (fkRectVerticalFundamentalWalkAux R x y n).concat
      (by simpa only [Function.iterate_succ_apply'] using
        (fkRectFullOpenGraph_adj_verticalPred R x
          ((SixVertexArrows.cyclicPred R.height_pos)^[n] y)))

noncomputable def fkRectHorizontalFundamentalWalkAux (R : FKRectTorus)
    (x : Fin R.width) :
    (n : Nat) -> (fkRectFullOpenGraph R).Walk
      (x, (⟨0, R.height_pos⟩ : Fin R.height))
      ((SixVertexArrows.cyclicPred R.width_pos)^[n] x,
        (⟨0, R.height_pos⟩ : Fin R.height))
  | 0 => .nil
  | n + 1 =>
      ((fkRectHorizontalFundamentalWalkAux R x n).concat
        (fkRectFullOpenGraph_adj_horizontalPred_diag_zero R
          ((SixVertexArrows.cyclicPred R.width_pos)^[n] x))).concat
        (by simpa only [Function.iterate_succ_apply'] using
          (fkRectFullOpenGraph_adj_verticalPred R
            (SixVertexArrows.cyclicPred R.width_pos
              ((SixVertexArrows.cyclicPred R.width_pos)^[n] x))
          (⟨0, R.height_pos⟩ : Fin R.height)).symm)

end
end StatMech.FrontierD
