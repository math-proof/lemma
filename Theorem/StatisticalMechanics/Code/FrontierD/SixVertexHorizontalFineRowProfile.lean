/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalRowZeroCount_le_width
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowZeroCount horizontal j <= T.width := by
  unfold sixVertexHorizontalRowZeroCount
  calc
    (∑ i : Fin T.width,
      if sixVertexHorizontalGaugeBit horizontal (i, j) = false
      then 1 else 0) <= ∑ _i : Fin T.width, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> simp
    _ = T.width := by simp

theorem sixVertexHorizontalRowNontransitionCount_le_width
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowNontransitionCount horizontal j <= T.width := by
  unfold sixVertexHorizontalRowNontransitionCount
  calc
    (∑ i : Fin T.width,
      if sixVertexHorizontalGaugeBit horizontal
            (SixVertexArrows.cyclicPred T.width_pos i, j) =
          sixVertexHorizontalGaugeBit horizontal (i, j)
      then 1 else 0) <= ∑ _i : Fin T.width, 1 := by
        apply Finset.sum_le_sum
        intro i hi
        split <;> simp
    _ = T.width := by simp


end
end StatMech.FrontierD
