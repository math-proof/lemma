/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineFiberFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineFiberFactorization.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairBigrade_eq_fineRowProfileGrade
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade horizontal =
      sixVertexHorizontalFineRowProfileGrade
        (sixVertexHorizontalPairBoundedFineRowProfile horizontal) := by
  apply Prod.ext
  · rw [sixVertexHorizontalFineRowProfileGrade]
    change sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 =
      ∑ j : Fin T.height,
        sixVertexHorizontalPairRowNontransitionProfile horizontal j
    exact (sum_sixVertexHorizontalPairRowNontransitionProfile horizontal).symm
  · rw [sixVertexHorizontalFineRowProfileGrade]
    change 2 * (sixVertexHorizontalZeroCount horizontal.1 +
        sixVertexHorizontalZeroCount horizontal.2) =
      2 * ∑ j : Fin T.height,
        sixVertexHorizontalPairRowZeroProfile horizontal j
    rw [sum_sixVertexHorizontalPairRowZeroProfile]

theorem sixVertexHorizontalPairRowZeroProfile_eq_fineRowProfileRowZero
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile horizontal =
      sixVertexHorizontalFineRowProfileRowZero
        (sixVertexHorizontalPairBoundedFineRowProfile horizontal) := by
  rfl


end
end StatMech.FrontierD
