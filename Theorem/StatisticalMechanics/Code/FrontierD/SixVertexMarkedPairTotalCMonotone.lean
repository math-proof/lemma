/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairTotalCMonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem markedDecorationMultiplicity_mono
    {sourceTotal targetTotal k : Nat} (htotal : sourceTotal <= targetTotal) :
    2 ^ (sourceTotal - k) * sourceTotal.choose k <=
      2 ^ (targetTotal - k) * targetTotal.choose k := by
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le_sub_right htotal k))
    (Nat.choose_le_choose k htotal)

theorem sixVertexMarkedPairMultiplicityNat_mono_of_totalC
    {T : EvenTorus} {omega eta alpha beta : SixVertexArrows T} {k : Nat}
    (htotal : sixVertexTorusCTypeCount omega +
        sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount alpha +
        sixVertexTorusCTypeCount beta) :
    sixVertexMarkedPairMultiplicityNat omega eta k <=
      sixVertexMarkedPairMultiplicityNat alpha beta k := by
  unfold sixVertexMarkedPairMultiplicityNat
  exact markedDecorationMultiplicity_mono htotal


end
end StatMech.FrontierD
