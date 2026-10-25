/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sum_sixVertexHorizontalRowZeroCount
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalRowZeroCount horizontal j) =
      sixVertexHorizontalZeroCount horizontal := by
  rw [sixVertexHorizontalZeroCount_eq_sum]
  unfold sixVertexHorizontalRowZeroCount
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem sum_sixVertexHorizontalPairRowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    (∑ j : Fin T.height,
      sixVertexHorizontalPairRowZeroProfile horizontal j) =
      sixVertexHorizontalZeroCount horizontal.1 +
        sixVertexHorizontalZeroCount horizontal.2 := by
  unfold sixVertexHorizontalPairRowZeroProfile
  rw [Finset.sum_add_distrib,
    sum_sixVertexHorizontalRowZeroCount,
    sum_sixVertexHorizontalRowZeroCount]

theorem sixVertexHorizontalRowZeroCount_reflect
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T)
    (j : Fin T.height) :
    sixVertexHorizontalRowZeroCount
        (sixVertexReflectHorizontalField horizontal) j =
      sixVertexHorizontalRowZeroCount horizontal j := by
  unfold sixVertexHorizontalRowZeroCount
  simp_rw [sixVertexHorizontalGaugeBit_reflect]
  exact (sixVertexCyclicNegEquiv T.width_pos).sum_comp
    (fun i : Fin T.width =>
      if sixVertexHorizontalGaugeBit horizontal (i, j) = false then 1 else 0)


theorem sixVertexSwitchHorizontalPair_rowZeroProfile
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexHorizontalRowZeroCount
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold sixVertexSwitchHorizontalPair sixVertexHorizontalGaugeBit
  cases hmask : mask i <;> simp [hmask, add_comm]

theorem sixVertexReflectFirstHorizontalLayer_rowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexReflectFirstHorizontalLayer
  rw [sixVertexHorizontalRowZeroCount_reflect]

theorem sixVertexReflectSecondHorizontalLayer_rowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  unfold sixVertexHorizontalPairRowZeroProfile
    sixVertexReflectSecondHorizontalLayer
  rw [sixVertexHorizontalRowZeroCount_reflect]

theorem sixVertexSwapHorizontalLayers_rowZeroProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairRowZeroProfile
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairRowZeroProfile horizontal := by
  funext j
  simp [sixVertexHorizontalPairRowZeroProfile,
    sixVertexSwapHorizontalLayers, add_comm]

end
end StatMech.FrontierD
