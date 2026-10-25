/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalFineRowProfile.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileAggregate.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalFineRowProfile.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairRowNontransitionProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairRowNontransitionProfile horizontal := by
  funext j
  rw [sixVertexSwitchHorizontalPair_rowNontransitionProfile,
    sixVertexHorizontalPairRowNontransitionProfile_eq_sum,
    Finset.sum_ite]
  change
    (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i),
        sixVertexHorizontalPairBondAgreementCount horizontal (i, j)) +
      (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => ¬mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)) = _
  rw [show (∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => ¬mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j)) =
      ∑ i ∈ (Finset.univ : Finset (Fin T.width)).filter
          (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) ≠ mask i),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal (i, j) by rfl,
    hbalanced j]
  exact Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin T.width))
    (fun i => mask (SixVertexArrows.cyclicPred T.width_pos i) = mask i)
    (fun i => sixVertexHorizontalPairBondAgreementCount horizontal (i, j))

theorem sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · exact congrFun
      (sixVertexSwitchHorizontalPair_rowNontransitionProfile_eq_of_balanced
        mask horizontal hbalanced) j
  · exact congrFun
      (sixVertexSwitchHorizontalPair_rowZeroProfile mask horizontal) j

theorem sixVertexSwitchHorizontalPair_boundedFineRowProfile_of_balanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchRowBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexSwitchHorizontalPair_fineRowProfile_of_balanced
      mask horizontal hbalanced)

theorem sixVertexReflectFirstHorizontalLayer_fineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · unfold sixVertexHorizontalPairFineRowProfile
      sixVertexHorizontalPairRowNontransitionProfile
      sixVertexReflectFirstHorizontalLayer
    rw [sixVertexHorizontalRowNontransitionCount_reflect]
  · exact congrFun
      (sixVertexReflectFirstHorizontalLayer_rowZeroProfile horizontal) j

theorem sixVertexReflectFirstHorizontalLayer_boundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexReflectFirstHorizontalLayer_fineRowProfile horizontal)

theorem sixVertexReflectSecondHorizontalLayer_fineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · unfold sixVertexHorizontalPairFineRowProfile
      sixVertexHorizontalPairRowNontransitionProfile
      sixVertexReflectSecondHorizontalLayer
    rw [sixVertexHorizontalRowNontransitionCount_reflect]
  · exact congrFun
      (sixVertexReflectSecondHorizontalLayer_rowZeroProfile horizontal) j

theorem sixVertexReflectSecondHorizontalLayer_boundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexReflectSecondHorizontalLayer_fineRowProfile horizontal)

theorem sixVertexSwapHorizontalLayers_fineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairFineRowProfile
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairFineRowProfile horizontal := by
  funext j
  apply Prod.ext
  · simp [sixVertexHorizontalPairFineRowProfile,
      sixVertexHorizontalPairRowNontransitionProfile,
      sixVertexSwapHorizontalLayers, add_comm]
  · exact congrFun (sixVertexSwapHorizontalLayers_rowZeroProfile horizontal) j

theorem sixVertexSwapHorizontalLayers_boundedFineRowProfile
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T ×
      SixVertexHorizontalField T) :
    sixVertexHorizontalPairBoundedFineRowProfile
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile horizontal :=
  sixVertexHorizontalPairBoundedFineRowProfile_eq_of_fine_eq
    (sixVertexSwapHorizontalLayers_fineRowProfile horizontal)


end
end StatMech.FrontierD
