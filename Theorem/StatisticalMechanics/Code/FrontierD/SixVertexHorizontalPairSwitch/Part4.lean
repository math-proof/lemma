/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchBoundaryBalanced mask horizontal) :
    sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).1 +
        sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).2 =
      sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 := by
  rw [sixVertexSwitchHorizontalPair_nontransitionCount,
    sixVertexHorizontalPair_nontransitionCount_eq_sum]
  rw [Finset.sum_ite]
  change
    (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) =
            mask v.1),
        sixVertexHorizontalPairBondAgreementCount horizontal v) +
      (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => ¬mask (SixVertexArrows.cyclicPred T.width_pos v.1) =
            mask v.1),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal v) = _
  rw [show (∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => ¬mask (SixVertexArrows.cyclicPred T.width_pos v.1) =
            mask v.1),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal v) =
      ∑ v ∈ (Finset.univ : Finset T.Vertex).filter
          (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) ≠
            mask v.1),
        sixVertexHorizontalPairBondCrossAgreementCount horizontal v by rfl,
    hbalanced]
  exact Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset T.Vertex)
    (fun v => mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1)
    (sixVertexHorizontalPairBondAgreementCount horizontal)


theorem sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hbalanced :
      SixVertexHorizontalPairSwitchBoundaryBalanced mask horizontal) :
    sixVertexHorizontalPairBigrade
        (sixVertexSwitchHorizontalPair mask horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade
  apply Prod.ext
  · exact sixVertexSwitchHorizontalPair_nontransitionCount_eq_of_boundaryBalanced
      mask horizontal hbalanced
  · simp only [sixVertexSwitchHorizontalPair_zeroCount]

end
end StatMech.FrontierD
