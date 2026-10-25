/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalPairSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPair_nontransitionCount_eq_sum
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalNontransitionCount horizontal.1 +
        sixVertexHorizontalNontransitionCount horizontal.2 =
      ∑ v : T.Vertex,
        sixVertexHorizontalPairBondAgreementCount horizontal v := by
  unfold sixVertexHorizontalNontransitionCount
    sixVertexHorizontalPairBondAgreementCount boolPairAgreementCount
  rw [Finset.sum_add_distrib]


theorem sixVertexSwitchHorizontalPair_bondAgreement
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (v : T.Vertex) :
    sixVertexHorizontalPairBondAgreementCount
        (sixVertexSwitchHorizontalPair mask horizontal) v =
      if mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1
      then sixVertexHorizontalPairBondAgreementCount horizontal v
      else sixVertexHorizontalPairBondCrossAgreementCount horizontal v := by
  unfold sixVertexHorizontalPairBondAgreementCount
    sixVertexHorizontalPairBondCrossAgreementCount
    sixVertexSwitchHorizontalPair sixVertexHorizontalGaugeBit
  cases hleft : mask (SixVertexArrows.cyclicPred T.width_pos v.1) <;>
    cases hright : mask v.1 <;>
    simp [hleft, hright, boolPairAgreementCount,
      boolPairCrossAgreementCount, add_comm]

theorem sixVertexSwitchHorizontalPair_nontransitionCount
    {T : EvenTorus} (mask : Fin T.width -> Bool)
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).1 +
        sixVertexHorizontalNontransitionCount
          (sixVertexSwitchHorizontalPair mask horizontal).2 =
      ∑ v : T.Vertex,
        if mask (SixVertexArrows.cyclicPred T.width_pos v.1) = mask v.1
        then sixVertexHorizontalPairBondAgreementCount horizontal v
        else sixVertexHorizontalPairBondCrossAgreementCount horizontal v := by
  rw [sixVertexHorizontalPair_nontransitionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact sixVertexSwitchHorizontalPair_bondAgreement mask horizontal v


end
end StatMech.FrontierD
