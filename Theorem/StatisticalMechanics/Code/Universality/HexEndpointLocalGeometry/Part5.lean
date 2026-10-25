/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part3


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem hexEndpoint_cyclicSucc_ne_pred (j : Fin 3) :
    hexCyclicSucc j ≠ hexCyclicPred j := by
  fin_cases j <;> decide


theorem HexEndpointCyclicLoopPair.contribution_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (P : HexEndpointCyclicLoopPair region a h0 v du) :
    (labelMid v du (hexCyclicSucc P.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicSucc P.baseLabel))
          (5 / 8) hexChi (P.base ++ P.loopQ) +
      (labelMid v du (hexCyclicPred P.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicPred P.baseLabel))
          (5 / 8) hexChi
            (P.base ++ hexEndpointLoopPartner P.loopQ) = 0 := by
  let d := labelMid v du P.baseLabel - v
  have hsucc : v + hexOmega * d =
      labelMid v du (hexCyclicSucc P.baseLabel) := by
    simpa [d] using (hexCyclicSucc_mid v du P.baseLabel).symm
  have hpred : v + hexOmega ^ 2 * d =
      labelMid v du (hexCyclicPred P.baseLabel) := by
    simpa [d] using (hexCyclicPred_mid v du P.baseLabel).symm
  have hne : P.loopQ ≠ [] := by
    obtain ⟨tail, htail⟩ := P.loopQ_first
    rw [htail]
    simp
  have hz := endpoint_genuine_pair_zero
    region a h0 v d P.base P.loopQ
      (hexEndpointLoopPartner P.loopQ) P.loopQ_sum
      (hexEndpointLoopPartner_sum P.loopQ P.loopQ_first P.loopQ_sum)
      (hexEndpointLoopPartner_length_of_ne_nil P.loopQ hne).symm
      (by simpa [hsucc] using P.succ_valid)
      (by simpa [hpred] using P.pred_valid)
  simpa [hsucc, hpred] using hz

theorem HexEndpointCyclicLoopPair.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointCyclicLoopPair region a h0 v du) :
    ∑ ts ∈ P.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  have hne : P.base ++ P.loopQ ≠
      P.base ++ hexEndpointLoopPartner P.loopQ := by
    intro heq
    have hm : labelMid v du (hexCyclicSucc P.baseLabel) =
        labelMid v du (hexCyclicPred P.baseLabel) :=
      P.succ_valid.2.2.symm.trans (heq ▸ P.pred_valid.2.2)
    exact hexEndpoint_cyclicSucc_ne_pred P.baseLabel
      (labelMid_injective hdu hm)
  rw [show (∑ ts ∈ P.piece,
      endpointCombinedSummand region a h0 v du ts) =
      endpointCombinedSummand region a h0 v du (P.base ++ P.loopQ) +
        endpointCombinedSummand region a h0 v du
          (P.base ++ hexEndpointLoopPartner P.loopQ) by
    simp [HexEndpointCyclicLoopPair.piece, hne]]
  rw [endpointCombinedSummand_at_label hdu
      (hexCyclicSucc P.baseLabel) P.succ_valid.2.2,
    endpointCombinedSummand_at_label hdu
      (hexCyclicPred P.baseLabel) P.pred_valid.2.2]
  exact P.contribution_zero


end
end StatMech.Universality
