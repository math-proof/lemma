/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part10


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem HexEndpointLoopPair.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (P : HexEndpointLoopPair region a h0 v du) :
    ∑ ts ∈ P.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  have hqr : P.base ++ P.loopQ ≠
      P.base ++ anchoredLoopReverse P.loopQ := by
    intro heq
    exact hexMid_q_ne_r hdu
      (P.q_valid.2.2.symm.trans (heq ▸ P.r_valid.2.2))
  rw [show (∑ ts ∈ P.piece,
      endpointCombinedSummand region a h0 v du ts) =
      endpointCombinedSummand region a h0 v du (P.base ++ P.loopQ) +
        endpointCombinedSummand region a h0 v du
          (P.base ++ anchoredLoopReverse P.loopQ) by
    simp [HexEndpointLoopPair.piece, hqr]]
  rw [endpointCombinedSummand_at_q hdu P.q_valid.2.2,
    endpointCombinedSummand_at_r hdu P.r_valid.2.2]
  exact
    endpoint_genuine_pair_zero_via_anchored_reversal region a h0 v du
      P.base P.loopQ P.loopQ_sum P.q_valid P.r_valid


end
end StatMech.Universality
