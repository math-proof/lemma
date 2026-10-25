/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part6


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_completedPrefixColumnWalk
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    HLHDAEndpointColumnWalk (M + 1) (hlhda_completedPrefix ts hleg) where
  legal := hlhda_completedPrefix_endpointIsLegalSAW ts hleg
  horizontal := hlhda_completedPrefix_horizontal hleg M hM hnonneg hcut
  topCoord := hlhc_prefixCoord (hlhda_prefixAugment ts hleg)
    (hlhda_prefixAugment_isLegalSAW ts hleg).1
    (hlhda_prefixAugment ts hleg).length
  top_white := (hlhda_prefixAugment_final_color_depth hleg M hM hcut).1
  top_depth := (hlhda_prefixAugment_final_color_depth hleg M hM hcut).2
  endsAt := hlhda_completedPrefix_endsAt hleg M hM hnonneg hcut

end
end StatMech.Universality
