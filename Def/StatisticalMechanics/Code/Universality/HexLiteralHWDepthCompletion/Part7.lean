/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part7


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhda_suffixAugmentColumnWalk
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    HLHDAEndpointColumnWalk (M + 1) (hlhda_suffixAugment ts hleg) where
  legal := (hlhda_suffixAugment_isLegalSAW ts hleg).endpointIsLegalSAW
  horizontal := by
    intro k hk
    exact hlhda_physical_book_bounds
      (hlhda_suffixAugment ts hleg)
      (hlhda_suffixAugment_isLegalSAW ts hleg) (M + 1) (by omega)
      (hlhda_suffixAugment_depth_bounds hleg M hM hnonneg hend hcut) hk
  topCoord := hlhc_prefixCoord (hlhda_suffixAugment ts hleg)
    (hlhda_suffixAugment_isLegalSAW ts hleg).1
    ((hlhda_suffixAugment ts hleg).length - 1)
  top_white :=
    (hlhda_suffixAugment_terminal_top hleg M hM hnonneg
      hend hendWhite hcut).1
  top_depth :=
    (hlhda_suffixAugment_terminal_top hleg M hM hnonneg
      hend hendWhite hcut).2.1
  endsAt :=
    (hlhda_suffixAugment_terminal_top hleg M hM hnonneg
      hend hendWhite hcut).2.2

end
end StatMech.Universality
