/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part7


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_completedSuffix_mem_topAtWidth
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    HexCSTopWalkAtWidth (M + 1) (by omega)
      (hlhda_completedSuffix ts hleg) := by
  change HexCSTopWalkAtWidth (M + 1) (by omega)
    (hlhda_suffixAugment ts hleg)
  exact (hlhda_suffixAugmentColumnWalk hleg M hM hnonneg hend
    hendWhite hcut).mem_topAtWidth (by omega)


theorem hlhda_completedPair_mem_topAtWidth
    {ts : List ℤ} (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (M : ℕ) (hM : 0 < M)
    (hnonneg : ∀ k, k ≤ ts.length → 0 ≤ hlhd_depth ts hleg k)
    (hend : hlhd_depth ts hleg ts.length = 0)
    (hendWhite : (hlhc_prefixCoord ts hleg.1 ts.length).color = .white)
    (hcut : hlhd_depth ts hleg (hlhda_cutPos ts hleg) = (M : ℤ)) :
    HexCSTopWalkAtWidth (M + 1) (by omega)
        (hlhda_completedPair ts hleg).1 ∧
      HexCSTopWalkAtWidth (M + 1) (by omega)
        (hlhda_completedPair ts hleg).2 := by
  constructor
  · simpa only [hlhda_completedPair] using
      hlhda_completedPrefix_mem_topAtWidth hleg M hM hnonneg hcut
  · simpa only [hlhda_completedPair] using
      hlhda_completedSuffix_mem_topAtWidth hleg M hM hnonneg
        hend hendWhite hcut


end
end StatMech.Universality
