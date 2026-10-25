/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhda_completedPrefix_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_completedPrefix ts hleg).length =
      (hlhda_prefixAugment ts hleg).length + 1 := by
  simp [hlhda_completedPrefix]

@[simp] theorem hlhda_completedSuffix_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_completedSuffix ts hleg).length =
      (hlhda_suffixAugment ts hleg).length := by
  simp [hlhda_completedSuffix]

theorem hlhda_completedPair_length (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    (hlhda_completedPair ts hleg).1.length +
        (hlhda_completedPair ts hleg).2.length = ts.length + 5 := by
  rw [hlhda_completedPair, hlhda_completedPrefix_length,
    hlhda_completedSuffix_length]
  have hraw := hlhda_augmentedPair_length ts hleg
  change (hlhda_prefixAugment ts hleg).length +
      (hlhda_suffixAugment ts hleg).length = ts.length + 4 at hraw
  omega


end
end StatMech.Universality
