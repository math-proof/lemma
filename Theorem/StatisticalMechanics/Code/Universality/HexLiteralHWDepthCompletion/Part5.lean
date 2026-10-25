/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part4


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_decodeCompletedPair_completed (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_decodeCompletedPair (hlhda_completedPair ts hleg) = ts := by
  rw [hlhda_decodeCompletedPair, hlhda_eraseCompletion_completed,
    hlhda_decodePair_augmented]


end
end StatMech.Universality
