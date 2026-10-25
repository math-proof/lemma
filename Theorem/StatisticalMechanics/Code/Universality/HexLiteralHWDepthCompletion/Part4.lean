/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhda_eraseCompletion_completed (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_eraseCompletion (hlhda_completedPair ts hleg) =
      hlhda_augmentedPair ts hleg := by
  simp [hlhda_eraseCompletion, hlhda_completedPair,
    hlhda_completedPrefix, hlhda_completedSuffix, hlhda_augmentedPair]

theorem hlhda_completedPair_injective
    {xs ys : List ℤ}
    (hx : (ofTurns hexAWStart 1 xs).IsLegalSAW)
    (hy : (ofTurns hexAWStart 1 ys).IsLegalSAW)
    (heq : hlhda_completedPair xs hx = hlhda_completedPair ys hy) :
    xs = ys := by
  apply hlhda_augmentedPair_injective hx hy
  have herase := congrArg hlhda_eraseCompletion heq
  simpa using herase

end
end StatMech.Universality
