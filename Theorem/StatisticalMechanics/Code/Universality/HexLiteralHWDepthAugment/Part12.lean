/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part11


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_decodePair_augmented (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_decodePair (hlhda_augmentedPair ts hleg) = ts := by
  classical
  unfold hlhda_decodePair
  rw [dif_pos ⟨ts, hleg, rfl⟩]
  let h : ∃ us : List ℤ, ∃ hu :
      (ofTurns hexAWStart 1 us).IsLegalSAW,
      hlhda_augmentedPair us hu = hlhda_augmentedPair ts hleg :=
    ⟨ts, hleg, rfl⟩
  obtain ⟨hu, hp⟩ := Classical.choose_spec h
  exact hlhda_augmentedPair_injective hu hleg hp


end
end StatMech.Universality
