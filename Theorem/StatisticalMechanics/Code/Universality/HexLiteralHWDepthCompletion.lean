/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCutBounds


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_prefixAugment_ne (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_prefixAugment ts hleg ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  rw [hlhda_prefixAugment_length] at hlen
  simp only [List.length_nil] at hlen
  omega

theorem hlhda_suffixAugment_ne (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_suffixAugment ts hleg ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  rw [hlhda_suffixAugment_length] at hlen
  simp only [List.length_nil, List.length_drop] at hlen
  omega


end
end StatMech.Universality
