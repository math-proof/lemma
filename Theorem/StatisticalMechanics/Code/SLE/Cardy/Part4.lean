/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Def.StatisticalMechanics.Code.SLE.Cardy.Part4
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

lemma sle_phase_trichotomy {κ : ℝ} (hκ : 0 ≤ κ) :
    IsSimplePhase κ ∨ IsSelfTouchingPhase κ ∨ IsSpaceFillingPhase κ := by
  unfold IsSimplePhase IsSelfTouchingPhase IsSpaceFillingPhase
  rcases le_or_gt κ 4 with h | h
  · exact Or.inl ⟨hκ, h⟩
  · rcases lt_or_ge κ 8 with h' | h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr h')


lemma not_simple_and_selfTouching {κ : ℝ}
    (h : IsSimplePhase κ) : ¬ IsSelfTouchingPhase κ := by
  rintro ⟨h₁, _⟩
  linarith [h.2]


lemma not_selfTouching_and_spaceFilling {κ : ℝ}
    (h : IsSelfTouchingPhase κ) : ¬ IsSpaceFillingPhase κ := by
  unfold IsSpaceFillingPhase
  linarith [h.2]


end StatMech.SLE
