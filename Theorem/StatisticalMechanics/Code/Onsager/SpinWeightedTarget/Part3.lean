/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedBounds
import Theorem.StatisticalMechanics.Code.Onsager.KWMultiaffineBounded
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget.Part2
import Def.StatisticalMechanics.Code.Onsager.SpinWeightedTarget.Part3


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_spinShermanRadius_pos (L : ℕ) :
    0 < ons_spinShermanRadius L := by
  by_cases h : 2 < L
  · letI : NeZero L := ⟨by omega⟩
    simpa [ons_spinShermanRadius, h] using ons_ShermanRadius_pos L
  · simp [ons_spinShermanRadius, h]

theorem ons_spinKacWardIdentities_of_weightedRoot
    (hweighted : ∀ (L : ℕ) (hL : 2 < L),
      letI : Fact (2 < L) := ⟨hL⟩
      ons_weightedRootIdentity L)
    (beta : ℝ) : ons_spinKacWardIdentities beta := by
  apply ons_spinKacWardIdentities_of_small
    ons_spinShermanRadius ons_spinShermanRadius_pos
  intro L hL
  letI : Fact (2 < L) := ⟨hL⟩
  intro x hx
  rw [ons_spinKacWardAt_iff_coefficientIdentity]
  have hx' : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L) := by
    simpa [ons_spinShermanRadius, hL] using hx
  exact ons_spinCoefficientIdentity_of_weightedRoot L (hweighted L hL) hx'

end StatMech.Onsager
