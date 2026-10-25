/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Taylor
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part2


namespace StatMech.Universality

open Set

noncomputable section

theorem harmonicDirectionalFourNeighborStencil_le
    (g₁ g₂ : Real → Real) (h M₁ M₂ : Real)
    (hg₁ : ContDiff Real 4 g₁) (hg₂ : ContDiff Real 4 g₂)
    (hfourth₁ : ∀ t, |iteratedDeriv 4 g₁ t| ≤ M₁)
    (hfourth₂ : ∀ t, |iteratedDeriv 4 g₂ t| ≤ M₂)
    (hharmonic : iteratedDeriv 2 g₁ 0 + iteratedDeriv 2 g₂ 0 = 0) :
    |directionalFourNeighborStencil g₁ g₂ h| ≤
      (M₁ + M₂) * |h| ^ 4 / 12 := by
  have h₁ := centralSecondDifference_remainder_le
    g₁ h M₁ hg₁ hfourth₁
  have h₂ := centralSecondDifference_remainder_le
    g₂ h M₂ hg₂ hfourth₂
  have hid : directionalFourNeighborStencil g₁ g₂ h =
      ((g₁ h + g₁ (-h) - 2 * g₁ 0) -
        iteratedDeriv 2 g₁ 0 * h ^ 2) +
      ((g₂ h + g₂ (-h) - 2 * g₂ 0) -
        iteratedDeriv 2 g₂ 0 * h ^ 2) := by
    unfold directionalFourNeighborStencil
    nlinarith
  rw [hid]
  calc
    |_ + _| ≤
        |(g₁ h + g₁ (-h) - 2 * g₁ 0) -
          iteratedDeriv 2 g₁ 0 * h ^ 2| +
        |(g₂ h + g₂ (-h) - 2 * g₂ 0) -
          iteratedDeriv 2 g₂ 0 * h ^ 2| := abs_add_le _ _
    _ ≤ M₁ * |h| ^ 4 / 12 + M₂ * |h| ^ 4 / 12 := add_le_add h₁ h₂
    _ = (M₁ + M₂) * |h| ^ 4 / 12 := by ring

end
end StatMech.Universality
