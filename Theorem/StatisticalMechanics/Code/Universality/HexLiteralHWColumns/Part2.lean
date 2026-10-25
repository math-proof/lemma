/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhc_coord_le_bound_i (c : HexAWCoord) :
    c.i ≤ (hlhc_coordBound c : ℕ) := by
  rcases c with ⟨i, j, color⟩
  have hj : (0 : ℤ) ≤ |j| := abs_nonneg j
  cases i <;> simp [hlhc_coordBound] <;> omega

theorem hlhc_coord_le_bound_j (c : HexAWCoord) :
    c.j ≤ (hlhc_coordBound c : ℕ) := by
  rcases c with ⟨i, j, color⟩
  have hi : (0 : ℤ) ≤ |i| := abs_nonneg i
  cases j <;> simp [hlhc_coordBound] <;> omega


end
end StatMech.Universality
