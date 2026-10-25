/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.Onsager.GroundUp

theorem rect_angleSum_iff_balance (c r : ℤ) :
    (90 * c + 270 * r = 180 * (c + r) - 360) ↔ (c - r = 4) := by
  omega


theorem balance_form (c r : ℤ) :
    (c - r = 4 ↔ 90 * (c - r) = 360) ∧ (c - r = -4 ↔ 90 * (c - r) = -360) := by
  omega


end StatMech.Onsager.GroundUp
