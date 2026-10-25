/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Universality.STT
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

theorem isCriticalSquare_iff (p0 p1 : ℝ) : IsCriticalSquare p0 p1 ↔ p0 + p1 = 1 := by
  unfold IsCriticalSquare kappaSquare; constructor <;> intro h <;> linarith


theorem isCriticalTri_iff (p0 p1 p2 : ℝ) :
    IsCriticalTri p0 p1 p2 ↔ p0 + p1 + p2 - p0 * p1 * p2 = 1 := by
  unfold IsCriticalTri kappaTri; constructor <;> intro h <;> linarith


theorem isCriticalTri_iff_isCriticalHex_compl (p0 p1 p2 : ℝ) :
    IsCriticalTri p0 p1 p2 ↔ IsCriticalHex (1 - p0) (1 - p1) (1 - p2) := by
  unfold IsCriticalTri IsCriticalHex kappaHex
  simp only [sub_sub_cancel]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith [neg_eq_zero.mp h]


end Universality
end StatMech
