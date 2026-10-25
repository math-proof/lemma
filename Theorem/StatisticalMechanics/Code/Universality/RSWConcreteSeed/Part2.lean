/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Abbrev.StatisticalMechanics.Code.Universality.RSWConcreteSeed
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box


theorem rcs_right_between_eq_diagonal (n : ℤ) :
    rlc_betweenEvent (rcs_rightLower n) (rcs_rightUpper n) =
      rlc_rightDiagonal n := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    have hx := rlc_mem_verticalSegment.mp x.2
    have hy := rlc_mem_verticalSegment.mp y.2
    let xl : leftSide 0 (2 * n) (-n) n := ⟨x.1, x.1.2, hx.1⟩
    let yr : rightSide 0 (2 * n) (-n) n := ⟨y.1, y.1.2, hy.1⟩
    exact ⟨xl, yr, hx.2.2, hy.2.1, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    let xr : rect 0 (2 * n) (-n) n := ⟨x, leftSide_subset x.2⟩
    let yr : rect 0 (2 * n) (-n) n := ⟨y, rightSide_subset y.2⟩
    have hxr : xr ∈ rcs_rightLower n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨x.2.2, (leftSide_subset x.2).2.2.1, hx⟩
    have hyr : yr ∈ rcs_rightUpper n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨y.2.2, hy, (rightSide_subset y.2).2.2.2⟩
    exact ⟨⟨xr, hxr⟩, ⟨yr, hyr⟩, hxy⟩

theorem rcs_left_between_eq_diagonal (n : ℤ) :
    rlc_betweenEvent (rcs_leftLower n) (rcs_leftUpper n) =
      rlc_leftDiagonal n := by
  ext omega
  constructor
  · rintro ⟨x, y, hxy⟩
    have hx := rlc_mem_verticalSegment.mp x.2
    have hy := rlc_mem_verticalSegment.mp y.2
    let xl : leftSide (-2 * n) 0 (-n) n := ⟨x.1, x.1.2, hx.1⟩
    let yr : rightSide (-2 * n) 0 (-n) n := ⟨y.1, y.1.2, hy.1⟩
    exact ⟨xl, yr, hx.2.2, hy.2.1, hxy⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    let xr : rect (-2 * n) 0 (-n) n := ⟨x, leftSide_subset x.2⟩
    let yr : rect (-2 * n) 0 (-n) n := ⟨y, rightSide_subset y.2⟩
    have hxr : xr ∈ rcs_leftLower n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨x.2.2, (leftSide_subset x.2).2.2.1, hx⟩
    have hyr : yr ∈ rcs_leftUpper n := by
      apply rlc_mem_verticalSegment.mpr
      exact ⟨y.2.2, hy, (rightSide_subset y.2).2.2.2⟩
    exact ⟨⟨xr, hxr⟩, ⟨yr, hyr⟩, hxy⟩

end Universality
end StatMech
