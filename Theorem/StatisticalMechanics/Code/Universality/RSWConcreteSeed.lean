/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConcreteSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box


theorem rcs_centeredSquare_vertical_eq_horizontal (n : ℤ) :
    rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n) =
      rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n) := by
  rw [crf_verticalCrossing_eq_horizontal_swap 0 (2 * n) (-n) n
    (rlc_horizontalCrossingEvent_measurableSet (-n) n 0 (2 * n))]
  let t : Site 2 := ![n, -n]
  have ht := cti_horizontalCrossing_translation_invariant (-n) n 0 (2 * n) t
    (rlc_horizontalCrossingEvent_measurableSet (-n) n 0 (2 * n))
  simpa [t, show n + n = 2 * n by ring,
    show 2 * n + -n = n by ring] using ht.symm


theorem rcs_diagonal_pair_lower_bound (n : ℤ) (hn : 0 < n) :
    let alpha := rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n)
    alpha ^ 3 / 4 ≤ rba_selfDualMeasure.real (rlc_rightDiagonal n) ∧
      alpha ^ 3 / 4 ≤ rba_selfDualMeasure.real (rlc_leftDiagonal n) := by
  dsimp only
  have hright := rlc_rightDiagonal_lower_bound (2⁻¹ : ℝ≥0) half_le_one n hn
    (rba_selfDualMeasure.real (horizontalCrossingEvent 0 (2 * n) (-n) n))
    measureReal_nonneg (le_refl _)
  have hvertical : rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) ≤
      rba_selfDualMeasure.real (verticalCrossingEvent 0 (2 * n) (-n) n) := by
    rw [rcs_centeredSquare_vertical_eq_horizontal]
  have hr : rba_selfDualMeasure.real
      (horizontalCrossingEvent 0 (2 * n) (-n) n) ^ 3 / 4 ≤
      rba_selfDualMeasure.real (rlc_rightDiagonal n) := by
    simpa [rba_selfDualMeasure] using hright hvertical
  refine ⟨hr, ?_⟩
  rw [rlc_leftDiagonal_prob_eq_right]
  exact hr


end Universality
end StatMech
