/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part5
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_insetRightOdd_right_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetRightOddToUpper n) =
      rba_selfDualMeasure.real (rlc_insetRightOddToStrictLower n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    1 (2 * n) (-n) (n - 1) (-1) (by ring)
    Set.univ rlc_upperHalf (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetRightOddToUpper,
    rlc_insetRightOddToStrictLower, rlc_affineFlipY_image_univ,
    rlc_negOneFlip_image_upper] using h

theorem rlc_insetRightOdd_left_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetRightOddStrictLowerToRight n) =
      rba_selfDualMeasure.real (rlc_insetRightOddUpperToRight n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    1 (2 * n) (-n) (n - 1) (-1) (by ring)
    rlc_strictLowerHalf Set.univ (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetRightOddStrictLowerToRight,
    rlc_insetRightOddUpperToRight, rlc_affineFlipY_image_univ,
    rlc_negOneFlip_image_strictLower] using h

theorem rlc_insetRightOdd_horizontal_subset_right (n : Int) :
    horizontalCrossingEvent 1 (2 * n) (-n) (n - 1) ⊆
      rlc_insetRightOddToUpper n ∪ rlc_insetRightOddToStrictLower n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hy : 0 <= (y : Site 2) 1
  · exact Or.inl ⟨x, y, Set.mem_univ _, hy, hxy⟩
  · exact Or.inr ⟨x, y, Set.mem_univ _, lt_of_not_ge hy, hxy⟩

theorem rlc_insetRightOdd_horizontal_subset_left (n : Int) :
    horizontalCrossingEvent 1 (2 * n) (-n) (n - 1) ⊆
      rlc_insetRightOddStrictLowerToRight n ∪ rlc_insetRightOddUpperToRight n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hx : (x : Site 2) 1 < 0
  · exact Or.inl ⟨x, y, hx, Set.mem_univ _, hxy⟩
  · exact Or.inr ⟨x, y, le_of_not_gt hx, Set.mem_univ _, hxy⟩

theorem rlc_insetRightOddToUpper_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1))) :
    alpha / 2 <= rba_selfDualMeasure.real (rlc_insetRightOddToUpper n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetRightOdd_horizontal_subset_right n)
    (rlc_insetRightOdd_right_reflection_prob n)

theorem rlc_insetRightOddStrictLowerToRight_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1))) :
    alpha / 2 <= rba_selfDualMeasure.real
      (rlc_insetRightOddStrictLowerToRight n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetRightOdd_horizontal_subset_left n)
    (rlc_insetRightOdd_left_reflection_prob n)

theorem rlc_insetRightOdd_horizontal_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
  have hbase := rlc_square_half (2 * n - 1) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * n - 1) 0 (2 * n - 1) (![1, -n] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * n - 1) 0 (2 * n - 1))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * n - 1) 0 (2 * n - 1)) := by
    simpa [show 2 * n - 1 + 1 = 2 * n by ring,
      show 2 * n - 1 + -n = n - 1 by ring] using htrans
  rwa [heq]

theorem rlc_insetRightOdd_vertical_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (verticalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
  have hH := rlc_insetRightOdd_horizontal_half n hn
  have hswap := crf_verticalCrossing_eq_horizontal_swap
    1 (2 * n) (-n) (n - 1)
    (rlc_horizontalCrossing_measurableSet (-n) (n - 1) 1 (2 * n))
  have htrans := cti_horizontalCrossing_translation_invariant
    (-n) (n - 1) 1 (2 * n) (![n + 1, -n - 1] : Site 2)
    (rlc_horizontalCrossing_measurableSet (-n) (n - 1) 1 (2 * n))
  have heq : rba_selfDualMeasure.real
      (verticalCrossingEvent 1 (2 * n) (-n) (n - 1)) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 1 (2 * n) (-n) (n - 1)) := by
    rw [hswap]
    simpa [show -n + (n + 1) = 1 by ring,
      show n - 1 + (n + 1) = 2 * n by ring,
      show 1 + (-n - 1) = -n by ring,
      show 2 * n + (-n - 1) = n - 1 by ring] using htrans.symm
  rwa [heq]

theorem rlc_insetRightOddSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetRightOddSourceCoreEvent n) := by
  let F := (rect_finite 1 (2 * n) (-n) (n - 1)).toFinset
  have h := rlc_diagonal_event_lower_bound (2⁻¹ : NNReal) half_le_one
    ((1 : Real) / 2) (by norm_num)
    (rlc_insetRightOddToUpper n)
    (rlc_insetRightOddStrictLowerToRight n)
    (verticalCrossingEvent 1 (2 * n) (-n) (n - 1))
    (rlc_insetRightOddSourceCoreEvent n)
    (edgesWithinFinset F) (edgesWithinFinset F) (edgesWithinFinset F)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing _ _ _ _)
    (by simpa [F, rlc_insetRightOddToUpper] using
      (rlc_lrRestrictedEvent_dependsOn 1 (2 * n) (-n) (n - 1)
        Set.univ rlc_upperHalf))
    (by simpa [F, rlc_insetRightOddStrictLowerToRight] using
      (rlc_lrRestrictedEvent_dependsOn 1 (2 * n) (-n) (n - 1)
        rlc_strictLowerHalf Set.univ))
    (by simpa [F] using
      rlc_verticalCrossing_dependsOn 1 (2 * n) (-n) (n - 1))
    (rlc_insetRightOddToUpper_half n ((1 : Real) / 2)
      (rlc_insetRightOdd_horizontal_half n hn))
    (rlc_insetRightOddStrictLowerToRight_half n ((1 : Real) / 2)
      (rlc_insetRightOdd_horizontal_half n hn))
    (rlc_insetRightOdd_vertical_half n hn)
    (rlc_lrRestricted_of_three 1 (2 * n) (-n) (n - 1)
      (by omega) (by omega) rlc_strictLowerHalf rlc_upperHalf)
  norm_num at h
  simpa [rba_selfDualMeasure] using h


end
end StatMech.Universality
