/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part6
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_insetLeftOdd_right_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetLeftOddToStrictUpper n) =
      rba_selfDualMeasure.real (rlc_insetLeftOddToLower n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    (-2 * n) (-1) (1 - n) n 1 (by ring)
    Set.univ rlc_strictUpperHalf (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetLeftOddToStrictUpper,
    rlc_insetLeftOddToLower, rlc_affineFlipY_image_univ,
    rlc_oneFlip_image_strictUpper] using h

theorem rlc_insetLeftOdd_left_reflection_prob (n : Int) :
    rba_selfDualMeasure.real (rlc_insetLeftOddLowerToRight n) =
      rba_selfDualMeasure.real (rlc_insetLeftOddStrictUpperToRight n) := by
  have h := rlc_affineFlipY_lrRestricted_prob_eq
    (-2 * n) (-1) (1 - n) n 1 (by ring)
    rlc_lowerHalf Set.univ (2⁻¹ : NNReal) half_le_one
  simpa [rba_selfDualMeasure, rlc_insetLeftOddLowerToRight,
    rlc_insetLeftOddStrictUpperToRight, rlc_affineFlipY_image_univ,
    rlc_oneFlip_image_lower] using h

theorem rlc_insetLeftOdd_horizontal_subset_right (n : Int) :
    horizontalCrossingEvent (-2 * n) (-1) (1 - n) n ⊆
      rlc_insetLeftOddToStrictUpper n ∪ rlc_insetLeftOddToLower n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hy : 0 < (y : Site 2) 1
  · exact Or.inl ⟨x, y, Set.mem_univ _, hy, hxy⟩
  · exact Or.inr ⟨x, y, Set.mem_univ _, le_of_not_gt hy, hxy⟩

theorem rlc_insetLeftOdd_horizontal_subset_left (n : Int) :
    horizontalCrossingEvent (-2 * n) (-1) (1 - n) n ⊆
      rlc_insetLeftOddLowerToRight n ∪ rlc_insetLeftOddStrictUpperToRight n := by
  rintro omega ⟨x, y, hxy⟩
  by_cases hx : (x : Site 2) 1 <= 0
  · exact Or.inl ⟨x, y, hx, Set.mem_univ _, hxy⟩
  · exact Or.inr ⟨x, y, lt_of_not_ge hx, Set.mem_univ _, hxy⟩

theorem rlc_insetLeftOddToStrictUpper_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n)) :
    alpha / 2 <= rba_selfDualMeasure.real (rlc_insetLeftOddToStrictUpper n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetLeftOdd_horizontal_subset_right n)
    (rlc_insetLeftOdd_right_reflection_prob n)

theorem rlc_insetLeftOddLowerToRight_half (n : Int) (alpha : Real)
    (hcross : alpha <= rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n)) :
    alpha / 2 <= rba_selfDualMeasure.real (rlc_insetLeftOddLowerToRight n) :=
  rlc_half_localization_of_reflected_union _ _ _ alpha hcross
    (rlc_insetLeftOdd_horizontal_subset_left n)
    (rlc_insetLeftOdd_left_reflection_prob n)

theorem rlc_insetLeftOdd_horizontal_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
  have hbase := rlc_square_half (2 * n - 1) (by omega)
  have htrans := cti_horizontalCrossing_translation_invariant
    0 (2 * n - 1) 0 (2 * n - 1) (![-2 * n, 1 - n] : Site 2)
    (rlc_horizontalCrossing_measurableSet 0 (2 * n - 1) 0 (2 * n - 1))
  have heq : rba_selfDualMeasure.real
      (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent 0 (2 * n - 1) 0 (2 * n - 1)) := by
    simpa [show 2 * n - 1 + -(2 * n) = -1 by ring,
      show 2 * n - 1 + (1 - n) = n by ring] using htrans
  rwa [heq]

theorem rlc_insetLeftOdd_vertical_half (n : Int) (hn : 0 < n) :
    (1 : Real) / 2 <= rba_selfDualMeasure.real
      (verticalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
  have hH := rlc_insetLeftOdd_horizontal_half n hn
  have hswap := crf_verticalCrossing_eq_horizontal_swap
    (-2 * n) (-1) (1 - n) n
    (rlc_horizontalCrossing_measurableSet (1 - n) n (-2 * n) (-1))
  have htrans := cti_horizontalCrossing_translation_invariant
    (1 - n) n (-2 * n) (-1) (![-n - 1, n + 1] : Site 2)
    (rlc_horizontalCrossing_measurableSet (1 - n) n (-2 * n) (-1))
  have heq : rba_selfDualMeasure.real
      (verticalCrossingEvent (-2 * n) (-1) (1 - n) n) =
      rba_selfDualMeasure.real
        (horizontalCrossingEvent (-2 * n) (-1) (1 - n) n) := by
    rw [hswap]
    simpa [show 1 - n + (-n - 1) = -2 * n by ring,
      show n + (-n - 1) = -1 by ring,
      show -(2 * n) + (n + 1) = 1 - n by ring,
      show -1 + (n + 1) = n by ring] using htrans.symm
  rwa [heq]

theorem rlc_insetLeftOddSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetLeftOddSourceCoreEvent n) := by
  let F := (rect_finite (-2 * n) (-1) (1 - n) n).toFinset
  have h := rlc_diagonal_event_lower_bound (2⁻¹ : NNReal) half_le_one
    ((1 : Real) / 2) (by norm_num)
    (rlc_insetLeftOddToStrictUpper n)
    (rlc_insetLeftOddLowerToRight n)
    (verticalCrossingEvent (-2 * n) (-1) (1 - n) n)
    (rlc_insetLeftOddSourceCoreEvent n)
    (edgesWithinFinset F) (edgesWithinFinset F) (edgesWithinFinset F)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (rlc_lrRestrictedEvent_isIncreasing _ _ _ _ _ _)
    (StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing _ _ _ _)
    (by simpa [F, rlc_insetLeftOddToStrictUpper] using
      (rlc_lrRestrictedEvent_dependsOn (-2 * n) (-1) (1 - n) n
        Set.univ rlc_strictUpperHalf))
    (by simpa [F, rlc_insetLeftOddLowerToRight] using
      (rlc_lrRestrictedEvent_dependsOn (-2 * n) (-1) (1 - n) n
        rlc_lowerHalf Set.univ))
    (by simpa [F] using
      rlc_verticalCrossing_dependsOn (-2 * n) (-1) (1 - n) n)
    (rlc_insetLeftOddToStrictUpper_half n ((1 : Real) / 2)
      (rlc_insetLeftOdd_horizontal_half n hn))
    (rlc_insetLeftOddLowerToRight_half n ((1 : Real) / 2)
      (rlc_insetLeftOdd_horizontal_half n hn))
    (rlc_insetLeftOdd_vertical_half n hn)
    (rlc_lrRestricted_of_three (-2 * n) (-1) (1 - n) n
      (by omega) (by omega) rlc_lowerHalf rlc_strictUpperHalf)
  norm_num at h
  simpa [rba_selfDualMeasure] using h


theorem rlc_insetRightOddSourceCore_subset (n : Int) :
    rlc_insetRightOddSourceCoreEvent n ⊆ rlc_insetRightSourceCoreEvent n := by
  rintro omega ⟨x, y, hx, hy, hxy⟩
  have hsub : rect 1 (2 * n) (-n) (n - 1) ⊆ rect 1 (2 * n) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  let xl : leftSide 1 (2 * n) (-n) n :=
    ⟨x, hsub (leftSide_subset x.2), x.2.2⟩
  let yr : rightSide 1 (2 * n) (-n) n :=
    ⟨y, hsub (rightSide_subset y.2), y.2.2⟩
  refine ⟨xl, yr, hx, hy, ?_⟩
  simpa [xl, yr] using
    (StatMech.RSW.Strip.connectedWithin_mono_set omega hsub hxy)

theorem rlc_insetLeftOddSourceCore_subset (n : Int) :
    rlc_insetLeftOddSourceCoreEvent n ⊆ rlc_insetLeftSourceCoreEvent n := by
  rintro omega ⟨x, y, hx, hy, hxy⟩
  have hsub : rect (-2 * n) (-1) (1 - n) n ⊆
      rect (-2 * n) (-1) (-n) n := by
    intro z hz
    rw [mem_rect] at hz ⊢
    omega
  let xl : leftSide (-2 * n) (-1) (-n) n :=
    ⟨x, hsub (leftSide_subset x.2), x.2.2⟩
  let yr : rightSide (-2 * n) (-1) (-n) n :=
    ⟨y, hsub (rightSide_subset y.2), y.2.2⟩
  refine ⟨xl, yr, hx, hy, ?_⟩
  simpa [xl, yr] using
    (StatMech.RSW.Strip.connectedWithin_mono_set omega hsub hxy)

theorem rlc_insetRightSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetRightSourceCoreEvent n) :=
  (rlc_insetRightOddSourceCore_mass_lower n hn).trans
    (measureReal_mono (rlc_insetRightOddSourceCore_subset n))

theorem rlc_insetLeftSourceCore_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 32 <=
      rba_selfDualMeasure.real (rlc_insetLeftSourceCoreEvent n) :=
  (rlc_insetLeftOddSourceCore_mass_lower n hn).trans
    (measureReal_mono (rlc_insetLeftOddSourceCore_subset n))

theorem rlc_strictAxisRightSourceEvent_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 64 <=
      rba_selfDualMeasure.real (rlc_strictAxisRightSourceEvent n) := by
  have hatt := rlc_insetRightSourceCore_to_strictAxis_mass
    (2⁻¹ : NNReal) half_le_one n
  have hcore := rlc_insetRightSourceCore_mass_lower n hn
  have hmul : (1 : Real) / 64 <=
      ((2⁻¹ : NNReal) : Real) *
        rba_selfDualMeasure.real (rlc_insetRightSourceCoreEvent n) := by
    norm_num
    linarith
  exact hmul.trans (by simpa [rba_selfDualMeasure] using hatt)

theorem rlc_strictAxisLeftSourceEvent_mass_lower (n : Int) (hn : 0 < n) :
    (1 : Real) / 64 <=
      rba_selfDualMeasure.real (rlc_strictAxisLeftSourceEvent n) := by
  have hatt := rlc_insetLeftSourceCore_to_strictAxis_mass
    (2⁻¹ : NNReal) half_le_one n
  have hcore := rlc_insetLeftSourceCore_mass_lower n hn
  have hmul : (1 : Real) / 64 <=
      ((2⁻¹ : NNReal) : Real) *
        rba_selfDualMeasure.real (rlc_insetLeftSourceCoreEvent n) := by
    norm_num
    linarith
  exact hmul.trans (by simpa [rba_selfDualMeasure] using hatt)

theorem rlc_strictAxisStoppedDiagonalEvent_mass_lower_unconditional
    {n : Int} (hn : 0 < n)
    (hright : RlcRightEnvelopeProperty n)
    (hleft : RlcLeftEnvelopeProperty n) :
    (1 : Real) / 4096 <=
      rba_selfDualMeasure.real (rlc_strictAxisStoppedDiagonalEvent n) := by
  have h := rlc_strictAxisStoppedDiagonalEvent_mass_lower
    (2⁻¹ : NNReal) half_le_one hn hright hleft (a := (1 : Real) / 64)
    (b := (1 : Real) / 64) (by norm_num)
    (rlc_strictAxisRightSourceEvent_mass_lower n hn)
    (rlc_strictAxisLeftSourceEvent_mass_lower n hn)
  norm_num at h
  simpa [rba_selfDualMeasure] using h

end
end StatMech.Universality
