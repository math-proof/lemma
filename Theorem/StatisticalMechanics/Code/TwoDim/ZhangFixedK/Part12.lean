/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part6
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.Universality.KestenBXPWire
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_matched_half_of_faithful_exclusive (N : ℕ)
    (hexcl : zfk_FaithfulMatchedExclusive N) :
    halfMeasure.real
      (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2 := by
  have hu := measureReal_le_one (μ := halfMeasure)
    (s := StatMech.RSW.Box.horizontalCrossingEvent
      (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪
        zfk_FaithfulDualVerticalEvent N)
  rw [measureReal_union hexcl (zfk_FaithfulDualVerticalEvent_measurableSet N),
    zfk_faithfulDualVertical_prob_eq_matched] at hu
  linarith


theorem zfk_thetaReal_zero_of_matched_half
    (hpa : PositivelyAssociated halfMeasure)
    (hhalf : ∀ N : ℕ,
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    halfMeasure.real (Universality.percolationEvent 2) = 0 := by
  by_contra hne
  have hpos : 0 < halfMeasure.real (Universality.percolationEvent 2) :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  exact zfk_fixedK_contradiction hpa zfk_armLower
    (zfk_armLower_tendsto_one hpos) zfk_armLower_nonneg
    (fun k N hkN => zfk_armLower_le_left hpa k N (by omega))
    (fun k N hkN => zfk_armLower_le_right hpa k N (by omega)) hhalf


theorem zfk_percolationProbability_zero_of_matched_half
    (hpa : PositivelyAssociated halfMeasure)
    (hhalf : ∀ N : ℕ,
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    Universality.percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 := by
  unfold Universality.percolationProbability
  have hr := zfk_thetaReal_zero_of_matched_half hpa hhalf
  have hle : halfMeasure (Universality.percolationEvent 2) ≤ 1 :=
    le_trans (measure_mono (subset_univ _)) (by simp [measure_univ])
  have hfin : halfMeasure (Universality.percolationEvent 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hle
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right hfin

theorem zfk_percolationProbability_zero_of_faithful_exclusive
    (hpa : PositivelyAssociated halfMeasure)
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
    Universality.percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 :=
  zfk_percolationProbability_zero_of_matched_half hpa
    (fun N => zfk_matched_half_of_faithful_exclusive N (hexcl N))


theorem zfk_criticalProbability_eq_half_of_faithful_exclusive
    (hpa : PositivelyAssociated halfMeasure)
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n →
      MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet
        (StatMech.RSW.Box.horizontalCrossingEvent (-1) n 0 (n - 1))) :
    criticalProbability 2 = (1 : ℝ) / 2 := by
  have hzero := zfk_percolationProbability_zero_of_faithful_exclusive hpa hexcl
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical hzero
  have hle : criticalProbability 2 ≤ (1 : ℝ) / 2 :=
    kbw_criticalProbability_le_half_square_faithful
      hmeasGenH hmeasFace hmeasThin
  linarith

end StatMech.TwoDim
