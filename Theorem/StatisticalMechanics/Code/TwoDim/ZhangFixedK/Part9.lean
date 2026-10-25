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
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part9
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_armPair_diff_merged_subset_errorUnion (k N : ℕ) :
    zfk_ArmPairEvent k N \ zfk_MergedArmPairEvent k N ⊆
      zfk_pairErrorUnion k N := by
  intro omega h
  obtain ⟨x, hxK, y, hyK, hxInf, hyInf, hxArm, hyArm⟩ := h.1
  have hnotConn : omega ∉ zbd_connectedWithinBox x y N := by
    intro hxy
    exact h.2 ⟨x, hxK, y, hyK, hxInf, hyInf, hxArm, hyArm, hxy⟩
  apply Set.mem_iUnion.mpr
  refine ⟨x, Set.mem_iUnion.mpr ⟨?_, Set.mem_iUnion.mpr ⟨y,
    Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩⟩⟩
  · simpa using hxK
  · simpa using hyK
  · exact ⟨⟨hxInf, hyInf⟩, hnotConn⟩


theorem zfk_pairErrorUnion_tendsto_zero (k : ℕ) :
    Tendsto (fun N => halfMeasure.real (zfk_pairErrorUnion k N))
      atTop (nhds 0) := by
  let F : ℕ → ℝ := fun N =>
    ∑ x ∈ zfk_leftCentralFinset k, ∑ y ∈ zfk_rightCentralFinset k,
      halfMeasure.real (zfk_pairError x y N)
  have hF : Tendsto F atTop (nhds 0) := by
    dsimp [F]
    convert tendsto_finset_sum (zfk_leftCentralFinset k) (fun x _ =>
      tendsto_finset_sum (zfk_rightCentralFinset k) (fun y _ =>
        zfk_pairError_tendsto_zero x y)) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF
  · intro N
    exact measureReal_nonneg
  · intro N
    exact le_trans (measureReal_biUnion_finset_le _ _)
      (Finset.sum_le_sum fun x _ => measureReal_biUnion_finset_le _ _)


theorem zfk_armPair_subset_crossing_union_error (k N : ℕ) :
    zfk_ArmPairEvent k N ⊆
      StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪
        zfk_pairErrorUnion k N := by
  intro omega harms
  by_cases hmerge : omega ∈ zfk_MergedArmPairEvent k N
  · exact Or.inl (zfk_mergedArmPair_subset_horizontalCrossing k N hmerge)
  · exact Or.inr (zfk_armPair_diff_merged_subset_errorUnion k N ⟨harms, hmerge⟩)

theorem zfk_armPair_probability_le_crossing_add_error (k N : ℕ) :
    halfMeasure.real (zfk_ArmPairEvent k N) ≤
      halfMeasure.real
          (StatMech.RSW.Box.horizontalCrossingEvent
            (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) +
        halfMeasure.real (zfk_pairErrorUnion k N) := by
  calc
    halfMeasure.real (zfk_ArmPairEvent k N) ≤
        halfMeasure.real
          (StatMech.RSW.Box.horizontalCrossingEvent
              (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪
            zfk_pairErrorUnion k N) :=
      measureReal_mono (zfk_armPair_subset_crossing_union_error k N)
        (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _


theorem zfk_armPair_fkg
    (hpa : PositivelyAssociated halfMeasure) (k N : ℕ) :
    halfMeasure.real (zfk_LeftArmEvent k N) *
        halfMeasure.real (zfk_RightArmEvent k N) ≤
      halfMeasure.real (zfk_ArmPairEvent k N) := by
  rw [zfk_armPair_eq_inter]
  exact hpa _ _ (zfk_LeftArmEvent_isIncreasing k N)
    (zfk_RightArmEvent_isIncreasing k N)


theorem zfk_fixedK_contradiction
    (hpa : PositivelyAssociated halfMeasure)
    (q : ℕ → ℝ) (hq : Tendsto q atTop (nhds 1))
    (hqnonneg : ∀ k, 0 ≤ q k)
    (hleft : ∀ k N, k + 1 ≤ N →
      q k ≤ halfMeasure.real (zfk_LeftArmEvent k N))
    (hright : ∀ k N, k + 1 ≤ N →
      q k ≤ halfMeasure.real (zfk_RightArmEvent k N))
    (hhalf : ∀ N : ℕ,
      halfMeasure.real
        (StatMech.RSW.Box.horizontalCrossingEvent
          (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    False := by
  have hk : ∀ k, q k * q k ≤ (1 : ℝ) / 2 := by
    intro k
    have hpoint : ∀ N, k + 1 ≤ N →
        q k * q k ≤ (1 : ℝ) / 2 +
          halfMeasure.real (zfk_pairErrorUnion k N) := by
      intro N hkN
      calc
        q k * q k ≤
            halfMeasure.real (zfk_LeftArmEvent k N) *
              halfMeasure.real (zfk_RightArmEvent k N) := by
          exact mul_le_mul (hleft k N hkN) (hright k N hkN)
            (hqnonneg k) measureReal_nonneg
        _ ≤ halfMeasure.real (zfk_ArmPairEvent k N) :=
          zfk_armPair_fkg hpa k N
        _ ≤ halfMeasure.real
              (StatMech.RSW.Box.horizontalCrossingEvent
                (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) +
              halfMeasure.real (zfk_pairErrorUnion k N) :=
          zfk_armPair_probability_le_crossing_add_error k N
        _ ≤ (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N) := by
          gcongr
          exact hhalf N
    have hlim : Tendsto
        (fun N => (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N))
        atTop (nhds ((1 : ℝ) / 2)) := by
      simpa using tendsto_const_nhds.add (zfk_pairErrorUnion_tendsto_zero k)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      ((eventually_ge_atTop (k + 1)).mono fun N hN => hpoint N hN)
  have hqq : Tendsto (fun k => q k * q k) atTop (nhds 1) := by
    have := hq.mul hq
    simpa using this
  have hbad : (1 : ℝ) ≤ (1 : ℝ) / 2 :=
    le_of_tendsto_of_tendsto hqq tendsto_const_nhds
      (Filter.Eventually.of_forall hk)
  norm_num at hbad


end StatMech.TwoDim
