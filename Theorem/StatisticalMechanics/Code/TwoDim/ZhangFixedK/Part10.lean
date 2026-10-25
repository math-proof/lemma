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
import Def.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part10
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation

open StatMech.RSW.Box


theorem zfk_armLower_nonneg (k : ℕ) : 0 ≤ zfk_armLower k := by
  have hbase0 : 0 ≤ 1 - halfMeasure.real (zbd_boxHitsInfinite k) := by
    linarith [measureReal_le_one (μ := halfMeasure)
      (s := zbd_boxHitsInfinite k)]
  have hbase1 : 1 - halfMeasure.real (zbd_boxHitsInfinite k) ≤ 1 := by
    linarith [measureReal_nonneg (μ := halfMeasure)
      (s := zbd_boxHitsInfinite k)]
  have hr := Real.rpow_le_one hbase0 hbase1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  unfold zfk_armLower
  linarith

theorem zfk_armLower_tendsto_one
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
    Tendsto zfk_armLower atTop (nhds 1) := by
  exact zhg_oneSubRpow_tendsto_one (zbd_boxHitsInfinite_tendsto_one hpos)


theorem zfk_armLower_le_left
    (hpa : PositivelyAssociated halfMeasure) (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_LeftArmEvent k N) := by
  let S := zrs_sideFamily (zfk_LeftArmEvent k N)
  have hinc : ∀ i : Fin 4, IsIncreasing (S i) := fun i =>
    zrs_sideFamily_isIncreasing (zfk_LeftArmEvent_isIncreasing k N) i
  have hmeas : ∀ i : Fin 4, MeasurableSet (S i) := fun i =>
    zrs_sideFamily_measurableSet (zfk_LeftArmEvent_measurableSet k N) i
  have hsym : ∀ i : Fin 4,
      halfMeasure.real (S i) = halfMeasure.real (S 0) := fun i =>
    zrs_side_symmetry (zfk_LeftArmEvent_measurableSet k N) i
  have hsqrt := zhg_sqrt_trick_four halfMeasure hpa
    (hinc 0) (hinc 1) (hinc 2) (hinc 3)
    (hmeas 0) (hmeas 1) (hmeas 2) (hmeas 3)
    (hsym 1).symm (hsym 2).symm (hsym 3).symm
  have hmono : halfMeasure.real (zbd_boxHitsInfinite k) ≤
      halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) :=
    measureReal_mono (zfk_boxHitsInfinite_subset_armUnion k N hkN)
      (measure_ne_top _ _)
  have hU0 : 0 ≤ 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
    linarith [measureReal_le_one (μ := halfMeasure)
      (s := S 0 ∪ S 1 ∪ S 2 ∪ S 3)]
  have hcomp : 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) ≤
      1 - halfMeasure.real (zbd_boxHitsInfinite k) := by linarith
  have hrpow := Real.rpow_le_rpow hU0 hcomp
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  change 1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) at hsqrt
  change (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤
    (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^ ((1 : ℝ) / 4) at hrpow
  have hfinal : 1 - (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by linarith
  simpa [zfk_armLower, S] using hfinal

theorem zfk_centeredRight_eq_rot2 (k N : ℕ) :
    zfk_CenteredRightArmEvent k N =
      zrs_rot (zrs_rot (zfk_LeftArmEvent k N)) := by
  rw [zfk_rot_leftArmEvent_eq_top, zfk_rot_topArmEvent_eq_right]

theorem zfk_CenteredRightArmEvent_measurableSet (k N : ℕ) :
    MeasurableSet (zfk_CenteredRightArmEvent k N) := by
  rw [zfk_centeredRight_eq_rot2]
  exact zrs_rotPreimage_measurableSet
    (zrs_rotPreimage_measurableSet (zfk_LeftArmEvent_measurableSet k N))

theorem zfk_centeredRight_prob_eq_left (k N : ℕ) :
    halfMeasure.real (zfk_CenteredRightArmEvent k N) =
      halfMeasure.real (zfk_LeftArmEvent k N) := by
  rw [zfk_centeredRight_eq_rot2]
  exact zrs_side_symmetry (zfk_LeftArmEvent_measurableSet k N) 1


theorem zfk_rightArmEvent_eq_translate_preimage (k N : ℕ) :
    zfk_RightArmEvent k N =
      translateConfig (![1, 0] : Site 2) ⁻¹' zfk_CenteredRightArmEvent k N := by
  ext omega
  change (∃ y ∈ zfk_rightCentralBox k,
      (cluster 2 omega y).Infinite ∧ zfk_RightArmFrom omega y N) ↔
    ∃ x ∈ box 2 k, (cluster 2 (translateConfig ![1, 0] omega) x).Infinite ∧
      ∃ (hx : x ∈ zfk_leftSquare N)
        (a : StatMech.RSW.Box.rightSide
          (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)),
        ConnectedWithin 2 (translateConfig ![1, 0] omega) (zfk_leftSquare N)
          ⟨(a : Site 2), StatMech.RSW.Box.rightSide_subset a.2⟩ ⟨x, hx⟩
  constructor
  · rintro ⟨y, hyK, hyInf, hyS, b, hyb⟩
    let x : Site 2 := y - ![1, 0]
    have hxK : x ∈ box 2 k := hyK
    have hxS : x ∈ zfk_leftSquare N := by
      simpa [zfk_leftSquare, zfk_rightSquare, mem_rect, x] using hyS
    let a : StatMech.RSW.Box.rightSide
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) :=
      ⟨(b : Site 2) - ![1, 0], by
        rcases b.2 with ⟨⟨hl, hr, hb, ht⟩, heq⟩
        refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
          simp only [Pi.sub_apply] <;> norm_num at * <;> omega⟩
    refine ⟨x, hxK, ?_, hxS, a, ?_⟩
    · apply (zfk_translate_clusterInfinite_iff (![1, 0] : Site 2) omega x).mpr
      have hxy : x + (![1, 0] : Site 2) = y := by
        change (y - (![1, 0] : Site 2)) + ![1, 0] = y
        exact sub_add_cancel y ![1, 0]
      rwa [hxy]
    · have hxy : x + (![1, 0] : Site 2) = y := by
        change (y - (![1, 0] : Site 2)) + ![1, 0] = y
        exact sub_add_cancel y ![1, 0]
      have hab : (a : Site 2) + (![1, 0] : Site 2) = (b : Site 2) := by
        dsimp [a]
        exact sub_add_cancel (b : Site 2) (![1, 0] : Site 2)
      have htranslated : ConnectedWithin 2 omega (zfk_rightSquare N)
          ⟨(a : Site 2) + ![1, 0], (zfk_shift_mem_rightSquare_iff N _).mp
            (StatMech.RSW.Box.rightSide_subset a.2)⟩
          ⟨x + ![1, 0], (zfk_shift_mem_rightSquare_iff N _).mp hxS⟩ := by
        convert hyb.symm using 1 <;> apply Subtype.ext
        · exact hab
        · exact hxy
      have hmap := (zfk_connectedWithin_shiftRight_iff omega N (a : Site 2) x
          (StatMech.RSW.Box.rightSide_subset a.2) hxS).mpr htranslated
      simpa [zfk_leftSquare, x, a] using hmap
  · rintro ⟨x, hxK, hxInf, hxS, a, hax⟩
    let y : Site 2 := x + ![1, 0]
    have hyK : y ∈ zfk_rightCentralBox k := by
      simpa [zfk_rightCentralBox, y] using hxK
    have hyS : y ∈ zfk_rightSquare N := by
      rw [zfk_rightSquare]
      simpa [y] using (cti_mem_rect_translate
        (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)
        (![1, 0] : Site 2) x).mp (by simpa [zfk_leftSquare] using hxS)
    let b : StatMech.RSW.Box.rightSide
        (-(N : ℤ) + 1) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) :=
      ⟨(a : Site 2) + ![1, 0], by
        simpa using (cti_mem_rightSide_translate
          (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)
          (![1, 0] : Site 2) a).mp a.2⟩
    refine ⟨y, hyK, ?_, hyS, b, ?_⟩
    · exact (zfk_translate_clusterInfinite_iff (![1, 0] : Site 2) omega x).mp hxInf
    · have hmap := (zfk_connectedWithin_shiftRight_iff omega N (a : Site 2) x
          (StatMech.RSW.Box.rightSide_subset a.2) hxS).mp hax
      exact hmap.symm

theorem zfk_right_prob_eq_left (k N : ℕ) :
    halfMeasure.real (zfk_RightArmEvent k N) =
      halfMeasure.real (zfk_LeftArmEvent k N) := by
  rw [zfk_rightArmEvent_eq_translate_preimage]
  calc
    halfMeasure.real
        (translateConfig (![1, 0] : Site 2) ⁻¹' zfk_CenteredRightArmEvent k N) =
        halfMeasure.real (zfk_CenteredRightArmEvent k N) :=
      (cti_selfDual_shift_invariant (![1, 0] : Site 2)).measureReal_preimage
        (zfk_CenteredRightArmEvent_measurableSet k N).nullMeasurableSet
    _ = halfMeasure.real (zfk_LeftArmEvent k N) :=
      zfk_centeredRight_prob_eq_left k N

theorem zfk_armLower_le_right
    (hpa : PositivelyAssociated halfMeasure) (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_RightArmEvent k N) := by
  rw [zfk_right_prob_eq_left]
  exact zfk_armLower_le_left hpa k N hkN


end StatMech.TwoDim
