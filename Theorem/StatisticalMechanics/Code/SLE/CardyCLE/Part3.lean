/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
import Def.StatisticalMechanics.Code.SLE.CardyCLE.Part3
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

lemma slePhase_of_le_four {κ : ℝ} (h : κ ≤ 4) : slePhase κ = SLEPhase.simple := by
  simp [slePhase, h]


lemma slePhase_of_mem_Ioo {κ : ℝ} (h1 : 4 < κ) (h2 : κ < 8) :
    slePhase κ = SLEPhase.selfTouching := by
  have : ¬ κ ≤ 4 := by linarith
  simp [slePhase, this, h2]


lemma slePhase_of_eight_le {κ : ℝ} (h : 8 ≤ κ) :
    slePhase κ = SLEPhase.spaceFilling := by
  have h1 : ¬ κ ≤ 4 := by linarith
  have h2 : ¬ κ < 8 := by linarith
  simp [slePhase, h1, h2]


@[simp] lemma slePhase_four : slePhase 4 = SLEPhase.simple :=
  slePhase_of_le_four le_rfl


@[simp] lemma slePhase_eight : slePhase 8 = SLEPhase.spaceFilling :=
  slePhase_of_eight_le le_rfl


@[simp] lemma slePhase_zero : slePhase 0 = SLEPhase.simple :=
  slePhase_of_le_four (by norm_num)


@[simp] lemma slePhase_six : slePhase 6 = SLEPhase.selfTouching :=
  slePhase_of_mem_Ioo (by norm_num) (by norm_num)


lemma slePhase_eq_simple_iff {κ : ℝ} (hκ : 0 ≤ κ) :
    slePhase κ = SLEPhase.simple ↔ IsSimplePhase κ := by
  unfold slePhase IsSimplePhase
  constructor
  · intro h
    by_cases hc : κ ≤ 4
    · exact ⟨hκ, hc⟩
    · simp only [hc, if_false] at h
      split at h <;> simp_all
  · rintro ⟨_, h4⟩
    simp [h4]


lemma slePhase_eq_selfTouching_iff {κ : ℝ} :
    slePhase κ = SLEPhase.selfTouching ↔ IsSelfTouchingPhase κ := by
  unfold slePhase IsSelfTouchingPhase
  constructor
  · intro h
    by_cases hc : κ ≤ 4
    · simp [hc] at h
    · by_cases hc' : κ < 8
      · exact ⟨lt_of_not_ge hc, hc'⟩
      · simp [hc, hc'] at h
  · rintro ⟨h4, h8⟩
    have : ¬ κ ≤ 4 := by linarith
    simp [this, h8]


lemma slePhase_eq_spaceFilling_iff {κ : ℝ} :
    slePhase κ = SLEPhase.spaceFilling ↔ IsSpaceFillingPhase κ := by
  unfold slePhase IsSpaceFillingPhase
  constructor
  · intro h
    by_cases hc : κ ≤ 4
    · simp [hc] at h
    · by_cases hc' : κ < 8
      · simp [hc, hc'] at h
      · exact le_of_not_gt hc'
  · intro h
    have h1 : ¬ κ ≤ 4 := by linarith
    have h2 : ¬ κ < 8 := by linarith
    simp [h1, h2]


lemma slePhase_kappaPercolation : slePhase kappaPercolation = SLEPhase.selfTouching :=
  slePhase_eq_selfTouching_iff.mpr kappaPercolation_selfTouching


lemma slePhase_kappaIsing : slePhase kappaIsing = SLEPhase.simple :=
  (slePhase_eq_simple_iff kappaIsing_simple.1).mpr kappaIsing_simple


lemma cardyCrossing_eq (s : ℝ) :
    cardyCrossing s =
      cardyPrefactor * s ^ ((1 : ℝ) / 3) *
        ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) s := rfl


lemma cardyCrossing_factor_pos {s : ℝ} (hs : 0 < s) :
    0 < cardyPrefactor * s ^ ((1 : ℝ) / 3) :=
  mul_pos cardyPrefactor_pos (Real.rpow_pos_of_pos hs _)


lemma cardyHypergeometric_zero :
    ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) (0 : ℝ) = 1 :=
  ordinaryHypergeometric_zero _ _ _


end StatMech.SLE
