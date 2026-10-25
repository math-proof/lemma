/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part6


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWReflectCoord_invol (c : HexAWCoord) :
    hexAWReflectCoord (hexAWReflectCoord c) = c := by
  rcases c with ⟨i, j, color⟩
  rfl

@[simp] theorem hexAWReflectEdge_invol (e : Fin 3) :
    hexAWReflectEdge (hexAWReflectEdge e) = e := by
  fin_cases e <;> rfl

@[simp] theorem hexAWReflectEdge_fixed_iff (e : Fin 3) :
    hexAWReflectEdge e = e ↔ e = 0 := by
  fin_cases e <;> simp [hexAWReflectEdge]

@[simp] theorem hexAWLong_reflect (c : HexAWCoord) :
    hexAWLong (hexAWReflectCoord c) = hexAWLong c := by
  simp [hexAWLong, hexAWReflectCoord, add_comm]

@[simp] theorem hexAWTrans_reflect (c : HexAWCoord) :
    hexAWTrans (hexAWReflectCoord c) = -hexAWTrans c := by
  simp [hexAWTrans, hexAWReflectCoord]

@[simp] theorem hexAWDepth_reflect (c : HexAWCoord) :
    hexAWDepth (hexAWReflectCoord c) = hexAWDepth c := by
  simp [hexAWDepth]

@[simp] theorem hexAWBookRe2_reflect (c : HexAWCoord) :
    hexAWBookRe2 (hexAWReflectCoord c) = hexAWBookRe2 c := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWBookRe2, hexAWDepth, hexAWLong, hexAWReflectCoord,
      add_comm]

@[simp] theorem hexAWBookSqrt3Im2_reflect (c : HexAWCoord) :
    hexAWBookSqrt3Im2 (hexAWReflectCoord c) =
      -hexAWBookSqrt3Im2 c := by
  simp [hexAWBookSqrt3Im2]

theorem hexAWInStrip_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWInStrip T L (hexAWReflectCoord c) ↔ hexAWInStrip T L c := by
  simp only [hexAWInStrip, hexAWBookRe2_reflect,
    hexAWBookSqrt3Im2_reflect]
  constructor
  · rintro ⟨hL, hU, hTn, hTp⟩
    exact ⟨hL, hU, by linarith, by linarith⟩
  · rintro ⟨hL, hU, hTn, hTp⟩
    exact ⟨hL, hU, by linarith, by linarith⟩

theorem hexAWCoordBox_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWReflectCoord c ∈ hexAWCoordBox T L ↔ c ∈ hexAWCoordBox T L := by
  rcases c with ⟨i, j, color⟩
  simp [hexAWCoordBox, hexAWReflectCoord, and_left_comm, and_comm]


theorem hexAWVertexSet_reflect_iff (T L : ℕ) (c : HexAWCoord) :
    hexAWReflectCoord c ∈ hexAWVertexSet T L ↔
      c ∈ hexAWVertexSet T L := by
  simp [hexAWVertexSet, hexAWCoordBox_reflect_iff,
    hexAWInStrip_reflect_iff]


theorem hexAWReflectCoord_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWReflectCoord (hexAWNeighbor c e) =
      hexAWNeighbor (hexAWReflectCoord c) (hexAWReflectEdge e) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;>
    simp [hexAWReflectCoord, hexAWNeighbor, hexAWReflectEdge]


theorem hexAWLinearReflect_four :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) = hexUnit 4 := by
  simpa using (hsc_genHexUnit 4 4).symm

theorem hexAWLinearReflect_zero :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) = hexUnit 2 := by
  calc
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) = hexUnit 8 := by
      simpa using (hsc_genHexUnit 4 0).symm
    _ = hexUnit 2 := by
      rw [show (8 : ℤ) = (2 + 3) + 3 by norm_num,
        hexUnit_add_three, hexUnit_add_three]
      ring

theorem hexAWLinearReflect_two :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) = hexUnit 0 := by
  calc
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) = hexUnit 6 := by
      simpa using (hsc_genHexUnit 4 2).symm
    _ = hexUnit 0 := by
      rw [show (6 : ℤ) = (0 + 3) + 3 by norm_num,
        hexUnit_add_three, hexUnit_add_three]
      ring

theorem hexAWLinearReflect_basisI :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI = hexAWBasisJ := by
  unfold hexAWBasisI hexAWBasisJ
  rw [map_sub]
  calc
    (hexUnit 4) ^ 2 *
        ((starRingEnd ℂ) (hexUnit 4) - (starRingEnd ℂ) (hexUnit 0)) =
      (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) -
        (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 0) := by ring
    _ = hexUnit 4 - hexUnit 2 := by
      rw [hexAWLinearReflect_four, hexAWLinearReflect_zero]

theorem hexAWLinearReflect_basisJ :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ = hexAWBasisI := by
  unfold hexAWBasisI hexAWBasisJ
  rw [map_sub]
  calc
    (hexUnit 4) ^ 2 *
        ((starRingEnd ℂ) (hexUnit 4) - (starRingEnd ℂ) (hexUnit 2)) =
      (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) -
        (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 2) := by ring
    _ = hexUnit 4 - hexUnit 0 := by
      rw [hexAWLinearReflect_four, hexAWLinearReflect_two]

theorem hexAWLinearReflect_start :
    (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart = hexAWStart := by
  unfold hexAWStart halfStep
  rw [map_mul, map_div₀, map_one, map_ofNat]
  calc
    (hexUnit 4) ^ 2 *
        ((1 : ℂ) / 2 * (starRingEnd ℂ) (hexUnit 4)) =
      (1 / 2 : ℂ) *
        ((hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4)) := by ring
    _ = (1 / 2 : ℂ) * hexUnit 4 := by rw [hexAWLinearReflect_four]


theorem hexAWPos_reflect (c : HexAWCoord) :
    hsc_refl hexAWStart 4 (hexAWPos c) =
      hexAWPos (hexAWReflectCoord c) := by
  rcases c with ⟨i, j, color⟩
  cases color
  · simp only [hsc_refl, hexAWPos, hexAWReflectCoord, map_sub, map_add,
      map_mul, map_intCast, map_zero]
    rw [show hexAWStart + (hexUnit 4) ^ 2 *
        ((i : ℂ) * (starRingEnd ℂ) hexAWBasisI +
          (j : ℂ) * (starRingEnd ℂ) hexAWBasisJ + 0 -
          (starRingEnd ℂ) hexAWStart) =
        (i : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI) +
          (j : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ) +
          (hexAWStart -
            (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart) by ring,
      hexAWLinearReflect_basisI, hexAWLinearReflect_basisJ,
      hexAWLinearReflect_start]
    ring
  · simp only [hsc_refl, hexAWPos, hexAWReflectCoord, hexAWAxis,
      map_sub, map_add, map_mul, map_intCast]
    rw [show hexAWStart + (hexUnit 4) ^ 2 *
        ((i : ℂ) * (starRingEnd ℂ) hexAWBasisI +
          (j : ℂ) * (starRingEnd ℂ) hexAWBasisJ +
          (starRingEnd ℂ) (hexUnit 4) -
          (starRingEnd ℂ) hexAWStart) =
        (i : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisI) +
          (j : ℂ) * ((hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWBasisJ) +
          (hexUnit 4) ^ 2 * (starRingEnd ℂ) (hexUnit 4) +
          (hexAWStart -
            (hexUnit 4) ^ 2 * (starRingEnd ℂ) hexAWStart) by ring,
      hexAWLinearReflect_basisI, hexAWLinearReflect_basisJ,
      hexAWLinearReflect_four, hexAWLinearReflect_start]
    ring


theorem hexAWRefl_average (x y : ℂ) :
    hsc_refl hexAWStart 4 ((x + y) / 2) =
      (hsc_refl hexAWStart 4 x + hsc_refl hexAWStart 4 y) / 2 := by
  unfold hsc_refl
  simp only [map_sub, map_div₀, map_add, map_ofNat]
  ring


theorem hexAWMid_reflect (c : HexAWCoord) (e : Fin 3) :
    hsc_refl hexAWStart 4 (hexAWMid c e) =
      hexAWMid (hexAWReflectCoord c) (hexAWReflectEdge e) := by
  unfold hexAWMid
  rw [hexAWRefl_average, hexAWPos_reflect, hexAWPos_reflect,
    hexAWReflectCoord_neighbor]


theorem hexAW_refl_one_eq_four (z : ℂ) :
    hsc_refl hexAWStart 1 z = hsc_refl hexAWStart 4 z := by
  unfold hsc_refl
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

theorem hexAWMid_reflect_one (c : HexAWCoord) (e : Fin 3) :
    hsc_refl hexAWStart 1 (hexAWMid c e) =
      hexAWMid (hexAWReflectCoord c) (hexAWReflectEdge e) := by
  rw [hexAW_refl_one_eq_four]
  exact hexAWMid_reflect c e


end
end StatMech.Universality
