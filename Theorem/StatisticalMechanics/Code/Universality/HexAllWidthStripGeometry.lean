/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexAWNeighbor_invol (c : HexAWCoord) (e : Fin 3) :
    hexAWNeighbor (hexAWNeighbor c e) e = c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> simp [hexAWNeighbor]


theorem hexAWNeighbor_ne (c : HexAWCoord) (e : Fin 3) :
    hexAWNeighbor c e ≠ c := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e <;> simp [hexAWNeighbor]


theorem hexAWPos_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWPos (hexAWNeighbor c e) - hexAWPos c =
      hexUnit (hexAWHeading c e) := by
  rcases c with ⟨i, j, color⟩
  cases color <;> fin_cases e
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWAxis]
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisI, hexAWAxis]
    ring
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisJ, hexAWAxis]
    ring
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWAxis]
    rw [show (7 : ℤ) = 4 + 3 by norm_num, hexUnit_add_three]
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisI, hexAWAxis]
    rw [show (3 : ℤ) = 0 + 3 by norm_num, hexUnit_add_three]
    ring
  · simp [hexAWNeighbor, hexAWPos, hexAWHeading, hexAWBasisJ, hexAWAxis]
    rw [show (5 : ℤ) = 2 + 3 by norm_num, hexUnit_add_three]
    ring


theorem hexAWMid_sub_pos (c : HexAWCoord) (e : Fin 3) :
    hexAWMid c e - hexAWPos c =
      (1 / 2 : ℂ) * hexUnit (hexAWHeading c e) := by
  unfold hexAWMid
  rw [show hexAWPos c + hexAWPos (hexAWNeighbor c e) =
      2 * hexAWPos c +
        (hexAWPos (hexAWNeighbor c e) - hexAWPos c) by ring,
    hexAWPos_neighbor]
  ring


@[simp] theorem hexAWMid_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWMid (hexAWNeighbor c e) e = hexAWMid c e := by
  simp [hexAWMid, add_comm]


theorem hexAWMid_sub_pos_neighbor (c : HexAWCoord) (e : Fin 3) :
    hexAWMid (hexAWNeighbor c e) e - hexAWPos (hexAWNeighbor c e) =
      -(hexAWMid c e - hexAWPos c) := by
  simp only [hexAWMid_neighbor]
  unfold hexAWMid
  ring


end
end StatMech.Universality
