/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Def.StatisticalMechanics.Code.Lattice.CornerBalance.Part3
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ucDart0_tail : ucDart0.tail = ![0, 0] := rfl

theorem ucDart1_tail : ucDart1.tail = ![0, 0] := rfl

theorem ucDart2_tail : ucDart2.tail = ![0, 0] := rfl

theorem ucDart3_tail : ucDart3.tail = ![0, 0] := rfl

theorem ucDart0_dir : ucDart0.dir = ![1, 0] := by rw [ucDart0, mkDart_dir]

theorem ucDart1_dir : ucDart1.dir = ![0, -1] := by rw [ucDart1, mkDart_dir]

theorem ucDart2_dir : ucDart2.dir = ![-1, 0] := by rw [ucDart2, mkDart_dir]

theorem ucDart3_dir : ucDart3.dir = ![0, 1] := by rw [ucDart3, mkDart_dir]

theorem ucDart0_head : ucDart0.head = ![1, 0] := by
  rw [ucDart0, mkDart_head]; funext i; fin_cases i <;> simp

theorem ucDart1_head : ucDart1.head = ![0, -1] := by
  rw [ucDart1, mkDart_head]; funext i; fin_cases i <;> simp

theorem ucDart2_head : ucDart2.head = ![-1, 0] := by
  rw [ucDart2, mkDart_head]; funext i; fin_cases i <;> simp

theorem ucDart3_head : ucDart3.head = ![0, 1] := by
  rw [ucDart3, mkDart_head]; funext i; fin_cases i <;> simp


theorem ucDart0_boundary : IsBoundaryDart unitCell ucDart0 :=
  ⟨by rw [ucDart0_tail]; exact origin_mem_unitCell,
   by rw [ucDart0_head]; exact not_mem_unitCell _ (Or.inl (by simp))⟩

theorem ucDart1_boundary : IsBoundaryDart unitCell ucDart1 :=
  ⟨by rw [ucDart1_tail]; exact origin_mem_unitCell,
   by rw [ucDart1_head]; exact not_mem_unitCell _ (Or.inr (by simp))⟩

theorem ucDart2_boundary : IsBoundaryDart unitCell ucDart2 :=
  ⟨by rw [ucDart2_tail]; exact origin_mem_unitCell,
   by rw [ucDart2_head]; exact not_mem_unitCell _ (Or.inl (by simp))⟩

theorem ucDart3_boundary : IsBoundaryDart unitCell ucDart3 :=
  ⟨by rw [ucDart3_tail]; exact origin_mem_unitCell,
   by rw [ucDart3_head]; exact not_mem_unitCell _ (Or.inr (by simp))⟩


theorem ucDart0_travel : -rot90Fun ucDart0.dir = ![0, -1] := by
  rw [ucDart0_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem ucDart1_travel : -rot90Fun ucDart1.dir = ![-1, 0] := by
  rw [ucDart1_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem ucDart2_travel : -rot90Fun ucDart2.dir = ![0, 1] := by
  rw [ucDart2_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem ucDart3_travel : -rot90Fun ucDart3.dir = ![1, 0] := by
  rw [ucDart3_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp


theorem ucDart0_front_nmem : ucDart0.head + (-rot90Fun ucDart0.dir) ∉ unitCell := by
  rw [ucDart0_head, ucDart0_travel]; exact not_mem_unitCell _ (Or.inl (by simp))

theorem ucDart0_side_nmem : ucDart0.tail + (-rot90Fun ucDart0.dir) ∉ unitCell := by
  rw [ucDart0_tail, ucDart0_travel]; exact not_mem_unitCell _ (Or.inr (by simp))

theorem ucDart1_front_nmem : ucDart1.head + (-rot90Fun ucDart1.dir) ∉ unitCell := by
  rw [ucDart1_head, ucDart1_travel]; exact not_mem_unitCell _ (Or.inl (by simp))

theorem ucDart1_side_nmem : ucDart1.tail + (-rot90Fun ucDart1.dir) ∉ unitCell := by
  rw [ucDart1_tail, ucDart1_travel]; exact not_mem_unitCell _ (Or.inl (by simp))

theorem ucDart2_front_nmem : ucDart2.head + (-rot90Fun ucDart2.dir) ∉ unitCell := by
  rw [ucDart2_head, ucDart2_travel]; exact not_mem_unitCell _ (Or.inl (by simp))

theorem ucDart2_side_nmem : ucDart2.tail + (-rot90Fun ucDart2.dir) ∉ unitCell := by
  rw [ucDart2_tail, ucDart2_travel]; exact not_mem_unitCell _ (Or.inr (by simp))

theorem ucDart3_front_nmem : ucDart3.head + (-rot90Fun ucDart3.dir) ∉ unitCell := by
  rw [ucDart3_head, ucDart3_travel]; exact not_mem_unitCell _ (Or.inl (by simp))

theorem ucDart3_side_nmem : ucDart3.tail + (-rot90Fun ucDart3.dir) ∉ unitCell := by
  rw [ucDart3_tail, ucDart3_travel]; exact not_mem_unitCell _ (Or.inl (by simp))


theorem ucDart0_turnZ : turnZ unitCell ucDart0 = -1 := by
  unfold turnZ; rw [if_neg ucDart0_front_nmem, if_neg ucDart0_side_nmem]

theorem ucDart1_turnZ : turnZ unitCell ucDart1 = -1 := by
  unfold turnZ; rw [if_neg ucDart1_front_nmem, if_neg ucDart1_side_nmem]

theorem ucDart2_turnZ : turnZ unitCell ucDart2 = -1 := by
  unfold turnZ; rw [if_neg ucDart2_front_nmem, if_neg ucDart2_side_nmem]

theorem ucDart3_turnZ : turnZ unitCell ucDart3 = -1 := by
  unfold turnZ; rw [if_neg ucDart3_front_nmem, if_neg ucDart3_side_nmem]

theorem dartNext_ucDart0 : dartNext unitCell ucDart0 = ucDart1 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart0 ucDart0_front_nmem ucDart0_side_nmem,
      ucDart0_tail, ucDart1_tail]
  · rw [dartNext_left_dir unitCell ucDart0 ucDart0_front_nmem ucDart0_side_nmem,
      ucDart0_travel, ucDart1_dir]

theorem dartNext_ucDart1 : dartNext unitCell ucDart1 = ucDart2 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart1 ucDart1_front_nmem ucDart1_side_nmem,
      ucDart1_tail, ucDart2_tail]
  · rw [dartNext_left_dir unitCell ucDart1 ucDart1_front_nmem ucDart1_side_nmem,
      ucDart1_travel, ucDart2_dir]

theorem dartNext_ucDart2 : dartNext unitCell ucDart2 = ucDart3 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart2 ucDart2_front_nmem ucDart2_side_nmem,
      ucDart2_tail, ucDart3_tail]
  · rw [dartNext_left_dir unitCell ucDart2 ucDart2_front_nmem ucDart2_side_nmem,
      ucDart2_travel, ucDart3_dir]

theorem dartNext_ucDart3 : dartNext unitCell ucDart3 = ucDart0 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail unitCell ucDart3 ucDart3_front_nmem ucDart3_side_nmem,
      ucDart3_tail, ucDart0_tail]
  · rw [dartNext_left_dir unitCell ucDart3 ucDart3_front_nmem ucDart3_side_nmem,
      ucDart3_travel, ucDart0_dir]


theorem iterate_ucDart_1 : (dartNext unitCell)^[1] ucDart0 = ucDart1 := by
  rw [Function.iterate_one]; exact dartNext_ucDart0

theorem iterate_ucDart_2 : (dartNext unitCell)^[2] ucDart0 = ucDart2 := by
  rw [Function.iterate_succ_apply', iterate_ucDart_1, dartNext_ucDart1]

theorem iterate_ucDart_3 : (dartNext unitCell)^[3] ucDart0 = ucDart3 := by
  rw [Function.iterate_succ_apply', iterate_ucDart_2, dartNext_ucDart2]

theorem iterate_ucDart_4 : (dartNext unitCell)^[4] ucDart0 = ucDart0 := by
  rw [Function.iterate_succ_apply', iterate_ucDart_3, dartNext_ucDart3]


theorem unitCell_totalTurnZ_four : totalTurnZ unitCell ucDart0 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart0_turnZ
  · rw [dartNext_ucDart0]; exact ucDart1_turnZ
  · rw [iterate_ucDart_2]; exact ucDart2_turnZ
  · rw [iterate_ucDart_3]; exact ucDart3_turnZ


end Lattice
end StatMech
