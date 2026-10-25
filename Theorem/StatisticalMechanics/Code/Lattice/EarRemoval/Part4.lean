/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarRemoval.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Def.StatisticalMechanics.Code.Lattice.EarRemoval.Part4
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dmD0_tail : dmD0.tail = ![0, 0] := rfl

theorem dmD1_tail : dmD1.tail = ![0, 0] := rfl

theorem dmD2_tail : dmD2.tail = ![0, 0] := rfl

theorem dmD3_tail : dmD3.tail = ![1, 0] := rfl

theorem dmD4_tail : dmD4.tail = ![1, 0] := rfl

theorem dmD5_tail : dmD5.tail = ![1, 0] := rfl

theorem dmD0_dir : dmD0.dir = ![0, -1] := by rw [dmD0, mkDart_dir]

theorem dmD1_dir : dmD1.dir = ![-1, 0] := by rw [dmD1, mkDart_dir]

theorem dmD2_dir : dmD2.dir = ![0, 1] := by rw [dmD2, mkDart_dir]

theorem dmD3_dir : dmD3.dir = ![0, 1] := by rw [dmD3, mkDart_dir]

theorem dmD4_dir : dmD4.dir = ![1, 0] := by rw [dmD4, mkDart_dir]

theorem dmD5_dir : dmD5.dir = ![0, -1] := by rw [dmD5, mkDart_dir]

theorem dmD0_head : dmD0.head = ![0, -1] := by
  rw [dmD0, mkDart_head]; funext i; fin_cases i <;> simp

theorem dmD1_head : dmD1.head = ![-1, 0] := by
  rw [dmD1, mkDart_head]; funext i; fin_cases i <;> simp

theorem dmD2_head : dmD2.head = ![0, 1] := by
  rw [dmD2, mkDart_head]; funext i; fin_cases i <;> simp

theorem dmD3_head : dmD3.head = ![1, 1] := by
  rw [dmD3, mkDart_head]; funext i; fin_cases i <;> simp

theorem dmD4_head : dmD4.head = ![2, 0] := by
  rw [dmD4, mkDart_head]; funext i; fin_cases i <;> simp

theorem dmD5_head : dmD5.head = ![1, -1] := by
  rw [dmD5, mkDart_head]; funext i; fin_cases i <;> simp


theorem dmD0_boundary : IsBoundaryDart domino dmD0 :=
  ⟨by rw [dmD0_tail]; exact origin_mem_domino,
   by rw [dmD0_head]; exact not_mem_domino _ (by decide)⟩


theorem dmD0_travel : -rot90Fun dmD0.dir = ![-1, 0] := by
  rw [dmD0_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem dmD1_travel : -rot90Fun dmD1.dir = ![0, 1] := by
  rw [dmD1_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem dmD2_travel : -rot90Fun dmD2.dir = ![1, 0] := by
  rw [dmD2_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem dmD3_travel : -rot90Fun dmD3.dir = ![1, 0] := by
  rw [dmD3_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem dmD4_travel : -rot90Fun dmD4.dir = ![0, -1] := by
  rw [dmD4_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp

theorem dmD5_travel : -rot90Fun dmD5.dir = ![-1, 0] := by
  rw [dmD5_dir, rot90Fun_apply]; funext i; fin_cases i <;> simp


theorem dmD0_front_nmem : dmD0.head + (-rot90Fun dmD0.dir) ∉ domino := by
  rw [dmD0_head, dmD0_travel]; exact not_mem_domino _ (by decide)

theorem dmD0_side_nmem : dmD0.tail + (-rot90Fun dmD0.dir) ∉ domino := by
  rw [dmD0_tail, dmD0_travel]; exact not_mem_domino _ (by decide)


theorem dmD1_front_nmem : dmD1.head + (-rot90Fun dmD1.dir) ∉ domino := by
  rw [dmD1_head, dmD1_travel]; exact not_mem_domino _ (by decide)

theorem dmD1_side_nmem : dmD1.tail + (-rot90Fun dmD1.dir) ∉ domino := by
  rw [dmD1_tail, dmD1_travel]; exact not_mem_domino _ (by decide)


theorem dmD2_front_nmem : dmD2.head + (-rot90Fun dmD2.dir) ∉ domino := by
  rw [dmD2_head, dmD2_travel]; exact not_mem_domino _ (by decide)

theorem dmD2_side_mem : dmD2.tail + (-rot90Fun dmD2.dir) ∈ domino := by
  rw [dmD2_tail, dmD2_travel]
  rw [show (![0,0] : Site 2) + ![1,0] = ![1,0] by funext i; fin_cases i <;> simp]
  exact one_mem_domino


theorem dmD3_front_nmem : dmD3.head + (-rot90Fun dmD3.dir) ∉ domino := by
  rw [dmD3_head, dmD3_travel]; exact not_mem_domino _ (by decide)

theorem dmD3_side_nmem : dmD3.tail + (-rot90Fun dmD3.dir) ∉ domino := by
  rw [dmD3_tail, dmD3_travel]; exact not_mem_domino _ (by decide)


theorem dmD4_front_nmem : dmD4.head + (-rot90Fun dmD4.dir) ∉ domino := by
  rw [dmD4_head, dmD4_travel]; exact not_mem_domino _ (by decide)

theorem dmD4_side_nmem : dmD4.tail + (-rot90Fun dmD4.dir) ∉ domino := by
  rw [dmD4_tail, dmD4_travel]; exact not_mem_domino _ (by decide)


theorem dmD5_front_nmem : dmD5.head + (-rot90Fun dmD5.dir) ∉ domino := by
  rw [dmD5_head, dmD5_travel]; exact not_mem_domino _ (by decide)

theorem dmD5_side_mem : dmD5.tail + (-rot90Fun dmD5.dir) ∈ domino := by
  rw [dmD5_tail, dmD5_travel]
  rw [show (![1,0] : Site 2) + ![-1,0] = ![0,0] by funext i; fin_cases i <;> simp]
  exact origin_mem_domino


theorem dmD0_turnZ : turnZ domino dmD0 = -1 := by
  unfold turnZ; rw [if_neg dmD0_front_nmem, if_neg dmD0_side_nmem]

theorem dmD1_turnZ : turnZ domino dmD1 = -1 := by
  unfold turnZ; rw [if_neg dmD1_front_nmem, if_neg dmD1_side_nmem]

theorem dmD2_turnZ : turnZ domino dmD2 = 0 := by
  unfold turnZ; rw [if_neg dmD2_front_nmem, if_pos dmD2_side_mem]

theorem dmD3_turnZ : turnZ domino dmD3 = -1 := by
  unfold turnZ; rw [if_neg dmD3_front_nmem, if_neg dmD3_side_nmem]

theorem dmD4_turnZ : turnZ domino dmD4 = -1 := by
  unfold turnZ; rw [if_neg dmD4_front_nmem, if_neg dmD4_side_nmem]

theorem dmD5_turnZ : turnZ domino dmD5 = 0 := by
  unfold turnZ; rw [if_neg dmD5_front_nmem, if_pos dmD5_side_mem]

theorem dartNext_dmD0 : dartNext domino dmD0 = dmD1 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD0 dmD0_front_nmem dmD0_side_nmem, dmD0_tail, dmD1_tail]
  · rw [dartNext_left_dir domino dmD0 dmD0_front_nmem dmD0_side_nmem, dmD0_travel, dmD1_dir]

theorem dartNext_dmD1 : dartNext domino dmD1 = dmD2 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD1 dmD1_front_nmem dmD1_side_nmem, dmD1_tail, dmD2_tail]
  · rw [dartNext_left_dir domino dmD1 dmD1_front_nmem dmD1_side_nmem, dmD1_travel, dmD2_dir]

theorem dartNext_dmD2 : dartNext domino dmD2 = dmD3 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_straight_tail domino dmD2 dmD2_front_nmem dmD2_side_mem, dmD2_tail, dmD2_travel,
      dmD3_tail]
    funext i; fin_cases i <;> simp
  · rw [dartNext_straight_dir domino dmD2 dmD2_front_nmem dmD2_side_mem, dmD2_dir, dmD3_dir]

theorem dartNext_dmD3 : dartNext domino dmD3 = dmD4 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD3 dmD3_front_nmem dmD3_side_nmem, dmD3_tail, dmD4_tail]
  · rw [dartNext_left_dir domino dmD3 dmD3_front_nmem dmD3_side_nmem, dmD3_travel, dmD4_dir]

theorem dartNext_dmD4 : dartNext domino dmD4 = dmD5 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_left_tail domino dmD4 dmD4_front_nmem dmD4_side_nmem, dmD4_tail, dmD5_tail]
  · rw [dartNext_left_dir domino dmD4 dmD4_front_nmem dmD4_side_nmem, dmD4_travel, dmD5_dir]

theorem dartNext_dmD5 : dartNext domino dmD5 = dmD0 := by
  apply dart_eq_of_tail_dir
  · rw [dartNext_straight_tail domino dmD5 dmD5_front_nmem dmD5_side_mem, dmD5_tail, dmD5_travel,
      dmD0_tail]
    funext i; fin_cases i <;> simp
  · rw [dartNext_straight_dir domino dmD5 dmD5_front_nmem dmD5_side_mem, dmD5_dir, dmD0_dir]


theorem iterate_dmD_1 : (dartNext domino)^[1] dmD0 = dmD1 := by
  rw [Function.iterate_one]; exact dartNext_dmD0

theorem iterate_dmD_2 : (dartNext domino)^[2] dmD0 = dmD2 := by
  rw [Function.iterate_succ_apply', iterate_dmD_1, dartNext_dmD1]

theorem iterate_dmD_3 : (dartNext domino)^[3] dmD0 = dmD3 := by
  rw [Function.iterate_succ_apply', iterate_dmD_2, dartNext_dmD2]

theorem iterate_dmD_4 : (dartNext domino)^[4] dmD0 = dmD4 := by
  rw [Function.iterate_succ_apply', iterate_dmD_3, dartNext_dmD3]

theorem iterate_dmD_5 : (dartNext domino)^[5] dmD0 = dmD5 := by
  rw [Function.iterate_succ_apply', iterate_dmD_4, dartNext_dmD4]

theorem iterate_dmD_6 : (dartNext domino)^[6] dmD0 = dmD0 := by
  rw [Function.iterate_succ_apply', iterate_dmD_5, dartNext_dmD5]


theorem domino_totalTurnZ_six : totalTurnZ domino dmD0 6 = -4 := by
  unfold totalTurnZ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  rw [Function.iterate_zero_apply, dmD0_turnZ]
  rw [iterate_dmD_1, dmD1_turnZ, iterate_dmD_2, dmD2_turnZ, iterate_dmD_3, dmD3_turnZ,
    iterate_dmD_4, dmD4_turnZ, iterate_dmD_5, dmD5_turnZ]
  ring


end Lattice
end StatMech
