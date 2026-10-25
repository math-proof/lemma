/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Def.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem unitCellFaceLoop_isCycle : unitCellFaceLoop.IsCycle :=
  orbitFaceWalk_isCycle unitCell ucDart0 ucDart0_boundary 4 (by norm_num)
    iterate_ucDart_4 unitCell_orbitFace_injOn


theorem dmFace0 : dartFace dmD0 = ![0, -1] := by
  rw [dartFace_of_dir_down _ dmD0_dir, dmD0_tail]; funext i; fin_cases i <;> simp


theorem dmFace1 : dartFace dmD1 = ![-1, -1] := by
  rw [dartFace_of_dir_left _ dmD1_dir, dmD1_tail]; funext i; fin_cases i <;> simp


theorem dmFace2 : dartFace dmD2 = ![-1, 0] := by
  rw [dartFace_of_dir_up _ dmD2_dir, dmD2_tail]; funext i; fin_cases i <;> simp


theorem dmFace3 : dartFace dmD3 = ![0, 0] := by
  rw [dartFace_of_dir_up _ dmD3_dir, dmD3_tail]; funext i; fin_cases i <;> simp


theorem dmFace4 : dartFace dmD4 = ![1, 0] := by
  rw [dartFace_of_dir_right _ dmD4_dir, dmD4_tail]; funext i; fin_cases i <;> simp


theorem dmFace5 : dartFace dmD5 = ![1, -1] := by
  rw [dartFace_of_dir_down _ dmD5_dir, dmD5_tail]; funext i; fin_cases i <;> simp


theorem domino_orbitFace_injOn :
    Set.InjOn (fun k => dartFace ((dartNext domino)^[k] dmD0)) (Set.Iio 6) := by
  have e0 : dartFace ((dartNext domino)^[0] dmD0) = ![0, -1] := by
    rw [Function.iterate_zero_apply]; exact dmFace0
  have e1 : dartFace ((dartNext domino)^[1] dmD0) = ![-1, -1] := by
    rw [iterate_dmD_1]; exact dmFace1
  have e2 : dartFace ((dartNext domino)^[2] dmD0) = ![-1, 0] := by
    rw [iterate_dmD_2]; exact dmFace2
  have e3 : dartFace ((dartNext domino)^[3] dmD0) = ![0, 0] := by
    rw [iterate_dmD_3]; exact dmFace3
  have e4 : dartFace ((dartNext domino)^[4] dmD0) = ![1, 0] := by
    rw [iterate_dmD_4]; exact dmFace4
  have e5 : dartFace ((dartNext domino)^[5] dmD0) = ![1, -1] := by
    rw [iterate_dmD_5]; exact dmFace5
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  interval_cases a <;> interval_cases b <;>
    simp only [e0, e1, e2, e3, e4, e5] at hab ⊢ <;>
    first
    | rfl
    | (exfalso; rw [funext_iff, Fin.forall_fin_two] at hab; simp at hab)


end Lattice
end StatMech
