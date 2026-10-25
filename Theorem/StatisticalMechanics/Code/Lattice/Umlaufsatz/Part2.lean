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
import Def.StatisticalMechanics.Code.Lattice.Umlaufsatz
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem orbitFace_injOn_of_noPinch (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (h : OrbitFaceNoPinch K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
  intro i hi j hj hface
  simp only at hface
  have hdir := h i hi j hj hface
  have hdart : (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
    dartFace_eq_of_dir_eq hdir hface
  exact orbitDart_injOn K a hi hj hdart


theorem orbitFace_noPinch_of_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
    OrbitFaceNoPinch K a := by
  intro i hi j hj hface
  have hij : i = j := hinj hi hj hface
  rw [hij]


theorem orbitFace_injOn_iff_dir_collision (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) ↔
      OrbitFaceNoPinch K a :=
  ⟨orbitFace_noPinch_of_injOn K a, orbitFace_injOn_of_noPinch K a⟩


theorem ucFace0 : dartFace ucDart0 = ![0, 0] := by
  rw [dartFace_of_dir_right _ ucDart0_dir, ucDart0_tail]; funext i; fin_cases i <;> simp


theorem ucFace1 : dartFace ucDart1 = ![0, -1] := by
  rw [dartFace_of_dir_down _ ucDart1_dir, ucDart1_tail]; funext i; fin_cases i <;> simp


theorem ucFace2 : dartFace ucDart2 = ![-1, -1] := by
  rw [dartFace_of_dir_left _ ucDart2_dir, ucDart2_tail]; funext i; fin_cases i <;> simp


theorem ucFace3 : dartFace ucDart3 = ![-1, 0] := by
  rw [dartFace_of_dir_up _ ucDart3_dir, ucDart3_tail]; funext i; fin_cases i <;> simp


theorem unitCell_orbitFace_injOn :
    Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucDart0)) (Set.Iio 4) := by
  have e0 : dartFace ((dartNext unitCell)^[0] ucDart0) = ![0, 0] := by
    rw [Function.iterate_zero_apply]; exact ucFace0
  have e1 : dartFace ((dartNext unitCell)^[1] ucDart0) = ![0, -1] := by
    rw [iterate_ucDart_1]; exact ucFace1
  have e2 : dartFace ((dartNext unitCell)^[2] ucDart0) = ![-1, -1] := by
    rw [iterate_ucDart_2]; exact ucFace2
  have e3 : dartFace ((dartNext unitCell)^[3] ucDart0) = ![-1, 0] := by
    rw [iterate_ucDart_3]; exact ucFace3
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  interval_cases a <;> interval_cases b <;>
    simp only [e0, e1, e2, e3] at hab ⊢ <;>
    first
    | rfl
    | (exfalso; rw [funext_iff, Fin.forall_fin_two] at hab; simp at hab)


end Lattice
end StatMech
