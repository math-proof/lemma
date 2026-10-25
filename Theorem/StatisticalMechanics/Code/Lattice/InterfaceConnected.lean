/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/InterfaceConnected.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dartNext_head_eq_iff_front_mem (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).head = e.head ↔ e.head + (-rot90Fun e.dir) ∈ K := by
  classical
  constructor
  · intro hhd
    by_contra hA
    by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · 
      have h := dartNext_straight_head K e hA hB
      rw [hhd] at h
      apply neg_rot90Fun_dartDir_ne_zero e
      have h' : e.head + (-rot90Fun e.dir) = e.head + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h'
    · 
      
      have h := dartNext_left_head K e hA hB
      rw [hhd] at h
      
      have hd : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
      rw [hd] at h
      have hdir : e.dir = -rot90Fun e.dir := add_left_cancel h
      exact neg_rot90Fun_dartDir_ne_dartDir e hdir.symm
  · intro hA
    exact (dartNext_front_head K e hA).1


theorem dartNext_rotates_head (K : Set (Site 2)) (e : Dart)
    (hA : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).head = e.head ∧ (dartNext K e).dir = rot90Fun e.dir :=
  dartNext_front_head K e hA


theorem dart_eq_of_common_head {e f : Dart}
    (hh : e.head = f.head) (hd : e.dir = f.dir) : e = f :=
  dart_eq_of_head_dir hh hd


theorem dartNext_dir_eq_rot90_of_front (K : Set (Site 2)) (e : Dart)
    (hA : e.head + (-rot90Fun e.dir) ∈ K) :
    (dartNext K e).dir = rot90Fun e.dir :=
  (dartNext_front_head K e hA).2


end Lattice
end StatMech
