/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases.Part3
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzEar.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnetEar
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzClose.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

@[simp] theorem uc_rotDart_tail (e : Dart) : (uc_rotDart e).tail = rot90Fun e.tail := rfl

@[simp] theorem uc_rotDart_dir (e : Dart) : (uc_rotDart e).dir = rot90Fun e.dir := by
  rw [uc_rotDart, mkDart_dir]

@[simp] theorem uc_rotDart_head (e : Dart) : (uc_rotDart e).head = rot90Fun e.head := by
  rw [uc_rotDart, mkDart_head, Dart.dir_def, sub_eq_add_neg, uc_rot90Fun_add, rot90Fun_neg]; abel


theorem uc_rotDart_injective : Function.Injective uc_rotDart := by
  intro a b h
  apply dart_eq_of_tail_dir
  · exact rot90Fun_injective (by have := congrArg Dart.tail h; simpa only [uc_rotDart_tail] using this)
  · exact rot90Fun_injective (by have := congrArg Dart.dir h; simpa only [uc_rotDart_dir] using this)


theorem uc_turnZ_rot (K : Set (Site 2)) (e : Dart) :
    turnZ (uc_rotSet K) (uc_rotDart e) = turnZ K e := by
  classical
  unfold turnZ
  rw [uc_rotDart_head, uc_rotDart_dir, uc_rotDart_tail]
  have m1 : (rot90Fun e.head + -rot90Fun (rot90Fun e.dir) ∈ uc_rotSet K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [show rot90Fun e.head + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.head + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  have m2 : (rot90Fun e.tail + -rot90Fun (rot90Fun e.dir) ∈ uc_rotSet K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [show rot90Fun e.tail + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.tail + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [if_pos (m1.mpr h1), if_pos h1]
  · rw [if_neg (fun hh => h1 (m1.mp hh)), if_neg h1]
    by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [if_pos (m2.mpr h2), if_pos h2]
    · rw [if_neg (fun hh => h2 (m2.mp hh)), if_neg h2]


theorem uc_dartNext_rot (K : Set (Site 2)) (e : Dart) :
    dartNext (uc_rotSet K) (uc_rotDart e) = uc_rotDart (dartNext K e) := by
  classical
  have m1 : ((uc_rotDart e).head + -rot90Fun (uc_rotDart e).dir ∈ uc_rotSet K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [uc_rotDart_head, uc_rotDart_dir,
        show rot90Fun e.head + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.head + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  have m2 : ((uc_rotDart e).tail + -rot90Fun (uc_rotDart e).dir ∈ uc_rotSet K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [uc_rotDart_tail, uc_rotDart_dir,
        show rot90Fun e.tail + -rot90Fun (rot90Fun e.dir)
        = rot90Fun (e.tail + -rot90Fun e.dir) by rw [uc_rot90Fun_add, rot90Fun_neg]]
    exact uc_rotSet_mem_iff K _
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [dartNext_of_front_mem (uc_rotSet K) (uc_rotDart e) (m1.mpr h1),
        dartNext_of_front_mem K e h1]
    apply dart_eq_of_tail_dir
    · simp only [mkDart_tail, uc_rotDart_head, uc_rotDart_dir, uc_rotDart_tail]
      rw [uc_rot90Fun_add, rot90Fun_neg]
    · simp only [mkDart_dir, uc_rotDart_dir]
  · by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [dartNext_of_side_mem (uc_rotSet K) (uc_rotDart e) (fun hh => h1 (m1.mp hh)) (m2.mpr h2),
          dartNext_of_side_mem K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, uc_rotDart_tail, uc_rotDart_dir]
        rw [uc_rot90Fun_add, rot90Fun_neg]
      · simp only [mkDart_dir, uc_rotDart_dir]
    · rw [dartNext_of_corner (uc_rotSet K) (uc_rotDart e) (fun hh => h1 (m1.mp hh))
            (fun hh => h2 (m2.mp hh)),
          dartNext_of_corner K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, uc_rotDart_tail]
      · simp only [mkDart_dir, uc_rotDart_dir]; rw [rot90Fun_neg]


theorem uc_iterate_dartNext_rot (K : Set (Site 2)) (e : Dart) (k : ℕ) :
    (dartNext (uc_rotSet K))^[k] (uc_rotDart e) = uc_rotDart ((dartNext K)^[k] e) := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, uc_dartNext_rot, ih]


theorem uc_rotDart_boundary (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    IsBoundaryDart (uc_rotSet K) (uc_rotDart e) := by
  refine ⟨?_, ?_⟩
  · rw [uc_rotDart_tail, uc_rotSet_mem_iff]; exact he.1
  · rw [uc_rotDart_head, uc_rotSet_mem_iff]; exact he.2


theorem uc_rightCornerCount_rot (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    rightCornerCount (uc_rotSet K) (uc_rotDart e) p = rightCornerCount K e p := by
  classical
  unfold rightCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [uc_iterate_dartNext_rot, uc_turnZ_rot]


theorem uc_leftCornerCount_rot (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    leftCornerCount (uc_rotSet K) (uc_rotDart e) p = leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [uc_iterate_dartNext_rot, uc_turnZ_rot]


end Lattice
end StatMech
