/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part5
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem transDart_tail (w : Site 2) (e : Dart) : (transDart w e).tail = e.tail + w := rfl

@[simp] theorem transDart_dir (w : Site 2) (e : Dart) : (transDart w e).dir = e.dir := by
  rw [transDart, mkDart_dir]

@[simp] theorem transDart_head (w : Site 2) (e : Dart) : (transDart w e).head = e.head + w := by
  rw [transDart, mkDart_head, Dart.dir_def]; abel


theorem transDart_injective (w : Site 2) : Function.Injective (transDart w) := by
  intro a b h
  apply dart_eq_of_tail_dir
  · have := congrArg Dart.tail h; simp only [transDart_tail] at this; exact add_right_cancel this
  · have := congrArg Dart.dir h; simpa only [transDart_dir] using this


theorem transDart_boundary (K : Set (Site 2)) (w : Site 2) (e : Dart)
    (he : IsBoundaryDart K e) : IsBoundaryDart (transSet w K) (transDart w e) := by
  refine ⟨?_, ?_⟩
  · rw [transDart_tail, mem_transSet]; simpa using he.1
  · rw [transDart_head, mem_transSet]; simpa using he.2


theorem turnZ_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) :
    turnZ (transSet w K) (transDart w e) = turnZ K e := by
  classical
  unfold turnZ
  rw [transDart_head, transDart_dir, transDart_tail]
  have m1 : (e.head + w + -rot90Fun e.dir ∈ transSet w K) ↔ (e.head + -rot90Fun e.dir ∈ K) := by
    rw [mem_transSet]; congr! 1; abel
  have m2 : (e.tail + w + -rot90Fun e.dir ∈ transSet w K) ↔ (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [mem_transSet]; congr! 1; abel
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [if_pos (m1.mpr h1), if_pos h1]
  · rw [if_neg (fun hh => h1 (m1.mp hh)), if_neg h1]
    by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [if_pos (m2.mpr h2), if_pos h2]
    · rw [if_neg (fun hh => h2 (m2.mp hh)), if_neg h2]


theorem dartNext_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) :
    dartNext (transSet w K) (transDart w e) = transDart w (dartNext K e) := by
  classical
  have m1 : ((transDart w e).head + -rot90Fun (transDart w e).dir ∈ transSet w K) ↔
            (e.head + -rot90Fun e.dir ∈ K) := by
    rw [transDart_head, transDart_dir, mem_transSet]; congr! 1; abel
  have m2 : ((transDart w e).tail + -rot90Fun (transDart w e).dir ∈ transSet w K) ↔
            (e.tail + -rot90Fun e.dir ∈ K) := by
    rw [transDart_tail, transDart_dir, mem_transSet]; congr! 1; abel
  by_cases h1 : e.head + -rot90Fun e.dir ∈ K
  · rw [dartNext_of_front_mem (transSet w K) (transDart w e) (m1.mpr h1),
        dartNext_of_front_mem K e h1]
    apply dart_eq_of_tail_dir
    · simp only [mkDart_tail, transDart_tail, transDart_head, transDart_dir]; abel
    · simp only [mkDart_dir, transDart_dir]
  · by_cases h2 : e.tail + -rot90Fun e.dir ∈ K
    · rw [dartNext_of_side_mem (transSet w K) (transDart w e) (fun hh => h1 (m1.mp hh)) (m2.mpr h2),
          dartNext_of_side_mem K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, transDart_tail, transDart_dir]; abel
      · simp only [mkDart_dir, transDart_dir]
    · rw [dartNext_of_corner (transSet w K) (transDart w e) (fun hh => h1 (m1.mp hh))
            (fun hh => h2 (m2.mp hh)),
          dartNext_of_corner K e h1 h2]
      apply dart_eq_of_tail_dir
      · simp only [mkDart_tail, transDart_tail, transDart_dir]
      · simp only [mkDart_dir, transDart_dir]


theorem iterate_dartNext_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) (k : ℕ) :
    (dartNext (transSet w K))^[k] (transDart w e) = transDart w ((dartNext K)^[k] e) := by
  induction k generalizing e with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dartNext_trans, ih]


theorem rightCornerCount_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) (p : ℕ) :
    rightCornerCount (transSet w K) (transDart w e) p = rightCornerCount K e p := by
  classical
  unfold rightCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [iterate_dartNext_trans, turnZ_trans]


theorem leftCornerCount_trans (K : Set (Site 2)) (w : Site 2) (e : Dart) (p : ℕ) :
    leftCornerCount (transSet w K) (transDart w e) p = leftCornerCount K e p := by
  classical
  unfold leftCornerCount
  congr 2
  apply Finset.filter_congr
  intro i _
  rw [iterate_dartNext_trans, turnZ_trans]


end Lattice
end StatMech
