/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_upleftfacecell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Walls.kc3_upleftfacecell.Part2
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem kc3_ul_witLeftDart_dir : kc3_ul_witLeftDart.dir = ![-1, 0] := mkDart_dir _ _ _

@[simp] theorem kc3_ul_witLeftDart_tail : kc3_ul_witLeftDart.tail = ![1, 1] := mkDart_tail _ _ _


theorem kc3_ul_witLeftDart_face : dartFace kc3_ul_witLeftDart = ![0, 0] := by
  rw [kc3_leftDart_face _ kc3_ul_witLeftDart_dir, kc3_ul_witLeftDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc3_ul_witLeftDart_head : kc3_ul_witLeftDart.head = ![0, 1] := by
  rw [dart_head_eq, kc3_ul_witLeftDart_tail, kc3_ul_witLeftDart_dir]
  funext i; fin_cases i <;> simp


theorem kc3_ul_witLeftDart_boundary_K1 :
    IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc3_ul_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc3_ul_witLeftDart_tail]
  · rw [Set.mem_singleton_iff, kc3_ul_witLeftDart_head]; intro h
    have := congrFun h 0; simp at this


theorem kc3_ul_witLeftDart_boundary_K2 :
    IsBoundaryDart ({![0, 0], ![1, 1]} : Set (Site 2)) kc3_ul_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [kc3_ul_witLeftDart_tail]; right; rfl
  · rw [kc3_ul_witLeftDart_head]; intro h
    rcases h with h | h
    · have := congrFun h 1; simp at this
    · rw [Set.mem_singleton_iff] at h; have := congrFun h 0; simp at this


theorem kc3_ul_witLeftDart_face_notin_K1 :
    dartFace kc3_ul_witLeftDart ∉ ({![1, 1]} : Set (Site 2)) := by
  rw [kc3_ul_witLeftDart_face, Set.mem_singleton_iff]
  intro h; have := congrFun h 0; simp at this


theorem kc3_ul_witLeftDart_face_in_K2 :
    dartFace kc3_ul_witLeftDart ∈ ({![0, 0], ![1, 1]} : Set (Site 2)) := by
  rw [kc3_ul_witLeftDart_face]; left; rfl


theorem kc3_face_membership_unpinned_up :
    ∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![0, 1] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂ :=
  ⟨kc3_ul_witUpDart, {![1, 0]}, {![0, 0], ![1, 0]}, kc3_ul_witUpDart_dir,
    kc3_ul_witUpDart_boundary_K1, kc3_ul_witUpDart_boundary_K2,
    kc3_ul_witUpDart_face_notin_K1, kc3_ul_witUpDart_face_in_K2⟩


theorem kc3_face_membership_unpinned_left :
    ∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![-1, 0] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂ :=
  ⟨kc3_ul_witLeftDart, {![1, 1]}, {![0, 0], ![1, 1]}, kc3_ul_witLeftDart_dir,
    kc3_ul_witLeftDart_boundary_K1, kc3_ul_witLeftDart_boundary_K2,
    kc3_ul_witLeftDart_face_notin_K1, kc3_ul_witLeftDart_face_in_K2⟩


theorem kc3_face_membership_unpinned :
    (∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![0, 1] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂)
    ∧
    (∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      e.dir = ![-1, 0] ∧ IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      dartFace e ∉ K₁ ∧ dartFace e ∈ K₂) :=
  ⟨kc3_face_membership_unpinned_up, kc3_face_membership_unpinned_left⟩

end Walls
end StatMech
