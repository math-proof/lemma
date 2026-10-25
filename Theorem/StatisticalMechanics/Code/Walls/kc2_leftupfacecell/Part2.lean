/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_leftupfacecell.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Def.StatisticalMechanics.Code.Walls.kc2_leftupfacecell
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem kc2_witLeftDart_dir : kc2_witLeftDart.dir = ![-1, 0] := mkDart_dir _ _ _

@[simp] theorem kc2_witLeftDart_tail : kc2_witLeftDart.tail = ![1, 1] := mkDart_tail _ _ _


theorem kc2_witLeftDart_face : dartFace kc2_witLeftDart = ![0, 0] := by
  rw [kc2_leftDart_face _ kc2_witLeftDart_dir, kc2_witLeftDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc2_witLeftDart_head : kc2_witLeftDart.head = ![0, 1] := by
  rw [dart_head_eq, kc2_witLeftDart_tail, kc2_witLeftDart_dir]
  funext i; fin_cases i <;> simp


theorem kc2_witLeftDart_boundary_K1 :
    IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc2_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc2_witLeftDart_tail]
  · rw [Set.mem_singleton_iff, kc2_witLeftDart_head]; intro h
    have := congrFun h 0; simp at this


theorem kc2_witLeftDart_boundary_K2 :
    IsBoundaryDart ({![0, 0], ![1, 1]} : Set (Site 2)) kc2_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [kc2_witLeftDart_tail]; right; rfl
  · rw [kc2_witLeftDart_head]; intro h
    rcases h with h | h
    · have := congrFun h 1; simp at this
    · rw [Set.mem_singleton_iff] at h; have := congrFun h 0; simp at this


theorem kc2_witLeftDart_P00_notin_K1 :
    npd_P00 (dartFace kc2_witLeftDart) ∉ ({![1, 1]} : Set (Site 2)) := by
  rw [kc2_P00_eq_self, kc2_witLeftDart_face, Set.mem_singleton_iff]
  intro h; have := congrFun h 0; simp at this


theorem kc2_witLeftDart_P00_in_K2 :
    npd_P00 (dartFace kc2_witLeftDart) ∈ ({![0, 0], ![1, 1]} : Set (Site 2)) := by
  rw [kc2_P00_eq_self, kc2_witLeftDart_face]; left; rfl


theorem kc2_face_membership_not_pinned :
    ∃ (e : Dart) (K₁ K₂ : Set (Site 2)),
      IsBoundaryDart K₁ e ∧ IsBoundaryDart K₂ e ∧
      npd_P00 (dartFace e) ∉ K₁ ∧ npd_P00 (dartFace e) ∈ K₂ :=
  ⟨kc2_witLeftDart, {![1, 1]}, {![0, 0], ![1, 1]},
    kc2_witLeftDart_boundary_K1, kc2_witLeftDart_boundary_K2,
    kc2_witLeftDart_P00_notin_K1, kc2_witLeftDart_P00_in_K2⟩

end Walls
end StatMech
