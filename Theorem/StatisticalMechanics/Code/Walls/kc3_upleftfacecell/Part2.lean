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
import Def.StatisticalMechanics.Code.Walls.kc3_upleftfacecell
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem kc3_ul_witUpDart_dir : kc3_ul_witUpDart.dir = ![0, 1] := mkDart_dir _ _ _

@[simp] theorem kc3_ul_witUpDart_tail : kc3_ul_witUpDart.tail = ![1, 0] := mkDart_tail _ _ _


theorem kc3_ul_witUpDart_face : dartFace kc3_ul_witUpDart = ![0, 0] := by
  rw [kc3_upDart_face _ kc3_ul_witUpDart_dir, kc3_ul_witUpDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc3_ul_witUpDart_head : kc3_ul_witUpDart.head = ![1, 1] := by
  rw [dart_head_eq, kc3_ul_witUpDart_tail, kc3_ul_witUpDart_dir]
  funext i; fin_cases i <;> simp


theorem kc3_ul_witUpDart_boundary_K1 :
    IsBoundaryDart ({![1, 0]} : Set (Site 2)) kc3_ul_witUpDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc3_ul_witUpDart_tail]
  · rw [Set.mem_singleton_iff, kc3_ul_witUpDart_head]; intro h
    have := congrFun h 1; simp at this


theorem kc3_ul_witUpDart_boundary_K2 :
    IsBoundaryDart ({![0, 0], ![1, 0]} : Set (Site 2)) kc3_ul_witUpDart := by
  refine ⟨?_, ?_⟩
  · rw [kc3_ul_witUpDart_tail]; right; rfl
  · rw [kc3_ul_witUpDart_head]; intro h
    rcases h with h | h
    · have := congrFun h 1; simp at this
    · rw [Set.mem_singleton_iff] at h; have := congrFun h 1; simp at this


theorem kc3_ul_witUpDart_face_notin_K1 :
    dartFace kc3_ul_witUpDart ∉ ({![1, 0]} : Set (Site 2)) := by
  rw [kc3_ul_witUpDart_face, Set.mem_singleton_iff]
  intro h; have := congrFun h 0; simp at this


theorem kc3_ul_witUpDart_face_in_K2 :
    dartFace kc3_ul_witUpDart ∈ ({![0, 0], ![1, 0]} : Set (Site 2)) := by
  rw [kc3_ul_witUpDart_face]; left; rfl


end Walls
end StatMech
