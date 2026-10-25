/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_tailinK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Def.StatisticalMechanics.Code.Walls.kc3_tailinK.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem kc3_witLeftDart_dir : kc3_witLeftDart.dir = ![-1, 0] := mkDart_dir _ _ _

@[simp] theorem kc3_witLeftDart_tail : kc3_witLeftDart.tail = ![1, 1] := mkDart_tail _ _ _


theorem kc3_witLeftDart_face : dartFace kc3_witLeftDart = ![0, 0] := by
  rw [kc3_left_face_SW _ kc3_witLeftDart_dir, kc3_witLeftDart_tail]
  funext i; fin_cases i <;> norm_num


theorem kc3_witLeftDart_head : kc3_witLeftDart.head = ![0, 1] := by
  rw [dart_head_eq, kc3_witLeftDart_tail, kc3_witLeftDart_dir]
  funext i; fin_cases i <;> simp


theorem kc3_witLeftDart_boundary :
    IsBoundaryDart ({![1, 1]} : Set (Site 2)) kc3_witLeftDart := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_singleton_iff, kc3_witLeftDart_tail]
  · rw [Set.mem_singleton_iff, kc3_witLeftDart_head]; intro h
    have := congrFun h 0; simp at this


theorem kc3_node_nonvacuous :
    kc3_witLeftDart.tail ∈ ({![1, 1]} : Set (Site 2)) ∧
      kc3_IsCellCorner (dartFace kc3_witLeftDart) kc3_witLeftDart.tail ∧
      (kc3_witLeftDart.dir = ![-1, 0] →
        dartFace kc3_witLeftDart =
          ![kc3_witLeftDart.tail 0 - 1, kc3_witLeftDart.tail 1 - 1] ∧
        kc3_witLeftDart.tail = npd_P11 (dartFace kc3_witLeftDart) ∧
        npd_P11 (dartFace kc3_witLeftDart) ∈ ({![1, 1]} : Set (Site 2))) :=
  kc3_tailInK_node kc3_witLeftDart_boundary

end Walls
end StatMech
