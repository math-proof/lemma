/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExteriorConnected.Part3
import Def.StatisticalMechanics.Code.Walls.kc3_downfaceheadout
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc3_downDart_dir : kc3_downDart.dir = ![0, -1] := by
  rw [kc3_downDart, mkDart_dir]


theorem kc3_downDart_isBoundary : IsBoundaryDart kc3_upperHalf kc3_downDart := by
  constructor
  · 
    show kc3_downDart.tail ∈ kc3_upperHalf
    rw [kc3_downDart, mkDart_tail]
    change (0 : ℤ) ≤ (0 : Site 2) 1
    simp
  · 
    show kc3_downDart.head ∉ kc3_upperHalf
    have hhead : kc3_downDart.head 1 = -1 := by
      rw [dart_head_eq, kc3_downDart_dir, kc3_downDart, mkDart_tail]
      simp [Pi.add_apply]
    intro h
    simp only [kc3_upperHalf, Set.mem_setOf_eq] at h
    rw [hhead] at h
    norm_num at h


theorem kc3_downDart_face_notMem :
    dartFace kc3_downDart ∉ kc3_upperHalf :=
  kc3_dartFace_down_notMem kc3_downDart_isBoundary kc3_downDart_dir

end Walls
end StatMech
