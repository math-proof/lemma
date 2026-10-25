/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc6_ivt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Def.StatisticalMechanics.Code.Walls.jc6_ivt
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc6_ivt_nonvacuous_middleRow :
    ∃ p ∈ jc6_vArc.support, p 1 = 1 := by
  apply jc6_walk_visits_row jc6_vArc 1
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; norm_num
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; norm_num


theorem jc6_ivt_nonvacuous_cannotHop :
    (5 : ℤ) < min ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) ∨
      max ((![0, 0] : Site 2) 1) ((![0, 2] : Site 2) 1) < (5 : ℤ) := by
  apply jc6_walk_cannot_hop jc6_vArc 5
  
  intro p hp
  
  simp only [jc6_vArc, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] <;> norm_num


end Walls
end StatMech
