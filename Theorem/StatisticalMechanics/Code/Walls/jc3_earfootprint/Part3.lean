/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Walls.jc_steplocal
import Theorem.StatisticalMechanics.Code.Walls.jc2_runframe.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc2_thickshelf.Part3
import Def.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem jc3_farDart_dir : jc3_farDart.dir = ![1, 0] := by
  unfold jc3_farDart; rw [mkDart_dir]


theorem jc3_farDart_avoidsOrigin :
    jc3_AvoidsEarFootprint (![0, 0] : Site 2) jc3_farDart := by
  
  have hdir : jc3_farDart.dir = ![1, 0] := jc3_farDart_dir
  constructor
  · 
    rw [jc_headTravel_eq, hdir]
    rw [jc3_mem_earFootprint]
    
    intro hcon
    have h0 : (jc3_farDart.head + (-rot90Fun (![1, 0] : Site 2))) 0 = 11 := by
      unfold jc3_farDart rot90Fun
      simp only [mkDart_head, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      norm_num
    rcases hcon with h | h | h | h | h <;>
      · rw [h] at h0
        revert h0
        simp only [Pi.add_apply, Matrix.cons_val_zero]
        norm_num
  · 
    rw [jc_tailTravel_eq, hdir]
    rw [jc3_mem_earFootprint]
    intro hcon
    have h0 : (jc3_farDart.tail + (-rot90Fun (![1, 0] : Site 2))) 0 = 10 := by
      unfold jc3_farDart rot90Fun
      simp only [mkDart_tail, Pi.add_apply, Pi.neg_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      norm_num
    rcases hcon with h | h | h | h | h <;>
      · rw [h] at h0
        revert h0
        simp only [Pi.add_apply, Matrix.cons_val_zero]
        norm_num


theorem jc3_farDart_step_eq (K : Set (Site 2)) :
    dartNext (K \ {(![0, 0] : Site 2)}) jc3_farDart = dartNext K jc3_farDart ∧
      turnZ (K \ {(![0, 0] : Site 2)}) jc3_farDart = turnZ K jc3_farDart :=
  jc3_step_eq_of_avoidsEarFootprint K (![0, 0] : Site 2) jc3_farDart jc3_farDart_avoidsOrigin


end Walls
end StatMech
