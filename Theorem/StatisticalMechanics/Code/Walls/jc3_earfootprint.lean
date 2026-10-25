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
import Def.StatisticalMechanics.Code.Walls.jc3_earfootprint
open SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc3_mem_earFootprint (r x : Site 2) :
    x ∈ jc3_earFootprint r ↔
      x = r ∨ x = r + ![1, 0] ∨ x = r + ![(-1 : ℤ), 0] ∨ x = r + ![0, 1] ∨
        x = r + ![0, (-1 : ℤ)] := by
  unfold jc3_earFootprint
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]


theorem jc3_self_mem_earFootprint (r : Site 2) : r ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inl rfl


theorem jc3_right_mem_earFootprint (r : Site 2) : r + ![1, 0] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inl rfl)


theorem jc3_left_mem_earFootprint (r : Site 2) :
    r + ![(-1 : ℤ), 0] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inr (Or.inl rfl))


theorem jc3_up_mem_earFootprint (r : Site 2) : r + ![0, 1] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))


theorem jc3_down_mem_earFootprint (r : Site 2) :
    r + ![0, (-1 : ℤ)] ∈ jc3_earFootprint r := by
  rw [jc3_mem_earFootprint]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))


theorem jc3_earFootprint_finite (r : Site 2) : (jc3_earFootprint r).Finite := by
  unfold jc3_earFootprint
  exact Set.toFinite _


end Walls
end StatMech
