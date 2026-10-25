/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_latticeconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
open Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

variable {d : ℕ}


theorem kc_reach_axis_le (x : Site d) (j : Fin d) (a : ℤ) (n : ℕ) :
    (hypercubicLattice d).Reachable (Function.update x j a)
      (Function.update x j (a + (n : ℤ))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have step : (hypercubicLattice d).Adj (Function.update x j (a + (m : ℤ)))
        (Function.update x j (a + (m : ℤ) + 1)) := adj_update_succ x j (a + (m : ℤ))
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    have he : a + (((m : ℕ) + 1 : ℕ) : ℤ) = a + (m : ℤ) + 1 := by push_cast; ring
    rw [he]; exact step


theorem kc_reach_axis (x : Site d) (j : Fin d) (a b : ℤ) :
    (hypercubicLattice d).Reachable (Function.update x j a) (Function.update x j b) := by
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact kc_reach_axis_le x j a n
  · obtain ⟨n, rfl⟩ := Int.le.dest hab; exact (kc_reach_axis_le x j b n).symm


end Walls
end StatMech
