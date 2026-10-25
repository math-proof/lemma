/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_raydisjoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Theorem.StatisticalMechanics.Code.Walls.bkm_dccthreeaxes
import Theorem.StatisticalMechanics.Code.Probability.MengerSplice.Part2
open Set SimpleGraph SimpleGraph.Walk
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc3_corridorWalk (j : Fin d) (L : ℕ) :
    (hypercubicLattice d).Walk (hrHD_rayPt j 0) (hrHD_rayPt j (L : ℤ)) := by
  induction L with
  | zero => exact SimpleGraph.Walk.nil
  | succ p ih =>
      refine ih.concat ?_
      have h := hrHD_adj_rayPt j (p : ℤ)
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [he] at h
      exact h


end StatMech.Walls
