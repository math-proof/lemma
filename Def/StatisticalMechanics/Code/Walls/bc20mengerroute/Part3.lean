/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part2
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


noncomputable def bc20_walk_removeSite (ω : ConfigSpace (Sym2 (Site d))) {a x : Site d}
    (w : (openSubgraph d ω).Walk a x) (h0 : (0 : Site d) ∉ w.support) :
    (openSubgraph d (removeSite 0 ω)).Walk a x := by
  induction w with
  | nil => exact Walk.nil
  | @cons u v t hadj p ih =>
      rw [Walk.support_cons, List.mem_cons] at h0
      push Not at h0
      obtain ⟨hu0, hrest⟩ := h0
      have hv0 : v ≠ 0 := fun hv => hrest (hv ▸ p.start_mem_support)
      exact Walk.cons (bc20_edge_removeSite ω hadj (Ne.symm hu0) hv0) (ih hrest)


end StatMech.Walls
