/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc12core.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


theorem bc23_corridor_of_walk (G : Finset (Sym2 (Site d))) {a b : Site d}
    (w : (hypercubicLattice d).Walk a b)
    (hedges : ∀ e ∈ w.edges, e ∈ G)
    (h0 : (0 : Site d) ∉ w.support) :
    Relation.ReflTransGen (CorridorStep G) a b := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u v t hadj p ih =>
      rw [Walk.support_cons, List.mem_cons] at h0
      push Not at h0
      obtain ⟨hu0, hrest⟩ := h0
      have hv0 : v ≠ 0 := fun hv => hrest (hv ▸ p.start_mem_support)
      
      have hmemG : s(u, v) ∈ G := hedges s(u, v) (by rw [Walk.edges_cons]; exact List.mem_cons_self ..)
      
      have hne0 : (0 : Site d) ∉ s(u, v) := by
        rw [Sym2.mem_iff]; push Not
        exact ⟨fun h => hu0 h, fun h => hv0 h.symm⟩
      
      have hstep : CorridorStep G u v := ⟨hadj, hmemG, hne0⟩
      
      have htail : Relation.ReflTransGen (CorridorStep G) v t := by
        apply ih
        · intro e he; exact hedges e (by rw [Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
        · exact hrest
      exact Relation.ReflTransGen.head hstep htail


end StatMech.Walls
