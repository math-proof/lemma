/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Def.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem pc2_mem_tromino (p q : ℤ) :
    (![p, q] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) ↔
      (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by
  unfold pc2_tromino
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
  rw [site2_eq, site2_eq, site2_eq]


theorem pc2_origin_mem_tromino : origin 2 ∈ pc2_tromino := by
  unfold pc2_tromino; rw [origin_eq_zerozero]; simp


theorem pc2_tromino_isConnectedCluster : IsConnectedCluster pc2_tromino := by
  refine ⟨pc2_origin_mem_tromino, ?_⟩
  intro x hx
  have hm : (![x 0, x 1] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [show (![x 0, x 1] : Site 2) = x from by funext i; fin_cases i <;> rfl, Finset.mem_coe]
    exact hx
  have h00 : origin 2 ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [Finset.mem_coe]; exact pc2_origin_mem_tromino
  rw [origin_eq_zerozero]
  rw [show x = ![x 0, x 1] from by funext i; fin_cases i <;> rfl]
  rw [pc2_mem_tromino] at hm
  
  have h00' : (![(0:ℤ), 0] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [pc2_mem_tromino]; tauto
  have m10 : (![(1:ℤ), 0] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [pc2_mem_tromino]; tauto
  have m01 : (![(0:ℤ), 1] : Site 2) ∈ (↑pc2_tromino : Set (Site 2)) := by
    rw [pc2_mem_tromino]; tauto
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    refine SimpleGraph.Adj.reachable ⟨?_, h00', m10⟩
    have := latAdj_right 0 0; rwa [show (0:ℤ) + 1 = 1 from by ring] at this
  · rw [h1, h2]
    refine SimpleGraph.Adj.reachable ⟨?_, h00', m01⟩
    have := latAdj_top 0 0; rwa [show (0:ℤ) + 1 = 1 from by ring] at this


end Lattice
end StatMech
