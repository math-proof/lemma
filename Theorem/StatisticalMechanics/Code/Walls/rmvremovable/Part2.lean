/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.earremovable.Part5
import Def.StatisticalMechanics.Code.Walls.rmvremovable
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem rmv_mem_block (v : Site 2) :
    v ∈ rmv_block ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, 1] := by
  unfold rmv_block; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]


theorem rmv_block_globalExtreme : ear_IsGlobalExtreme rmv_block ![1, 1] := by
  refine ⟨by rw [rmv_mem_block]; tauto, ?_⟩
  intro v hv
  rw [rmv_mem_block] at hv
  unfold ear_gKey
  rcases hv with h | h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem rmv_block_diag_mem : (![1, 1] : Site 2) + ![-1, -1] ∈ rmv_block := by
  rw [rmv_mem_block]
  left; funext i; fin_cases i <;> simp [Pi.add_apply]


theorem rmv_block_cellConnected : CellConnected rmv_block := by
  classical
  rw [CellConnected, SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], by rw [rmv_mem_block]; tauto⟩⟩⟩
  intro u v
  
  have h00 : (![0, 0] : Site 2) ∈ rmv_block := by rw [rmv_mem_block]; tauto
  have anchor : ∀ t : ↥rmv_block,
      ((hypercubicLattice 2).induce rmv_block).Reachable ⟨![0, 0], h00⟩ t := by
    rintro ⟨t, ht⟩
    rw [rmv_mem_block] at ht
    rcases ht with h | h | h | h <;> subst h
    · exact Reachable.refl _
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
    · refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
    · 
      have h1 : ((hypercubicLattice 2).induce rmv_block).Adj
          ⟨![0, 0], by rw [rmv_mem_block]; tauto⟩ ⟨![1, 0], by rw [rmv_mem_block]; tauto⟩ := by
        rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
      have h2 : ((hypercubicLattice 2).induce rmv_block).Adj
          ⟨![1, 0], by rw [rmv_mem_block]; tauto⟩ ⟨![1, 1], by rw [rmv_mem_block]; tauto⟩ := by
        rw [SimpleGraph.induce_adj, hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
      exact h1.reachable.trans h2.reachable
  exact (anchor u).symm.trans (anchor v)


theorem rmv_block_removable : CellConnected (rmv_block \ {![1, 1]}) :=
  rmv_extreme_diag_noncut rmv_block_cellConnected rmv_block_globalExtreme rmv_block_diag_mem


theorem rmv_tromino_nonvacuous :
    ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧
      (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) :=
  ear_tromino_nonvacuous


theorem rmv_vtromino_reflex_residue :
    (![0, 0] : Site 2) + ![-1, -1] ∉ ear_vtromino ∧
      ¬ CellConnected (ear_vtromino \ {![0, 0]}) := by
  refine ⟨?_, ear_vtromino_extreme_cut⟩
  rw [ear_mem_vtromino]
  push Not
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  · have := congrFun h 0; norm_num [Pi.add_apply] at this
  · have := congrFun h 1; norm_num [Pi.add_apply] at this
  · have := congrFun h 0; norm_num [Pi.add_apply] at this


end Walls
end StatMech
