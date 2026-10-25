/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Def.StatisticalMechanics.Code.Walls.earremovable.Part3
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ear_mem_vtromino (v : Site 2) :
    v ∈ ear_vtromino ↔ v = ![0, 0] ∨ v = ![-1, 0] ∨ v = ![0, -1] := by
  unfold ear_vtromino; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem ear_vt_v00 : (![0, 0] : Site 2) ∈ ear_vtromino := by rw [ear_mem_vtromino]; tauto

theorem ear_vt_vm10 : (![-1, 0] : Site 2) ∈ ear_vtromino := by rw [ear_mem_vtromino]; tauto

theorem ear_vt_v0m1 : (![0, -1] : Site 2) ∈ ear_vtromino := by rw [ear_mem_vtromino]; tauto


theorem ear_vtromino_globalExtreme : ear_IsGlobalExtreme ear_vtromino ![0, 0] := by
  refine ⟨ear_vt_v00, ?_⟩
  intro v hv
  rw [ear_mem_vtromino] at hv
  unfold ear_gKey
  rcases hv with h | h | h <;> subst h <;> rw [Prod.Lex.toLex_le_toLex] <;> simp


theorem ear_vtromino_two_neighbours :
    ear_leftCell (![0, 0] : Site 2) ∈ ear_vtromino ∧
      ear_downCell (![0, 0] : Site 2) ∈ ear_vtromino := by
  constructor
  · rw [ear_mem_vtromino, ear_leftCell]; right; left; funext i; fin_cases i <;> simp
  · rw [ear_mem_vtromino, ear_downCell]; right; right; funext i; fin_cases i <;> simp

theorem ear_vtd_vm10 : (![-1, 0] : Site 2) ∈ ear_vtromino \ {![0, 0]} := by
  refine ⟨ear_vt_vm10, ?_⟩
  simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 0; simp at this

theorem ear_vtd_v0m1 : (![0, -1] : Site 2) ∈ ear_vtromino \ {![0, 0]} := by
  refine ⟨ear_vt_v0m1, ?_⟩
  simp only [Set.mem_singleton_iff]; intro h; have := congrFun h 1; simp at this


theorem ear_vtromino_arm_isolated :
    ((hypercubicLattice 2).induce (ear_vtromino \ {![0, 0]})).neighborSet ⟨![-1, 0], ear_vtd_vm10⟩
      = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨w, hw⟩ hadj
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj, hypercubicLattice_adj,
    Fin.sum_univ_two] at hadj
  obtain ⟨hwK, hwne⟩ := hw
  rw [Set.mem_singleton_iff] at hwne
  rw [ear_mem_vtromino] at hwK
  rcases hwK with h | h | h <;> subst h
  · exact hwne rfl
  · simp at hadj
  · simp at hadj

theorem ear_vtromino_arm_ne :
    (⟨![-1, 0], ear_vtd_vm10⟩ : ↑(ear_vtromino \ {![0, 0]})) ≠ ⟨![0, -1], ear_vtd_v0m1⟩ := by
  intro h
  have := congrFun (congrArg Subtype.val h) 0
  norm_num at this


theorem ear_vtromino_extreme_cut : ¬ CellConnected (ear_vtromino \ {![0, 0]}) := by
  intro h
  have hreach := h.preconnected ⟨![-1, 0], ear_vtd_vm10⟩ ⟨![0, -1], ear_vtd_v0m1⟩
  exact not_reachable_of_neighborSet_left_eq_empty ear_vtromino_arm_ne
    ear_vtromino_arm_isolated hreach


end Walls
end StatMech
