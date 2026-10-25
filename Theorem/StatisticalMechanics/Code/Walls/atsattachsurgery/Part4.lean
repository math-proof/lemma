/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
import Def.StatisticalMechanics.Code.Walls.atsattachsurgery.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ats_insert_domino_eq_tromino :
    insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino := by
  unfold ats_domino pc2_tromino
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto


theorem ats_domino_isConnectedCluster : IsConnectedCluster ats_domino := by
  refine ⟨by unfold ats_domino; rw [origin_eq_zerozero]; simp, ?_⟩
  intro x hx
  have hm : (![x 0, x 1] : Site 2) ∈ (↑ats_domino : Set (Site 2)) := by
    rw [show (![x 0, x 1] : Site 2) = x from by funext i; fin_cases i <;> rfl, Finset.mem_coe]
    exact hx
  unfold ats_domino at hm
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hm
  rw [origin_eq_zerozero, show x = ![x 0, x 1] from by funext i; fin_cases i <;> rfl]
  have m00 : (![(0:ℤ), 0] : Site 2) ∈ (↑ats_domino : Set (Site 2)) := by
    unfold ats_domino; simp
  have m10 : (![(1:ℤ), 0] : Site 2) ∈ (↑ats_domino : Set (Site 2)) := by
    unfold ats_domino; simp
  rcases hm with h | h
  · rw [h]
  · rw [h]
    refine SimpleGraph.Adj.reachable ⟨?_, m00, m10⟩
    have := latAdj_right 0 0; rwa [show (0:ℤ) + 1 = 1 from by ring] at this


theorem ats_c_notMem_domino : (![(0:ℤ), 1] : Site 2) ∉ ats_domino := by
  unfold ats_domino
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rw [site2_eq, site2_eq]; omega


theorem ats_support_tromino_subset :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).support ⊆ (pc2_tromFrame : Set (Site 2)) := by
  intro f hf
  have h := support_faceBoundaryGraph_subset (↑pc2_tromino : Set (Site 2)) hf
  rw [Set.mem_iUnion] at h
  obtain ⟨c, hc⟩ := h
  rw [Set.mem_iUnion] at hc
  obtain ⟨hcK, hfc⟩ := hc
  
  rw [Finset.mem_coe] at hcK
  have hcc : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
  rw [hcc, ← Finset.mem_coe, pc2_mem_tromino] at hcK
  
  rw [Finset.mem_coe] at hfc
  unfold cornerFaces at hfc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfc
  
  rw [Finset.mem_coe]
  unfold pc2_tromFrame
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hff : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  
  rcases hcK with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    (rcases hfc with hfe | hfe | hfe | hfe <;>
      (rw [hfe];
       rw [site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq, site2_eq];
       omega))


theorem ats_tromino_boundaryReachable :
    fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  fbc_boundaryReachable_of_faceBoundaryConnected ats_support_tromino_subset
    pc2_tromino_faceBoundaryConnected


theorem ats_attachStep_witness_tromino :
    (![(0:ℤ), 1] : Site 2) ∉ ats_domino ∧
      IsConnectedCluster ats_domino ∧
      insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧
      IsConnectedCluster pc2_tromino ∧
      fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) :=
  ⟨ats_c_notMem_domino, ats_domino_isConnectedCluster, ats_insert_domino_eq_tromino,
    pc2_tromino_isConnectedCluster, ats_tromino_boundaryReachable⟩


end Walls
end StatMech
