/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/nbcnoncut.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Def.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem nbc_atc_of_boundaryNonCut (h : nbc_BoundaryNonCutExists) : atc_HasRemovableConnCell := by
  intro K hcard hconn
  obtain ⟨c, hcK, hcorigin, hbdry, hcell⟩ := h K hcard hconn
  exact ⟨c, hcK, hcorigin, hbdry, nbc_isConnectedCluster_erase hconn.1 hcorigin hcell⟩


theorem nbc_fbc_hasRemovableCell_of_boundaryNonCut (h : nbc_BoundaryNonCutExists) :
    fbc_HasRemovableCell :=
  atc_hasRemovableCell_of_conn (nbc_atc_of_boundaryNonCut h)


theorem nbc_pendant_boundary {K : Finset (Site 2)} {c : Site 2}
    (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
    ∃ n ∉ K, (hypercubicLattice 2).Adj c n := by
  classical
  obtain ⟨hc, u, ⟨huK, hadj⟩, huniq⟩ := hpend
  
  set n1 := c + ![1, 0] with hn1
  set n2 := c + ![-1, 0] with hn2
  set n3 := c + ![0, 1] with hn3
  set n4 := c + ![0, -1] with hn4
  have hadj1 : (hypercubicLattice 2).Adj c n1 := by
    rw [hn1, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]
  have hadj2 : (hypercubicLattice 2).Adj c n2 := by
    rw [hn2, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]
  have hadj3 : (hypercubicLattice 2).Adj c n3 := by
    rw [hn3, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]
  
  have hne12 : n1 ≠ n2 := by
    rw [hn1, hn2]; intro h; have := congrFun h 0; simp [Pi.add_apply] at this
  have hne13 : n1 ≠ n3 := by
    rw [hn1, hn3]; intro h; have := congrFun h 0; simp [Pi.add_apply] at this
  have hne23 : n2 ≠ n3 := by
    rw [hn2, hn3]; intro h; have := congrFun h 0; simp [Pi.add_apply] at this
  
  by_contra hcon
  push Not at hcon
  
  have h1 : n1 ∈ K := by by_contra h; exact hcon n1 h hadj1
  have h2 : n2 ∈ K := by by_contra h; exact hcon n2 h hadj2
  have h3 : n3 ∈ K := by by_contra h; exact hcon n3 h hadj3
  
  have e1 : n1 = u := huniq n1 ⟨by exact_mod_cast h1, hadj1⟩
  have e2 : n2 = u := huniq n2 ⟨by exact_mod_cast h2, hadj2⟩
  have e3 : n3 = u := huniq n3 ⟨by exact_mod_cast h3, hadj3⟩
  exact hne12 (e1.trans e2.symm)


theorem nbc_boundaryNonCut_of_pendant {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {c : Site 2} (hcorigin : c ≠ origin 2)
    (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
    ∃ c ∈ K, c ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {c}) := by
  refine ⟨c, by exact_mod_cast hpend.1, hcorigin, nbc_pendant_boundary hpend, ?_⟩
  exact jc_cellConnected_diff_of_pendant (↑K : Set (Site 2)) c
    (nbc_cellConnected_of_isConnectedCluster hconn) hpend


theorem nbc_tromino_pendant_10 : jc_IsPendantCell (↑pc2_tromino : Set (Site 2)) ![1, 0] := by
  classical
  refine ⟨?_, ![0, 0], ⟨?_, ?_⟩, ?_⟩
  · rw [pc2_mem_tromino]; tauto
  · rw [pc2_mem_tromino]; tauto
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rintro w ⟨hwK, hadj⟩
    unfold pc2_tromino at hwK
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
      Set.mem_singleton_iff] at hwK
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    
    rcases hwK with h | h | h <;> subst h <;> revert hadj <;> decide


theorem nbc_tromino_nonvacuous :
    ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧
      (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧
      CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
  have hne : (![1, 0] : Site 2) ≠ origin 2 := by
    rw [origin_eq_zerozero]; intro h; have := congrFun h 0; simp at this
  exact nbc_boundaryNonCut_of_pendant pc2_tromino_isConnectedCluster hne nbc_tromino_pendant_10

end Walls
end StatMech
