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
import Def.StatisticalMechanics.Code.Walls.earremovable.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ear_adj_leftCell (c : Site 2) : (hypercubicLattice 2).Adj c (ear_leftCell c) := by
  rw [ear_leftCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]

theorem ear_adj_downCell (c : Site 2) : (hypercubicLattice 2).Adj c (ear_downCell c) := by
  rw [ear_downCell, hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]

theorem ear_leftCell_ne_downCell (c : Site 2) : ear_leftCell c ≠ ear_downCell c := by
  rw [ear_leftCell, ear_downCell]; intro h
  have := congrFun h 0; simp [Pi.add_apply] at this


theorem ear_globalExtreme_neighbor_leftCell_or_downCell (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj c v) :
    v = ear_leftCell c ∨ v = ear_downCell c := by
  have h := ear_globalExtreme_neighbor_left_or_down K c v hc hv hadj.symm
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h


theorem ear_exists_neighbor_of_conn {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : c ∈ K) :
    ∃ v ∈ K, (hypercubicLattice 2).Adj c v := by
  classical
  by_contra hcon
  push Not at hcon
  
  have hcell : CellConnected (↑K : Set (Site 2)) := nbc_cellConnected_of_isConnectedCluster hconn
  obtain ⟨d, hdK, hdc⟩ : ∃ d ∈ K, d ≠ c := by
    by_contra h
    push Not at h
    
    have hsub : K ⊆ {c} := by
      intro x hx; rw [Finset.mem_singleton]; exact h x hx
    have := Finset.card_le_card hsub
    simp at this; omega
  have hcK : c ∈ (↑K : Set (Site 2)) := by exact_mod_cast hc
  have hdK' : d ∈ (↑K : Set (Site 2)) := by exact_mod_cast hdK
  
  have hr := hcell.preconnected ⟨c, hcK⟩ ⟨d, hdK'⟩
  obtain ⟨w⟩ := hr
  
  cases w with
  | nil => exact hdc rfl
  | @cons _ b _ hab _ =>
    have hab' : (hypercubicLattice 2).Adj c b.1 := by
      simpa only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype] using hab
    exact hcon b.1 (by exact_mod_cast b.2) hab'


theorem ear_globalExtreme_pendant_of_down_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hdown : ear_downCell c ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) c := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hc.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hc.mem, ear_leftCell c, ⟨?_, ear_adj_leftCell c⟩, ?_⟩
  · 
    rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c v hc hvK' hadj with
      h | h
    · rw [← h]; exact hvK'
    · exact absurd (h ▸ hvK') hdown
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c w hc hwK hwadj with
      h | h
    · exact h
    · exact absurd (h ▸ hwK) hdown


theorem ear_globalExtreme_pendant_of_left_nmem {K : Finset (Site 2)} (hcard : 2 ≤ K.card)
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hleft : ear_leftCell c ∉ (↑K : Set (Site 2))) :
    jc_IsPendantCell (↑K : Set (Site 2)) c := by
  classical
  obtain ⟨v, hvK, hadj⟩ := ear_exists_neighbor_of_conn hcard hconn (by exact_mod_cast hc.mem)
  have hvK' : v ∈ (↑K : Set (Site 2)) := by exact_mod_cast hvK
  refine ⟨hc.mem, ear_downCell c, ⟨?_, ear_adj_downCell c⟩, ?_⟩
  · rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c v hc hvK' hadj with
      h | h
    · exact absurd (h ▸ hvK') hleft
    · rw [← h]; exact hvK'
  · rintro w ⟨hwK, hwadj⟩
    rcases ear_globalExtreme_neighbor_leftCell_or_downCell (↑K : Set (Site 2)) c w hc hwK hwadj with
      h | h
    · exact absurd (h ▸ hwK) hleft
    · exact h


theorem ear_removable_of_pendant_ne_origin {K : Finset (Site 2)}
    (hconn : IsConnectedCluster K) {c : Site 2} (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
    (hcorigin : c ≠ origin 2) (hpend : jc_IsPendantCell (↑K : Set (Site 2)) c) :
    ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧
      CellConnected ((↑K : Set (Site 2)) \ {d}) := by
  refine ⟨c, by exact_mod_cast hc.mem, hcorigin,
    ear_globalExtreme_boundary (↑K : Set (Site 2)) c hc, ?_⟩
  exact jc_cellConnected_diff_of_pendant (↑K : Set (Site 2)) c
    (nbc_cellConnected_of_isConnectedCluster hconn) hpend


end Walls
end StatMech
