/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.bpt2corridors
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bpt2_closeI_le (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) :
    bpt2_closeI I ω ≤ ω := by
  intro e; unfold bpt2_closeI; by_cases h : e ∈ I <;> simp [h]


theorem bpt2_removeSite_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (z : Site 2) : removeSite z ω ≤ removeSite z ω' := by
  intro e
  by_cases hz : z ∈ e
  · simp [removeSite, hz]
  · simp only [removeSite, hz, if_false]; exact h e


theorem bpt2_closeI_forceOpen (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2))) :
    bpt2_closeI I (forceOpenFinset I ω) = bpt2_closeI I ω := by
  funext e
  unfold bpt2_closeI
  by_cases h : e ∈ I
  · simp [h]
  · simp [h]


theorem bpt2_openEdge_data (ω : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (h : IsOpenEdge 2 (removeSite 0 ω) u v) :
    (0 : Site 2) ∉ s(u, v) ∧ (hypercubicLattice 2).Adj u v ∧ ω s(u, v) = true := by
  obtain ⟨hadj, hval⟩ := h
  by_cases h0 : (0 : Site 2) ∈ s(u, v)
  · rw [removeSite_apply_of_mem h0] at hval; exact absurd hval (by simp)
  · rw [removeSite_apply_of_notMem h0] at hval; exact ⟨h0, hadj, hval⟩


theorem bpt2_closed_combined (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2)))
    {S : Set (Site 2)}
    (hIresp : ∀ u v : Site 2, s(u, v) ∈ I → u ∈ S → v ∈ S)
    (hSclosed : ∀ u v : Site 2, u ∈ S →
      IsOpenEdge 2 (removeSite 0 (bpt2_closeI I ω)) u v → v ∈ S) :
    ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 (removeSite 0 ω) x y → y ∈ S := by
  intro x y hx hop
  obtain ⟨h0, hadj, hval⟩ := bpt2_openEdge_data ω hop
  by_cases hI : s(x, y) ∈ I
  · exact hIresp x y hI hx
  · refine hSclosed x y hx ⟨hadj, ?_⟩
    rw [removeSite_apply_of_notMem h0]
    unfold bpt2_closeI
    rw [if_neg hI]; exact hval


theorem bpt2_walk_invariant (ω : ConfigSpace (Sym2 (Site 2))) {S : Set (Site 2)}
    (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 (removeSite 0 ω) x y → y ∈ S)
    {x y : Site 2} (w : (openSubgraph 2 (removeSite 0 ω)).Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih => exact ih (hclosed a b hx hab)


theorem bpt2_cluster_confined (I : Finset (Sym2 (Site 2))) (ω : ConfigSpace (Sym2 (Site 2)))
    {a : Site 2} {S : Set (Site 2)} (ha : a ∈ S)
    (hIresp : ∀ u v : Site 2, s(u, v) ∈ I → u ∈ S → v ∈ S)
    (hSclosed : ∀ u v : Site 2, u ∈ S →
      IsOpenEdge 2 (removeSite 0 (bpt2_closeI I ω)) u v → v ∈ S) :
    cluster 2 (removeSite 0 ω) a ⊆ S := by
  intro y hy
  obtain ⟨w⟩ := (hy : (openSubgraph 2 (removeSite 0 ω)).Reachable a y)
  exact bpt2_walk_invariant ω (bpt2_closed_combined I ω hIresp hSclosed) w ha


end StatMech.Walls
