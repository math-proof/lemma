/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem latticeMinusBarrier_adj (S : Set (Site 2)) (x y : Site 2) :
    (latticeMinusBarrier S).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ ¬ bdEdge S s(x, y) := Iff.rfl


theorem latticeMinusBarrier_le (S : Set (Site 2)) :
    latticeMinusBarrier S ≤ hypercubicLattice 2 := fun _ _ h => h.1


theorem latticeMinusBarrier_sameSide (S : Set (Site 2)) {x y : Site 2}
    (w : (latticeMinusBarrier S).Walk x y) : (x ∈ S ↔ y ∈ S) := by
  classical
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hab p ih =>
    have hnb : ¬ bdEdge S s(a, b) := hab.2
    rw [bdEdge_mk] at hnb
    have hab_side : (a ∈ S ↔ b ∈ S) := by
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp_all
    exact hab_side.trans ih


theorem not_reachable_latticeMinusBarrier (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (latticeMinusBarrier S).Reachable x y := by
  rintro ⟨w⟩
  exact hy ((latticeMinusBarrier_sameSide S w).mp hx)


theorem faceBoundaryGraph_sharedPrimalEdge_bdEdge (S : Set (Site 2)) {f g : Site 2}
    (h : (faceBoundaryGraph S).Adj f g) : bdEdge S (sharedPrimalEdge f g) := h.2


theorem sharedPrimalEdge_isLatticeEdge {f g : Site 2}
    (_h : (hypercubicLattice 2).Adj f g) :
    ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q := by
  classical
  unfold sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0]
    exact ⟨_, _, rfl, by simp [hypercubicLattice_adj, Fin.sum_univ_two]⟩
  · rw [if_neg h0]
    exact ⟨_, _, rfl, by simp [hypercubicLattice_adj, Fin.sum_univ_two]⟩


theorem faceBoundaryWalk_edges_bdEdge (S : Set (Site 2)) {u v : Site 2}
    (c : (faceBoundaryGraph S).Walk u v) {f g : Site 2} (h : s(f, g) ∈ c.edges) :
    bdEdge S (sharedPrimalEdge f g) := by
  have hadj : (faceBoundaryGraph S).Adj f g := c.adj_of_mem_edges h
  exact faceBoundaryGraph_sharedPrimalEdge_bdEdge S hadj


variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem cluster_separated_from_exterior (o : Site 2) {z : Site 2}
    (hz : z ∉ cluster 2 ω o) :
    ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z :=
  not_reachable_latticeMinusBarrier (cluster 2 ω o) (self_mem_cluster ω o) hz


theorem origin_crossCount_odd (o : Site 2) {z : Site 2}
    (hz : z ∉ cluster 2 ω o) (w : (hypercubicLattice 2).Walk o z) :
    ¬ Even (crossCount (cluster 2 ω o) w) :=
  crossCount_odd_of_separated (cluster 2 ω o) (self_mem_cluster ω o) hz w


theorem cluster_enclosed_by_dualCircuit (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) ∧
      ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z := by
  refine ⟨exists_dualCircuit_of_finite_cluster o hfin w hz,
    cluster_separated_from_exterior o hz⟩


theorem cluster_enclosed_with_winding (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    {z : Site 2} (w : (hypercubicLattice 2).Walk o z) (hz : z ∉ cluster 2 ω o) :
    (∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω o)).Walk u u), c.IsCycle) ∧
      ¬ (latticeMinusBarrier (cluster 2 ω o)).Reachable o z ∧
      ∀ γ : (hypercubicLattice 2).Walk o z, ¬ Even (crossCount (cluster 2 ω o) γ) := by
  refine ⟨exists_dualCircuit_of_finite_cluster o hfin w hz,
    cluster_separated_from_exterior o hz, fun γ => origin_crossCount_odd o hz γ⟩

end Lattice
end StatMech
