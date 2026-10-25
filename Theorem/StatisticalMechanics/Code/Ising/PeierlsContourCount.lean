/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part4
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pcc_crossEdges_subset_biUnion (K : Finset (Site d)) (n : ℕ) :
    crossEdges (↑K) (bondFinsetTouch d n)
      ⊆ K.biUnion (fun v => (hypercubicLattice d).incidenceFinset v) := by
  intro e he
  have heB : e ∈ bondFinsetTouch d n := (Finset.mem_filter.mp he).1
  have hcr : crosses (↑K) e := (Finset.mem_filter.mp he).2
  rw [Finset.mem_biUnion]
  induction e with
  | h x y =>
    rw [crosses_mk] at hcr
    have hadj : (hypercubicLattice d).Adj x y := adj_of_mem_bondFinsetTouch (n := n) heB
    by_cases hx : x ∈ (↑K : Set (Site d))
    · exact ⟨x, hx, by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨hadj, Sym2.mem_mk_left x y⟩⟩
    · have hy : y ∈ (↑K : Set (Site d)) := by by_contra h; exact hx (hcr.mpr h)
      exact ⟨y, hy, by rw [SimpleGraph.mem_incidenceFinset]; exact ⟨hadj, Sym2.mem_mk_right x y⟩⟩


theorem pcc_contourLen_le_card_mul (K : Finset (Site d)) (n : ℕ) :
    contourLen (↑K) (bondFinsetTouch d n) ≤ 2 * d * K.card := by
  unfold contourLen
  calc (crossEdges (↑K) (bondFinsetTouch d n)).card
      ≤ (K.biUnion (fun v => (hypercubicLattice d).incidenceFinset v)).card :=
        Finset.card_le_card (pcc_crossEdges_subset_biUnion K n)
    _ ≤ ∑ v ∈ K, ((hypercubicLattice d).incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ K, (hypercubicLattice d).degree v :=
        Finset.sum_congr rfl (fun v _ => SimpleGraph.card_incidenceFinset_eq_degree _ v)
    _ ≤ ∑ _v ∈ K, 2 * d := Finset.sum_le_sum (fun v _ => degree_le d v)
    _ = K.card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * d * K.card := by ring


end Ising
end StatMech
