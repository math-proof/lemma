/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Percolation.DctDifferential.Part3
open MeasureTheory Function Set
open scoped NNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


@[simp]
theorem mem_boxCrossingEvent {n : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ boxCrossingEvent d n ↔ ∃ (x : Site d) (hx : x ∈ box d n), x ∈ vertexBoundary d n ∧
      ∃ (h0 : origin d ∈ box d n),
        ConnectedWithin d ω (box d n) ⟨origin d, h0⟩ ⟨x, hx⟩ :=
  Iff.rfl


theorem openSubgraphInduce_box_congr (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y)) :
    openSubgraphInduce d ω (box d n) = openSubgraphInduce d ω' (box d n) := by
  apply SimpleGraph.ext
  ext a b
  simp only [openSubgraphInduce_adj, openSubgraph_adj]
  rw [h a b a.2 b.2]


theorem boxCrossingEvent_congr (n : ℕ) {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ e ∈ (boxEdgeFinset d n : Set (Sym2 (Site d))), ω e = ω' e) :
    ω ∈ boxCrossingEvent d n ↔ ω' ∈ boxCrossingEvent d n := by
  have hcoord : ∀ x y : Site d, x ∈ box d n → y ∈ box d n → ω s(x, y) = ω' s(x, y) :=
    coord_of_agree n h
  have hG := openSubgraphInduce_box_congr n hcoord
  unfold boxCrossingEvent ConnectedWithin
  simp only [Set.mem_setOf_eq, hG]


theorem boxCrossingEvent_dependsOn (n : ℕ) :
    DependsOn ((boxCrossingEvent d n).indicator (fun _ => (1 : ℝ)))
      ((boxEdgeFinset d n : Set (Sym2 (Site d)))) := by
  intro ω ω' h
  have hiff := boxCrossingEvent_congr n (fun e he => h e he)
  by_cases hω : ω ∈ boxCrossingEvent d n
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]


theorem boxCrossingEvent_isIncreasing (n : ℕ) : IsIncreasing (boxCrossingEvent d n) := by
  intro a b hab ha
  obtain ⟨x, hx, hxb, h0, hconn⟩ := ha
  refine ⟨x, hx, hxb, h0, hconn.mono ?_⟩
  intro u v huv
  simp only [openSubgraphInduce_adj, openSubgraph_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  have := hab s(u, v)
  rw [huv.2] at this
  exact le_antisymm (Bool.le_true _) this


end Percolation
end StatMech
