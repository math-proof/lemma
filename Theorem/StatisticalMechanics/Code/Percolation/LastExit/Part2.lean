/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.LastExit
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


theorem boundaryOpen_dependsOn (C : Set (Site d)) (x y : Site d) :
    DependsOn ({ω | boundaryOpen d C x y ω}.indicator (fun _ => (1 : ℝ)))
      ({s(x, y)} : Set (Sym2 (Site d))) := by
  intro ω ω' h
  have hedge : ω s(x, y) = ω' s(x, y) := h s(x, y) rfl
  have hiff : (ω ∈ {ω | boundaryOpen d C x y ω}) ↔ (ω' ∈ {ω | boundaryOpen d C x y ω}) := by
    simp only [Set.mem_setOf_eq, boundaryOpen, IsOpenEdge, hedge]
  by_cases hmem : ω ∈ {ω | boundaryOpen d C x y ω}
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun hc => hmem (hiff.mpr hc))]


theorem crossingEvent_lastExit_subset (S : Finset (Site d))
    (hoS : origin d ∈ (S : Set (Site d))) (n : ℕ)
    (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
    crossingEvent d n ⊆
      ⋃ (C : Set (Site d)), ⋃ (x : Site d), ⋃ (y : Site d),
        (clusterEvent d (S : Set (Site d)) (origin d) C
          ∩ {ω | boundaryOpen d C x y ω}
          ∩ {ω | offClusterCrossing d C y n ω}) := by
  intro ω hω
  obtain ⟨v, hconn, hv⟩ := hω
  set C := clusterWithin d ω (S : Set (Site d)) (origin d) with hC
  have hoC : origin d ∈ C := ⟨hoS, hoS, connectedWithin_refl ω _ ⟨origin d, hoS⟩⟩
  have hCsub : C ⊆ (S : Set (Site d)) := fun z hz => hz.1
  have hvC : v ∉ C := fun hvc => hv (hSbox (hCsub hvc))
  obtain ⟨x, y, hx, hy, hopen, hwithin⟩ := lattice_lastExit ω C (origin d) v hoC hvC hconn
  simp only [Set.mem_iUnion]
  exact ⟨C, x, y, ⟨⟨rfl, ⟨hx, hy, hopen⟩⟩, ⟨v, hv, hy, hvC, hwithin⟩⟩⟩

end Percolation
end StatMech
