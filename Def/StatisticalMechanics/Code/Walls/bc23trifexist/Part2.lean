/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc12core.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc23trifexist.Part2
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


def bc23_LatticeCorridorRouting (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
      (w₁ : (hypercubicLattice d).Walk a₁ b₁) (w₂ : (hypercubicLattice d).Walk a₂ b₂)
      (w₃ : (hypercubicLattice d).Walk a₃ b₃),
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃) ∧
      ((0 : Site d) ∉ w₁.support ∧ (0 : Site d) ∉ w₂.support ∧ (0 : Site d) ∉ w₃.support) ∧
      ((0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧
        (0 : Site d) ∉ cluster d ω b₃) ∧
      ((cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite) ∧
      ∃ S₁ S₂ S₃ : Set (Site d),
        (b₁ ∈ S₁ ∧ b₂ ∈ S₂ ∧ b₃ ∈ S₃) ∧
        (∀ u v, u ∈ S₁ →
          (openSubgraph d (removeSite 0 (forceOpenFinset
            (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₁) ∧
        (∀ u v, u ∈ S₂ →
          (openSubgraph d (removeSite 0 (forceOpenFinset
            (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₂) ∧
        (∀ u v, u ∈ S₃ →
          (openSubgraph d (removeSite 0 (forceOpenFinset
            (bc23_walkEdges w₁ ∪ bc23_walkEdges w₂ ∪ bc23_walkEdges w₃) ω))).Adj u v → v ∈ S₃) ∧
        (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)


end StatMech.Walls
