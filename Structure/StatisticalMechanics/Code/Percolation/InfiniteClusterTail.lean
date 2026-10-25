/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/InfiniteClusterTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Percolation.InfiniteClusterTail.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Percolation

variable {d : ℕ}

structure InfiniteClusterTailData (omega : ConfigSpace (Sym2 (Site d)))
    (K : Finset (Site d)) (x : Site d) where
  inside : Site d
  outside : Site d
  tail : Set (Site d)
  inside_mem : inside ∈ K
  outside_not_mem : outside ∉ K
  exit_open : (openSubgraph d omega).Adj inside outside
  outside_mem_tail : outside ∈ tail
  tail_infinite : tail.Infinite
  tail_subset_cluster : tail ⊆ cluster d omega x
  tail_connected_outside :
    ∀ a ∈ tail, ∀ b ∈ tail,
      ∃ (ha : a ∉ (K : Set (Site d))) (hb : b ∉ (K : Set (Site d))),
        ((openSubgraph d omega).induce (K : Set (Site d))ᶜ).Reachable
          ⟨a, ha⟩ ⟨b, hb⟩


end StatMech.Percolation
