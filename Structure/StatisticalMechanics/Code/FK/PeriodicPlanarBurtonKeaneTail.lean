/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

structure PeriodicGraph.InfiniteTailData (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) (K : Finset V) (x : V) where
  inside : V
  outside : V
  tail : Set V
  inside_mem : inside ∈ K
  outside_not_mem : outside ∉ K
  exit_open : (P.openSubgraph omega).Adj inside outside
  outside_mem_tail : outside ∈ tail
  tail_infinite : tail.Infinite
  tail_subset_cluster : tail ⊆ P.cluster omega x
  tail_connected_outside :
    ∀ a ∈ tail, ∀ b ∈ tail,
      ∃ (ha : a ∉ (K : Set V)) (hb : b ∉ (K : Set V)),
        ((P.openSubgraph omega).induce (K : Set V)ᶜ).Reachable
          ⟨a, ha⟩ ⟨b, hb⟩

end StatMech.FK.PeriodicPlanar
