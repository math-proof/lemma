/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part8
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem numClustersWired_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    StatMech.Lattice.numClustersWired (boxGraph d (n+1)) (innerBdry d n) (crossExt d n ω)
      = StatMech.Lattice.numClustersWired (boxGraph d n) (boxBoundary d n) ω
        + annulusCard d n := by
  
  
  
  show Nat.card (crossWiredGraph d n ω).ConnectedComponent
      = Nat.card (innerWiredGraph d n ω).ConnectedComponent + annulusCard d n
  rw [annulusCard, ← Nat.card_sum, Nat.card_congr (crossComponentEquiv d n ω).symm]


theorem innerEdge_mem_edgeSet_iff (d n : ℕ) (e : Sym2 (boxVerts d n)) :
    innerEdge d n e ∈ (boxGraph d (n+1)).edgeSet ↔ e ∈ (boxGraph d n).edgeSet := by
  refine Sym2.inductionOn e (fun a b => ?_)
  rw [innerEdge, Sym2.map_mk, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet,
    boxGraph_adj_boxVertIncl]


theorem innerEdge_image_edgeFinset (d n : ℕ) :
    (boxGraph d n).edgeFinset.image (innerEdge d n)
      = (boxGraph d (n+1)).edgeFinset.filter (· ∈ Set.range (innerEdge d n)) := by
  ext e
  simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_edgeFinset, Set.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(innerEdge_mem_edgeSet_iff d n a).mpr ha, a, rfl⟩
  · rintro ⟨hmem, a, rfl⟩
    exact ⟨a, (innerEdge_mem_edgeSet_iff d n a).mp hmem, rfl⟩


end FK
end StatMech
