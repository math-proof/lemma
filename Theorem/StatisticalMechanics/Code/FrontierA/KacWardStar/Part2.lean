/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Instance.StatisticalMechanics.Code.FrontierA.KacWardStar
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising


theorem kwStarGraph_isAcyclic (ι : Type) : (kwStarGraph ι).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  intro e he
  rw [kwStarGraph, SimpleGraph.edgeSet_completeBipartiteGraph] at he
  obtain ⟨p, rfl⟩ := he
  rcases p with ⟨centre, leaf⟩
  letI : Nonempty ι := ⟨leaf⟩
  letI : Nontrivial (Unit ⊕ ι) :=
    ⟨⟨Sum.inl Unit.unit, Sum.inr leaf, by simp⟩⟩
  rw [SimpleGraph.isBridge_iff]
  refine ⟨by simp [kwStarGraph], ?_⟩
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (by simp)
  ext v
  rcases v with centre' | other
  · have hc : centre' = centre := Subsingleton.elim _ _
    subst centre'
    simp [kwStarGraph, SimpleGraph.deleteEdges_adj]
  · simp [kwStarGraph, SimpleGraph.deleteEdges_adj]


end StatMech.FrontierA
