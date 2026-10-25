/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/SourceCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Def.StatisticalMechanics.Code.FrontierB.SourceCurrentTail.Part2
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem walkEdges_subset_edgeFinset {u v : V} (p : G.Walk u v) :
    p.edges.toFinset ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨⟨x, y⟩, hxy⟩ := e.exists_rep
  rw [← hxy] at he ⊢
  simpa using p.adj_of_mem_edges (by simpa using he)


theorem ofEdgeFun_pathEdgeCurrent {u v : V} (p : G.Walk u v) :
    ofEdgeFun G (pathEdgeCurrent G p) =
      edgeIndicatorCurrent p.edges.toFinset := by
  funext e
  by_cases he : e ∈ G.edgeFinset
  · simp [ofEdgeFun, pathEdgeCurrent, edgeIndicatorCurrent, he]
  · have hp : e ∉ p.edges.toFinset := fun h =>
      he (walkEdges_subset_edgeFinset G p h)
    simp [ofEdgeFun, pathEdgeCurrent, edgeIndicatorCurrent, he, hp]


theorem sources_pathEdgeCurrent {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (huv : u ≠ v) :
    sources G (ofEdgeFun G (pathEdgeCurrent G p)) = {u, v} := by
  rw [ofEdgeFun_pathEdgeCurrent G p]
  apply sources_edgeIndicatorCurrent G p.edges.toFinset {u, v}
    (walkEdges_subset_edgeFinset G p)
  rw [← sourcePair_eq_pair huv]
  exact hasOddBoundary_path_edges p hp


end StatMech.FrontierB
