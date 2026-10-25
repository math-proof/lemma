/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part16
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem hexagonal_adj_neighbor (u : HexVertex) (i : Fin 3) :
    hexagonalGraph.Adj u (hexagonalNeighbor u i) := by
  rw [hexagonalGraph_adj]
  rcases h : u.2 with _ | _
  · left
    simp [hexagonalNeighbor, h]
  · right
    simp [hexagonalNeighbor, h]

theorem hexagonal_mem_candidates_of_adj {u v : HexVertex}
    (h : hexagonalGraph.Adj u v) :
    v ∈ Finset.univ.image (hexagonalNeighbor u) := by
  rw [hexagonalGraph_adj] at h
  rcases h with ⟨hu, hv, i, hi⟩ | ⟨hv, hu, i, hi⟩
  · rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · have hcoord : u.1 + hexagonalStep i = v.1 := by
        ext j
        have hj := congrFun hi j
        simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
        omega
      simpa [hexagonalNeighbor, hu] using hcoord
    · simp [hexagonalNeighbor, hu, hv]
  · rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · have hcoord : u.1 - hexagonalStep i = v.1 := by
        ext j
        have hj := congrFun hi j
        simp only [Pi.sub_apply] at hj ⊢
        omega
      simpa [hexagonalNeighbor, hu] using hcoord
    · simp [hexagonalNeighbor, hu, hv]

end PeriodicPlanar
end FK
end StatMech
