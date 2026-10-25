/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part12
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


theorem triangular_adj_neighbor (x : Site 2) (ib : Fin 3 × Bool) :
    triangularGraph.Adj x (triangularNeighbor x ib) := by
  rcases ib with ⟨i, b⟩
  rw [triangularGraph_adj]
  rcases b with _ | _
  · exact ⟨i, Or.inr (by simp [triangularNeighbor])⟩
  · exact ⟨i, Or.inl (by simp [triangularNeighbor])⟩

theorem triangular_mem_candidates_of_adj {x y : Site 2}
    (h : triangularGraph.Adj x y) :
    y ∈ Finset.univ.image (triangularNeighbor x) := by
  rw [triangularGraph_adj] at h
  obtain ⟨i, h | h⟩ := h
  · rw [Finset.mem_image]
    refine ⟨(i, true), Finset.mem_univ _, ?_⟩
    have hcoord : x + triangularStep i = y := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply, Pi.add_apply] at hj ⊢
      omega
    simpa [triangularNeighbor] using hcoord
  · rw [Finset.mem_image]
    refine ⟨(i, false), Finset.mem_univ _, ?_⟩
    have hcoord : x - triangularStep i = y := by
      ext j
      have hj := congrFun h j
      simp only [Pi.sub_apply] at hj ⊢
      omega
    simpa [triangularNeighbor] using hcoord

end PeriodicPlanar
end FK
end StatMech
