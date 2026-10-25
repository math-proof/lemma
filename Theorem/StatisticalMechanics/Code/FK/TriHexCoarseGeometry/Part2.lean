/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Def.StatisticalMechanics.Code.FK.TriHexCoarseGeometry
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


theorem triangularStep_eq_hexagonalStep_sub (i : Fin 3) :
    triangularStep i =
      hexagonalStep (triHexLiftEntry i) -
        hexagonalStep (triHexLiftExit i) := by
  fin_cases i <;> decide


theorem exists_hexagonal_walk_of_triangular_step
    {x y : Site 2} (i : Fin 3) (h : y - x = triangularStep i) :
    ∃ w : hexagonalGraph.Walk (x, false) (y, false), w.length = 2 := by
  let m := x + hexagonalStep (triHexLiftEntry i)
  have hxm : hexagonalGraph.Adj (x, false) (m, true) := by
    rw [hexagonalGraph_adj]
    exact Or.inl ⟨rfl, rfl, triHexLiftEntry i, by simp [m]⟩
  have hmy : hexagonalGraph.Adj (m, true) (y, false) := by
    rw [hexagonalGraph_adj]
    refine Or.inr ⟨rfl, rfl, triHexLiftExit i, ?_⟩
    calc
      m - y = hexagonalStep (triHexLiftEntry i) - (y - x) := by
        simp only [m]
        abel
      _ = hexagonalStep (triHexLiftExit i) := by
        rw [h, triangularStep_eq_hexagonalStep_sub]
        abel
  exact ⟨Walk.cons hxm (Walk.cons hmy Walk.nil), by simp⟩


theorem exists_hexagonal_walk_of_triangular_adj
    {x y : Site 2} (hxy : triangularGraph.Adj x y) :
    ∃ w : hexagonalGraph.Walk (x, false) (y, false), w.length = 2 := by
  rw [triangularGraph_adj] at hxy
  obtain ⟨i, h | h⟩ := hxy
  · exact exists_hexagonal_walk_of_triangular_step i h
  · obtain ⟨w, hw⟩ := exists_hexagonal_walk_of_triangular_step i h
    exact ⟨w.reverse, by simpa using hw⟩


theorem exists_hexagonal_walk_of_triangular_walk
    {x y : Site 2} (w : triangularGraph.Walk x y) :
    ∃ W : hexagonalGraph.Walk (x, false) (y, false),
      W.length = 2 * w.length := by
  induction w with
  | nil => exact ⟨Walk.nil, by simp⟩
  | @cons x y z hxy w ih =>
      obtain ⟨e, he⟩ := exists_hexagonal_walk_of_triangular_adj hxy
      obtain ⟨W, hW⟩ := ih
      refine ⟨e.append W, ?_⟩
      rw [Walk.length_append, he, hW, Walk.length_cons]
      omega


end PeriodicPlanar
end FK
end StatMech
