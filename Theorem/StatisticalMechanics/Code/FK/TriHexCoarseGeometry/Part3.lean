/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCoarseGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Def.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part2
open Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


theorem exists_hexagonal_walk_to_anchor (u : HexVertex) :
    ∃ w : hexagonalGraph.Walk u (hexToTriAnchor u, false),
      w.length ≤ 1 := by
  rcases u with ⟨x, b⟩
  cases b with
  | false =>
      exact ⟨Walk.nil, by simp [hexToTriAnchor]⟩
  | true =>
      have h : hexagonalGraph.Adj (x, true)
          (hexToTriAnchor (x, true), false) := by
        rw [hexagonalGraph_adj]
        refine Or.inr ⟨rfl, rfl, 0, ?_⟩
        simp [hexToTriAnchor]
      exact ⟨Walk.cons h Walk.nil, by simp⟩


theorem hexagonalGraph_connected : hexagonalGraph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨(0, false)⟩⟩
  intro u v
  obtain ⟨wu, _⟩ := exists_hexagonal_walk_to_anchor u
  obtain ⟨wv, _⟩ := exists_hexagonal_walk_to_anchor v
  obtain ⟨wt⟩ := triangularGraph_connected.preconnected
    (hexToTriAnchor u) (hexToTriAnchor v)
  obtain ⟨wh, _⟩ := exists_hexagonal_walk_of_triangular_walk wt
  exact ⟨wu.append (wh.append wv.reverse)⟩


theorem hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two
    (u v : HexVertex) :
    hexagonalGraph.dist u v ≤
      2 * triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) + 2 := by
  obtain ⟨wu, hwu⟩ := exists_hexagonal_walk_to_anchor u
  obtain ⟨wv, hwv⟩ := exists_hexagonal_walk_to_anchor v
  obtain ⟨wt, hwt⟩ := triangularGraph_connected.exists_walk_length_eq_dist
    (hexToTriAnchor u) (hexToTriAnchor v)
  obtain ⟨wh, hwh⟩ := exists_hexagonal_walk_of_triangular_walk wt
  have hlen : (wu.append (wh.append wv.reverse)).length ≤
      2 * triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) + 2 := by
    simp only [Walk.length_append, Walk.length_reverse]
    rw [hwh, hwt]
    omega
  exact (SimpleGraph.dist_le (wu.append (wh.append wv.reverse))).trans hlen


theorem half_hexagonal_dist_le_triangular_anchor_dist_add_one
    (u v : HexVertex) :
    (1 / 2 : Real) * (hexagonalGraph.dist u v : Real) ≤
      (triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) : Real) + 1 := by
  have h := hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two u v
  have h' : (hexagonalGraph.dist u v : Real) ≤
      2 * (triangularGraph.dist (hexToTriAnchor u) (hexToTriAnchor v) : Real) + 2 := by
    exact_mod_cast h
  linarith


theorem hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box
    {u v : HexVertex} {n : Nat}
    (huv : hexToTriAnchor v - hexToTriAnchor u ∈ box 2 n) :
    hexagonalGraph.dist u v ≤ 4 * n + 2 := by
  have htri := triangular_dist_le_two_mul_of_sub_mem_box huv
  have hhex := hexagonal_dist_le_two_mul_triangular_anchor_dist_add_two u v
  omega

end PeriodicPlanar
end FK
end StatMech
