/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/dg2degree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Def.StatisticalMechanics.Code.Walls.dg2degree.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


theorem dg2_degree_le_two {K : Set (Site 2)} (hK : dg2_NoPinch K) (f : Site 2) :
    (faceBoundaryGraph K).degree f ≤ 2 := by
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  rw [hf]
  set a := f 0
  set b := f 1
  have heven : Even ((faceBoundaryGraph K).degree ![a, b]) := degree_faceBoundaryGraph_even K _
  have hle4 : (faceBoundaryGraph K).degree ![a, b] ≤ 4 := by
    rw [dg2_degree_eq_transitions]; exact faceBoundaryDegree_le_four K a b
  
  have hne4 : (faceBoundaryGraph K).degree ![a, b] ≠ 4 := by
    intro h4
    exact hK a b ((dg2_degree_eq_four_iff_checker K a b).mp h4)
  rw [Nat.even_iff] at heven
  omega


theorem dg2_degree_pos_of_mem_support {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    1 ≤ (faceBoundaryGraph K).degree f := by
  obtain ⟨g, hg⟩ := hf
  have : g ∈ (faceBoundaryGraph K).neighborFinset f := by
    rw [SimpleGraph.mem_neighborFinset]; exact hg
  rw [SimpleGraph.degree]
  exact Finset.card_pos.mpr ⟨g, this⟩


theorem dg2_boundary_degree_eq_two {K : Set (Site 2)} (hK : dg2_NoPinch K) {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 := by
  have heven : Even ((faceBoundaryGraph K).degree f) := degree_faceBoundaryGraph_even K f
  have hpos : 1 ≤ (faceBoundaryGraph K).degree f := dg2_degree_pos_of_mem_support hf
  have hle : (faceBoundaryGraph K).degree f ≤ 2 := dg2_degree_le_two hK f
  rw [Nat.even_iff] at heven
  omega


end Walls
end StatMech
