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
import Def.StatisticalMechanics.Code.Walls.dg2degree
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice

attribute [local instance] Classical.propDecidable


theorem dg2_degree_eq_four_iff_checker (K : Set (Site 2)) (a b : ℤ) :
    (faceBoundaryGraph K).degree ![a, b] = 4 ↔ dg2_Checker K a b := by
  rw [dg2_degree_eq_transitions]
  unfold faceBoundaryDegree bdInd dg2_Checker
  simp only [faceCorner00, faceCorner10, faceCorner11, faceCorner01]
  by_cases h0 : (![a, b] : Site 2) ∈ K <;>
    by_cases h1 : (![a + 1, b] : Site 2) ∈ K <;>
    by_cases h2 : (![a + 1, b + 1] : Site 2) ∈ K <;>
    by_cases h3 : (![a, b + 1] : Site 2) ∈ K <;>
    simp_all


theorem dg2_degree_eq_zero_iff_uniform (K : Set (Site 2)) (a b : ℤ) :
    (faceBoundaryGraph K).degree ![a, b] = 0 ↔
      ((![a, b] : Site 2) ∈ K ↔ (![a + 1, b] : Site 2) ∈ K) ∧
      ((![a + 1, b] : Site 2) ∈ K ↔ (![a + 1, b + 1] : Site 2) ∈ K) ∧
      ((![a + 1, b + 1] : Site 2) ∈ K ↔ (![a, b + 1] : Site 2) ∈ K) := by
  rw [dg2_degree_eq_transitions]
  unfold faceBoundaryDegree bdInd
  simp only [faceCorner00, faceCorner10, faceCorner11, faceCorner01]
  by_cases h0 : (![a, b] : Site 2) ∈ K <;>
    by_cases h1 : (![a + 1, b] : Site 2) ∈ K <;>
    by_cases h2 : (![a + 1, b + 1] : Site 2) ∈ K <;>
    by_cases h3 : (![a, b + 1] : Site 2) ∈ K <;>
    simp_all


end Walls
end StatMech
