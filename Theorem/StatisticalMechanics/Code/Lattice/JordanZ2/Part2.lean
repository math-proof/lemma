/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Def.StatisticalMechanics.Code.Lattice.JordanZ2.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem bdInd_comm (S : Set (Site 2)) (x y : Site 2) : bdInd S x y = bdInd S y x := by
  classical
  unfold bdInd
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp_all


theorem bdInd_eq_one_iff (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) :
    bdInd S x y = 1 ↔ (x, y) ∈ edgeBoundary 2 S := by
  classical
  unfold bdInd
  simp only [mem_edgeBoundary, hadj, true_and]
  by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]


end Lattice
end StatMech
