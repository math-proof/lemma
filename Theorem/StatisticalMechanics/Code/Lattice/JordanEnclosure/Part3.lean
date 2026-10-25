/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

@[simp] theorem bdEdge_mk (S : Set (Site 2)) (x y : Site 2) :
    bdEdge S s(x, y) ↔ (x ∈ S ↔ y ∉ S) := by
  unfold bdEdge; rfl

theorem bdEdge_iff_bdInd (S : Set (Site 2)) (x y : Site 2) :
    bdEdge S s(x, y) ↔ bdInd S x y = 1 := by
  rw [bdEdge_mk]
  unfold bdInd
  by_cases h : (x ∈ S ↔ y ∉ S) <;> simp [h]


theorem sharedPrimalEdge_comm_of_adj {f g : Site 2}
    (h : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge f g = sharedPrimalEdge g f := by
  classical
  unfold sharedPrimalEdge
  by_cases h0 : f 0 = g 0
  · rw [if_pos h0, if_pos h0.symm, h0, max_comm]
  · rw [if_neg h0, if_neg (fun hc => h0 hc.symm)]
    have hadj := h
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
    have h1 : f 1 = g 1 := by
      by_contra hne
      have : (f 1 - g 1).natAbs ≥ 1 := by omega
      have : (f 0 - g 0).natAbs ≥ 1 := by
        rcases Int.natAbs_eq (f 0 - g 0) with he | he <;> omega
      omega
    rw [h1, max_comm]


end Lattice
end StatMech
