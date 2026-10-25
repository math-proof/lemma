/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourAnchor
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem axisSite_zero_eq_origin : axisSite 0 = origin 2 := by
  funext i; fin_cases i <;> rfl

@[simp] theorem axisSite_coord0 (j : ℕ) : axisSite j 0 = (j : ℤ) := rfl

@[simp] theorem axisSite_coord1 (j : ℕ) : axisSite j 1 = 0 := rfl


theorem axisSite_zero_mem_cluster :
    axisSite 0 ∈ cluster 2 ω (origin 2) := by
  rw [axisSite_zero_eq_origin]; exact self_mem_cluster ω (origin 2)


theorem exists_axisSite_not_mem_cluster (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ j : ℕ, axisSite j ∉ cluster 2 ω (origin 2) := by
  by_contra hcon
  push Not at hcon
  
  have hinj : Function.Injective axisSite := by
    intro a b hab
    have := congrFun hab 0
    simpa [axisSite] using this
  have hsub : Set.range axisSite ⊆ cluster 2 ω (origin 2) := by
    rintro x ⟨j, rfl⟩; exact hcon j
  have hran : (Set.range axisSite).Infinite :=
    Set.infinite_range_of_injective hinj
  exact hran (hfin.subset hsub)


end Lattice
end StatMech
