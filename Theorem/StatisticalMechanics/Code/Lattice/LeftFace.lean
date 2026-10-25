/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Def.StatisticalMechanics.Code.Lattice.LeftFace
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem leftAxisSite_zero_eq_origin : leftAxisSite 0 = origin 2 := by
  funext i; fin_cases i <;> rfl

@[simp] theorem leftAxisSite_coord0 (k : ℕ) : leftAxisSite k 0 = -(k : ℤ) := rfl

@[simp] theorem leftAxisSite_coord1 (k : ℕ) : leftAxisSite k 1 = 0 := rfl


theorem leftAxisSite_zero_mem_cluster :
    leftAxisSite 0 ∈ cluster 2 ω (origin 2) := by
  rw [leftAxisSite_zero_eq_origin]; exact self_mem_cluster ω (origin 2)


theorem exists_leftAxisSite_not_mem_cluster (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ k : ℕ, leftAxisSite k ∉ cluster 2 ω (origin 2) := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (leftAxisSite) := by
    intro a b hab
    have := congrFun hab 0
    simp only [leftAxisSite, Matrix.cons_val_zero, neg_inj, Nat.cast_inj] at this
    exact this
  have hsub : Set.range (leftAxisSite) ⊆ cluster 2 ω (origin 2) := by
    rintro x ⟨k, rfl⟩; exact hcon k
  have hran : (Set.range (leftAxisSite)).Infinite :=
    Set.infinite_range_of_injective hinj
  exact hran (hfin.subset hsub)


end Lattice
end StatMech
