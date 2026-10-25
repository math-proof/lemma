/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc59_DisjointCorridors (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
    (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    (s((0 : Site d), a₁) ∈ G ∧ s((0 : Site d), a₂) ∈ G ∧ s((0 : Site d), a₃) ∈ G) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) ∧
    (¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₂ ∧
     ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₁ a₃ ∧
     ¬ Connected d (removeSite 0 (forceOpenFinset G ω)) a₂ a₃)


end StatMech.Walls
