/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc95forestdensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc94density.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Def.StatisticalMechanics.Code.Walls.bc95forestdensity
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc95_ae_genuineCount_of_armReaching (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hres : bc95_AeArmReaching μ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, bc89_genuineTcount ω n ≤ boxSV_boundaryCard d n := by
  filter_upwards [hres n hn] with ω hω
  obtain ⟨hcanon, harmbox, _⟩ := hω
  exact bc90_genuineTcount_le_boundary_of_genuine_armsInBox ω n hn hcanon harmbox


theorem bc95_forestResidue_of_ae_armReaching (μ : Measure (ConfigSpace (Sym2 (Site d))))
    (hres : bc95_AeArmReaching μ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ ω ∂μ, bst_BoxOpenForest ω n := by
  filter_upwards [hres n hn] with ω hω
  obtain ⟨hcanon, harmbox, hexists⟩ := hω
  exact bc95_boxOpenForest_of_harmbox ω n hn hcanon harmbox hexists


end StatMech.Walls
