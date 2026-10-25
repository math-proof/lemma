/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsOuterContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Percolation (anchorFinset)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem poc_cyclesAtLen_card_le_real (ℓ : ℕ) :
    ((Percolation.cyclesAtLen ℓ).card : ℝ) ≤ 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by
  have h : ((Percolation.cyclesAtLen ℓ).card : ℕ) ≤ 2 * ℓ * 4 ^ ℓ := Percolation.cyclesAtLen_card ℓ
  calc ((Percolation.cyclesAtLen ℓ).card : ℝ)
      ≤ ((2 * ℓ * 4 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * ((ℓ : ℝ) * (2 * 2 : ℝ) ^ ℓ) := by push_cast; ring


end Ising
end StatMech
