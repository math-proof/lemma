/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def pcUpperBound (p : ℝ) : ℝ :=
  ∑' ℓ : ℕ, (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ


noncomputable def pcRatio (p : ℝ) : ℝ := 4 * (1 - p)

end Percolation
end StatMech
