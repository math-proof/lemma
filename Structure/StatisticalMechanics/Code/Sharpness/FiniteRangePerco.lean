/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


structure FiniteRangeKernel (d : ℕ) where
  coupling : Site d → ℝ
  nonneg : ∀ z, 0 ≤ coupling z
  zero : coupling 0 = 0
  symmetric : ∀ z, coupling (-z) = coupling z
  range : ℕ
  support : ∀ z, coupling z ≠ 0 → z ∈ box d range

end Sharpness
end StatMech
