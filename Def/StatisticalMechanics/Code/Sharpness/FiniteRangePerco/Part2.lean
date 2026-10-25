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
import Theorem.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


noncomputable def frpGraph (K : FiniteRangeKernel d) : SimpleGraph (Site d) where
  Adj x y := 0 < K.coupling (y - x)
  symm := by
    constructor
    intro x y h
    rwa [show x - y = -(y - x) by abel, K.symmetric]
  loopless := ⟨by
    intro x h
    have hz : x - x = (0 : Site d) := sub_self x
    rw [hz, K.zero] at h
    exact (lt_irrefl 0 h)⟩

end Sharpness
end StatMech
