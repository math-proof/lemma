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
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


@[simp] theorem frpEdgeCoupling_mk (K : FiniteRangeKernel d) (x y : Site d) :
    frpEdgeCoupling K s(x, y) = K.coupling (y - x) := rfl


end Sharpness
end StatMech
