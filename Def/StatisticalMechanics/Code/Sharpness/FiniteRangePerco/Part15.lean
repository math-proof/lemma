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
import Theorem.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part14
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


def frpSubcriticalSet (K : FiniteRangeKernel d) : Set ℝ :=
  {beta | 0 ≤ beta ∧ ∀ gamma, 0 ≤ gamma → gamma ≤ beta →
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ frpPhi K gamma S < 1}

noncomputable def frpTildeBetaC (K : FiniteRangeKernel d) : ℝ :=
  sSup (frpSubcriticalSet K)

end Sharpness
end StatMech
