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
import Theorem.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part13
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


def frpCrossingEventFrom (K : FiniteRangeKernel d) (y : Site d) (n : ℕ) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  connEvent (frpGraph K) Set.univ y (box d (n - 1))ᶜ

end Sharpness
end StatMech
