/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingExponentialPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpness
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingExponentialPlus.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech


namespace StatMech

namespace Sharpness

open Ising (spin plusState spin_eq_pm spin_sq boxFinset mem_boxFinset)

open Lattice Percolation ConfigSpace

variable {d : ℕ}


def plusCorrTailSet (d : ℕ) (beta : ℝ) (n : ℕ) : Set ℝ :=
  insert 0 {r | ∃ z : Site d, n ≤ l1dist d (origin d) z ∧
    r = plusCorr d beta (origin d) z}

noncomputable def plusCorrTailSup (d : ℕ) (beta : ℝ) (n : ℕ) : ℝ :=
  sSup (plusCorrTailSet d beta n)

end Sharpness
end StatMech
