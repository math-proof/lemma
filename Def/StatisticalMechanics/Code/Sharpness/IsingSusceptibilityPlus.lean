/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/IsingSusceptibilityPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.CorrelationMonotone
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators StatMech


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation ConfigSpace

variable {d : ℕ}


noncomputable def plusCorrWindowSum (d : ℕ) (beta : ℝ)
    (L : Finset (Site d)) : ℝ :=
  ∑ z ∈ L, plusCorr d beta (Percolation.origin d) z


noncomputable def plusCorrWindowSup (d : ℕ) (beta : ℝ) (n : ℕ) : ℝ :=
  sSup {r : ℝ | ∃ L : Finset (Site d), L.card ≤ n ∧
    r = plusCorrWindowSum d beta L}

end Sharpness
end StatMech
