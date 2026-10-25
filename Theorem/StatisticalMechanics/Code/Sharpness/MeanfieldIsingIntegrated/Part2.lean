/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part2
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


theorem hasDerivAt_sctOriginMag_sq_beta (d n : ℕ) (h beta : ℝ) :
    HasDerivAt (fun b => (sctOriginMag d b h n) ^ 2)
      (sctOriginMagSqBetaDeriv d n h beta) beta := by
  convert (hasDerivAt_sctOriginMag_beta d n h beta).pow 2 using 1 <;>
    simp [sctOriginMagSqBetaDeriv] <;> ring

@[simp]
theorem deriv_sctOriginMag_sq_beta (d n : ℕ) (h beta : ℝ) :
    deriv (fun b => (sctOriginMag d b h n) ^ 2) beta =
      sctOriginMagSqBetaDeriv d n h beta :=
  (hasDerivAt_sctOriginMag_sq_beta d n h beta).deriv


end Sharpness
end StatMech
