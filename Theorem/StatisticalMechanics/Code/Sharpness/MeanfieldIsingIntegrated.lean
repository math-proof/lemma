/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


theorem hasDerivAt_sctOriginMag_beta (d n : ℕ) (h beta : ℝ) :
    HasDerivAt (fun b => sctOriginMag d b h n)
      (sctOriginMagBetaDeriv d n h beta) beta := by
  exact hasDerivAt_expectation_beta (sctBoxGraph d n) beta h
    (fun s => spin s (sctBoxOrigin d n))


end Sharpness
end StatMech
