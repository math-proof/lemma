/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part3
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


noncomputable def sctMeanfieldIntegratedError
    (d n : ℕ) (h beta : ℝ) : ℝ :=
  2 * beta * (1 - sctLatticeC d beta h n) *
      (1 - (sctOriginMag d beta h n) ^ 2) +
    2 * beta ^ 2 * sctLatticeC d beta h n *
      sctBoundaryCovarianceError d beta h n

end Sharpness
end StatMech
