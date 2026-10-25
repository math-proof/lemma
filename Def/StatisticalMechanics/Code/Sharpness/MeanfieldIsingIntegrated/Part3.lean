/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part2
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


noncomputable def sctMeanfieldG (d n : ℕ) (h beta : ℝ) : ℝ :=
  beta ^ 2 * (1 - (sctOriginMag d beta h n) ^ 2)


noncomputable def sctMeanfieldGDeriv (d n : ℕ) (h beta : ℝ) : ℝ :=
  2 * beta * (1 - (sctOriginMag d beta h n) ^ 2) -
    beta ^ 2 * sctOriginMagSqBetaDeriv d n h beta

end Sharpness
end StatMech
