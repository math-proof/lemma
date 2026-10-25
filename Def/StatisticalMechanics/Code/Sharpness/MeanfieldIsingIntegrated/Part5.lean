/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part4
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


noncomputable def sctInfiniteMeanfieldG (d : ℕ) (h beta : ℝ) : ℝ :=
  beta ^ 2 * (1 - (sctInfiniteFieldMag d beta h) ^ 2)

end Sharpness
end StatMech
