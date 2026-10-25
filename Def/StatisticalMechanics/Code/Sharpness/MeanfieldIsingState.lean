/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFull.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState
open MeasureTheory Real Set Filter Topology
open scoped BigOperators


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


noncomputable def sctFieldToZero (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)


noncomputable def sctZeroPlusMag (d : ℕ) (beta : ℝ) : ℝ :=
  ⨅ n : ℕ, sctInfiniteFieldMag d beta (sctFieldToZero n)

end Sharpness
end StatMech
