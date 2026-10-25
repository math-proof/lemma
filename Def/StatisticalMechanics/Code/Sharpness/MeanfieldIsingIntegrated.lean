/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


noncomputable def sctOriginMagBetaDeriv (d n : ℕ) (h beta : ℝ) : ℝ :=
  isingExpectation (sctBoxGraph d n) beta h
      (fun s => spin s (sctBoxOrigin d n) * negHam (sctBoxGraph d n) h s) -
    sctOriginMag d beta h n *
      isingExpectation (sctBoxGraph d n) beta h (negHam (sctBoxGraph d n) h)


end Sharpness
end StatMech
