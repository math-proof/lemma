/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SimonPlusLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


noncomputable def simonBoundaryIntegral
    (β : ℝ) (S : Finset (Site d)) (o z : Site d)
    (μ : Measure (ConfigSpace (Site d))) : ℝ :=
  ∑ e ∈ boundaryEdges d S,
    Real.tanh β * corrOriginInner d β S e.1 *
      (∫ ω, spin ω e.2 * spin ω z ∂μ)


noncomputable def simonBoundaryPlus
    (β : ℝ) (S : Finset (Site d)) (o z : Site d) : ℝ :=
  ∑ e ∈ boundaryEdges d S,
    Real.tanh β * corrOriginInner d β S e.1 * plusCorr d β e.2 z


end Sharpness
end StatMech
