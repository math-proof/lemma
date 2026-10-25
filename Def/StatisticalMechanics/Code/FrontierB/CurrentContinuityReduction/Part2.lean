/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfinitePlusFreeSourceSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.Sharpness.IsingMagnetizationZero
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityReduction
open Filter MeasureTheory Set Topology BoundedContinuousFunction


namespace StatMech.FrontierB

open Ising Lattice Percolation Sharpness

variable {d : ℕ}


def CurrentContinuityTwoPointInfluenceBound
    (d : ℕ) (beta : ℝ) (hbeta : 0 < beta) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x y : Site d,
    |currentContinuityPlusTwoPoint d beta x y -
      currentContinuityFreeTwoPoint d beta x y| ≤
      C * (currentContinuityMixedTraceLaw d beta hbeta : Measure _).real
        (percolationEvent d)


end StatMech.FrontierB
