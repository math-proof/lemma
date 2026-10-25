/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBridgeVariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterZeroFieldSheet
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBondUpper.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBridgeVariance


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def twoBridgeTiltVariance (t A E : Real) : Real :=
  (1 - t ^ 2) *
      (A ^ 2 * t ^ 2 - A ^ 2 - 2 * A * E * t + 2 * A * t -
        2 * E ^ 2 * t ^ 2 - 2 * E * t ^ 2 + 2 * E + 2) /
    (1 + A * t + E * t ^ 2) ^ 2


end
end StatMech.Ising
