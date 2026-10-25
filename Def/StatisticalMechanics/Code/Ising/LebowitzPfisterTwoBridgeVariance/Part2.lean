/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBridgeVariance.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBridgeVariance


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def twoBridgeTiltMean (t A E : Real) : Real :=
  2 * t + (1 - t ^ 2) * (A + 2 * E * t) /
    (1 + A * t + E * t ^ 2)


end
end StatMech.Ising
