/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def sixVertexDualGapPowerTerm (x : Real) (n : Nat) : Real :=
  4 * Real.log
    ((1 + x ^ (2 * n + 1)) / (1 - x ^ (2 * n + 1)))


def sixVertexDualGapPowerSeries (x : Real) : Real :=
  ∑' n : Nat, sixVertexDualGapPowerTerm x n

end
end StatMech.FrontierD
