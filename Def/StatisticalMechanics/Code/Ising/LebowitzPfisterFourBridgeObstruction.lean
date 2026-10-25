/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite


namespace StatMech.Ising

noncomputable section

def fourBridgeTiltVariance (t a b c d : Real) : Real :=
  (t - 1) * (t + 1) *
      (-3 * a ^ 2 * t ^ 2 + a ^ 2 - 4 * a * b * t ^ 3 +
        2 * a * b * t + 6 * a * d * t ^ 5 - 4 * a * d * t ^ 3 -
        6 * a * t - 2 * b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 -
        2 * b * c * t ^ 5 + 4 * b * c * t ^ 3 +
        2 * b * d * t ^ 6 + 2 * b * d * t ^ 4 - 2 * b * t ^ 2 -
        2 * b - c ^ 2 * t ^ 6 + 3 * c ^ 2 * t ^ 4 +
        6 * c * d * t ^ 5 + 4 * c * t ^ 3 - 6 * c * t +
        4 * d ^ 2 * t ^ 6 + 12 * d * t ^ 4 - 12 * d * t ^ 2 - 4) /
    (1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4) ^ 2


def fourBridgeTiltMean (t a b c d : Real) : Real :=
  4 * t + (1 - t ^ 2) *
    (a + 2 * b * t + 3 * c * t ^ 2 + 4 * d * t ^ 3) /
      (1 + a * t + b * t ^ 2 + c * t ^ 3 + d * t ^ 4)


end
end StatMech.Ising
