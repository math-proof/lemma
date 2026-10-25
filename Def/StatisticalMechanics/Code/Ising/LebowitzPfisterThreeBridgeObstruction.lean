/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBridgeVariance.Part3


namespace StatMech.Ising

noncomputable section

def threeBridgeTiltVariance (t a b c : Real) : Real :=
  (t - 1) * (t + 1) *
      (-2 * a ^ 2 * t ^ 2 + a ^ 2 - 2 * a * b * t ^ 3 +
        2 * a * b * t + 2 * a * c * t ^ 4 - 4 * a * t -
        b ^ 2 * t ^ 4 + 2 * b ^ 2 * t ^ 2 + 4 * b * c * t ^ 3 -
        2 * b + 3 * c ^ 2 * t ^ 4 + 6 * c * t ^ 3 -
        6 * c * t - 3) /
    (1 + a * t + b * t ^ 2 + c * t ^ 3) ^ 2


def threeBridgeVarianceSkewPolynomial (t a b c : Real) : Real :=
  -a ^ 3 * b * t ^ 4 + a ^ 3 + 2 * a ^ 2 * b * c * t ^ 6 -
    3 * a ^ 2 * b * c * t ^ 4 + a ^ 2 * c * t ^ 4 +
    4 * a ^ 2 * c * t ^ 2 + a * b ^ 3 * t ^ 4 +
    3 * a * b ^ 2 * t ^ 4 - 2 * a * b ^ 2 * t ^ 2 +
    3 * a * b * c ^ 2 * t ^ 8 - 2 * a * b * c ^ 2 * t ^ 6 +
    2 * a * b * t ^ 2 - 3 * a * b - 2 * a * c ^ 2 * t ^ 6 +
    9 * a * c ^ 2 * t ^ 4 - a - b ^ 3 * c * t ^ 8 -
    4 * b ^ 2 * c * t ^ 6 - b ^ 2 * c * t ^ 4 +
    b * c ^ 3 * t ^ 8 - 9 * b * c * t ^ 4 +
    2 * b * c * t ^ 2 - 3 * c ^ 3 * t ^ 8 +
    6 * c ^ 3 * t ^ 6 - 6 * c * t ^ 2 + 3 * c


def threeBridgeVarianceSkewBernsteinCoeff
    (a b c : Real) : Fin 5 -> Real
  | 0 => a ^ 3 - 3 * a * b - a + 3 * c
  | 1 =>
      (2 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 5 * a * b - 2 * a +
        b * c + 3 * c) / 2
  | 2 =>
      -(a ^ 3 * b - 6 * a ^ 3 + 3 * a ^ 2 * b * c - 13 * a ^ 2 * c -
        a * b ^ 3 + 3 * a * b ^ 2 + 12 * a * b - 9 * a * c ^ 2 +
        6 * a + b ^ 2 * c + 3 * b * c) / 6
  | 3 =>
      -(a * b - 2 * a - 3 * c) * (a - b + c - 1) *
        (a + b + c + 1) / 2
  | 4 =>
      -(a - b + c - 1) * (a + b + c + 1) *
        (a * b - a - b * c - 3 * c)


end
end StatMech.Ising
