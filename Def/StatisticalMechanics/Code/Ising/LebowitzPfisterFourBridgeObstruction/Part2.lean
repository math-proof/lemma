/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeClosure
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterStrongMarkedSite
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeObstruction


namespace StatMech.Ising

noncomputable section

def fourBridgeVarianceSkewPolynomial (t a b c d : Real) : Real :=
  -a ^ 3 * b * t ^ 4 - 6 * a ^ 3 * d * t ^ 6 +
    3 * a ^ 3 * d * t ^ 4 + a ^ 3 + 2 * a ^ 2 * b * c * t ^ 6 -
    3 * a ^ 2 * b * c * t ^ 4 - 9 * a ^ 2 * c * d * t ^ 8 +
    2 * a ^ 2 * c * d * t ^ 6 + a ^ 2 * c * t ^ 4 +
    4 * a ^ 2 * c * t ^ 2 + a * b ^ 3 * t ^ 4 +
    a * b ^ 2 * d * t ^ 8 + 4 * a * b ^ 2 * d * t ^ 6 +
    3 * a * b ^ 2 * t ^ 4 - 2 * a * b ^ 2 * t ^ 2 +
    3 * a * b * c ^ 2 * t ^ 8 - 2 * a * b * c ^ 2 * t ^ 6 -
    2 * a * b * d ^ 2 * t ^ 10 + 9 * a * b * d ^ 2 * t ^ 8 +
    16 * a * b * d * t ^ 6 - 10 * a * b * d * t ^ 4 +
    2 * a * b * t ^ 2 - 3 * a * b - 4 * a * c ^ 2 * d * t ^ 10 -
    a * c ^ 2 * d * t ^ 8 - 2 * a * c ^ 2 * t ^ 6 +
    9 * a * c ^ 2 * t ^ 4 - 3 * a * d ^ 3 * t ^ 12 +
    6 * a * d ^ 3 * t ^ 10 + 9 * a * d ^ 2 * t ^ 8 -
    4 * a * d ^ 2 * t ^ 6 + 11 * a * d * t ^ 4 -
    10 * a * d * t ^ 2 - a - b ^ 3 * c * t ^ 8 +
    2 * b ^ 2 * c * d * t ^ 10 - 3 * b ^ 2 * c * d * t ^ 8 -
    4 * b ^ 2 * c * t ^ 6 - b ^ 2 * c * t ^ 4 +
    b * c ^ 3 * t ^ 8 + 3 * b * c * d ^ 2 * t ^ 12 -
    2 * b * c * d ^ 2 * t ^ 10 + 10 * b * c * d * t ^ 8 -
    16 * b * c * d * t ^ 6 - 9 * b * c * t ^ 4 +
    2 * b * c * t ^ 2 - c ^ 3 * d * t ^ 12 -
    3 * c ^ 3 * t ^ 8 + 6 * c ^ 3 * t ^ 6 +
    c * d ^ 3 * t ^ 12 + 10 * c * d ^ 2 * t ^ 10 -
    11 * c * d ^ 2 * t ^ 8 + 4 * c * d * t ^ 6 -
    9 * c * d * t ^ 4 - 6 * c * t ^ 2 + 3 * c


def fourBridgeVarianceSkewBernsteinCoeff
    (a b c d : Real) : Fin 7 -> Real
  | 0 => a ^ 3 - 3 * a * b - a + 3 * c
  | 1 =>
      (3 * a ^ 3 + 2 * a ^ 2 * c - a * b ^ 2 - 8 * a * b -
        5 * a * d - 3 * a + b * c + 6 * c) / 3
  | 2 =>
      -(a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
        3 * a ^ 2 * b * c - 21 * a ^ 2 * c - a * b ^ 3 +
        7 * a * b ^ 2 + 10 * a * b * d + 35 * a * b -
        9 * a * c ^ 2 + 39 * a * d + 15 * a + b ^ 2 * c -
        b * c + 9 * c * d - 15 * c) / 15
  | 3 =>
      -(2 * a ^ 3 * b - 3 * a ^ 3 * d - 10 * a ^ 3 +
        5 * a ^ 2 * b * c - a ^ 2 * c * d - 22 * a ^ 2 * c -
        2 * a * b ^ 3 - 2 * a * b ^ 2 * d + 4 * a * b ^ 2 +
        a * b * c ^ 2 + 12 * a * b * d + 20 * a * b -
        17 * a * c ^ 2 + 2 * a * d ^ 2 + 28 * a * d + 10 * a +
        4 * b ^ 2 * c + 8 * b * c * d + 8 * b * c -
        3 * c ^ 3 + 16 * c * d) / 10
  | 4 =>
      -(6 * a ^ 3 * b - 15 * a ^ 3 + 12 * a ^ 2 * b * c +
        3 * a ^ 2 * c * d - 46 * a ^ 2 * c - 6 * a * b ^ 3 -
        13 * a * b ^ 2 * d + 2 * a * b ^ 2 + 3 * a * b * c ^ 2 -
        9 * a * b * d ^ 2 + 12 * a * b * d + 25 * a * b +
        a * c ^ 2 * d - 48 * a * c ^ 2 + 3 * a * d ^ 2 +
        34 * a * d + 15 * a + b ^ 3 * c + 3 * b ^ 2 * c * d +
        18 * b ^ 2 * c - b * c ^ 3 + 38 * b * c * d +
        34 * b * c - 15 * c ^ 3 + 11 * c * d ^ 2 +
        42 * c * d + 15 * c) / 15
  | 5 =>
      -(a - b + c - d - 1) * (a + b + c + d + 1) *
        (2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c) / 3
  | 6 =>
      -(a - b + c - d - 1) * (a + b + c + d + 1) *
        (a * b + 3 * a * d - a - b * c + c * d - 3 * c)


end
end StatMech.Ising
