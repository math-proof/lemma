/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeProductBounds


namespace StatMech.Ising

noncomputable section

def fourBridgeSecondMiddleNumerator (a b c d : Real) : Real :=
  a ^ 3 * b - 3 * a ^ 3 * d - 15 * a ^ 3 +
    3 * a ^ 2 * b * c - 21 * a ^ 2 * c - a * b ^ 3 +
    7 * a * b ^ 2 + 10 * a * b * d + 35 * a * b -
    9 * a * c ^ 2 + 39 * a * d + 15 * a + b ^ 2 * c -
    b * c + 9 * c * d - 15 * c


end
end StatMech.Ising
