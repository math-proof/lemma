/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostVarianceSector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part5


namespace StatMech.Ising

noncomputable section

def lpTwoGhostPlusSectorVariance
    (a b c d e : Real) : Real :=
  (d + e) / (1 + c) - ((a + b) / (1 + c)) ^ 2


def lpTwoGhostMinusSectorVariance
    (a b c d e : Real) : Real :=
  (d - e) / (1 - c) - ((a - b) / (1 - c)) ^ 2


end
end StatMech.Ising
