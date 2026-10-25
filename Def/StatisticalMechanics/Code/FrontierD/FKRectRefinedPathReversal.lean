/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedPathReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryRepeatedVisits


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def fkRectIntegralSquareDartReverse
    (d : FKRectIntegralSquareDart) : FKRectIntegralSquareDart :=
  (fkRectIntegralSquareDartEnd d, d.2 + 2)


def fkRectIntegralSquareDartListReverse
    (l : List FKRectIntegralSquareDart) : List FKRectIntegralSquareDart :=
  l.reverse.map fkRectIntegralSquareDartReverse

end
end StatMech.FrontierD
