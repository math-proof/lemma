/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalBarrierCapstone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedHorizontalEndpoint
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDiagonalBlockLower.Part2
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectPositiveBandBarrierConstant
    (k scale : Nat) (q : Real) : Real :=
  let c := FK.cFE (fkRectCriticalP q) q
  c ^ (2 * (2 * (k + 3))) *
    (((c ^ ((4 * scale + 1) * (24 * scale + 4))) *
      c ^ ((4 * scale + 1) * (40 * scale + 7))) * c)

end
end StatMech.FrontierD
