/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


noncomputable instance instDecidableRelFKRectHorizontalCylinderGraph
    (R : FKRectTorus) : DecidableRel (fkRectHorizontalCylinderGraph R).Adj :=
  fun _ _ => Classical.dec _

end
end StatMech.FrontierD
