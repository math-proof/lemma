/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalPointDisjoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualPrimalOpenInteraction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearEmbedding.Part2


namespace StatMech.FrontierD

noncomputable section

def FKRectIntegralDartListUsesPoint
    (l : List FKRectIntegralSquareDart) (p : Int × Int) : Prop :=
  p ∈ l.flatMap (fun d => [d.1, fkRectIntegralSquareDartEnd d])

end
end StatMech.FrontierD
