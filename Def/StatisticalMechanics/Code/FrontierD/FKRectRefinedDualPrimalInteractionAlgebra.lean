/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualPrimalInteractionAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenWalkCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualPrimalInteractionAlgebra
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

def fkRectRefinedDeckTranslation (R : FKRectTorus) (u : Int × Int) :
    Int × Int :=
  (4 * (fkRectSquareDeckTranslation R u).1,
    4 * (fkRectSquareDeckTranslation R u).2)


end
end StatMech.FrontierD
