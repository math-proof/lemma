/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part4
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnTranslationConfigurationEquiv
    (R : FKRectTorus) (s : Int) : R.Configuration ≃ R.Configuration :=
  Equiv.arrowCongr (fkRectColumnTranslationEdgeEquiv R s)
    (Equiv.refl Bool)

end
end StatMech.FrontierD
