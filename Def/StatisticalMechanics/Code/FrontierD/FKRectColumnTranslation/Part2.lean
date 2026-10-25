/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnTranslationEquiv (R : FKRectTorus) (s : Int) :
    Fin R.width ≃ Fin R.width where
  toFun := fkRectColumnTranslate R s
  invFun := fkRectColumnTranslate R (-s)
  left_inv := fkRectColumnTranslate_neg_left R s
  right_inv := fkRectColumnTranslate_neg_right R s

end
end StatMech.FrontierD
