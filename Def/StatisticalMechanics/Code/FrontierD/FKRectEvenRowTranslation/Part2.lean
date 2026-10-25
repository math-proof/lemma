/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectRowTranslationEquiv (R : FKRectTorus) (s : Int) :
    Fin R.height ≃ Fin R.height where
  toFun := fkRectRowTranslate R s
  invFun := fkRectRowTranslate R (-s)
  left_inv := fkRectRowTranslate_neg_left R s
  right_inv := fkRectRowTranslate_neg_right R s

end
end StatMech.FrontierD
