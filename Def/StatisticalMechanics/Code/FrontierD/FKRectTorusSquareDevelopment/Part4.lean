/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectSquareDeckTranslation (R : FKRectTorus) (u : Int × Int) :
    Int × Int :=
  ((R.width : Int) * u.1 + (R.height / 2 : Nat) * u.2,
    (R.width : Int) * u.1 - (R.height / 2 : Nat) * u.2)


def fkRectSquareDeckHom (R : FKRectTorus) :
    (Int × Int) →+ (Int × Int) where
  toFun := fkRectSquareDeckTranslation R
  map_zero' := by
    simp [fkRectSquareDeckTranslation]
  map_add' := by
    intro u v
    apply Prod.ext <;> simp [fkRectSquareDeckTranslation] <;> ring

end
end StatMech.FrontierD
